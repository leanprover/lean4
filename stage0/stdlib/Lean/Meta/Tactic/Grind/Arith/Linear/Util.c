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
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableEqRat_decEq(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg(lean_object* v_x_317_, size_t v_x_318_, lean_object* v_x_319_){
_start:
{
if (lean_obj_tag(v_x_317_) == 0)
{
lean_object* v_es_320_; lean_object* v___x_321_; size_t v___x_322_; size_t v___x_323_; lean_object* v_j_324_; lean_object* v___x_325_; 
v_es_320_ = lean_ctor_get(v_x_317_, 0);
v___x_321_ = lean_box(2);
v___x_322_ = ((size_t)31ULL);
v___x_323_ = lean_usize_land(v_x_318_, v___x_322_);
v_j_324_ = lean_usize_to_nat(v___x_323_);
v___x_325_ = lean_array_get_borrowed(v___x_321_, v_es_320_, v_j_324_);
lean_dec(v_j_324_);
switch(lean_obj_tag(v___x_325_))
{
case 0:
{
lean_object* v_key_326_; lean_object* v_val_327_; uint8_t v___x_328_; 
v_key_326_ = lean_ctor_get(v___x_325_, 0);
v_val_327_ = lean_ctor_get(v___x_325_, 1);
v___x_328_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_319_, v_key_326_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; 
v___x_329_ = lean_box(0);
return v___x_329_;
}
else
{
lean_object* v___x_330_; 
lean_inc(v_val_327_);
v___x_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_330_, 0, v_val_327_);
return v___x_330_;
}
}
case 1:
{
lean_object* v_node_331_; size_t v___x_332_; size_t v___x_333_; 
v_node_331_ = lean_ctor_get(v___x_325_, 0);
v___x_332_ = ((size_t)5ULL);
v___x_333_ = lean_usize_shift_right(v_x_318_, v___x_332_);
v_x_317_ = v_node_331_;
v_x_318_ = v___x_333_;
goto _start;
}
default: 
{
lean_object* v___x_335_; 
v___x_335_ = lean_box(0);
return v___x_335_;
}
}
}
else
{
lean_object* v_ks_336_; lean_object* v_vs_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v_ks_336_ = lean_ctor_get(v_x_317_, 0);
v_vs_337_ = lean_ctor_get(v_x_317_, 1);
v___x_338_ = lean_unsigned_to_nat(0u);
v___x_339_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_336_, v_vs_337_, v___x_338_, v_x_319_);
return v___x_339_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_340_, lean_object* v_x_341_, lean_object* v_x_342_){
_start:
{
size_t v_x_866__boxed_343_; lean_object* v_res_344_; 
v_x_866__boxed_343_ = lean_unbox_usize(v_x_341_);
lean_dec(v_x_341_);
v_res_344_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg(v_x_340_, v_x_866__boxed_343_, v_x_342_);
lean_dec_ref(v_x_342_);
lean_dec_ref(v_x_340_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg(lean_object* v_x_345_, lean_object* v_x_346_){
_start:
{
uint64_t v___x_347_; size_t v___x_348_; lean_object* v___x_349_; 
v___x_347_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_346_);
v___x_348_ = lean_uint64_to_usize(v___x_347_);
v___x_349_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg(v_x_345_, v___x_348_, v_x_346_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg___boxed(lean_object* v_x_350_, lean_object* v_x_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg(v_x_350_, v_x_351_);
lean_dec_ref(v_x_351_);
lean_dec_ref(v_x_350_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(lean_object* v_e_353_, lean_object* v_a_354_, lean_object* v_a_355_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_367_; 
v_a_358_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_367_ == 0)
{
v___x_360_ = v___x_357_;
v_isShared_361_ = v_isSharedCheck_367_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_357_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_367_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v_exprToStructId_362_; lean_object* v___x_363_; lean_object* v___x_365_; 
v_exprToStructId_362_ = lean_ctor_get(v_a_358_, 2);
lean_inc_ref(v_exprToStructId_362_);
lean_dec(v_a_358_);
v___x_363_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg(v_exprToStructId_362_, v_e_353_);
lean_dec_ref(v_exprToStructId_362_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 0, v___x_363_);
v___x_365_ = v___x_360_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_363_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
else
{
lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_375_; 
v_a_368_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_375_ == 0)
{
v___x_370_ = v___x_357_;
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_357_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_373_; 
if (v_isShared_371_ == 0)
{
v___x_373_ = v___x_370_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_a_368_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg___boxed(lean_object* v_e_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_e_376_, v_a_377_, v_a_378_);
lean_dec_ref(v_a_378_);
lean_dec(v_a_377_);
lean_dec_ref(v_e_376_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f(lean_object* v_e_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_e_381_, v_a_382_, v_a_390_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___boxed(lean_object* v_e_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f(v_e_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
lean_dec(v_a_404_);
lean_dec_ref(v_a_403_);
lean_dec(v_a_402_);
lean_dec_ref(v_a_401_);
lean_dec(v_a_400_);
lean_dec_ref(v_a_399_);
lean_dec(v_a_398_);
lean_dec_ref(v_a_397_);
lean_dec(v_a_396_);
lean_dec(v_a_395_);
lean_dec_ref(v_e_394_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0(lean_object* v_00_u03b2_407_, lean_object* v_x_408_, lean_object* v_x_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg(v_x_408_, v_x_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___boxed(lean_object* v_00_u03b2_411_, lean_object* v_x_412_, lean_object* v_x_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0(v_00_u03b2_411_, v_x_412_, v_x_413_);
lean_dec_ref(v_x_413_);
lean_dec_ref(v_x_412_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_415_, lean_object* v_x_416_, size_t v_x_417_, lean_object* v_x_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg(v_x_416_, v_x_417_, v_x_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_420_, lean_object* v_x_421_, lean_object* v_x_422_, lean_object* v_x_423_){
_start:
{
size_t v_x_977__boxed_424_; lean_object* v_res_425_; 
v_x_977__boxed_424_ = lean_unbox_usize(v_x_422_);
lean_dec(v_x_422_);
v_res_425_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0(v_00_u03b2_420_, v_x_421_, v_x_977__boxed_424_, v_x_423_);
lean_dec_ref(v_x_423_);
lean_dec_ref(v_x_421_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_426_, lean_object* v_keys_427_, lean_object* v_vals_428_, lean_object* v_heq_429_, lean_object* v_i_430_, lean_object* v_k_431_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_427_, v_vals_428_, v_i_430_, v_k_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_433_, lean_object* v_keys_434_, lean_object* v_vals_435_, lean_object* v_heq_436_, lean_object* v_i_437_, lean_object* v_k_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_433_, v_keys_434_, v_vals_435_, v_heq_436_, v_i_437_, v_k_438_);
lean_dec_ref(v_k_438_);
lean_dec_ref(v_vals_435_);
lean_dec_ref(v_keys_434_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_440_, lean_object* v_x_441_, lean_object* v_x_442_, lean_object* v_x_443_){
_start:
{
lean_object* v_ks_444_; lean_object* v_vs_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_469_; 
v_ks_444_ = lean_ctor_get(v_x_440_, 0);
v_vs_445_ = lean_ctor_get(v_x_440_, 1);
v_isSharedCheck_469_ = !lean_is_exclusive(v_x_440_);
if (v_isSharedCheck_469_ == 0)
{
v___x_447_ = v_x_440_;
v_isShared_448_ = v_isSharedCheck_469_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_vs_445_);
lean_inc(v_ks_444_);
lean_dec(v_x_440_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_469_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_449_; uint8_t v___x_450_; 
v___x_449_ = lean_array_get_size(v_ks_444_);
v___x_450_ = lean_nat_dec_lt(v_x_441_, v___x_449_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_454_; 
lean_dec(v_x_441_);
v___x_451_ = lean_array_push(v_ks_444_, v_x_442_);
v___x_452_ = lean_array_push(v_vs_445_, v_x_443_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 1, v___x_452_);
lean_ctor_set(v___x_447_, 0, v___x_451_);
v___x_454_ = v___x_447_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_451_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v___x_452_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
else
{
lean_object* v_k_x27_456_; uint8_t v___x_457_; 
v_k_x27_456_ = lean_array_fget_borrowed(v_ks_444_, v_x_441_);
v___x_457_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_442_, v_k_x27_456_);
if (v___x_457_ == 0)
{
lean_object* v___x_459_; 
if (v_isShared_448_ == 0)
{
v___x_459_ = v___x_447_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_ks_444_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v_vs_445_);
v___x_459_ = v_reuseFailAlloc_463_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = lean_unsigned_to_nat(1u);
v___x_461_ = lean_nat_add(v_x_441_, v___x_460_);
lean_dec(v_x_441_);
v_x_440_ = v___x_459_;
v_x_441_ = v___x_461_;
goto _start;
}
}
else
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_467_; 
v___x_464_ = lean_array_fset(v_ks_444_, v_x_441_, v_x_442_);
v___x_465_ = lean_array_fset(v_vs_445_, v_x_441_, v_x_443_);
lean_dec(v_x_441_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 1, v___x_465_);
lean_ctor_set(v___x_447_, 0, v___x_464_);
v___x_467_ = v___x_447_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_464_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v___x_465_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_470_, lean_object* v_k_471_, lean_object* v_v_472_){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = lean_unsigned_to_nat(0u);
v___x_474_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_470_, v___x_473_, v_k_471_, v_v_472_);
return v___x_474_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(lean_object* v_x_476_, size_t v_x_477_, size_t v_x_478_, lean_object* v_x_479_, lean_object* v_x_480_){
_start:
{
if (lean_obj_tag(v_x_476_) == 0)
{
lean_object* v_es_481_; size_t v___x_482_; size_t v___x_483_; lean_object* v_j_484_; lean_object* v___x_485_; uint8_t v___x_486_; 
v_es_481_ = lean_ctor_get(v_x_476_, 0);
v___x_482_ = ((size_t)31ULL);
v___x_483_ = lean_usize_land(v_x_477_, v___x_482_);
v_j_484_ = lean_usize_to_nat(v___x_483_);
v___x_485_ = lean_array_get_size(v_es_481_);
v___x_486_ = lean_nat_dec_lt(v_j_484_, v___x_485_);
if (v___x_486_ == 0)
{
lean_dec(v_j_484_);
lean_dec(v_x_480_);
lean_dec_ref(v_x_479_);
return v_x_476_;
}
else
{
lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_525_; 
lean_inc_ref(v_es_481_);
v_isSharedCheck_525_ = !lean_is_exclusive(v_x_476_);
if (v_isSharedCheck_525_ == 0)
{
lean_object* v_unused_526_; 
v_unused_526_ = lean_ctor_get(v_x_476_, 0);
lean_dec(v_unused_526_);
v___x_488_ = v_x_476_;
v_isShared_489_ = v_isSharedCheck_525_;
goto v_resetjp_487_;
}
else
{
lean_dec(v_x_476_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_525_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v_v_490_; lean_object* v___x_491_; lean_object* v_xs_x27_492_; lean_object* v___y_494_; 
v_v_490_ = lean_array_fget(v_es_481_, v_j_484_);
v___x_491_ = lean_box(0);
v_xs_x27_492_ = lean_array_fset(v_es_481_, v_j_484_, v___x_491_);
switch(lean_obj_tag(v_v_490_))
{
case 0:
{
lean_object* v_key_499_; lean_object* v_val_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_510_; 
v_key_499_ = lean_ctor_get(v_v_490_, 0);
v_val_500_ = lean_ctor_get(v_v_490_, 1);
v_isSharedCheck_510_ = !lean_is_exclusive(v_v_490_);
if (v_isSharedCheck_510_ == 0)
{
v___x_502_ = v_v_490_;
v_isShared_503_ = v_isSharedCheck_510_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_val_500_);
lean_inc(v_key_499_);
lean_dec(v_v_490_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_510_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
uint8_t v___x_504_; 
v___x_504_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_479_, v_key_499_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; lean_object* v___x_506_; 
lean_del_object(v___x_502_);
v___x_505_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_499_, v_val_500_, v_x_479_, v_x_480_);
v___x_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
v___y_494_ = v___x_506_;
goto v___jp_493_;
}
else
{
lean_object* v___x_508_; 
lean_dec(v_val_500_);
lean_dec(v_key_499_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 1, v_x_480_);
lean_ctor_set(v___x_502_, 0, v_x_479_);
v___x_508_ = v___x_502_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_x_479_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v_x_480_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
v___y_494_ = v___x_508_;
goto v___jp_493_;
}
}
}
}
case 1:
{
lean_object* v_node_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_523_; 
v_node_511_ = lean_ctor_get(v_v_490_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v_v_490_);
if (v_isSharedCheck_523_ == 0)
{
v___x_513_ = v_v_490_;
v_isShared_514_ = v_isSharedCheck_523_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_node_511_);
lean_dec(v_v_490_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_523_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
size_t v___x_515_; size_t v___x_516_; size_t v___x_517_; size_t v___x_518_; lean_object* v___x_519_; lean_object* v___x_521_; 
v___x_515_ = ((size_t)5ULL);
v___x_516_ = lean_usize_shift_right(v_x_477_, v___x_515_);
v___x_517_ = ((size_t)1ULL);
v___x_518_ = lean_usize_add(v_x_478_, v___x_517_);
v___x_519_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_node_511_, v___x_516_, v___x_518_, v_x_479_, v_x_480_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 0, v___x_519_);
v___x_521_ = v___x_513_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_519_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
v___y_494_ = v___x_521_;
goto v___jp_493_;
}
}
}
default: 
{
lean_object* v___x_524_; 
v___x_524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_524_, 0, v_x_479_);
lean_ctor_set(v___x_524_, 1, v_x_480_);
v___y_494_ = v___x_524_;
goto v___jp_493_;
}
}
v___jp_493_:
{
lean_object* v___x_495_; lean_object* v___x_497_; 
v___x_495_ = lean_array_fset(v_xs_x27_492_, v_j_484_, v___y_494_);
lean_dec(v_j_484_);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 0, v___x_495_);
v___x_497_ = v___x_488_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_495_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
}
}
else
{
lean_object* v_ks_527_; lean_object* v_vs_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_548_; 
v_ks_527_ = lean_ctor_get(v_x_476_, 0);
v_vs_528_ = lean_ctor_get(v_x_476_, 1);
v_isSharedCheck_548_ = !lean_is_exclusive(v_x_476_);
if (v_isSharedCheck_548_ == 0)
{
v___x_530_ = v_x_476_;
v_isShared_531_ = v_isSharedCheck_548_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_vs_528_);
lean_inc(v_ks_527_);
lean_dec(v_x_476_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_548_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_533_; 
if (v_isShared_531_ == 0)
{
v___x_533_ = v___x_530_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_ks_527_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v_vs_528_);
v___x_533_ = v_reuseFailAlloc_547_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
lean_object* v_newNode_534_; uint8_t v___y_536_; size_t v___x_542_; uint8_t v___x_543_; 
v_newNode_534_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1___redArg(v___x_533_, v_x_479_, v_x_480_);
v___x_542_ = ((size_t)7ULL);
v___x_543_ = lean_usize_dec_le(v___x_542_, v_x_478_);
if (v___x_543_ == 0)
{
lean_object* v___x_544_; lean_object* v___x_545_; uint8_t v___x_546_; 
v___x_544_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_534_);
v___x_545_ = lean_unsigned_to_nat(4u);
v___x_546_ = lean_nat_dec_lt(v___x_544_, v___x_545_);
lean_dec(v___x_544_);
v___y_536_ = v___x_546_;
goto v___jp_535_;
}
else
{
v___y_536_ = v___x_543_;
goto v___jp_535_;
}
v___jp_535_:
{
if (v___y_536_ == 0)
{
lean_object* v_ks_537_; lean_object* v_vs_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v_ks_537_ = lean_ctor_get(v_newNode_534_, 0);
lean_inc_ref(v_ks_537_);
v_vs_538_ = lean_ctor_get(v_newNode_534_, 1);
lean_inc_ref(v_vs_538_);
lean_dec_ref(v_newNode_534_);
v___x_539_ = lean_unsigned_to_nat(0u);
v___x_540_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___closed__0);
v___x_541_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg(v_x_478_, v_ks_537_, v_vs_538_, v___x_539_, v___x_540_);
lean_dec_ref(v_vs_538_);
lean_dec_ref(v_ks_537_);
return v___x_541_;
}
else
{
return v_newNode_534_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg(size_t v_depth_549_, lean_object* v_keys_550_, lean_object* v_vals_551_, lean_object* v_i_552_, lean_object* v_entries_553_){
_start:
{
lean_object* v___x_554_; uint8_t v___x_555_; 
v___x_554_ = lean_array_get_size(v_keys_550_);
v___x_555_ = lean_nat_dec_lt(v_i_552_, v___x_554_);
if (v___x_555_ == 0)
{
lean_dec(v_i_552_);
return v_entries_553_;
}
else
{
lean_object* v_k_556_; lean_object* v_v_557_; uint64_t v___x_558_; size_t v_h_559_; size_t v___x_560_; lean_object* v___x_561_; size_t v___x_562_; size_t v___x_563_; size_t v___x_564_; size_t v_h_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v_k_556_ = lean_array_fget_borrowed(v_keys_550_, v_i_552_);
v_v_557_ = lean_array_fget_borrowed(v_vals_551_, v_i_552_);
v___x_558_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_556_);
v_h_559_ = lean_uint64_to_usize(v___x_558_);
v___x_560_ = ((size_t)5ULL);
v___x_561_ = lean_unsigned_to_nat(1u);
v___x_562_ = ((size_t)1ULL);
v___x_563_ = lean_usize_sub(v_depth_549_, v___x_562_);
v___x_564_ = lean_usize_mul(v___x_560_, v___x_563_);
v_h_565_ = lean_usize_shift_right(v_h_559_, v___x_564_);
v___x_566_ = lean_nat_add(v_i_552_, v___x_561_);
lean_dec(v_i_552_);
lean_inc(v_v_557_);
lean_inc(v_k_556_);
v___x_567_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_entries_553_, v_h_565_, v_depth_549_, v_k_556_, v_v_557_);
v_i_552_ = v___x_566_;
v_entries_553_ = v___x_567_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_569_, lean_object* v_keys_570_, lean_object* v_vals_571_, lean_object* v_i_572_, lean_object* v_entries_573_){
_start:
{
size_t v_depth_boxed_574_; lean_object* v_res_575_; 
v_depth_boxed_574_ = lean_unbox_usize(v_depth_569_);
lean_dec(v_depth_569_);
v_res_575_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_574_, v_keys_570_, v_vals_571_, v_i_572_, v_entries_573_);
lean_dec_ref(v_vals_571_);
lean_dec_ref(v_keys_570_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___boxed(lean_object* v_x_576_, lean_object* v_x_577_, lean_object* v_x_578_, lean_object* v_x_579_, lean_object* v_x_580_){
_start:
{
size_t v_x_7022__boxed_581_; size_t v_x_7023__boxed_582_; lean_object* v_res_583_; 
v_x_7022__boxed_581_ = lean_unbox_usize(v_x_577_);
lean_dec(v_x_577_);
v_x_7023__boxed_582_ = lean_unbox_usize(v_x_578_);
lean_dec(v_x_578_);
v_res_583_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_x_576_, v_x_7022__boxed_581_, v_x_7023__boxed_582_, v_x_579_, v_x_580_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0___redArg(lean_object* v_x_584_, lean_object* v_x_585_, lean_object* v_x_586_){
_start:
{
uint64_t v___x_587_; size_t v___x_588_; size_t v___x_589_; lean_object* v___x_590_; 
v___x_587_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_585_);
v___x_588_ = lean_uint64_to_usize(v___x_587_);
v___x_589_ = ((size_t)1ULL);
v___x_590_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_x_584_, v___x_588_, v___x_589_, v_x_585_, v_x_586_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___lam__0(lean_object* v_e_591_, lean_object* v_a_592_, lean_object* v_s_593_){
_start:
{
lean_object* v_structs_594_; lean_object* v_typeIdOf_595_; lean_object* v_exprToStructId_596_; lean_object* v_exprToStructIdEntries_597_; lean_object* v_forbiddenNatModules_598_; lean_object* v_natStructs_599_; lean_object* v_natTypeIdOf_600_; lean_object* v_exprToNatStructId_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_611_; 
v_structs_594_ = lean_ctor_get(v_s_593_, 0);
v_typeIdOf_595_ = lean_ctor_get(v_s_593_, 1);
v_exprToStructId_596_ = lean_ctor_get(v_s_593_, 2);
v_exprToStructIdEntries_597_ = lean_ctor_get(v_s_593_, 3);
v_forbiddenNatModules_598_ = lean_ctor_get(v_s_593_, 4);
v_natStructs_599_ = lean_ctor_get(v_s_593_, 5);
v_natTypeIdOf_600_ = lean_ctor_get(v_s_593_, 6);
v_exprToNatStructId_601_ = lean_ctor_get(v_s_593_, 7);
v_isSharedCheck_611_ = !lean_is_exclusive(v_s_593_);
if (v_isSharedCheck_611_ == 0)
{
v___x_603_ = v_s_593_;
v_isShared_604_ = v_isSharedCheck_611_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_exprToNatStructId_601_);
lean_inc(v_natTypeIdOf_600_);
lean_inc(v_natStructs_599_);
lean_inc(v_forbiddenNatModules_598_);
lean_inc(v_exprToStructIdEntries_597_);
lean_inc(v_exprToStructId_596_);
lean_inc(v_typeIdOf_595_);
lean_inc(v_structs_594_);
lean_dec(v_s_593_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_611_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_609_; 
lean_inc_n(v_a_592_, 2);
lean_inc_ref(v_e_591_);
v___x_605_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0___redArg(v_exprToStructId_596_, v_e_591_, v_a_592_);
v___x_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_606_, 0, v_e_591_);
lean_ctor_set(v___x_606_, 1, v_a_592_);
v___x_607_ = l_Lean_PersistentArray_push___redArg(v_exprToStructIdEntries_597_, v___x_606_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 3, v___x_607_);
lean_ctor_set(v___x_603_, 2, v___x_605_);
v___x_609_ = v___x_603_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_structs_594_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_typeIdOf_595_);
lean_ctor_set(v_reuseFailAlloc_610_, 2, v___x_605_);
lean_ctor_set(v_reuseFailAlloc_610_, 3, v___x_607_);
lean_ctor_set(v_reuseFailAlloc_610_, 4, v_forbiddenNatModules_598_);
lean_ctor_set(v_reuseFailAlloc_610_, 5, v_natStructs_599_);
lean_ctor_set(v_reuseFailAlloc_610_, 6, v_natTypeIdOf_600_);
lean_ctor_set(v_reuseFailAlloc_610_, 7, v_exprToNatStructId_601_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___lam__0___boxed(lean_object* v_e_612_, lean_object* v_a_613_, lean_object* v_s_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___lam__0(v_e_612_, v_a_613_, v_s_614_);
lean_dec(v_a_613_);
return v_res_615_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__1(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__0));
v___x_618_ = l_Lean_stringToMessageData(v___x_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg(lean_object* v_e_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_e_619_, v_a_621_, v_a_626_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_a_633_);
lean_dec_ref_known(v___x_632_, 1);
if (lean_obj_tag(v_a_633_) == 1)
{
lean_object* v_val_634_; uint8_t v___x_635_; 
v_val_634_ = lean_ctor_get(v_a_633_, 0);
lean_inc(v_val_634_);
lean_dec_ref_known(v_a_633_, 1);
v___x_635_ = lean_nat_dec_eq(v_val_634_, v_a_620_);
lean_dec(v_val_634_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; 
v___x_636_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_622_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v_a_637_; uint8_t v_verbose_638_; 
v_a_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc(v_a_637_);
lean_dec_ref_known(v___x_636_, 1);
v_verbose_638_ = lean_ctor_get_uint8(v_a_637_, 0);
lean_dec(v_a_637_);
if (v_verbose_638_ == 0)
{
lean_dec_ref(v_e_619_);
goto v___jp_629_;
}
else
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_639_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__1);
v___x_640_ = l_Lean_indentExpr(v_e_619_);
v___x_641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_639_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
v___x_642_ = l_Lean_Meta_Sym_reportIssue(v___x_641_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_dec_ref_known(v___x_642_, 1);
goto v___jp_629_;
}
else
{
return v___x_642_;
}
}
}
else
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
lean_dec_ref(v_e_619_);
v_a_643_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_650_ == 0)
{
v___x_645_ = v___x_636_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_636_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_643_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
else
{
lean_dec_ref(v_e_619_);
goto v___jp_629_;
}
}
else
{
lean_object* v___f_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
lean_dec(v_a_633_);
lean_inc(v_a_620_);
v___f_651_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_651_, 0, v_e_619_);
lean_closure_set(v___f_651_, 1, v_a_620_);
v___x_652_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_653_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_652_, v___f_651_, v_a_621_);
return v___x_653_;
}
}
else
{
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_661_; 
lean_dec_ref(v_e_619_);
v_a_654_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_661_ == 0)
{
v___x_656_ = v___x_632_;
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_632_);
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
v___jp_629_:
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = lean_box(0);
v___x_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
return v___x_631_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___boxed(lean_object* v_e_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg(v_e_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_);
lean_dec(v_a_670_);
lean_dec_ref(v_a_669_);
lean_dec(v_a_668_);
lean_dec_ref(v_a_667_);
lean_dec(v_a_666_);
lean_dec_ref(v_a_665_);
lean_dec(v_a_664_);
lean_dec(v_a_663_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId(lean_object* v_e_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg(v_e_673_, v_a_674_, v_a_675_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___boxed(lean_object* v_e_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId(v_e_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
lean_dec(v_a_696_);
lean_dec_ref(v_a_695_);
lean_dec(v_a_694_);
lean_dec_ref(v_a_693_);
lean_dec(v_a_692_);
lean_dec_ref(v_a_691_);
lean_dec(v_a_690_);
lean_dec(v_a_689_);
lean_dec(v_a_688_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0(lean_object* v_00_u03b2_701_, lean_object* v_x_702_, lean_object* v_x_703_, lean_object* v_x_704_){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0___redArg(v_x_702_, v_x_703_, v_x_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0(lean_object* v_00_u03b2_706_, lean_object* v_x_707_, size_t v_x_708_, size_t v_x_709_, lean_object* v_x_710_, lean_object* v_x_711_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_x_707_, v_x_708_, v_x_709_, v_x_710_, v_x_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_713_, lean_object* v_x_714_, lean_object* v_x_715_, lean_object* v_x_716_, lean_object* v_x_717_, lean_object* v_x_718_){
_start:
{
size_t v_x_7303__boxed_719_; size_t v_x_7304__boxed_720_; lean_object* v_res_721_; 
v_x_7303__boxed_719_ = lean_unbox_usize(v_x_715_);
lean_dec(v_x_715_);
v_x_7304__boxed_720_ = lean_unbox_usize(v_x_716_);
lean_dec(v_x_716_);
v_res_721_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0(v_00_u03b2_713_, v_x_714_, v_x_7303__boxed_719_, v_x_7304__boxed_720_, v_x_717_, v_x_718_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_722_, lean_object* v_n_723_, lean_object* v_k_724_, lean_object* v_v_725_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1___redArg(v_n_723_, v_k_724_, v_v_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_727_, size_t v_depth_728_, lean_object* v_keys_729_, lean_object* v_vals_730_, lean_object* v_heq_731_, lean_object* v_i_732_, lean_object* v_entries_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg(v_depth_728_, v_keys_729_, v_vals_730_, v_i_732_, v_entries_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_735_, lean_object* v_depth_736_, lean_object* v_keys_737_, lean_object* v_vals_738_, lean_object* v_heq_739_, lean_object* v_i_740_, lean_object* v_entries_741_){
_start:
{
size_t v_depth_boxed_742_; lean_object* v_res_743_; 
v_depth_boxed_742_ = lean_unbox_usize(v_depth_736_);
lean_dec(v_depth_736_);
v_res_743_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2(v_00_u03b2_735_, v_depth_boxed_742_, v_keys_737_, v_vals_738_, v_heq_739_, v_i_740_, v_entries_741_);
lean_dec_ref(v_vals_738_);
lean_dec_ref(v_keys_737_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_744_, lean_object* v_x_745_, lean_object* v_x_746_, lean_object* v_x_747_, lean_object* v_x_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_745_, v_x_746_, v_x_747_, v_x_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0(lean_object* v_msgData_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v___x_756_; lean_object* v_env_757_; lean_object* v___x_758_; lean_object* v_mctx_759_; lean_object* v_lctx_760_; lean_object* v_options_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_756_ = lean_st_ref_get(v___y_754_);
v_env_757_ = lean_ctor_get(v___x_756_, 0);
lean_inc_ref(v_env_757_);
lean_dec(v___x_756_);
v___x_758_ = lean_st_ref_get(v___y_752_);
v_mctx_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc_ref(v_mctx_759_);
lean_dec(v___x_758_);
v_lctx_760_ = lean_ctor_get(v___y_751_, 2);
v_options_761_ = lean_ctor_get(v___y_753_, 2);
lean_inc_ref(v_options_761_);
lean_inc_ref(v_lctx_760_);
v___x_762_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_762_, 0, v_env_757_);
lean_ctor_set(v___x_762_, 1, v_mctx_759_);
lean_ctor_set(v___x_762_, 2, v_lctx_760_);
lean_ctor_set(v___x_762_, 3, v_options_761_);
v___x_763_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_763_, 0, v___x_762_);
lean_ctor_set(v___x_763_, 1, v_msgData_750_);
v___x_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_764_, 0, v___x_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0___boxed(lean_object* v_msgData_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0(v_msgData_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(lean_object* v_msg_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v_ref_778_; lean_object* v___x_779_; lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_788_; 
v_ref_778_ = lean_ctor_get(v___y_775_, 5);
v___x_779_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0(v_msg_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
v_a_780_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_788_ == 0)
{
v___x_782_ = v___x_779_;
v_isShared_783_ = v_isSharedCheck_788_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_779_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_788_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_784_; lean_object* v___x_786_; 
lean_inc(v_ref_778_);
v___x_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_784_, 0, v_ref_778_);
lean_ctor_set(v___x_784_, 1, v_a_780_);
if (v_isShared_783_ == 0)
{
lean_ctor_set_tag(v___x_782_, 1);
lean_ctor_set(v___x_782_, 0, v___x_784_);
v___x_786_ = v___x_782_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_784_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg___boxed(lean_object* v_msg_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v_msg_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_);
lean_dec(v___y_793_);
lean_dec_ref(v___y_792_);
lean_dec(v___y_791_);
lean_dec_ref(v___y_790_);
return v_res_795_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1(void){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__0));
v___x_798_ = l_Lean_stringToMessageData(v___x_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst(lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_823_; 
v_a_812_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_823_ == 0)
{
v___x_814_ = v___x_811_;
v_isShared_815_ = v_isSharedCheck_823_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_811_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_823_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v_noNatDivInst_x3f_816_; 
v_noNatDivInst_x3f_816_ = lean_ctor_get(v_a_812_, 11);
lean_inc(v_noNatDivInst_x3f_816_);
lean_dec(v_a_812_);
if (lean_obj_tag(v_noNatDivInst_x3f_816_) == 1)
{
lean_object* v_val_817_; lean_object* v___x_819_; 
v_val_817_ = lean_ctor_get(v_noNatDivInst_x3f_816_, 0);
lean_inc(v_val_817_);
lean_dec_ref_known(v_noNatDivInst_x3f_816_, 1);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 0, v_val_817_);
v___x_819_ = v___x_814_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_val_817_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
else
{
lean_object* v___x_821_; lean_object* v___x_822_; 
lean_dec(v_noNatDivInst_x3f_816_);
lean_del_object(v___x_814_);
v___x_821_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1);
v___x_822_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_821_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
return v___x_822_;
}
}
}
else
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_831_; 
v_a_824_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_831_ == 0)
{
v___x_826_ = v___x_811_;
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_811_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
if (v_isShared_827_ == 0)
{
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_a_824_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___boxed(lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst(v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_);
lean_dec(v_a_842_);
lean_dec_ref(v_a_841_);
lean_dec(v_a_840_);
lean_dec_ref(v_a_839_);
lean_dec(v_a_838_);
lean_dec_ref(v_a_837_);
lean_dec(v_a_836_);
lean_dec_ref(v_a_835_);
lean_dec(v_a_834_);
lean_dec(v_a_833_);
lean_dec(v_a_832_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0(lean_object* v_00_u03b1_845_, lean_object* v_msg_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v_msg_846_, v___y_854_, v___y_855_, v___y_856_, v___y_857_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___boxed(lean_object* v_00_u03b1_860_, lean_object* v_msg_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0(v_00_u03b1_860_, v_msg_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec(v___y_864_);
lean_dec(v___y_863_);
lean_dec(v___y_862_);
return v_res_874_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1(void){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__0));
v___x_877_ = l_Lean_stringToMessageData(v___x_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLEInst(lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_902_; 
v_a_891_ = lean_ctor_get(v___x_890_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_902_ == 0)
{
v___x_893_ = v___x_890_;
v_isShared_894_ = v_isSharedCheck_902_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_890_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_902_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v_leInst_x3f_895_; 
v_leInst_x3f_895_ = lean_ctor_get(v_a_891_, 5);
lean_inc(v_leInst_x3f_895_);
lean_dec(v_a_891_);
if (lean_obj_tag(v_leInst_x3f_895_) == 1)
{
lean_object* v_val_896_; lean_object* v___x_898_; 
v_val_896_ = lean_ctor_get(v_leInst_x3f_895_, 0);
lean_inc(v_val_896_);
lean_dec_ref_known(v_leInst_x3f_895_, 1);
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 0, v_val_896_);
v___x_898_ = v___x_893_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_val_896_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
else
{
lean_object* v___x_900_; lean_object* v___x_901_; 
lean_dec(v_leInst_x3f_895_);
lean_del_object(v___x_893_);
v___x_900_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1);
v___x_901_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_900_, v_a_885_, v_a_886_, v_a_887_, v_a_888_);
return v___x_901_;
}
}
}
else
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
v_a_903_ = lean_ctor_get(v___x_890_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_890_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_890_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_a_903_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLEInst___boxed(lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lean_Meta_Grind_Arith_Linear_getLEInst(v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
lean_dec(v_a_921_);
lean_dec_ref(v_a_920_);
lean_dec(v_a_919_);
lean_dec_ref(v_a_918_);
lean_dec(v_a_917_);
lean_dec_ref(v_a_916_);
lean_dec(v_a_915_);
lean_dec_ref(v_a_914_);
lean_dec(v_a_913_);
lean_dec(v_a_912_);
lean_dec(v_a_911_);
return v_res_923_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1(void){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_925_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__0));
v___x_926_ = l_Lean_stringToMessageData(v___x_925_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLTInst(lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_);
if (lean_obj_tag(v___x_939_) == 0)
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_951_; 
v_a_940_ = lean_ctor_get(v___x_939_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_951_ == 0)
{
v___x_942_ = v___x_939_;
v_isShared_943_ = v_isSharedCheck_951_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_939_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_951_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v_ltInst_x3f_944_; 
v_ltInst_x3f_944_ = lean_ctor_get(v_a_940_, 6);
lean_inc(v_ltInst_x3f_944_);
lean_dec(v_a_940_);
if (lean_obj_tag(v_ltInst_x3f_944_) == 1)
{
lean_object* v_val_945_; lean_object* v___x_947_; 
v_val_945_ = lean_ctor_get(v_ltInst_x3f_944_, 0);
lean_inc(v_val_945_);
lean_dec_ref_known(v_ltInst_x3f_944_, 1);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 0, v_val_945_);
v___x_947_ = v___x_942_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_val_945_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
else
{
lean_object* v___x_949_; lean_object* v___x_950_; 
lean_dec(v_ltInst_x3f_944_);
lean_del_object(v___x_942_);
v___x_949_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1);
v___x_950_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_949_, v_a_934_, v_a_935_, v_a_936_, v_a_937_);
return v___x_950_;
}
}
}
else
{
lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_959_; 
v_a_952_ = lean_ctor_get(v___x_939_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_959_ == 0)
{
v___x_954_ = v___x_939_;
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_a_952_);
lean_dec(v___x_939_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
if (v_isShared_955_ == 0)
{
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_a_952_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLTInst___boxed(lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Lean_Meta_Grind_Arith_Linear_getLTInst(v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
lean_dec(v_a_968_);
lean_dec_ref(v_a_967_);
lean_dec(v_a_966_);
lean_dec_ref(v_a_965_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
lean_dec(v_a_962_);
lean_dec(v_a_961_);
lean_dec(v_a_960_);
return v_res_972_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1(void){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__0));
v___x_975_ = l_Lean_stringToMessageData(v___x_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst(lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1000_; 
v_a_989_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_991_ = v___x_988_;
v_isShared_992_ = v_isSharedCheck_1000_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_988_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1000_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v_lawfulOrderLTInst_x3f_993_; 
v_lawfulOrderLTInst_x3f_993_ = lean_ctor_get(v_a_989_, 7);
lean_inc(v_lawfulOrderLTInst_x3f_993_);
lean_dec(v_a_989_);
if (lean_obj_tag(v_lawfulOrderLTInst_x3f_993_) == 1)
{
lean_object* v_val_994_; lean_object* v___x_996_; 
v_val_994_ = lean_ctor_get(v_lawfulOrderLTInst_x3f_993_, 0);
lean_inc(v_val_994_);
lean_dec_ref_known(v_lawfulOrderLTInst_x3f_993_, 1);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 0, v_val_994_);
v___x_996_ = v___x_991_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_val_994_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
else
{
lean_object* v___x_998_; lean_object* v___x_999_; 
lean_dec(v_lawfulOrderLTInst_x3f_993_);
lean_del_object(v___x_991_);
v___x_998_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1);
v___x_999_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_998_, v_a_983_, v_a_984_, v_a_985_, v_a_986_);
return v___x_999_;
}
}
}
else
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
v_a_1001_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1003_ = v___x_988_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_988_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_1001_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___boxed(lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst(v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
lean_dec(v_a_1019_);
lean_dec_ref(v_a_1018_);
lean_dec(v_a_1017_);
lean_dec_ref(v_a_1016_);
lean_dec(v_a_1015_);
lean_dec_ref(v_a_1014_);
lean_dec(v_a_1013_);
lean_dec_ref(v_a_1012_);
lean_dec(v_a_1011_);
lean_dec(v_a_1010_);
lean_dec(v_a_1009_);
return v_res_1021_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1(void){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__0));
v___x_1024_ = l_Lean_stringToMessageData(v___x_1023_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst(lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_){
_start:
{
lean_object* v___x_1037_; 
v___x_1037_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1049_; 
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1040_ = v___x_1037_;
v_isShared_1041_ = v_isSharedCheck_1049_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1037_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1049_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v_isPreorderInst_x3f_1042_; 
v_isPreorderInst_x3f_1042_ = lean_ctor_get(v_a_1038_, 8);
lean_inc(v_isPreorderInst_x3f_1042_);
lean_dec(v_a_1038_);
if (lean_obj_tag(v_isPreorderInst_x3f_1042_) == 1)
{
lean_object* v_val_1043_; lean_object* v___x_1045_; 
v_val_1043_ = lean_ctor_get(v_isPreorderInst_x3f_1042_, 0);
lean_inc(v_val_1043_);
lean_dec_ref_known(v_isPreorderInst_x3f_1042_, 1);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 0, v_val_1043_);
v___x_1045_ = v___x_1040_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_val_1043_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
else
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
lean_dec(v_isPreorderInst_x3f_1042_);
lean_del_object(v___x_1040_);
v___x_1047_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1);
v___x_1048_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1047_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_);
return v___x_1048_;
}
}
}
else
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
v_a_1050_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1052_ = v___x_1037_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_1037_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1050_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___boxed(lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst(v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_);
lean_dec(v_a_1068_);
lean_dec_ref(v_a_1067_);
lean_dec(v_a_1066_);
lean_dec_ref(v_a_1065_);
lean_dec(v_a_1064_);
lean_dec_ref(v_a_1063_);
lean_dec(v_a_1062_);
lean_dec_ref(v_a_1061_);
lean_dec(v_a_1060_);
lean_dec(v_a_1059_);
lean_dec(v_a_1058_);
return v_res_1070_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1(void){
_start:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__0));
v___x_1073_ = l_Lean_stringToMessageData(v___x_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst(lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1098_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1089_ = v___x_1086_;
v_isShared_1090_ = v_isSharedCheck_1098_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1086_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1098_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v_orderedAddInst_x3f_1091_; 
v_orderedAddInst_x3f_1091_ = lean_ctor_get(v_a_1087_, 9);
lean_inc(v_orderedAddInst_x3f_1091_);
lean_dec(v_a_1087_);
if (lean_obj_tag(v_orderedAddInst_x3f_1091_) == 1)
{
lean_object* v_val_1092_; lean_object* v___x_1094_; 
v_val_1092_ = lean_ctor_get(v_orderedAddInst_x3f_1091_, 0);
lean_inc(v_val_1092_);
lean_dec_ref_known(v_orderedAddInst_x3f_1091_, 1);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v_val_1092_);
v___x_1094_ = v___x_1089_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_val_1092_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
else
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
lean_dec(v_orderedAddInst_x3f_1091_);
lean_del_object(v___x_1089_);
v___x_1096_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1);
v___x_1097_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1096_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_);
return v___x_1097_;
}
}
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
v_a_1099_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1101_ = v___x_1086_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1086_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___boxed(lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst(v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
lean_dec(v_a_1115_);
lean_dec_ref(v_a_1114_);
lean_dec(v_a_1113_);
lean_dec_ref(v_a_1112_);
lean_dec(v_a_1111_);
lean_dec_ref(v_a_1110_);
lean_dec(v_a_1109_);
lean_dec(v_a_1108_);
lean_dec(v_a_1107_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1148_; 
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1135_ = v___x_1132_;
v_isShared_1136_ = v_isSharedCheck_1148_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1132_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1148_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v_orderedAddInst_x3f_1137_; 
v_orderedAddInst_x3f_1137_ = lean_ctor_get(v_a_1133_, 9);
lean_inc(v_orderedAddInst_x3f_1137_);
lean_dec(v_a_1133_);
if (lean_obj_tag(v_orderedAddInst_x3f_1137_) == 0)
{
uint8_t v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1141_; 
v___x_1138_ = 0;
v___x_1139_ = lean_box(v___x_1138_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v___x_1139_);
v___x_1141_ = v___x_1135_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1139_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
else
{
uint8_t v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1146_; 
lean_dec_ref_known(v_orderedAddInst_x3f_1137_, 1);
v___x_1143_ = 1;
v___x_1144_ = lean_box(v___x_1143_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v___x_1144_);
v___x_1146_ = v___x_1135_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1144_);
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
else
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1156_; 
v_a_1149_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1151_ = v___x_1132_;
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1132_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1154_; 
if (v_isShared_1152_ == 0)
{
v___x_1154_ = v___x_1151_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_a_1149_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd___boxed(lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
lean_dec(v_a_1163_);
lean_dec_ref(v_a_1162_);
lean_dec(v_a_1161_);
lean_dec_ref(v_a_1160_);
lean_dec(v_a_1159_);
lean_dec(v_a_1158_);
lean_dec(v_a_1157_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg___lam__0(lean_object* v_toPure_1170_, lean_object* v_inst_1171_, lean_object* v_inst_1172_, lean_object* v_____do__lift_1173_){
_start:
{
lean_object* v_ltFn_x3f_1174_; 
v_ltFn_x3f_1174_ = lean_ctor_get(v_____do__lift_1173_, 21);
lean_inc(v_ltFn_x3f_1174_);
lean_dec_ref(v_____do__lift_1173_);
if (lean_obj_tag(v_ltFn_x3f_1174_) == 1)
{
lean_object* v_val_1175_; lean_object* v___x_1176_; 
lean_dec_ref(v_inst_1172_);
lean_dec_ref(v_inst_1171_);
v_val_1175_ = lean_ctor_get(v_ltFn_x3f_1174_, 0);
lean_inc(v_val_1175_);
lean_dec_ref_known(v_ltFn_x3f_1174_, 1);
v___x_1176_ = lean_apply_2(v_toPure_1170_, lean_box(0), v_val_1175_);
return v___x_1176_;
}
else
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
lean_dec(v_ltFn_x3f_1174_);
lean_dec(v_toPure_1170_);
v___x_1177_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1);
v___x_1178_ = l_Lean_throwError___redArg(v_inst_1171_, v_inst_1172_, v___x_1177_);
return v___x_1178_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg(lean_object* v_inst_1179_, lean_object* v_inst_1180_, lean_object* v_inst_1181_){
_start:
{
lean_object* v_toApplicative_1182_; lean_object* v_toBind_1183_; lean_object* v_toPure_1184_; lean_object* v___f_1185_; lean_object* v___x_1186_; 
v_toApplicative_1182_ = lean_ctor_get(v_inst_1179_, 0);
v_toBind_1183_ = lean_ctor_get(v_inst_1179_, 1);
lean_inc(v_toBind_1183_);
v_toPure_1184_ = lean_ctor_get(v_toApplicative_1182_, 1);
lean_inc(v_toPure_1184_);
v___f_1185_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1185_, 0, v_toPure_1184_);
lean_closure_set(v___f_1185_, 1, v_inst_1179_);
lean_closure_set(v___f_1185_, 2, v_inst_1180_);
v___x_1186_ = lean_apply_4(v_toBind_1183_, lean_box(0), lean_box(0), v_inst_1181_, v___f_1185_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn(lean_object* v_m_1187_, lean_object* v_inst_1188_, lean_object* v_inst_1189_, lean_object* v_inst_1190_){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg(v_inst_1188_, v_inst_1189_, v_inst_1190_);
return v___x_1191_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__0));
v___x_1194_ = l_Lean_stringToMessageData(v___x_1193_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0(lean_object* v_toPure_1195_, lean_object* v_inst_1196_, lean_object* v_inst_1197_, lean_object* v_____do__lift_1198_){
_start:
{
lean_object* v_leFn_x3f_1199_; 
v_leFn_x3f_1199_ = lean_ctor_get(v_____do__lift_1198_, 20);
lean_inc(v_leFn_x3f_1199_);
lean_dec_ref(v_____do__lift_1198_);
if (lean_obj_tag(v_leFn_x3f_1199_) == 1)
{
lean_object* v_val_1200_; lean_object* v___x_1201_; 
lean_dec_ref(v_inst_1197_);
lean_dec_ref(v_inst_1196_);
v_val_1200_ = lean_ctor_get(v_leFn_x3f_1199_, 0);
lean_inc(v_val_1200_);
lean_dec_ref_known(v_leFn_x3f_1199_, 1);
v___x_1201_ = lean_apply_2(v_toPure_1195_, lean_box(0), v_val_1200_);
return v___x_1201_;
}
else
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
lean_dec(v_leFn_x3f_1199_);
lean_dec(v_toPure_1195_);
v___x_1202_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1);
v___x_1203_ = l_Lean_throwError___redArg(v_inst_1196_, v_inst_1197_, v___x_1202_);
return v___x_1203_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg(lean_object* v_inst_1204_, lean_object* v_inst_1205_, lean_object* v_inst_1206_){
_start:
{
lean_object* v_toApplicative_1207_; lean_object* v_toBind_1208_; lean_object* v_toPure_1209_; lean_object* v___f_1210_; lean_object* v___x_1211_; 
v_toApplicative_1207_ = lean_ctor_get(v_inst_1204_, 0);
v_toBind_1208_ = lean_ctor_get(v_inst_1204_, 1);
lean_inc(v_toBind_1208_);
v_toPure_1209_ = lean_ctor_get(v_toApplicative_1207_, 1);
lean_inc(v_toPure_1209_);
v___f_1210_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1210_, 0, v_toPure_1209_);
lean_closure_set(v___f_1210_, 1, v_inst_1204_);
lean_closure_set(v___f_1210_, 2, v_inst_1205_);
v___x_1211_ = lean_apply_4(v_toBind_1208_, lean_box(0), lean_box(0), v_inst_1206_, v___f_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn(lean_object* v_m_1212_, lean_object* v_inst_1213_, lean_object* v_inst_1214_, lean_object* v_inst_1215_){
_start:
{
lean_object* v___x_1216_; 
v___x_1216_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg(v_inst_1213_, v_inst_1214_, v_inst_1215_);
return v___x_1216_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1(void){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1218_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__0));
v___x_1219_ = l_Lean_stringToMessageData(v___x_1218_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst(lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_){
_start:
{
lean_object* v___x_1232_; 
v___x_1232_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1244_; 
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1235_ = v___x_1232_;
v_isShared_1236_ = v_isSharedCheck_1244_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1232_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1244_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v_isLinearInst_x3f_1237_; 
v_isLinearInst_x3f_1237_ = lean_ctor_get(v_a_1233_, 10);
lean_inc(v_isLinearInst_x3f_1237_);
lean_dec(v_a_1233_);
if (lean_obj_tag(v_isLinearInst_x3f_1237_) == 1)
{
lean_object* v_val_1238_; lean_object* v___x_1240_; 
v_val_1238_ = lean_ctor_get(v_isLinearInst_x3f_1237_, 0);
lean_inc(v_val_1238_);
lean_dec_ref_known(v_isLinearInst_x3f_1237_, 1);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 0, v_val_1238_);
v___x_1240_ = v___x_1235_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_val_1238_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
else
{
lean_object* v___x_1242_; lean_object* v___x_1243_; 
lean_dec(v_isLinearInst_x3f_1237_);
lean_del_object(v___x_1235_);
v___x_1242_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1);
v___x_1243_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1242_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_);
return v___x_1243_;
}
}
}
else
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
v_a_1245_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1247_ = v___x_1232_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1232_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1245_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___boxed(lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst(v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_);
lean_dec(v_a_1263_);
lean_dec_ref(v_a_1262_);
lean_dec(v_a_1261_);
lean_dec_ref(v_a_1260_);
lean_dec(v_a_1259_);
lean_dec_ref(v_a_1258_);
lean_dec(v_a_1257_);
lean_dec_ref(v_a_1256_);
lean_dec(v_a_1255_);
lean_dec(v_a_1254_);
lean_dec(v_a_1253_);
return v_res_1265_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1(void){
_start:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1267_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__0));
v___x_1268_ = l_Lean_stringToMessageData(v___x_1267_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRingInst(lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1293_; 
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1284_ = v___x_1281_;
v_isShared_1285_ = v_isSharedCheck_1293_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1281_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1293_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v_ringInst_x3f_1286_; 
v_ringInst_x3f_1286_ = lean_ctor_get(v_a_1282_, 12);
lean_inc(v_ringInst_x3f_1286_);
lean_dec(v_a_1282_);
if (lean_obj_tag(v_ringInst_x3f_1286_) == 1)
{
lean_object* v_val_1287_; lean_object* v___x_1289_; 
v_val_1287_ = lean_ctor_get(v_ringInst_x3f_1286_, 0);
lean_inc(v_val_1287_);
lean_dec_ref_known(v_ringInst_x3f_1286_, 1);
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 0, v_val_1287_);
v___x_1289_ = v___x_1284_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_val_1287_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
else
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
lean_dec(v_ringInst_x3f_1286_);
lean_del_object(v___x_1284_);
v___x_1291_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1);
v___x_1292_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1291_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_);
return v___x_1292_;
}
}
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
v_a_1294_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___x_1281_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1281_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRingInst___boxed(lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l_Lean_Meta_Grind_Arith_Linear_getRingInst(v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_);
lean_dec(v_a_1312_);
lean_dec_ref(v_a_1311_);
lean_dec(v_a_1310_);
lean_dec_ref(v_a_1309_);
lean_dec(v_a_1308_);
lean_dec_ref(v_a_1307_);
lean_dec(v_a_1306_);
lean_dec_ref(v_a_1305_);
lean_dec(v_a_1304_);
lean_dec(v_a_1303_);
lean_dec(v_a_1302_);
return v_res_1314_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1(void){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__0));
v___x_1317_ = l_Lean_stringToMessageData(v___x_1316_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getCommRingInst(lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_){
_start:
{
lean_object* v___x_1330_; 
v___x_1330_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1342_; 
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1333_ = v___x_1330_;
v_isShared_1334_ = v_isSharedCheck_1342_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1330_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1342_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v_commRingInst_x3f_1335_; 
v_commRingInst_x3f_1335_ = lean_ctor_get(v_a_1331_, 13);
lean_inc(v_commRingInst_x3f_1335_);
lean_dec(v_a_1331_);
if (lean_obj_tag(v_commRingInst_x3f_1335_) == 1)
{
lean_object* v_val_1336_; lean_object* v___x_1338_; 
v_val_1336_ = lean_ctor_get(v_commRingInst_x3f_1335_, 0);
lean_inc(v_val_1336_);
lean_dec_ref_known(v_commRingInst_x3f_1335_, 1);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 0, v_val_1336_);
v___x_1338_ = v___x_1333_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_val_1336_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
else
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
lean_dec(v_commRingInst_x3f_1335_);
lean_del_object(v___x_1333_);
v___x_1340_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1);
v___x_1341_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1340_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
return v___x_1341_;
}
}
}
else
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1350_; 
v_a_1343_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1345_ = v___x_1330_;
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1330_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1343_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___boxed(lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Lean_Meta_Grind_Arith_Linear_getCommRingInst(v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_);
lean_dec(v_a_1361_);
lean_dec_ref(v_a_1360_);
lean_dec(v_a_1359_);
lean_dec_ref(v_a_1358_);
lean_dec(v_a_1357_);
lean_dec_ref(v_a_1356_);
lean_dec(v_a_1355_);
lean_dec_ref(v_a_1354_);
lean_dec(v_a_1353_);
lean_dec(v_a_1352_);
lean_dec(v_a_1351_);
return v_res_1363_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1(void){
_start:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1365_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__0));
v___x_1366_ = l_Lean_stringToMessageData(v___x_1365_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst(lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_){
_start:
{
lean_object* v___x_1379_; 
v___x_1379_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1391_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1382_ = v___x_1379_;
v_isShared_1383_ = v_isSharedCheck_1391_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1379_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1391_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v_orderedRingInst_x3f_1384_; 
v_orderedRingInst_x3f_1384_ = lean_ctor_get(v_a_1380_, 14);
lean_inc(v_orderedRingInst_x3f_1384_);
lean_dec(v_a_1380_);
if (lean_obj_tag(v_orderedRingInst_x3f_1384_) == 1)
{
lean_object* v_val_1385_; lean_object* v___x_1387_; 
v_val_1385_ = lean_ctor_get(v_orderedRingInst_x3f_1384_, 0);
lean_inc(v_val_1385_);
lean_dec_ref_known(v_orderedRingInst_x3f_1384_, 1);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 0, v_val_1385_);
v___x_1387_ = v___x_1382_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_val_1385_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
else
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
lean_dec(v_orderedRingInst_x3f_1384_);
lean_del_object(v___x_1382_);
v___x_1389_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1);
v___x_1390_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1389_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
return v___x_1390_;
}
}
}
else
{
lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1399_; 
v_a_1392_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1394_ = v___x_1379_;
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v___x_1379_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1397_; 
if (v_isShared_1395_ == 0)
{
v___x_1397_ = v___x_1394_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_a_1392_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___boxed(lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst(v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_);
lean_dec(v_a_1410_);
lean_dec_ref(v_a_1409_);
lean_dec(v_a_1408_);
lean_dec_ref(v_a_1407_);
lean_dec(v_a_1406_);
lean_dec_ref(v_a_1405_);
lean_dec(v_a_1404_);
lean_dec_ref(v_a_1403_);
lean_dec(v_a_1402_);
lean_dec(v_a_1401_);
lean_dec(v_a_1400_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go_spec__0(lean_object* v_a_1413_){
_start:
{
lean_object* v___x_1414_; 
v___x_1414_ = l_Rat_ofInt(v_a_1413_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go(lean_object* v_a_1415_, lean_object* v_v_1416_, lean_object* v_a_1417_){
_start:
{
if (lean_obj_tag(v_a_1417_) == 0)
{
lean_object* v___x_1418_; 
v___x_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1418_, 0, v_v_1416_);
return v___x_1418_;
}
else
{
lean_object* v_k_1419_; lean_object* v_v_1420_; lean_object* v_p_1421_; lean_object* v_size_1422_; uint8_t v___x_1423_; 
v_k_1419_ = lean_ctor_get(v_a_1417_, 0);
lean_inc(v_k_1419_);
v_v_1420_ = lean_ctor_get(v_a_1417_, 1);
lean_inc(v_v_1420_);
v_p_1421_ = lean_ctor_get(v_a_1417_, 2);
lean_inc(v_p_1421_);
lean_dec_ref_known(v_a_1417_, 3);
v_size_1422_ = lean_ctor_get(v_a_1415_, 2);
v___x_1423_ = lean_nat_dec_lt(v_v_1420_, v_size_1422_);
if (v___x_1423_ == 0)
{
lean_object* v___x_1424_; 
lean_dec(v_p_1421_);
lean_dec(v_v_1420_);
lean_dec(v_k_1419_);
lean_dec_ref(v_v_1416_);
v___x_1424_ = lean_box(0);
return v___x_1424_;
}
else
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1425_ = l_Rat_ofInt(v_k_1419_);
v___x_1426_ = l_instInhabitedRat;
v___x_1427_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1426_, v_a_1415_, v_v_1420_);
lean_dec(v_v_1420_);
v___x_1428_ = l_Rat_mul(v___x_1425_, v___x_1427_);
lean_dec_ref(v___x_1425_);
v___x_1429_ = l_Rat_add(v_v_1416_, v___x_1428_);
v_v_1416_ = v___x_1429_;
v_a_1417_ = v_p_1421_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go___boxed(lean_object* v_a_1431_, lean_object* v_v_1432_, lean_object* v_a_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go(v_a_1431_, v_v_1432_, v_a_1433_);
lean_dec_ref(v_a_1431_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_Linarith_Poly_eval_x3f_spec__0(lean_object* v_a_1435_){
_start:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1436_ = lean_nat_to_int(v_a_1435_);
v___x_1437_ = l_Rat_ofInt(v___x_1436_);
return v___x_1437_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0(void){
_start:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1438_ = lean_unsigned_to_nat(0u);
v___x_1439_ = l_Nat_cast___at___00Lean_Grind_Linarith_Poly_eval_x3f_spec__0(v___x_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_eval_x3f(lean_object* v_p_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_){
_start:
{
lean_object* v___x_1453_; 
v___x_1453_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_);
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1464_; 
v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1456_ = v___x_1453_;
v_isShared_1457_ = v_isSharedCheck_1464_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1453_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1464_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v_assignment_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1462_; 
v_assignment_1458_ = lean_ctor_get(v_a_1454_, 35);
lean_inc_ref(v_assignment_1458_);
lean_dec(v_a_1454_);
v___x_1459_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0, &l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once, _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0);
v___x_1460_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go(v_assignment_1458_, v___x_1459_, v_p_1440_);
lean_dec_ref(v_assignment_1458_);
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 0, v___x_1460_);
v___x_1462_ = v___x_1456_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1460_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
else
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1472_; 
lean_dec(v_p_1440_);
v_a_1465_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1467_ = v___x_1453_;
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1453_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
if (v_isShared_1468_ == 0)
{
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_a_1465_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_eval_x3f___boxed(lean_object* v_p_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_Lean_Grind_Linarith_Poly_eval_x3f(v_p_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_);
lean_dec(v_a_1484_);
lean_dec_ref(v_a_1483_);
lean_dec(v_a_1482_);
lean_dec_ref(v_a_1481_);
lean_dec(v_a_1480_);
lean_dec_ref(v_a_1479_);
lean_dec(v_a_1478_);
lean_dec_ref(v_a_1477_);
lean_dec(v_a_1476_);
lean_dec(v_a_1475_);
lean_dec(v_a_1474_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Lean_Grind_Linarith_Poly_eval_x3f_spec__0_spec__0(lean_object* v_a_1487_){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = lean_nat_to_int(v_a_1487_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied(lean_object* v_c_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_){
_start:
{
lean_object* v_p_1502_; uint8_t v_strict_1503_; lean_object* v___x_1504_; 
v_p_1502_ = lean_ctor_get(v_c_1489_, 0);
lean_inc(v_p_1502_);
v_strict_1503_ = lean_ctor_get_uint8(v_c_1489_, sizeof(void*)*2);
lean_dec_ref(v_c_1489_);
v___x_1504_ = l_Lean_Grind_Linarith_Poly_eval_x3f(v_p_1502_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v_a_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1530_; 
v_a_1505_ = lean_ctor_get(v___x_1504_, 0);
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1507_ = v___x_1504_;
v_isShared_1508_ = v_isSharedCheck_1530_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_a_1505_);
lean_dec(v___x_1504_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1530_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
if (lean_obj_tag(v_a_1505_) == 1)
{
if (v_strict_1503_ == 0)
{
lean_object* v_val_1509_; lean_object* v___x_1510_; uint8_t v___x_1511_; uint8_t v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1515_; 
v_val_1509_ = lean_ctor_get(v_a_1505_, 0);
lean_inc(v_val_1509_);
lean_dec_ref_known(v_a_1505_, 1);
v___x_1510_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0, &l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once, _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0);
v___x_1511_ = l_Rat_instDecidableLe(v_val_1509_, v___x_1510_);
v___x_1512_ = l_Lean_Bool_toLBool(v___x_1511_);
v___x_1513_ = lean_box(v___x_1512_);
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 0, v___x_1513_);
v___x_1515_ = v___x_1507_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1513_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
else
{
lean_object* v_val_1517_; lean_object* v___x_1518_; uint8_t v___x_1519_; uint8_t v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1523_; 
v_val_1517_ = lean_ctor_get(v_a_1505_, 0);
lean_inc(v_val_1517_);
lean_dec_ref_known(v_a_1505_, 1);
v___x_1518_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0, &l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once, _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0);
v___x_1519_ = l_Rat_blt(v_val_1517_, v___x_1518_);
v___x_1520_ = l_Lean_Bool_toLBool(v___x_1519_);
v___x_1521_ = lean_box(v___x_1520_);
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 0, v___x_1521_);
v___x_1523_ = v___x_1507_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1521_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
else
{
uint8_t v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1528_; 
lean_dec(v_a_1505_);
v___x_1525_ = 2;
v___x_1526_ = lean_box(v___x_1525_);
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 0, v___x_1526_);
v___x_1528_ = v___x_1507_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v___x_1526_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
}
else
{
lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1538_; 
v_a_1531_ = lean_ctor_get(v___x_1504_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1533_ = v___x_1504_;
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_dec(v___x_1504_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1536_; 
if (v_isShared_1534_ == 0)
{
v___x_1536_ = v___x_1533_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_a_1531_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied___boxed(lean_object* v_c_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied(v_c_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_);
lean_dec(v_a_1550_);
lean_dec_ref(v_a_1549_);
lean_dec(v_a_1548_);
lean_dec_ref(v_a_1547_);
lean_dec(v_a_1546_);
lean_dec_ref(v_a_1545_);
lean_dec(v_a_1544_);
lean_dec_ref(v_a_1543_);
lean_dec(v_a_1542_);
lean_dec(v_a_1541_);
lean_dec(v_a_1540_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(lean_object* v_c_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_){
_start:
{
lean_object* v_p_1566_; lean_object* v___x_1567_; 
v_p_1566_ = lean_ctor_get(v_c_1553_, 0);
lean_inc(v_p_1566_);
lean_dec_ref(v_c_1553_);
v___x_1567_ = l_Lean_Grind_Linarith_Poly_eval_x3f(v_p_1566_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1586_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1570_ = v___x_1567_;
v_isShared_1571_ = v_isSharedCheck_1586_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1567_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1586_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
if (lean_obj_tag(v_a_1568_) == 1)
{
lean_object* v_val_1572_; lean_object* v___x_1573_; uint8_t v___x_1574_; uint8_t v___x_1575_; uint8_t v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1579_; 
v_val_1572_ = lean_ctor_get(v_a_1568_, 0);
lean_inc(v_val_1572_);
lean_dec_ref_known(v_a_1568_, 1);
v___x_1573_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0, &l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once, _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0);
v___x_1574_ = l_instDecidableEqRat_decEq(v_val_1572_, v___x_1573_);
lean_dec(v_val_1572_);
v___x_1575_ = lean_bool_not(v___x_1574_);
v___x_1576_ = l_Lean_Bool_toLBool(v___x_1575_);
v___x_1577_ = lean_box(v___x_1576_);
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 0, v___x_1577_);
v___x_1579_ = v___x_1570_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1577_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
else
{
uint8_t v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1584_; 
lean_dec(v_a_1568_);
v___x_1581_ = 2;
v___x_1582_ = lean_box(v___x_1581_);
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 0, v___x_1582_);
v___x_1584_ = v___x_1570_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1582_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
else
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1594_; 
v_a_1587_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1589_ = v___x_1567_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1567_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1590_ == 0)
{
v___x_1592_ = v___x_1589_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1587_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied___boxed(lean_object* v_c_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(v_c_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_);
lean_dec(v_a_1606_);
lean_dec_ref(v_a_1605_);
lean_dec(v_a_1604_);
lean_dec_ref(v_a_1603_);
lean_dec(v_a_1602_);
lean_dec_ref(v_a_1601_);
lean_dec(v_a_1600_);
lean_dec_ref(v_a_1599_);
lean_dec(v_a_1598_);
lean_dec(v_a_1597_);
lean_dec(v_a_1596_);
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0(lean_object* v_a_1609_, lean_object* v_x_1610_, lean_object* v_s_1611_){
_start:
{
lean_object* v_structs_1612_; lean_object* v_typeIdOf_1613_; lean_object* v_exprToStructId_1614_; lean_object* v_exprToStructIdEntries_1615_; lean_object* v_forbiddenNatModules_1616_; lean_object* v_natStructs_1617_; lean_object* v_natTypeIdOf_1618_; lean_object* v_exprToNatStructId_1619_; lean_object* v___x_1620_; uint8_t v___x_1621_; 
v_structs_1612_ = lean_ctor_get(v_s_1611_, 0);
v_typeIdOf_1613_ = lean_ctor_get(v_s_1611_, 1);
v_exprToStructId_1614_ = lean_ctor_get(v_s_1611_, 2);
v_exprToStructIdEntries_1615_ = lean_ctor_get(v_s_1611_, 3);
v_forbiddenNatModules_1616_ = lean_ctor_get(v_s_1611_, 4);
v_natStructs_1617_ = lean_ctor_get(v_s_1611_, 5);
v_natTypeIdOf_1618_ = lean_ctor_get(v_s_1611_, 6);
v_exprToNatStructId_1619_ = lean_ctor_get(v_s_1611_, 7);
v___x_1620_ = lean_array_get_size(v_structs_1612_);
v___x_1621_ = lean_nat_dec_lt(v_a_1609_, v___x_1620_);
if (v___x_1621_ == 0)
{
return v_s_1611_;
}
else
{
lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1683_; 
lean_inc_ref(v_exprToNatStructId_1619_);
lean_inc_ref(v_natTypeIdOf_1618_);
lean_inc_ref(v_natStructs_1617_);
lean_inc_ref(v_forbiddenNatModules_1616_);
lean_inc_ref(v_exprToStructIdEntries_1615_);
lean_inc_ref(v_exprToStructId_1614_);
lean_inc_ref(v_typeIdOf_1613_);
lean_inc_ref(v_structs_1612_);
v_isSharedCheck_1683_ = !lean_is_exclusive(v_s_1611_);
if (v_isSharedCheck_1683_ == 0)
{
lean_object* v_unused_1684_; lean_object* v_unused_1685_; lean_object* v_unused_1686_; lean_object* v_unused_1687_; lean_object* v_unused_1688_; lean_object* v_unused_1689_; lean_object* v_unused_1690_; lean_object* v_unused_1691_; 
v_unused_1684_ = lean_ctor_get(v_s_1611_, 7);
lean_dec(v_unused_1684_);
v_unused_1685_ = lean_ctor_get(v_s_1611_, 6);
lean_dec(v_unused_1685_);
v_unused_1686_ = lean_ctor_get(v_s_1611_, 5);
lean_dec(v_unused_1686_);
v_unused_1687_ = lean_ctor_get(v_s_1611_, 4);
lean_dec(v_unused_1687_);
v_unused_1688_ = lean_ctor_get(v_s_1611_, 3);
lean_dec(v_unused_1688_);
v_unused_1689_ = lean_ctor_get(v_s_1611_, 2);
lean_dec(v_unused_1689_);
v_unused_1690_ = lean_ctor_get(v_s_1611_, 1);
lean_dec(v_unused_1690_);
v_unused_1691_ = lean_ctor_get(v_s_1611_, 0);
lean_dec(v_unused_1691_);
v___x_1623_ = v_s_1611_;
v_isShared_1624_ = v_isSharedCheck_1683_;
goto v_resetjp_1622_;
}
else
{
lean_dec(v_s_1611_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1683_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v_v_1625_; lean_object* v_id_1626_; lean_object* v_ringId_x3f_1627_; lean_object* v_type_1628_; lean_object* v_u_1629_; lean_object* v_intModuleInst_1630_; lean_object* v_leInst_x3f_1631_; lean_object* v_ltInst_x3f_1632_; lean_object* v_lawfulOrderLTInst_x3f_1633_; lean_object* v_isPreorderInst_x3f_1634_; lean_object* v_orderedAddInst_x3f_1635_; lean_object* v_isLinearInst_x3f_1636_; lean_object* v_noNatDivInst_x3f_1637_; lean_object* v_ringInst_x3f_1638_; lean_object* v_commRingInst_x3f_1639_; lean_object* v_orderedRingInst_x3f_1640_; lean_object* v_fieldInst_x3f_1641_; lean_object* v_charInst_x3f_1642_; lean_object* v_zero_1643_; lean_object* v_ofNatZero_1644_; lean_object* v_one_x3f_1645_; lean_object* v_leFn_x3f_1646_; lean_object* v_ltFn_x3f_1647_; lean_object* v_addFn_1648_; lean_object* v_zsmulFn_1649_; lean_object* v_nsmulFn_1650_; lean_object* v_zsmulFn_x3f_1651_; lean_object* v_nsmulFn_x3f_1652_; lean_object* v_homomulFn_x3f_1653_; lean_object* v_subFn_1654_; lean_object* v_negFn_1655_; lean_object* v_vars_1656_; lean_object* v_varMap_1657_; lean_object* v_lowers_1658_; lean_object* v_uppers_1659_; lean_object* v_diseqs_1660_; lean_object* v_assignment_1661_; uint8_t v_caseSplits_1662_; lean_object* v_conflict_x3f_1663_; lean_object* v_diseqSplits_1664_; lean_object* v_elimEqs_1665_; lean_object* v_elimStack_1666_; lean_object* v_occurs_1667_; lean_object* v_ignored_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1682_; 
v_v_1625_ = lean_array_fget(v_structs_1612_, v_a_1609_);
v_id_1626_ = lean_ctor_get(v_v_1625_, 0);
v_ringId_x3f_1627_ = lean_ctor_get(v_v_1625_, 1);
v_type_1628_ = lean_ctor_get(v_v_1625_, 2);
v_u_1629_ = lean_ctor_get(v_v_1625_, 3);
v_intModuleInst_1630_ = lean_ctor_get(v_v_1625_, 4);
v_leInst_x3f_1631_ = lean_ctor_get(v_v_1625_, 5);
v_ltInst_x3f_1632_ = lean_ctor_get(v_v_1625_, 6);
v_lawfulOrderLTInst_x3f_1633_ = lean_ctor_get(v_v_1625_, 7);
v_isPreorderInst_x3f_1634_ = lean_ctor_get(v_v_1625_, 8);
v_orderedAddInst_x3f_1635_ = lean_ctor_get(v_v_1625_, 9);
v_isLinearInst_x3f_1636_ = lean_ctor_get(v_v_1625_, 10);
v_noNatDivInst_x3f_1637_ = lean_ctor_get(v_v_1625_, 11);
v_ringInst_x3f_1638_ = lean_ctor_get(v_v_1625_, 12);
v_commRingInst_x3f_1639_ = lean_ctor_get(v_v_1625_, 13);
v_orderedRingInst_x3f_1640_ = lean_ctor_get(v_v_1625_, 14);
v_fieldInst_x3f_1641_ = lean_ctor_get(v_v_1625_, 15);
v_charInst_x3f_1642_ = lean_ctor_get(v_v_1625_, 16);
v_zero_1643_ = lean_ctor_get(v_v_1625_, 17);
v_ofNatZero_1644_ = lean_ctor_get(v_v_1625_, 18);
v_one_x3f_1645_ = lean_ctor_get(v_v_1625_, 19);
v_leFn_x3f_1646_ = lean_ctor_get(v_v_1625_, 20);
v_ltFn_x3f_1647_ = lean_ctor_get(v_v_1625_, 21);
v_addFn_1648_ = lean_ctor_get(v_v_1625_, 22);
v_zsmulFn_1649_ = lean_ctor_get(v_v_1625_, 23);
v_nsmulFn_1650_ = lean_ctor_get(v_v_1625_, 24);
v_zsmulFn_x3f_1651_ = lean_ctor_get(v_v_1625_, 25);
v_nsmulFn_x3f_1652_ = lean_ctor_get(v_v_1625_, 26);
v_homomulFn_x3f_1653_ = lean_ctor_get(v_v_1625_, 27);
v_subFn_1654_ = lean_ctor_get(v_v_1625_, 28);
v_negFn_1655_ = lean_ctor_get(v_v_1625_, 29);
v_vars_1656_ = lean_ctor_get(v_v_1625_, 30);
v_varMap_1657_ = lean_ctor_get(v_v_1625_, 31);
v_lowers_1658_ = lean_ctor_get(v_v_1625_, 32);
v_uppers_1659_ = lean_ctor_get(v_v_1625_, 33);
v_diseqs_1660_ = lean_ctor_get(v_v_1625_, 34);
v_assignment_1661_ = lean_ctor_get(v_v_1625_, 35);
v_caseSplits_1662_ = lean_ctor_get_uint8(v_v_1625_, sizeof(void*)*42);
v_conflict_x3f_1663_ = lean_ctor_get(v_v_1625_, 36);
v_diseqSplits_1664_ = lean_ctor_get(v_v_1625_, 37);
v_elimEqs_1665_ = lean_ctor_get(v_v_1625_, 38);
v_elimStack_1666_ = lean_ctor_get(v_v_1625_, 39);
v_occurs_1667_ = lean_ctor_get(v_v_1625_, 40);
v_ignored_1668_ = lean_ctor_get(v_v_1625_, 41);
v_isSharedCheck_1682_ = !lean_is_exclusive(v_v_1625_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1670_ = v_v_1625_;
v_isShared_1671_ = v_isSharedCheck_1682_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_ignored_1668_);
lean_inc(v_occurs_1667_);
lean_inc(v_elimStack_1666_);
lean_inc(v_elimEqs_1665_);
lean_inc(v_diseqSplits_1664_);
lean_inc(v_conflict_x3f_1663_);
lean_inc(v_assignment_1661_);
lean_inc(v_diseqs_1660_);
lean_inc(v_uppers_1659_);
lean_inc(v_lowers_1658_);
lean_inc(v_varMap_1657_);
lean_inc(v_vars_1656_);
lean_inc(v_negFn_1655_);
lean_inc(v_subFn_1654_);
lean_inc(v_homomulFn_x3f_1653_);
lean_inc(v_nsmulFn_x3f_1652_);
lean_inc(v_zsmulFn_x3f_1651_);
lean_inc(v_nsmulFn_1650_);
lean_inc(v_zsmulFn_1649_);
lean_inc(v_addFn_1648_);
lean_inc(v_ltFn_x3f_1647_);
lean_inc(v_leFn_x3f_1646_);
lean_inc(v_one_x3f_1645_);
lean_inc(v_ofNatZero_1644_);
lean_inc(v_zero_1643_);
lean_inc(v_charInst_x3f_1642_);
lean_inc(v_fieldInst_x3f_1641_);
lean_inc(v_orderedRingInst_x3f_1640_);
lean_inc(v_commRingInst_x3f_1639_);
lean_inc(v_ringInst_x3f_1638_);
lean_inc(v_noNatDivInst_x3f_1637_);
lean_inc(v_isLinearInst_x3f_1636_);
lean_inc(v_orderedAddInst_x3f_1635_);
lean_inc(v_isPreorderInst_x3f_1634_);
lean_inc(v_lawfulOrderLTInst_x3f_1633_);
lean_inc(v_ltInst_x3f_1632_);
lean_inc(v_leInst_x3f_1631_);
lean_inc(v_intModuleInst_1630_);
lean_inc(v_u_1629_);
lean_inc(v_type_1628_);
lean_inc(v_ringId_x3f_1627_);
lean_inc(v_id_1626_);
lean_dec(v_v_1625_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1682_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1672_; lean_object* v_xs_x27_1673_; lean_object* v___x_1674_; lean_object* v___x_1676_; 
v___x_1672_ = lean_box(0);
v_xs_x27_1673_ = lean_array_fset(v_structs_1612_, v_a_1609_, v___x_1672_);
v___x_1674_ = l_Lean_Meta_Grind_Arith_shrink(v_assignment_1661_, v_x_1610_);
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 35, v___x_1674_);
v___x_1676_ = v___x_1670_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_id_1626_);
lean_ctor_set(v_reuseFailAlloc_1681_, 1, v_ringId_x3f_1627_);
lean_ctor_set(v_reuseFailAlloc_1681_, 2, v_type_1628_);
lean_ctor_set(v_reuseFailAlloc_1681_, 3, v_u_1629_);
lean_ctor_set(v_reuseFailAlloc_1681_, 4, v_intModuleInst_1630_);
lean_ctor_set(v_reuseFailAlloc_1681_, 5, v_leInst_x3f_1631_);
lean_ctor_set(v_reuseFailAlloc_1681_, 6, v_ltInst_x3f_1632_);
lean_ctor_set(v_reuseFailAlloc_1681_, 7, v_lawfulOrderLTInst_x3f_1633_);
lean_ctor_set(v_reuseFailAlloc_1681_, 8, v_isPreorderInst_x3f_1634_);
lean_ctor_set(v_reuseFailAlloc_1681_, 9, v_orderedAddInst_x3f_1635_);
lean_ctor_set(v_reuseFailAlloc_1681_, 10, v_isLinearInst_x3f_1636_);
lean_ctor_set(v_reuseFailAlloc_1681_, 11, v_noNatDivInst_x3f_1637_);
lean_ctor_set(v_reuseFailAlloc_1681_, 12, v_ringInst_x3f_1638_);
lean_ctor_set(v_reuseFailAlloc_1681_, 13, v_commRingInst_x3f_1639_);
lean_ctor_set(v_reuseFailAlloc_1681_, 14, v_orderedRingInst_x3f_1640_);
lean_ctor_set(v_reuseFailAlloc_1681_, 15, v_fieldInst_x3f_1641_);
lean_ctor_set(v_reuseFailAlloc_1681_, 16, v_charInst_x3f_1642_);
lean_ctor_set(v_reuseFailAlloc_1681_, 17, v_zero_1643_);
lean_ctor_set(v_reuseFailAlloc_1681_, 18, v_ofNatZero_1644_);
lean_ctor_set(v_reuseFailAlloc_1681_, 19, v_one_x3f_1645_);
lean_ctor_set(v_reuseFailAlloc_1681_, 20, v_leFn_x3f_1646_);
lean_ctor_set(v_reuseFailAlloc_1681_, 21, v_ltFn_x3f_1647_);
lean_ctor_set(v_reuseFailAlloc_1681_, 22, v_addFn_1648_);
lean_ctor_set(v_reuseFailAlloc_1681_, 23, v_zsmulFn_1649_);
lean_ctor_set(v_reuseFailAlloc_1681_, 24, v_nsmulFn_1650_);
lean_ctor_set(v_reuseFailAlloc_1681_, 25, v_zsmulFn_x3f_1651_);
lean_ctor_set(v_reuseFailAlloc_1681_, 26, v_nsmulFn_x3f_1652_);
lean_ctor_set(v_reuseFailAlloc_1681_, 27, v_homomulFn_x3f_1653_);
lean_ctor_set(v_reuseFailAlloc_1681_, 28, v_subFn_1654_);
lean_ctor_set(v_reuseFailAlloc_1681_, 29, v_negFn_1655_);
lean_ctor_set(v_reuseFailAlloc_1681_, 30, v_vars_1656_);
lean_ctor_set(v_reuseFailAlloc_1681_, 31, v_varMap_1657_);
lean_ctor_set(v_reuseFailAlloc_1681_, 32, v_lowers_1658_);
lean_ctor_set(v_reuseFailAlloc_1681_, 33, v_uppers_1659_);
lean_ctor_set(v_reuseFailAlloc_1681_, 34, v_diseqs_1660_);
lean_ctor_set(v_reuseFailAlloc_1681_, 35, v___x_1674_);
lean_ctor_set(v_reuseFailAlloc_1681_, 36, v_conflict_x3f_1663_);
lean_ctor_set(v_reuseFailAlloc_1681_, 37, v_diseqSplits_1664_);
lean_ctor_set(v_reuseFailAlloc_1681_, 38, v_elimEqs_1665_);
lean_ctor_set(v_reuseFailAlloc_1681_, 39, v_elimStack_1666_);
lean_ctor_set(v_reuseFailAlloc_1681_, 40, v_occurs_1667_);
lean_ctor_set(v_reuseFailAlloc_1681_, 41, v_ignored_1668_);
lean_ctor_set_uint8(v_reuseFailAlloc_1681_, sizeof(void*)*42, v_caseSplits_1662_);
v___x_1676_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
lean_object* v___x_1677_; lean_object* v___x_1679_; 
v___x_1677_ = lean_array_fset(v_xs_x27_1673_, v_a_1609_, v___x_1676_);
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 0, v___x_1677_);
v___x_1679_ = v___x_1623_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v___x_1677_);
lean_ctor_set(v_reuseFailAlloc_1680_, 1, v_typeIdOf_1613_);
lean_ctor_set(v_reuseFailAlloc_1680_, 2, v_exprToStructId_1614_);
lean_ctor_set(v_reuseFailAlloc_1680_, 3, v_exprToStructIdEntries_1615_);
lean_ctor_set(v_reuseFailAlloc_1680_, 4, v_forbiddenNatModules_1616_);
lean_ctor_set(v_reuseFailAlloc_1680_, 5, v_natStructs_1617_);
lean_ctor_set(v_reuseFailAlloc_1680_, 6, v_natTypeIdOf_1618_);
lean_ctor_set(v_reuseFailAlloc_1680_, 7, v_exprToNatStructId_1619_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0___boxed(lean_object* v_a_1692_, lean_object* v_x_1693_, lean_object* v_s_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0(v_a_1692_, v_x_1693_, v_s_1694_);
lean_dec(v_x_1693_);
lean_dec(v_a_1692_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(lean_object* v_x_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_){
_start:
{
lean_object* v___f_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
lean_inc(v_a_1697_);
v___f_1700_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1700_, 0, v_a_1697_);
lean_closure_set(v___f_1700_, 1, v_x_1696_);
v___x_1701_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1702_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1701_, v___f_1700_, v_a_1698_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___boxed(lean_object* v_x_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(v_x_1703_, v_a_1704_, v_a_1705_);
lean_dec(v_a_1705_);
lean_dec(v_a_1704_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom(lean_object* v_x_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_){
_start:
{
lean_object* v___x_1721_; 
v___x_1721_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(v_x_1708_, v_a_1709_, v_a_1710_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___boxed(lean_object* v_x_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom(v_x_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_);
lean_dec(v_a_1733_);
lean_dec_ref(v_a_1732_);
lean_dec(v_a_1731_);
lean_dec_ref(v_a_1730_);
lean_dec(v_a_1729_);
lean_dec_ref(v_a_1728_);
lean_dec(v_a_1727_);
lean_dec_ref(v_a_1726_);
lean_dec(v_a_1725_);
lean_dec(v_a_1724_);
lean_dec(v_a_1723_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getVar(lean_object* v_x_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_){
_start:
{
lean_object* v___x_1749_; 
v___x_1749_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1766_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1752_ = v___x_1749_;
v_isShared_1753_ = v_isSharedCheck_1766_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1749_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1766_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v_vars_1754_; lean_object* v_size_1755_; lean_object* v___x_1756_; uint8_t v___x_1757_; 
v_vars_1754_ = lean_ctor_get(v_a_1750_, 30);
lean_inc_ref(v_vars_1754_);
lean_dec(v_a_1750_);
v_size_1755_ = lean_ctor_get(v_vars_1754_, 2);
v___x_1756_ = l_Lean_instInhabitedExpr;
v___x_1757_ = lean_nat_dec_lt(v_x_1736_, v_size_1755_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; lean_object* v___x_1760_; 
lean_dec_ref(v_vars_1754_);
v___x_1758_ = l_outOfBounds___redArg(v___x_1756_);
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 0, v___x_1758_);
v___x_1760_ = v___x_1752_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v___x_1758_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
else
{
lean_object* v___x_1762_; lean_object* v___x_1764_; 
v___x_1762_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1756_, v_vars_1754_, v_x_1736_);
lean_dec_ref(v_vars_1754_);
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 0, v___x_1762_);
v___x_1764_ = v___x_1752_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1762_);
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
else
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1774_; 
v_a_1767_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1769_ = v___x_1749_;
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1749_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1770_ == 0)
{
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_a_1767_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getVar___boxed(lean_object* v_x_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_x_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_);
lean_dec(v_a_1786_);
lean_dec_ref(v_a_1785_);
lean_dec(v_a_1784_);
lean_dec_ref(v_a_1783_);
lean_dec(v_a_1782_);
lean_dec_ref(v_a_1781_);
lean_dec(v_a_1780_);
lean_dec_ref(v_a_1779_);
lean_dec(v_a_1778_);
lean_dec(v_a_1777_);
lean_dec(v_a_1776_);
lean_dec(v_x_1775_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inconsistent(lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_){
_start:
{
lean_object* v___x_1801_; 
v___x_1801_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_1790_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v_a_1802_; uint8_t v___x_1803_; 
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
lean_inc(v_a_1802_);
v___x_1803_ = lean_unbox(v_a_1802_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; 
lean_dec_ref_known(v___x_1801_, 1);
v___x_1804_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
if (lean_obj_tag(v___x_1804_) == 0)
{
lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1818_; 
v_a_1805_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1807_ = v___x_1804_;
v_isShared_1808_ = v_isSharedCheck_1818_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1804_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1818_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v_conflict_x3f_1809_; 
v_conflict_x3f_1809_ = lean_ctor_get(v_a_1805_, 36);
lean_inc(v_conflict_x3f_1809_);
lean_dec(v_a_1805_);
if (lean_obj_tag(v_conflict_x3f_1809_) == 0)
{
lean_object* v___x_1811_; 
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 0, v_a_1802_);
v___x_1811_ = v___x_1807_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_a_1802_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
else
{
uint8_t v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1816_; 
lean_dec_ref_known(v_conflict_x3f_1809_, 1);
lean_dec(v_a_1802_);
v___x_1813_ = 1;
v___x_1814_ = lean_box(v___x_1813_);
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 0, v___x_1814_);
v___x_1816_ = v___x_1807_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v___x_1814_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
else
{
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1826_; 
lean_dec(v_a_1802_);
v_a_1819_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1821_ = v___x_1804_;
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v___x_1804_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1824_; 
if (v_isShared_1822_ == 0)
{
v___x_1824_ = v___x_1821_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_a_1819_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
}
else
{
lean_dec(v_a_1802_);
return v___x_1801_;
}
}
else
{
return v___x_1801_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inconsistent___boxed(lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_){
_start:
{
lean_object* v_res_1839_; 
v_res_1839_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_);
lean_dec(v_a_1837_);
lean_dec_ref(v_a_1836_);
lean_dec(v_a_1835_);
lean_dec_ref(v_a_1834_);
lean_dec(v_a_1833_);
lean_dec_ref(v_a_1832_);
lean_dec(v_a_1831_);
lean_dec_ref(v_a_1830_);
lean_dec(v_a_1829_);
lean_dec(v_a_1828_);
lean_dec(v_a_1827_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_eliminated(lean_object* v_x_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_){
_start:
{
lean_object* v___x_1853_; 
v___x_1853_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1876_; 
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1856_ = v___x_1853_;
v_isShared_1857_ = v_isSharedCheck_1876_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1853_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1876_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___y_1859_; lean_object* v_elimEqs_1870_; lean_object* v_size_1871_; lean_object* v___x_1872_; uint8_t v___x_1873_; 
v_elimEqs_1870_ = lean_ctor_get(v_a_1854_, 38);
lean_inc_ref(v_elimEqs_1870_);
lean_dec(v_a_1854_);
v_size_1871_ = lean_ctor_get(v_elimEqs_1870_, 2);
v___x_1872_ = lean_box(0);
v___x_1873_ = lean_nat_dec_lt(v_x_1840_, v_size_1871_);
if (v___x_1873_ == 0)
{
lean_object* v___x_1874_; 
lean_dec_ref(v_elimEqs_1870_);
v___x_1874_ = l_outOfBounds___redArg(v___x_1872_);
v___y_1859_ = v___x_1874_;
goto v___jp_1858_;
}
else
{
lean_object* v___x_1875_; 
v___x_1875_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1872_, v_elimEqs_1870_, v_x_1840_);
lean_dec_ref(v_elimEqs_1870_);
v___y_1859_ = v___x_1875_;
goto v___jp_1858_;
}
v___jp_1858_:
{
if (lean_obj_tag(v___y_1859_) == 0)
{
uint8_t v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1863_; 
v___x_1860_ = 0;
v___x_1861_ = lean_box(v___x_1860_);
if (v_isShared_1857_ == 0)
{
lean_ctor_set(v___x_1856_, 0, v___x_1861_);
v___x_1863_ = v___x_1856_;
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
else
{
uint8_t v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1868_; 
lean_dec_ref_known(v___y_1859_, 1);
v___x_1865_ = 1;
v___x_1866_ = lean_box(v___x_1865_);
if (v_isShared_1857_ == 0)
{
lean_ctor_set(v___x_1856_, 0, v___x_1866_);
v___x_1868_ = v___x_1856_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v___x_1866_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
}
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
v_a_1877_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___x_1853_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1853_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1877_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_eliminated___boxed(lean_object* v_x_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l_Lean_Meta_Grind_Arith_Linear_eliminated(v_x_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_);
lean_dec(v_a_1896_);
lean_dec_ref(v_a_1895_);
lean_dec(v_a_1894_);
lean_dec_ref(v_a_1893_);
lean_dec(v_a_1892_);
lean_dec_ref(v_a_1891_);
lean_dec(v_a_1890_);
lean_dec_ref(v_a_1889_);
lean_dec(v_a_1888_);
lean_dec(v_a_1887_);
lean_dec(v_a_1886_);
lean_dec(v_x_1885_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOccursOf(lean_object* v_x_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_){
_start:
{
lean_object* v___x_1912_; 
v___x_1912_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1929_; 
v_a_1913_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1915_ = v___x_1912_;
v_isShared_1916_ = v_isSharedCheck_1929_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1912_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1929_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v_occurs_1917_; lean_object* v_size_1918_; lean_object* v___x_1919_; uint8_t v___x_1920_; 
v_occurs_1917_ = lean_ctor_get(v_a_1913_, 40);
lean_inc_ref(v_occurs_1917_);
lean_dec(v_a_1913_);
v_size_1918_ = lean_ctor_get(v_occurs_1917_, 2);
v___x_1919_ = lean_box(1);
v___x_1920_ = lean_nat_dec_lt(v_x_1899_, v_size_1918_);
if (v___x_1920_ == 0)
{
lean_object* v___x_1921_; lean_object* v___x_1923_; 
lean_dec_ref(v_occurs_1917_);
v___x_1921_ = l_outOfBounds___redArg(v___x_1919_);
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 0, v___x_1921_);
v___x_1923_ = v___x_1915_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v___x_1921_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
else
{
lean_object* v___x_1925_; lean_object* v___x_1927_; 
v___x_1925_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1919_, v_occurs_1917_, v_x_1899_);
lean_dec_ref(v_occurs_1917_);
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 0, v___x_1925_);
v___x_1927_ = v___x_1915_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1925_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
else
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
v_a_1930_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1932_ = v___x_1912_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1912_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1933_ == 0)
{
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1930_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOccursOf___boxed(lean_object* v_x_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_){
_start:
{
lean_object* v_res_1951_; 
v_res_1951_ = l_Lean_Meta_Grind_Arith_Linear_getOccursOf(v_x_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_);
lean_dec(v_a_1949_);
lean_dec_ref(v_a_1948_);
lean_dec(v_a_1947_);
lean_dec_ref(v_a_1946_);
lean_dec(v_a_1945_);
lean_dec_ref(v_a_1944_);
lean_dec(v_a_1943_);
lean_dec_ref(v_a_1942_);
lean_dec(v_a_1941_);
lean_dec(v_a_1940_);
lean_dec(v_a_1939_);
lean_dec(v_x_1938_);
return v_res_1951_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(lean_object* v_k_1952_, lean_object* v_t_1953_){
_start:
{
if (lean_obj_tag(v_t_1953_) == 0)
{
lean_object* v_k_1954_; lean_object* v_l_1955_; lean_object* v_r_1956_; uint8_t v___x_1957_; 
v_k_1954_ = lean_ctor_get(v_t_1953_, 1);
v_l_1955_ = lean_ctor_get(v_t_1953_, 3);
v_r_1956_ = lean_ctor_get(v_t_1953_, 4);
v___x_1957_ = lean_nat_dec_lt(v_k_1952_, v_k_1954_);
if (v___x_1957_ == 0)
{
uint8_t v___x_1958_; 
v___x_1958_ = lean_nat_dec_eq(v_k_1952_, v_k_1954_);
if (v___x_1958_ == 0)
{
v_t_1953_ = v_r_1956_;
goto _start;
}
else
{
return v___x_1958_;
}
}
else
{
v_t_1953_ = v_l_1955_;
goto _start;
}
}
else
{
uint8_t v___x_1961_; 
v___x_1961_ = 0;
return v___x_1961_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg___boxed(lean_object* v_k_1962_, lean_object* v_t_1963_){
_start:
{
uint8_t v_res_1964_; lean_object* v_r_1965_; 
v_res_1964_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_k_1962_, v_t_1963_);
lean_dec(v_t_1963_);
lean_dec(v_k_1962_);
v_r_1965_ = lean_box(v_res_1964_);
return v_r_1965_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(lean_object* v_k_1966_, lean_object* v_v_1967_, lean_object* v_t_1968_){
_start:
{
if (lean_obj_tag(v_t_1968_) == 0)
{
lean_object* v_size_1969_; lean_object* v_k_1970_; lean_object* v_v_1971_; lean_object* v_l_1972_; lean_object* v_r_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_2254_; 
v_size_1969_ = lean_ctor_get(v_t_1968_, 0);
v_k_1970_ = lean_ctor_get(v_t_1968_, 1);
v_v_1971_ = lean_ctor_get(v_t_1968_, 2);
v_l_1972_ = lean_ctor_get(v_t_1968_, 3);
v_r_1973_ = lean_ctor_get(v_t_1968_, 4);
v_isSharedCheck_2254_ = !lean_is_exclusive(v_t_1968_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_1975_ = v_t_1968_;
v_isShared_1976_ = v_isSharedCheck_2254_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_r_1973_);
lean_inc(v_l_1972_);
lean_inc(v_v_1971_);
lean_inc(v_k_1970_);
lean_inc(v_size_1969_);
lean_dec(v_t_1968_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_2254_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
uint8_t v___x_1977_; 
v___x_1977_ = lean_nat_dec_lt(v_k_1966_, v_k_1970_);
if (v___x_1977_ == 0)
{
uint8_t v___x_1978_; 
v___x_1978_ = lean_nat_dec_eq(v_k_1966_, v_k_1970_);
if (v___x_1978_ == 0)
{
lean_object* v_impl_1979_; lean_object* v___x_1980_; 
lean_dec(v_size_1969_);
v_impl_1979_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_k_1966_, v_v_1967_, v_r_1973_);
v___x_1980_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1972_) == 0)
{
lean_object* v_size_1981_; lean_object* v_size_1982_; lean_object* v_k_1983_; lean_object* v_v_1984_; lean_object* v_l_1985_; lean_object* v_r_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; uint8_t v___x_1989_; 
v_size_1981_ = lean_ctor_get(v_l_1972_, 0);
v_size_1982_ = lean_ctor_get(v_impl_1979_, 0);
lean_inc(v_size_1982_);
v_k_1983_ = lean_ctor_get(v_impl_1979_, 1);
lean_inc(v_k_1983_);
v_v_1984_ = lean_ctor_get(v_impl_1979_, 2);
lean_inc(v_v_1984_);
v_l_1985_ = lean_ctor_get(v_impl_1979_, 3);
lean_inc(v_l_1985_);
v_r_1986_ = lean_ctor_get(v_impl_1979_, 4);
lean_inc(v_r_1986_);
v___x_1987_ = lean_unsigned_to_nat(3u);
v___x_1988_ = lean_nat_mul(v___x_1987_, v_size_1981_);
v___x_1989_ = lean_nat_dec_lt(v___x_1988_, v_size_1982_);
lean_dec(v___x_1988_);
if (v___x_1989_ == 0)
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1993_; 
lean_dec(v_r_1986_);
lean_dec(v_l_1985_);
lean_dec(v_v_1984_);
lean_dec(v_k_1983_);
v___x_1990_ = lean_nat_add(v___x_1980_, v_size_1981_);
v___x_1991_ = lean_nat_add(v___x_1990_, v_size_1982_);
lean_dec(v_size_1982_);
lean_dec(v___x_1990_);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 4, v_impl_1979_);
lean_ctor_set(v___x_1975_, 0, v___x_1991_);
v___x_1993_ = v___x_1975_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1991_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v_k_1970_);
lean_ctor_set(v_reuseFailAlloc_1994_, 2, v_v_1971_);
lean_ctor_set(v_reuseFailAlloc_1994_, 3, v_l_1972_);
lean_ctor_set(v_reuseFailAlloc_1994_, 4, v_impl_1979_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
else
{
lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2058_; 
v_isSharedCheck_2058_ = !lean_is_exclusive(v_impl_1979_);
if (v_isSharedCheck_2058_ == 0)
{
lean_object* v_unused_2059_; lean_object* v_unused_2060_; lean_object* v_unused_2061_; lean_object* v_unused_2062_; lean_object* v_unused_2063_; 
v_unused_2059_ = lean_ctor_get(v_impl_1979_, 4);
lean_dec(v_unused_2059_);
v_unused_2060_ = lean_ctor_get(v_impl_1979_, 3);
lean_dec(v_unused_2060_);
v_unused_2061_ = lean_ctor_get(v_impl_1979_, 2);
lean_dec(v_unused_2061_);
v_unused_2062_ = lean_ctor_get(v_impl_1979_, 1);
lean_dec(v_unused_2062_);
v_unused_2063_ = lean_ctor_get(v_impl_1979_, 0);
lean_dec(v_unused_2063_);
v___x_1996_ = v_impl_1979_;
v_isShared_1997_ = v_isSharedCheck_2058_;
goto v_resetjp_1995_;
}
else
{
lean_dec(v_impl_1979_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2058_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v_size_1998_; lean_object* v_k_1999_; lean_object* v_v_2000_; lean_object* v_l_2001_; lean_object* v_r_2002_; lean_object* v_size_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; uint8_t v___x_2006_; 
v_size_1998_ = lean_ctor_get(v_l_1985_, 0);
v_k_1999_ = lean_ctor_get(v_l_1985_, 1);
v_v_2000_ = lean_ctor_get(v_l_1985_, 2);
v_l_2001_ = lean_ctor_get(v_l_1985_, 3);
v_r_2002_ = lean_ctor_get(v_l_1985_, 4);
v_size_2003_ = lean_ctor_get(v_r_1986_, 0);
v___x_2004_ = lean_unsigned_to_nat(2u);
v___x_2005_ = lean_nat_mul(v___x_2004_, v_size_2003_);
v___x_2006_ = lean_nat_dec_lt(v_size_1998_, v___x_2005_);
lean_dec(v___x_2005_);
if (v___x_2006_ == 0)
{
lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2034_; 
lean_inc(v_r_2002_);
lean_inc(v_l_2001_);
lean_inc(v_v_2000_);
lean_inc(v_k_1999_);
v_isSharedCheck_2034_ = !lean_is_exclusive(v_l_1985_);
if (v_isSharedCheck_2034_ == 0)
{
lean_object* v_unused_2035_; lean_object* v_unused_2036_; lean_object* v_unused_2037_; lean_object* v_unused_2038_; lean_object* v_unused_2039_; 
v_unused_2035_ = lean_ctor_get(v_l_1985_, 4);
lean_dec(v_unused_2035_);
v_unused_2036_ = lean_ctor_get(v_l_1985_, 3);
lean_dec(v_unused_2036_);
v_unused_2037_ = lean_ctor_get(v_l_1985_, 2);
lean_dec(v_unused_2037_);
v_unused_2038_ = lean_ctor_get(v_l_1985_, 1);
lean_dec(v_unused_2038_);
v_unused_2039_ = lean_ctor_get(v_l_1985_, 0);
lean_dec(v_unused_2039_);
v___x_2008_ = v_l_1985_;
v_isShared_2009_ = v_isSharedCheck_2034_;
goto v_resetjp_2007_;
}
else
{
lean_dec(v_l_1985_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2034_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2024_; 
v___x_2010_ = lean_nat_add(v___x_1980_, v_size_1981_);
v___x_2011_ = lean_nat_add(v___x_2010_, v_size_1982_);
lean_dec(v_size_1982_);
if (lean_obj_tag(v_l_2001_) == 0)
{
lean_object* v_size_2032_; 
v_size_2032_ = lean_ctor_get(v_l_2001_, 0);
lean_inc(v_size_2032_);
v___y_2024_ = v_size_2032_;
goto v___jp_2023_;
}
else
{
lean_object* v___x_2033_; 
v___x_2033_ = lean_unsigned_to_nat(0u);
v___y_2024_ = v___x_2033_;
goto v___jp_2023_;
}
v___jp_2012_:
{
lean_object* v___x_2016_; lean_object* v___x_2018_; 
v___x_2016_ = lean_nat_add(v___y_2014_, v___y_2015_);
lean_dec(v___y_2015_);
lean_dec(v___y_2014_);
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 4, v_r_1986_);
lean_ctor_set(v___x_2008_, 3, v_r_2002_);
lean_ctor_set(v___x_2008_, 2, v_v_1984_);
lean_ctor_set(v___x_2008_, 1, v_k_1983_);
lean_ctor_set(v___x_2008_, 0, v___x_2016_);
v___x_2018_ = v___x_2008_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_2016_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v_k_1983_);
lean_ctor_set(v_reuseFailAlloc_2022_, 2, v_v_1984_);
lean_ctor_set(v_reuseFailAlloc_2022_, 3, v_r_2002_);
lean_ctor_set(v_reuseFailAlloc_2022_, 4, v_r_1986_);
v___x_2018_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
lean_object* v___x_2020_; 
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 4, v___x_2018_);
lean_ctor_set(v___x_1996_, 3, v___y_2013_);
lean_ctor_set(v___x_1996_, 2, v_v_2000_);
lean_ctor_set(v___x_1996_, 1, v_k_1999_);
lean_ctor_set(v___x_1996_, 0, v___x_2011_);
v___x_2020_ = v___x_1996_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2011_);
lean_ctor_set(v_reuseFailAlloc_2021_, 1, v_k_1999_);
lean_ctor_set(v_reuseFailAlloc_2021_, 2, v_v_2000_);
lean_ctor_set(v_reuseFailAlloc_2021_, 3, v___y_2013_);
lean_ctor_set(v_reuseFailAlloc_2021_, 4, v___x_2018_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
v___jp_2023_:
{
lean_object* v___x_2025_; lean_object* v___x_2027_; 
v___x_2025_ = lean_nat_add(v___x_2010_, v___y_2024_);
lean_dec(v___y_2024_);
lean_dec(v___x_2010_);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 4, v_l_2001_);
lean_ctor_set(v___x_1975_, 0, v___x_2025_);
v___x_2027_ = v___x_1975_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v___x_2025_);
lean_ctor_set(v_reuseFailAlloc_2031_, 1, v_k_1970_);
lean_ctor_set(v_reuseFailAlloc_2031_, 2, v_v_1971_);
lean_ctor_set(v_reuseFailAlloc_2031_, 3, v_l_1972_);
lean_ctor_set(v_reuseFailAlloc_2031_, 4, v_l_2001_);
v___x_2027_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
lean_object* v___x_2028_; 
v___x_2028_ = lean_nat_add(v___x_1980_, v_size_2003_);
if (lean_obj_tag(v_r_2002_) == 0)
{
lean_object* v_size_2029_; 
v_size_2029_ = lean_ctor_get(v_r_2002_, 0);
lean_inc(v_size_2029_);
v___y_2013_ = v___x_2027_;
v___y_2014_ = v___x_2028_;
v___y_2015_ = v_size_2029_;
goto v___jp_2012_;
}
else
{
lean_object* v___x_2030_; 
v___x_2030_ = lean_unsigned_to_nat(0u);
v___y_2013_ = v___x_2027_;
v___y_2014_ = v___x_2028_;
v___y_2015_ = v___x_2030_;
goto v___jp_2012_;
}
}
}
}
}
else
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2044_; 
lean_del_object(v___x_1975_);
v___x_2040_ = lean_nat_add(v___x_1980_, v_size_1981_);
v___x_2041_ = lean_nat_add(v___x_2040_, v_size_1982_);
lean_dec(v_size_1982_);
v___x_2042_ = lean_nat_add(v___x_2040_, v_size_1998_);
lean_dec(v___x_2040_);
lean_inc_ref(v_l_1972_);
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 4, v_l_1985_);
lean_ctor_set(v___x_1996_, 3, v_l_1972_);
lean_ctor_set(v___x_1996_, 2, v_v_1971_);
lean_ctor_set(v___x_1996_, 1, v_k_1970_);
lean_ctor_set(v___x_1996_, 0, v___x_2042_);
v___x_2044_ = v___x_1996_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_2042_);
lean_ctor_set(v_reuseFailAlloc_2057_, 1, v_k_1970_);
lean_ctor_set(v_reuseFailAlloc_2057_, 2, v_v_1971_);
lean_ctor_set(v_reuseFailAlloc_2057_, 3, v_l_1972_);
lean_ctor_set(v_reuseFailAlloc_2057_, 4, v_l_1985_);
v___x_2044_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2051_; 
v_isSharedCheck_2051_ = !lean_is_exclusive(v_l_1972_);
if (v_isSharedCheck_2051_ == 0)
{
lean_object* v_unused_2052_; lean_object* v_unused_2053_; lean_object* v_unused_2054_; lean_object* v_unused_2055_; lean_object* v_unused_2056_; 
v_unused_2052_ = lean_ctor_get(v_l_1972_, 4);
lean_dec(v_unused_2052_);
v_unused_2053_ = lean_ctor_get(v_l_1972_, 3);
lean_dec(v_unused_2053_);
v_unused_2054_ = lean_ctor_get(v_l_1972_, 2);
lean_dec(v_unused_2054_);
v_unused_2055_ = lean_ctor_get(v_l_1972_, 1);
lean_dec(v_unused_2055_);
v_unused_2056_ = lean_ctor_get(v_l_1972_, 0);
lean_dec(v_unused_2056_);
v___x_2046_ = v_l_1972_;
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
else
{
lean_dec(v_l_1972_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2049_; 
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 4, v_r_1986_);
lean_ctor_set(v___x_2046_, 3, v___x_2044_);
lean_ctor_set(v___x_2046_, 2, v_v_1984_);
lean_ctor_set(v___x_2046_, 1, v_k_1983_);
lean_ctor_set(v___x_2046_, 0, v___x_2041_);
v___x_2049_ = v___x_2046_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2041_);
lean_ctor_set(v_reuseFailAlloc_2050_, 1, v_k_1983_);
lean_ctor_set(v_reuseFailAlloc_2050_, 2, v_v_1984_);
lean_ctor_set(v_reuseFailAlloc_2050_, 3, v___x_2044_);
lean_ctor_set(v_reuseFailAlloc_2050_, 4, v_r_1986_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2064_; 
v_l_2064_ = lean_ctor_get(v_impl_1979_, 3);
lean_inc(v_l_2064_);
if (lean_obj_tag(v_l_2064_) == 0)
{
lean_object* v_r_2065_; lean_object* v_k_2066_; lean_object* v_v_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2090_; 
v_r_2065_ = lean_ctor_get(v_impl_1979_, 4);
v_k_2066_ = lean_ctor_get(v_impl_1979_, 1);
v_v_2067_ = lean_ctor_get(v_impl_1979_, 2);
v_isSharedCheck_2090_ = !lean_is_exclusive(v_impl_1979_);
if (v_isSharedCheck_2090_ == 0)
{
lean_object* v_unused_2091_; lean_object* v_unused_2092_; 
v_unused_2091_ = lean_ctor_get(v_impl_1979_, 3);
lean_dec(v_unused_2091_);
v_unused_2092_ = lean_ctor_get(v_impl_1979_, 0);
lean_dec(v_unused_2092_);
v___x_2069_ = v_impl_1979_;
v_isShared_2070_ = v_isSharedCheck_2090_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_r_2065_);
lean_inc(v_v_2067_);
lean_inc(v_k_2066_);
lean_dec(v_impl_1979_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2090_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v_k_2071_; lean_object* v_v_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2086_; 
v_k_2071_ = lean_ctor_get(v_l_2064_, 1);
v_v_2072_ = lean_ctor_get(v_l_2064_, 2);
v_isSharedCheck_2086_ = !lean_is_exclusive(v_l_2064_);
if (v_isSharedCheck_2086_ == 0)
{
lean_object* v_unused_2087_; lean_object* v_unused_2088_; lean_object* v_unused_2089_; 
v_unused_2087_ = lean_ctor_get(v_l_2064_, 4);
lean_dec(v_unused_2087_);
v_unused_2088_ = lean_ctor_get(v_l_2064_, 3);
lean_dec(v_unused_2088_);
v_unused_2089_ = lean_ctor_get(v_l_2064_, 0);
lean_dec(v_unused_2089_);
v___x_2074_ = v_l_2064_;
v_isShared_2075_ = v_isSharedCheck_2086_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_v_2072_);
lean_inc(v_k_2071_);
lean_dec(v_l_2064_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2086_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2076_; lean_object* v___x_2078_; 
v___x_2076_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2065_, 2);
if (v_isShared_2075_ == 0)
{
lean_ctor_set(v___x_2074_, 4, v_r_2065_);
lean_ctor_set(v___x_2074_, 3, v_r_2065_);
lean_ctor_set(v___x_2074_, 2, v_v_1971_);
lean_ctor_set(v___x_2074_, 1, v_k_1970_);
lean_ctor_set(v___x_2074_, 0, v___x_1980_);
v___x_2078_ = v___x_2074_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v___x_1980_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v_k_1970_);
lean_ctor_set(v_reuseFailAlloc_2085_, 2, v_v_1971_);
lean_ctor_set(v_reuseFailAlloc_2085_, 3, v_r_2065_);
lean_ctor_set(v_reuseFailAlloc_2085_, 4, v_r_2065_);
v___x_2078_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
lean_object* v___x_2080_; 
lean_inc(v_r_2065_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 3, v_r_2065_);
lean_ctor_set(v___x_2069_, 0, v___x_1980_);
v___x_2080_ = v___x_2069_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_1980_);
lean_ctor_set(v_reuseFailAlloc_2084_, 1, v_k_2066_);
lean_ctor_set(v_reuseFailAlloc_2084_, 2, v_v_2067_);
lean_ctor_set(v_reuseFailAlloc_2084_, 3, v_r_2065_);
lean_ctor_set(v_reuseFailAlloc_2084_, 4, v_r_2065_);
v___x_2080_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
lean_object* v___x_2082_; 
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 4, v___x_2080_);
lean_ctor_set(v___x_1975_, 3, v___x_2078_);
lean_ctor_set(v___x_1975_, 2, v_v_2072_);
lean_ctor_set(v___x_1975_, 1, v_k_2071_);
lean_ctor_set(v___x_1975_, 0, v___x_2076_);
v___x_2082_ = v___x_1975_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2076_);
lean_ctor_set(v_reuseFailAlloc_2083_, 1, v_k_2071_);
lean_ctor_set(v_reuseFailAlloc_2083_, 2, v_v_2072_);
lean_ctor_set(v_reuseFailAlloc_2083_, 3, v___x_2078_);
lean_ctor_set(v_reuseFailAlloc_2083_, 4, v___x_2080_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
}
}
}
else
{
lean_object* v_r_2093_; 
v_r_2093_ = lean_ctor_get(v_impl_1979_, 4);
lean_inc(v_r_2093_);
if (lean_obj_tag(v_r_2093_) == 0)
{
lean_object* v_k_2094_; lean_object* v_v_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2106_; 
v_k_2094_ = lean_ctor_get(v_impl_1979_, 1);
v_v_2095_ = lean_ctor_get(v_impl_1979_, 2);
v_isSharedCheck_2106_ = !lean_is_exclusive(v_impl_1979_);
if (v_isSharedCheck_2106_ == 0)
{
lean_object* v_unused_2107_; lean_object* v_unused_2108_; lean_object* v_unused_2109_; 
v_unused_2107_ = lean_ctor_get(v_impl_1979_, 4);
lean_dec(v_unused_2107_);
v_unused_2108_ = lean_ctor_get(v_impl_1979_, 3);
lean_dec(v_unused_2108_);
v_unused_2109_ = lean_ctor_get(v_impl_1979_, 0);
lean_dec(v_unused_2109_);
v___x_2097_ = v_impl_1979_;
v_isShared_2098_ = v_isSharedCheck_2106_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_v_2095_);
lean_inc(v_k_2094_);
lean_dec(v_impl_1979_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2106_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2099_; lean_object* v___x_2101_; 
v___x_2099_ = lean_unsigned_to_nat(3u);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 4, v_l_2064_);
lean_ctor_set(v___x_2097_, 2, v_v_1971_);
lean_ctor_set(v___x_2097_, 1, v_k_1970_);
lean_ctor_set(v___x_2097_, 0, v___x_1980_);
v___x_2101_ = v___x_2097_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v___x_1980_);
lean_ctor_set(v_reuseFailAlloc_2105_, 1, v_k_1970_);
lean_ctor_set(v_reuseFailAlloc_2105_, 2, v_v_1971_);
lean_ctor_set(v_reuseFailAlloc_2105_, 3, v_l_2064_);
lean_ctor_set(v_reuseFailAlloc_2105_, 4, v_l_2064_);
v___x_2101_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
lean_object* v___x_2103_; 
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 4, v_r_2093_);
lean_ctor_set(v___x_1975_, 3, v___x_2101_);
lean_ctor_set(v___x_1975_, 2, v_v_2095_);
lean_ctor_set(v___x_1975_, 1, v_k_2094_);
lean_ctor_set(v___x_1975_, 0, v___x_2099_);
v___x_2103_ = v___x_1975_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v___x_2099_);
lean_ctor_set(v_reuseFailAlloc_2104_, 1, v_k_2094_);
lean_ctor_set(v_reuseFailAlloc_2104_, 2, v_v_2095_);
lean_ctor_set(v_reuseFailAlloc_2104_, 3, v___x_2101_);
lean_ctor_set(v_reuseFailAlloc_2104_, 4, v_r_2093_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
}
else
{
lean_object* v___x_2110_; lean_object* v___x_2112_; 
v___x_2110_ = lean_unsigned_to_nat(2u);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 4, v_impl_1979_);
lean_ctor_set(v___x_1975_, 3, v_r_2093_);
lean_ctor_set(v___x_1975_, 0, v___x_2110_);
v___x_2112_ = v___x_1975_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v___x_2110_);
lean_ctor_set(v_reuseFailAlloc_2113_, 1, v_k_1970_);
lean_ctor_set(v_reuseFailAlloc_2113_, 2, v_v_1971_);
lean_ctor_set(v_reuseFailAlloc_2113_, 3, v_r_2093_);
lean_ctor_set(v_reuseFailAlloc_2113_, 4, v_impl_1979_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
}
}
else
{
lean_object* v___x_2115_; 
lean_dec(v_v_1971_);
lean_dec(v_k_1970_);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 2, v_v_1967_);
lean_ctor_set(v___x_1975_, 1, v_k_1966_);
v___x_2115_ = v___x_1975_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_size_1969_);
lean_ctor_set(v_reuseFailAlloc_2116_, 1, v_k_1966_);
lean_ctor_set(v_reuseFailAlloc_2116_, 2, v_v_1967_);
lean_ctor_set(v_reuseFailAlloc_2116_, 3, v_l_1972_);
lean_ctor_set(v_reuseFailAlloc_2116_, 4, v_r_1973_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
else
{
lean_object* v_impl_2117_; lean_object* v___x_2118_; 
lean_dec(v_size_1969_);
v_impl_2117_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_k_1966_, v_v_1967_, v_l_1972_);
v___x_2118_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1973_) == 0)
{
lean_object* v_size_2119_; lean_object* v_size_2120_; lean_object* v_k_2121_; lean_object* v_v_2122_; lean_object* v_l_2123_; lean_object* v_r_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; uint8_t v___x_2127_; 
v_size_2119_ = lean_ctor_get(v_r_1973_, 0);
v_size_2120_ = lean_ctor_get(v_impl_2117_, 0);
lean_inc(v_size_2120_);
v_k_2121_ = lean_ctor_get(v_impl_2117_, 1);
lean_inc(v_k_2121_);
v_v_2122_ = lean_ctor_get(v_impl_2117_, 2);
lean_inc(v_v_2122_);
v_l_2123_ = lean_ctor_get(v_impl_2117_, 3);
lean_inc(v_l_2123_);
v_r_2124_ = lean_ctor_get(v_impl_2117_, 4);
lean_inc(v_r_2124_);
v___x_2125_ = lean_unsigned_to_nat(3u);
v___x_2126_ = lean_nat_mul(v___x_2125_, v_size_2119_);
v___x_2127_ = lean_nat_dec_lt(v___x_2126_, v_size_2120_);
lean_dec(v___x_2126_);
if (v___x_2127_ == 0)
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2131_; 
lean_dec(v_r_2124_);
lean_dec(v_l_2123_);
lean_dec(v_v_2122_);
lean_dec(v_k_2121_);
v___x_2128_ = lean_nat_add(v___x_2118_, v_size_2120_);
lean_dec(v_size_2120_);
v___x_2129_ = lean_nat_add(v___x_2128_, v_size_2119_);
lean_dec(v___x_2128_);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 3, v_impl_2117_);
lean_ctor_set(v___x_1975_, 0, v___x_2129_);
v___x_2131_ = v___x_1975_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v___x_2129_);
lean_ctor_set(v_reuseFailAlloc_2132_, 1, v_k_1970_);
lean_ctor_set(v_reuseFailAlloc_2132_, 2, v_v_1971_);
lean_ctor_set(v_reuseFailAlloc_2132_, 3, v_impl_2117_);
lean_ctor_set(v_reuseFailAlloc_2132_, 4, v_r_1973_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
else
{
lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2198_; 
v_isSharedCheck_2198_ = !lean_is_exclusive(v_impl_2117_);
if (v_isSharedCheck_2198_ == 0)
{
lean_object* v_unused_2199_; lean_object* v_unused_2200_; lean_object* v_unused_2201_; lean_object* v_unused_2202_; lean_object* v_unused_2203_; 
v_unused_2199_ = lean_ctor_get(v_impl_2117_, 4);
lean_dec(v_unused_2199_);
v_unused_2200_ = lean_ctor_get(v_impl_2117_, 3);
lean_dec(v_unused_2200_);
v_unused_2201_ = lean_ctor_get(v_impl_2117_, 2);
lean_dec(v_unused_2201_);
v_unused_2202_ = lean_ctor_get(v_impl_2117_, 1);
lean_dec(v_unused_2202_);
v_unused_2203_ = lean_ctor_get(v_impl_2117_, 0);
lean_dec(v_unused_2203_);
v___x_2134_ = v_impl_2117_;
v_isShared_2135_ = v_isSharedCheck_2198_;
goto v_resetjp_2133_;
}
else
{
lean_dec(v_impl_2117_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2198_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v_size_2136_; lean_object* v_size_2137_; lean_object* v_k_2138_; lean_object* v_v_2139_; lean_object* v_l_2140_; lean_object* v_r_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; uint8_t v___x_2144_; 
v_size_2136_ = lean_ctor_get(v_l_2123_, 0);
v_size_2137_ = lean_ctor_get(v_r_2124_, 0);
v_k_2138_ = lean_ctor_get(v_r_2124_, 1);
v_v_2139_ = lean_ctor_get(v_r_2124_, 2);
v_l_2140_ = lean_ctor_get(v_r_2124_, 3);
v_r_2141_ = lean_ctor_get(v_r_2124_, 4);
v___x_2142_ = lean_unsigned_to_nat(2u);
v___x_2143_ = lean_nat_mul(v___x_2142_, v_size_2136_);
v___x_2144_ = lean_nat_dec_lt(v_size_2137_, v___x_2143_);
lean_dec(v___x_2143_);
if (v___x_2144_ == 0)
{
lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2173_; 
lean_inc(v_r_2141_);
lean_inc(v_l_2140_);
lean_inc(v_v_2139_);
lean_inc(v_k_2138_);
v_isSharedCheck_2173_ = !lean_is_exclusive(v_r_2124_);
if (v_isSharedCheck_2173_ == 0)
{
lean_object* v_unused_2174_; lean_object* v_unused_2175_; lean_object* v_unused_2176_; lean_object* v_unused_2177_; lean_object* v_unused_2178_; 
v_unused_2174_ = lean_ctor_get(v_r_2124_, 4);
lean_dec(v_unused_2174_);
v_unused_2175_ = lean_ctor_get(v_r_2124_, 3);
lean_dec(v_unused_2175_);
v_unused_2176_ = lean_ctor_get(v_r_2124_, 2);
lean_dec(v_unused_2176_);
v_unused_2177_ = lean_ctor_get(v_r_2124_, 1);
lean_dec(v_unused_2177_);
v_unused_2178_ = lean_ctor_get(v_r_2124_, 0);
lean_dec(v_unused_2178_);
v___x_2146_ = v_r_2124_;
v_isShared_2147_ = v_isSharedCheck_2173_;
goto v_resetjp_2145_;
}
else
{
lean_dec(v_r_2124_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2173_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___y_2151_; lean_object* v___y_2152_; lean_object* v___y_2153_; lean_object* v___x_2161_; lean_object* v___y_2163_; 
v___x_2148_ = lean_nat_add(v___x_2118_, v_size_2120_);
lean_dec(v_size_2120_);
v___x_2149_ = lean_nat_add(v___x_2148_, v_size_2119_);
lean_dec(v___x_2148_);
v___x_2161_ = lean_nat_add(v___x_2118_, v_size_2136_);
if (lean_obj_tag(v_l_2140_) == 0)
{
lean_object* v_size_2171_; 
v_size_2171_ = lean_ctor_get(v_l_2140_, 0);
lean_inc(v_size_2171_);
v___y_2163_ = v_size_2171_;
goto v___jp_2162_;
}
else
{
lean_object* v___x_2172_; 
v___x_2172_ = lean_unsigned_to_nat(0u);
v___y_2163_ = v___x_2172_;
goto v___jp_2162_;
}
v___jp_2150_:
{
lean_object* v___x_2154_; lean_object* v___x_2156_; 
v___x_2154_ = lean_nat_add(v___y_2152_, v___y_2153_);
lean_dec(v___y_2153_);
lean_dec(v___y_2152_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 4, v_r_1973_);
lean_ctor_set(v___x_2146_, 3, v_r_2141_);
lean_ctor_set(v___x_2146_, 2, v_v_1971_);
lean_ctor_set(v___x_2146_, 1, v_k_1970_);
lean_ctor_set(v___x_2146_, 0, v___x_2154_);
v___x_2156_ = v___x_2146_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2154_);
lean_ctor_set(v_reuseFailAlloc_2160_, 1, v_k_1970_);
lean_ctor_set(v_reuseFailAlloc_2160_, 2, v_v_1971_);
lean_ctor_set(v_reuseFailAlloc_2160_, 3, v_r_2141_);
lean_ctor_set(v_reuseFailAlloc_2160_, 4, v_r_1973_);
v___x_2156_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
lean_object* v___x_2158_; 
if (v_isShared_2135_ == 0)
{
lean_ctor_set(v___x_2134_, 4, v___x_2156_);
lean_ctor_set(v___x_2134_, 3, v___y_2151_);
lean_ctor_set(v___x_2134_, 2, v_v_2139_);
lean_ctor_set(v___x_2134_, 1, v_k_2138_);
lean_ctor_set(v___x_2134_, 0, v___x_2149_);
v___x_2158_ = v___x_2134_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v___x_2149_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v_k_2138_);
lean_ctor_set(v_reuseFailAlloc_2159_, 2, v_v_2139_);
lean_ctor_set(v_reuseFailAlloc_2159_, 3, v___y_2151_);
lean_ctor_set(v_reuseFailAlloc_2159_, 4, v___x_2156_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
v___jp_2162_:
{
lean_object* v___x_2164_; lean_object* v___x_2166_; 
v___x_2164_ = lean_nat_add(v___x_2161_, v___y_2163_);
lean_dec(v___y_2163_);
lean_dec(v___x_2161_);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 4, v_l_2140_);
lean_ctor_set(v___x_1975_, 3, v_l_2123_);
lean_ctor_set(v___x_1975_, 2, v_v_2122_);
lean_ctor_set(v___x_1975_, 1, v_k_2121_);
lean_ctor_set(v___x_1975_, 0, v___x_2164_);
v___x_2166_ = v___x_1975_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v___x_2164_);
lean_ctor_set(v_reuseFailAlloc_2170_, 1, v_k_2121_);
lean_ctor_set(v_reuseFailAlloc_2170_, 2, v_v_2122_);
lean_ctor_set(v_reuseFailAlloc_2170_, 3, v_l_2123_);
lean_ctor_set(v_reuseFailAlloc_2170_, 4, v_l_2140_);
v___x_2166_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
lean_object* v___x_2167_; 
v___x_2167_ = lean_nat_add(v___x_2118_, v_size_2119_);
if (lean_obj_tag(v_r_2141_) == 0)
{
lean_object* v_size_2168_; 
v_size_2168_ = lean_ctor_get(v_r_2141_, 0);
lean_inc(v_size_2168_);
v___y_2151_ = v___x_2166_;
v___y_2152_ = v___x_2167_;
v___y_2153_ = v_size_2168_;
goto v___jp_2150_;
}
else
{
lean_object* v___x_2169_; 
v___x_2169_ = lean_unsigned_to_nat(0u);
v___y_2151_ = v___x_2166_;
v___y_2152_ = v___x_2167_;
v___y_2153_ = v___x_2169_;
goto v___jp_2150_;
}
}
}
}
}
else
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2184_; 
lean_del_object(v___x_1975_);
v___x_2179_ = lean_nat_add(v___x_2118_, v_size_2120_);
lean_dec(v_size_2120_);
v___x_2180_ = lean_nat_add(v___x_2179_, v_size_2119_);
lean_dec(v___x_2179_);
v___x_2181_ = lean_nat_add(v___x_2118_, v_size_2119_);
v___x_2182_ = lean_nat_add(v___x_2181_, v_size_2137_);
lean_dec(v___x_2181_);
lean_inc_ref(v_r_1973_);
if (v_isShared_2135_ == 0)
{
lean_ctor_set(v___x_2134_, 4, v_r_1973_);
lean_ctor_set(v___x_2134_, 3, v_r_2124_);
lean_ctor_set(v___x_2134_, 2, v_v_1971_);
lean_ctor_set(v___x_2134_, 1, v_k_1970_);
lean_ctor_set(v___x_2134_, 0, v___x_2182_);
v___x_2184_ = v___x_2134_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___x_2182_);
lean_ctor_set(v_reuseFailAlloc_2197_, 1, v_k_1970_);
lean_ctor_set(v_reuseFailAlloc_2197_, 2, v_v_1971_);
lean_ctor_set(v_reuseFailAlloc_2197_, 3, v_r_2124_);
lean_ctor_set(v_reuseFailAlloc_2197_, 4, v_r_1973_);
v___x_2184_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2191_; 
v_isSharedCheck_2191_ = !lean_is_exclusive(v_r_1973_);
if (v_isSharedCheck_2191_ == 0)
{
lean_object* v_unused_2192_; lean_object* v_unused_2193_; lean_object* v_unused_2194_; lean_object* v_unused_2195_; lean_object* v_unused_2196_; 
v_unused_2192_ = lean_ctor_get(v_r_1973_, 4);
lean_dec(v_unused_2192_);
v_unused_2193_ = lean_ctor_get(v_r_1973_, 3);
lean_dec(v_unused_2193_);
v_unused_2194_ = lean_ctor_get(v_r_1973_, 2);
lean_dec(v_unused_2194_);
v_unused_2195_ = lean_ctor_get(v_r_1973_, 1);
lean_dec(v_unused_2195_);
v_unused_2196_ = lean_ctor_get(v_r_1973_, 0);
lean_dec(v_unused_2196_);
v___x_2186_ = v_r_1973_;
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
else
{
lean_dec(v_r_1973_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2189_; 
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 4, v___x_2184_);
lean_ctor_set(v___x_2186_, 3, v_l_2123_);
lean_ctor_set(v___x_2186_, 2, v_v_2122_);
lean_ctor_set(v___x_2186_, 1, v_k_2121_);
lean_ctor_set(v___x_2186_, 0, v___x_2180_);
v___x_2189_ = v___x_2186_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2180_);
lean_ctor_set(v_reuseFailAlloc_2190_, 1, v_k_2121_);
lean_ctor_set(v_reuseFailAlloc_2190_, 2, v_v_2122_);
lean_ctor_set(v_reuseFailAlloc_2190_, 3, v_l_2123_);
lean_ctor_set(v_reuseFailAlloc_2190_, 4, v___x_2184_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2204_; 
v_l_2204_ = lean_ctor_get(v_impl_2117_, 3);
lean_inc(v_l_2204_);
if (lean_obj_tag(v_l_2204_) == 0)
{
lean_object* v_r_2205_; lean_object* v_k_2206_; lean_object* v_v_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2218_; 
v_r_2205_ = lean_ctor_get(v_impl_2117_, 4);
v_k_2206_ = lean_ctor_get(v_impl_2117_, 1);
v_v_2207_ = lean_ctor_get(v_impl_2117_, 2);
v_isSharedCheck_2218_ = !lean_is_exclusive(v_impl_2117_);
if (v_isSharedCheck_2218_ == 0)
{
lean_object* v_unused_2219_; lean_object* v_unused_2220_; 
v_unused_2219_ = lean_ctor_get(v_impl_2117_, 3);
lean_dec(v_unused_2219_);
v_unused_2220_ = lean_ctor_get(v_impl_2117_, 0);
lean_dec(v_unused_2220_);
v___x_2209_ = v_impl_2117_;
v_isShared_2210_ = v_isSharedCheck_2218_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_r_2205_);
lean_inc(v_v_2207_);
lean_inc(v_k_2206_);
lean_dec(v_impl_2117_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2218_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2211_; lean_object* v___x_2213_; 
v___x_2211_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2205_);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 3, v_r_2205_);
lean_ctor_set(v___x_2209_, 2, v_v_1971_);
lean_ctor_set(v___x_2209_, 1, v_k_1970_);
lean_ctor_set(v___x_2209_, 0, v___x_2118_);
v___x_2213_ = v___x_2209_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v___x_2118_);
lean_ctor_set(v_reuseFailAlloc_2217_, 1, v_k_1970_);
lean_ctor_set(v_reuseFailAlloc_2217_, 2, v_v_1971_);
lean_ctor_set(v_reuseFailAlloc_2217_, 3, v_r_2205_);
lean_ctor_set(v_reuseFailAlloc_2217_, 4, v_r_2205_);
v___x_2213_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
lean_object* v___x_2215_; 
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 4, v___x_2213_);
lean_ctor_set(v___x_1975_, 3, v_l_2204_);
lean_ctor_set(v___x_1975_, 2, v_v_2207_);
lean_ctor_set(v___x_1975_, 1, v_k_2206_);
lean_ctor_set(v___x_1975_, 0, v___x_2211_);
v___x_2215_ = v___x_1975_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v___x_2211_);
lean_ctor_set(v_reuseFailAlloc_2216_, 1, v_k_2206_);
lean_ctor_set(v_reuseFailAlloc_2216_, 2, v_v_2207_);
lean_ctor_set(v_reuseFailAlloc_2216_, 3, v_l_2204_);
lean_ctor_set(v_reuseFailAlloc_2216_, 4, v___x_2213_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
}
else
{
lean_object* v_r_2221_; 
v_r_2221_ = lean_ctor_get(v_impl_2117_, 4);
lean_inc(v_r_2221_);
if (lean_obj_tag(v_r_2221_) == 0)
{
lean_object* v_k_2222_; lean_object* v_v_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2246_; 
v_k_2222_ = lean_ctor_get(v_impl_2117_, 1);
v_v_2223_ = lean_ctor_get(v_impl_2117_, 2);
v_isSharedCheck_2246_ = !lean_is_exclusive(v_impl_2117_);
if (v_isSharedCheck_2246_ == 0)
{
lean_object* v_unused_2247_; lean_object* v_unused_2248_; lean_object* v_unused_2249_; 
v_unused_2247_ = lean_ctor_get(v_impl_2117_, 4);
lean_dec(v_unused_2247_);
v_unused_2248_ = lean_ctor_get(v_impl_2117_, 3);
lean_dec(v_unused_2248_);
v_unused_2249_ = lean_ctor_get(v_impl_2117_, 0);
lean_dec(v_unused_2249_);
v___x_2225_ = v_impl_2117_;
v_isShared_2226_ = v_isSharedCheck_2246_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_v_2223_);
lean_inc(v_k_2222_);
lean_dec(v_impl_2117_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2246_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v_k_2227_; lean_object* v_v_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2242_; 
v_k_2227_ = lean_ctor_get(v_r_2221_, 1);
v_v_2228_ = lean_ctor_get(v_r_2221_, 2);
v_isSharedCheck_2242_ = !lean_is_exclusive(v_r_2221_);
if (v_isSharedCheck_2242_ == 0)
{
lean_object* v_unused_2243_; lean_object* v_unused_2244_; lean_object* v_unused_2245_; 
v_unused_2243_ = lean_ctor_get(v_r_2221_, 4);
lean_dec(v_unused_2243_);
v_unused_2244_ = lean_ctor_get(v_r_2221_, 3);
lean_dec(v_unused_2244_);
v_unused_2245_ = lean_ctor_get(v_r_2221_, 0);
lean_dec(v_unused_2245_);
v___x_2230_ = v_r_2221_;
v_isShared_2231_ = v_isSharedCheck_2242_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_v_2228_);
lean_inc(v_k_2227_);
lean_dec(v_r_2221_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2242_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2232_; lean_object* v___x_2234_; 
v___x_2232_ = lean_unsigned_to_nat(3u);
if (v_isShared_2231_ == 0)
{
lean_ctor_set(v___x_2230_, 4, v_l_2204_);
lean_ctor_set(v___x_2230_, 3, v_l_2204_);
lean_ctor_set(v___x_2230_, 2, v_v_2223_);
lean_ctor_set(v___x_2230_, 1, v_k_2222_);
lean_ctor_set(v___x_2230_, 0, v___x_2118_);
v___x_2234_ = v___x_2230_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2118_);
lean_ctor_set(v_reuseFailAlloc_2241_, 1, v_k_2222_);
lean_ctor_set(v_reuseFailAlloc_2241_, 2, v_v_2223_);
lean_ctor_set(v_reuseFailAlloc_2241_, 3, v_l_2204_);
lean_ctor_set(v_reuseFailAlloc_2241_, 4, v_l_2204_);
v___x_2234_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
lean_object* v___x_2236_; 
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 4, v_l_2204_);
lean_ctor_set(v___x_2225_, 2, v_v_1971_);
lean_ctor_set(v___x_2225_, 1, v_k_1970_);
lean_ctor_set(v___x_2225_, 0, v___x_2118_);
v___x_2236_ = v___x_2225_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2118_);
lean_ctor_set(v_reuseFailAlloc_2240_, 1, v_k_1970_);
lean_ctor_set(v_reuseFailAlloc_2240_, 2, v_v_1971_);
lean_ctor_set(v_reuseFailAlloc_2240_, 3, v_l_2204_);
lean_ctor_set(v_reuseFailAlloc_2240_, 4, v_l_2204_);
v___x_2236_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
lean_object* v___x_2238_; 
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 4, v___x_2236_);
lean_ctor_set(v___x_1975_, 3, v___x_2234_);
lean_ctor_set(v___x_1975_, 2, v_v_2228_);
lean_ctor_set(v___x_1975_, 1, v_k_2227_);
lean_ctor_set(v___x_1975_, 0, v___x_2232_);
v___x_2238_ = v___x_1975_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v___x_2232_);
lean_ctor_set(v_reuseFailAlloc_2239_, 1, v_k_2227_);
lean_ctor_set(v_reuseFailAlloc_2239_, 2, v_v_2228_);
lean_ctor_set(v_reuseFailAlloc_2239_, 3, v___x_2234_);
lean_ctor_set(v_reuseFailAlloc_2239_, 4, v___x_2236_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
}
}
}
else
{
lean_object* v___x_2250_; lean_object* v___x_2252_; 
v___x_2250_ = lean_unsigned_to_nat(2u);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 4, v_r_2221_);
lean_ctor_set(v___x_1975_, 3, v_impl_2117_);
lean_ctor_set(v___x_1975_, 0, v___x_2250_);
v___x_2252_ = v___x_1975_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v___x_2250_);
lean_ctor_set(v_reuseFailAlloc_2253_, 1, v_k_1970_);
lean_ctor_set(v_reuseFailAlloc_2253_, 2, v_v_1971_);
lean_ctor_set(v_reuseFailAlloc_2253_, 3, v_impl_2117_);
lean_ctor_set(v_reuseFailAlloc_2253_, 4, v_r_2221_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = lean_unsigned_to_nat(1u);
v___x_2256_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2255_);
lean_ctor_set(v___x_2256_, 1, v_k_1966_);
lean_ctor_set(v___x_2256_, 2, v_v_1967_);
lean_ctor_set(v___x_2256_, 3, v_t_1968_);
lean_ctor_set(v___x_2256_, 4, v_t_1968_);
return v___x_2256_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2(lean_object* v_y_2257_, lean_object* v_x_2258_, size_t v_x_2259_, size_t v_x_2260_){
_start:
{
if (lean_obj_tag(v_x_2258_) == 0)
{
lean_object* v_cs_2261_; size_t v_j_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; uint8_t v___x_2265_; 
v_cs_2261_ = lean_ctor_get(v_x_2258_, 0);
v_j_2262_ = lean_usize_shift_right(v_x_2259_, v_x_2260_);
v___x_2263_ = lean_usize_to_nat(v_j_2262_);
v___x_2264_ = lean_array_get_size(v_cs_2261_);
v___x_2265_ = lean_nat_dec_lt(v___x_2263_, v___x_2264_);
if (v___x_2265_ == 0)
{
lean_dec(v___x_2263_);
lean_dec(v_y_2257_);
return v_x_2258_;
}
else
{
lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2283_; 
lean_inc_ref(v_cs_2261_);
v_isSharedCheck_2283_ = !lean_is_exclusive(v_x_2258_);
if (v_isSharedCheck_2283_ == 0)
{
lean_object* v_unused_2284_; 
v_unused_2284_ = lean_ctor_get(v_x_2258_, 0);
lean_dec(v_unused_2284_);
v___x_2267_ = v_x_2258_;
v_isShared_2268_ = v_isSharedCheck_2283_;
goto v_resetjp_2266_;
}
else
{
lean_dec(v_x_2258_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2283_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
size_t v___x_2269_; size_t v___x_2270_; size_t v___x_2271_; size_t v_i_2272_; size_t v___x_2273_; size_t v_shift_2274_; lean_object* v_v_2275_; lean_object* v___x_2276_; lean_object* v_xs_x27_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2281_; 
v___x_2269_ = ((size_t)1ULL);
v___x_2270_ = lean_usize_shift_left(v___x_2269_, v_x_2260_);
v___x_2271_ = lean_usize_sub(v___x_2270_, v___x_2269_);
v_i_2272_ = lean_usize_land(v_x_2259_, v___x_2271_);
v___x_2273_ = ((size_t)5ULL);
v_shift_2274_ = lean_usize_sub(v_x_2260_, v___x_2273_);
v_v_2275_ = lean_array_fget(v_cs_2261_, v___x_2263_);
v___x_2276_ = lean_box(0);
v_xs_x27_2277_ = lean_array_fset(v_cs_2261_, v___x_2263_, v___x_2276_);
v___x_2278_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2(v_y_2257_, v_v_2275_, v_i_2272_, v_shift_2274_);
v___x_2279_ = lean_array_fset(v_xs_x27_2277_, v___x_2263_, v___x_2278_);
lean_dec(v___x_2263_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 0, v___x_2279_);
v___x_2281_ = v___x_2267_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v___x_2279_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
}
else
{
lean_object* v_vs_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; uint8_t v___x_2288_; 
v_vs_2285_ = lean_ctor_get(v_x_2258_, 0);
v___x_2286_ = lean_usize_to_nat(v_x_2259_);
v___x_2287_ = lean_array_get_size(v_vs_2285_);
v___x_2288_ = lean_nat_dec_lt(v___x_2286_, v___x_2287_);
if (v___x_2288_ == 0)
{
lean_dec(v___x_2286_);
lean_dec(v_y_2257_);
return v_x_2258_;
}
else
{
lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2303_; 
lean_inc_ref(v_vs_2285_);
v_isSharedCheck_2303_ = !lean_is_exclusive(v_x_2258_);
if (v_isSharedCheck_2303_ == 0)
{
lean_object* v_unused_2304_; 
v_unused_2304_ = lean_ctor_get(v_x_2258_, 0);
lean_dec(v_unused_2304_);
v___x_2290_ = v_x_2258_;
v_isShared_2291_ = v_isSharedCheck_2303_;
goto v_resetjp_2289_;
}
else
{
lean_dec(v_x_2258_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2303_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v_v_2292_; lean_object* v___x_2293_; lean_object* v_xs_x27_2294_; lean_object* v___y_2296_; uint8_t v___x_2301_; 
v_v_2292_ = lean_array_fget(v_vs_2285_, v___x_2286_);
v___x_2293_ = lean_box(0);
v_xs_x27_2294_ = lean_array_fset(v_vs_2285_, v___x_2286_, v___x_2293_);
v___x_2301_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_y_2257_, v_v_2292_);
if (v___x_2301_ == 0)
{
lean_object* v___x_2302_; 
v___x_2302_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_y_2257_, v___x_2293_, v_v_2292_);
v___y_2296_ = v___x_2302_;
goto v___jp_2295_;
}
else
{
lean_dec(v_y_2257_);
v___y_2296_ = v_v_2292_;
goto v___jp_2295_;
}
v___jp_2295_:
{
lean_object* v___x_2297_; lean_object* v___x_2299_; 
v___x_2297_ = lean_array_fset(v_xs_x27_2294_, v___x_2286_, v___y_2296_);
lean_dec(v___x_2286_);
if (v_isShared_2291_ == 0)
{
lean_ctor_set(v___x_2290_, 0, v___x_2297_);
v___x_2299_ = v___x_2290_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v___x_2297_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2___boxed(lean_object* v_y_2305_, lean_object* v_x_2306_, lean_object* v_x_2307_, lean_object* v_x_2308_){
_start:
{
size_t v_x_6038__boxed_2309_; size_t v_x_6039__boxed_2310_; lean_object* v_res_2311_; 
v_x_6038__boxed_2309_ = lean_unbox_usize(v_x_2307_);
lean_dec(v_x_2307_);
v_x_6039__boxed_2310_ = lean_unbox_usize(v_x_2308_);
lean_dec(v_x_2308_);
v_res_2311_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2(v_y_2305_, v_x_2306_, v_x_6038__boxed_2309_, v_x_6039__boxed_2310_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2(lean_object* v_y_2312_, lean_object* v_t_2313_, lean_object* v_i_2314_){
_start:
{
lean_object* v_root_2315_; lean_object* v_tail_2316_; lean_object* v_size_2317_; size_t v_shift_2318_; lean_object* v_tailOff_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2346_; 
v_root_2315_ = lean_ctor_get(v_t_2313_, 0);
v_tail_2316_ = lean_ctor_get(v_t_2313_, 1);
v_size_2317_ = lean_ctor_get(v_t_2313_, 2);
v_shift_2318_ = lean_ctor_get_usize(v_t_2313_, 4);
v_tailOff_2319_ = lean_ctor_get(v_t_2313_, 3);
v_isSharedCheck_2346_ = !lean_is_exclusive(v_t_2313_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2321_ = v_t_2313_;
v_isShared_2322_ = v_isSharedCheck_2346_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_tailOff_2319_);
lean_inc(v_size_2317_);
lean_inc(v_tail_2316_);
lean_inc(v_root_2315_);
lean_dec(v_t_2313_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2346_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
uint8_t v___x_2323_; 
v___x_2323_ = lean_nat_dec_le(v_tailOff_2319_, v_i_2314_);
if (v___x_2323_ == 0)
{
size_t v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2327_; 
v___x_2324_ = lean_usize_of_nat(v_i_2314_);
v___x_2325_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2(v_y_2312_, v_root_2315_, v___x_2324_, v_shift_2318_);
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 0, v___x_2325_);
v___x_2327_ = v___x_2321_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v___x_2325_);
lean_ctor_set(v_reuseFailAlloc_2328_, 1, v_tail_2316_);
lean_ctor_set(v_reuseFailAlloc_2328_, 2, v_size_2317_);
lean_ctor_set(v_reuseFailAlloc_2328_, 3, v_tailOff_2319_);
lean_ctor_set_usize(v_reuseFailAlloc_2328_, 4, v_shift_2318_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
else
{
lean_object* v___x_2329_; lean_object* v___x_2330_; uint8_t v___x_2331_; 
v___x_2329_ = lean_nat_sub(v_i_2314_, v_tailOff_2319_);
v___x_2330_ = lean_array_get_size(v_tail_2316_);
v___x_2331_ = lean_nat_dec_lt(v___x_2329_, v___x_2330_);
if (v___x_2331_ == 0)
{
lean_object* v___x_2333_; 
lean_dec(v___x_2329_);
lean_dec(v_y_2312_);
if (v_isShared_2322_ == 0)
{
v___x_2333_ = v___x_2321_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_root_2315_);
lean_ctor_set(v_reuseFailAlloc_2334_, 1, v_tail_2316_);
lean_ctor_set(v_reuseFailAlloc_2334_, 2, v_size_2317_);
lean_ctor_set(v_reuseFailAlloc_2334_, 3, v_tailOff_2319_);
lean_ctor_set_usize(v_reuseFailAlloc_2334_, 4, v_shift_2318_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
else
{
lean_object* v_v_2335_; lean_object* v___x_2336_; lean_object* v_xs_x27_2337_; lean_object* v___y_2339_; uint8_t v___x_2344_; 
v_v_2335_ = lean_array_fget(v_tail_2316_, v___x_2329_);
v___x_2336_ = lean_box(0);
v_xs_x27_2337_ = lean_array_fset(v_tail_2316_, v___x_2329_, v___x_2336_);
v___x_2344_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_y_2312_, v_v_2335_);
if (v___x_2344_ == 0)
{
lean_object* v___x_2345_; 
v___x_2345_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_y_2312_, v___x_2336_, v_v_2335_);
v___y_2339_ = v___x_2345_;
goto v___jp_2338_;
}
else
{
lean_dec(v_y_2312_);
v___y_2339_ = v_v_2335_;
goto v___jp_2338_;
}
v___jp_2338_:
{
lean_object* v___x_2340_; lean_object* v___x_2342_; 
v___x_2340_ = lean_array_fset(v_xs_x27_2337_, v___x_2329_, v___y_2339_);
lean_dec(v___x_2329_);
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 1, v___x_2340_);
v___x_2342_ = v___x_2321_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_root_2315_);
lean_ctor_set(v_reuseFailAlloc_2343_, 1, v___x_2340_);
lean_ctor_set(v_reuseFailAlloc_2343_, 2, v_size_2317_);
lean_ctor_set(v_reuseFailAlloc_2343_, 3, v_tailOff_2319_);
lean_ctor_set_usize(v_reuseFailAlloc_2343_, 4, v_shift_2318_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2___boxed(lean_object* v_y_2347_, lean_object* v_t_2348_, lean_object* v_i_2349_){
_start:
{
lean_object* v_res_2350_; 
v_res_2350_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2(v_y_2347_, v_t_2348_, v_i_2349_);
lean_dec(v_i_2349_);
return v_res_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0(lean_object* v_a_2351_, lean_object* v_y_2352_, lean_object* v_x_2353_, lean_object* v_s_2354_){
_start:
{
lean_object* v_structs_2355_; lean_object* v_typeIdOf_2356_; lean_object* v_exprToStructId_2357_; lean_object* v_exprToStructIdEntries_2358_; lean_object* v_forbiddenNatModules_2359_; lean_object* v_natStructs_2360_; lean_object* v_natTypeIdOf_2361_; lean_object* v_exprToNatStructId_2362_; lean_object* v___x_2363_; uint8_t v___x_2364_; 
v_structs_2355_ = lean_ctor_get(v_s_2354_, 0);
v_typeIdOf_2356_ = lean_ctor_get(v_s_2354_, 1);
v_exprToStructId_2357_ = lean_ctor_get(v_s_2354_, 2);
v_exprToStructIdEntries_2358_ = lean_ctor_get(v_s_2354_, 3);
v_forbiddenNatModules_2359_ = lean_ctor_get(v_s_2354_, 4);
v_natStructs_2360_ = lean_ctor_get(v_s_2354_, 5);
v_natTypeIdOf_2361_ = lean_ctor_get(v_s_2354_, 6);
v_exprToNatStructId_2362_ = lean_ctor_get(v_s_2354_, 7);
v___x_2363_ = lean_array_get_size(v_structs_2355_);
v___x_2364_ = lean_nat_dec_lt(v_a_2351_, v___x_2363_);
if (v___x_2364_ == 0)
{
lean_dec(v_y_2352_);
return v_s_2354_;
}
else
{
lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2426_; 
lean_inc_ref(v_exprToNatStructId_2362_);
lean_inc_ref(v_natTypeIdOf_2361_);
lean_inc_ref(v_natStructs_2360_);
lean_inc_ref(v_forbiddenNatModules_2359_);
lean_inc_ref(v_exprToStructIdEntries_2358_);
lean_inc_ref(v_exprToStructId_2357_);
lean_inc_ref(v_typeIdOf_2356_);
lean_inc_ref(v_structs_2355_);
v_isSharedCheck_2426_ = !lean_is_exclusive(v_s_2354_);
if (v_isSharedCheck_2426_ == 0)
{
lean_object* v_unused_2427_; lean_object* v_unused_2428_; lean_object* v_unused_2429_; lean_object* v_unused_2430_; lean_object* v_unused_2431_; lean_object* v_unused_2432_; lean_object* v_unused_2433_; lean_object* v_unused_2434_; 
v_unused_2427_ = lean_ctor_get(v_s_2354_, 7);
lean_dec(v_unused_2427_);
v_unused_2428_ = lean_ctor_get(v_s_2354_, 6);
lean_dec(v_unused_2428_);
v_unused_2429_ = lean_ctor_get(v_s_2354_, 5);
lean_dec(v_unused_2429_);
v_unused_2430_ = lean_ctor_get(v_s_2354_, 4);
lean_dec(v_unused_2430_);
v_unused_2431_ = lean_ctor_get(v_s_2354_, 3);
lean_dec(v_unused_2431_);
v_unused_2432_ = lean_ctor_get(v_s_2354_, 2);
lean_dec(v_unused_2432_);
v_unused_2433_ = lean_ctor_get(v_s_2354_, 1);
lean_dec(v_unused_2433_);
v_unused_2434_ = lean_ctor_get(v_s_2354_, 0);
lean_dec(v_unused_2434_);
v___x_2366_ = v_s_2354_;
v_isShared_2367_ = v_isSharedCheck_2426_;
goto v_resetjp_2365_;
}
else
{
lean_dec(v_s_2354_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2426_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v_v_2368_; lean_object* v_id_2369_; lean_object* v_ringId_x3f_2370_; lean_object* v_type_2371_; lean_object* v_u_2372_; lean_object* v_intModuleInst_2373_; lean_object* v_leInst_x3f_2374_; lean_object* v_ltInst_x3f_2375_; lean_object* v_lawfulOrderLTInst_x3f_2376_; lean_object* v_isPreorderInst_x3f_2377_; lean_object* v_orderedAddInst_x3f_2378_; lean_object* v_isLinearInst_x3f_2379_; lean_object* v_noNatDivInst_x3f_2380_; lean_object* v_ringInst_x3f_2381_; lean_object* v_commRingInst_x3f_2382_; lean_object* v_orderedRingInst_x3f_2383_; lean_object* v_fieldInst_x3f_2384_; lean_object* v_charInst_x3f_2385_; lean_object* v_zero_2386_; lean_object* v_ofNatZero_2387_; lean_object* v_one_x3f_2388_; lean_object* v_leFn_x3f_2389_; lean_object* v_ltFn_x3f_2390_; lean_object* v_addFn_2391_; lean_object* v_zsmulFn_2392_; lean_object* v_nsmulFn_2393_; lean_object* v_zsmulFn_x3f_2394_; lean_object* v_nsmulFn_x3f_2395_; lean_object* v_homomulFn_x3f_2396_; lean_object* v_subFn_2397_; lean_object* v_negFn_2398_; lean_object* v_vars_2399_; lean_object* v_varMap_2400_; lean_object* v_lowers_2401_; lean_object* v_uppers_2402_; lean_object* v_diseqs_2403_; lean_object* v_assignment_2404_; uint8_t v_caseSplits_2405_; lean_object* v_conflict_x3f_2406_; lean_object* v_diseqSplits_2407_; lean_object* v_elimEqs_2408_; lean_object* v_elimStack_2409_; lean_object* v_occurs_2410_; lean_object* v_ignored_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2425_; 
v_v_2368_ = lean_array_fget(v_structs_2355_, v_a_2351_);
v_id_2369_ = lean_ctor_get(v_v_2368_, 0);
v_ringId_x3f_2370_ = lean_ctor_get(v_v_2368_, 1);
v_type_2371_ = lean_ctor_get(v_v_2368_, 2);
v_u_2372_ = lean_ctor_get(v_v_2368_, 3);
v_intModuleInst_2373_ = lean_ctor_get(v_v_2368_, 4);
v_leInst_x3f_2374_ = lean_ctor_get(v_v_2368_, 5);
v_ltInst_x3f_2375_ = lean_ctor_get(v_v_2368_, 6);
v_lawfulOrderLTInst_x3f_2376_ = lean_ctor_get(v_v_2368_, 7);
v_isPreorderInst_x3f_2377_ = lean_ctor_get(v_v_2368_, 8);
v_orderedAddInst_x3f_2378_ = lean_ctor_get(v_v_2368_, 9);
v_isLinearInst_x3f_2379_ = lean_ctor_get(v_v_2368_, 10);
v_noNatDivInst_x3f_2380_ = lean_ctor_get(v_v_2368_, 11);
v_ringInst_x3f_2381_ = lean_ctor_get(v_v_2368_, 12);
v_commRingInst_x3f_2382_ = lean_ctor_get(v_v_2368_, 13);
v_orderedRingInst_x3f_2383_ = lean_ctor_get(v_v_2368_, 14);
v_fieldInst_x3f_2384_ = lean_ctor_get(v_v_2368_, 15);
v_charInst_x3f_2385_ = lean_ctor_get(v_v_2368_, 16);
v_zero_2386_ = lean_ctor_get(v_v_2368_, 17);
v_ofNatZero_2387_ = lean_ctor_get(v_v_2368_, 18);
v_one_x3f_2388_ = lean_ctor_get(v_v_2368_, 19);
v_leFn_x3f_2389_ = lean_ctor_get(v_v_2368_, 20);
v_ltFn_x3f_2390_ = lean_ctor_get(v_v_2368_, 21);
v_addFn_2391_ = lean_ctor_get(v_v_2368_, 22);
v_zsmulFn_2392_ = lean_ctor_get(v_v_2368_, 23);
v_nsmulFn_2393_ = lean_ctor_get(v_v_2368_, 24);
v_zsmulFn_x3f_2394_ = lean_ctor_get(v_v_2368_, 25);
v_nsmulFn_x3f_2395_ = lean_ctor_get(v_v_2368_, 26);
v_homomulFn_x3f_2396_ = lean_ctor_get(v_v_2368_, 27);
v_subFn_2397_ = lean_ctor_get(v_v_2368_, 28);
v_negFn_2398_ = lean_ctor_get(v_v_2368_, 29);
v_vars_2399_ = lean_ctor_get(v_v_2368_, 30);
v_varMap_2400_ = lean_ctor_get(v_v_2368_, 31);
v_lowers_2401_ = lean_ctor_get(v_v_2368_, 32);
v_uppers_2402_ = lean_ctor_get(v_v_2368_, 33);
v_diseqs_2403_ = lean_ctor_get(v_v_2368_, 34);
v_assignment_2404_ = lean_ctor_get(v_v_2368_, 35);
v_caseSplits_2405_ = lean_ctor_get_uint8(v_v_2368_, sizeof(void*)*42);
v_conflict_x3f_2406_ = lean_ctor_get(v_v_2368_, 36);
v_diseqSplits_2407_ = lean_ctor_get(v_v_2368_, 37);
v_elimEqs_2408_ = lean_ctor_get(v_v_2368_, 38);
v_elimStack_2409_ = lean_ctor_get(v_v_2368_, 39);
v_occurs_2410_ = lean_ctor_get(v_v_2368_, 40);
v_ignored_2411_ = lean_ctor_get(v_v_2368_, 41);
v_isSharedCheck_2425_ = !lean_is_exclusive(v_v_2368_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2413_ = v_v_2368_;
v_isShared_2414_ = v_isSharedCheck_2425_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_ignored_2411_);
lean_inc(v_occurs_2410_);
lean_inc(v_elimStack_2409_);
lean_inc(v_elimEqs_2408_);
lean_inc(v_diseqSplits_2407_);
lean_inc(v_conflict_x3f_2406_);
lean_inc(v_assignment_2404_);
lean_inc(v_diseqs_2403_);
lean_inc(v_uppers_2402_);
lean_inc(v_lowers_2401_);
lean_inc(v_varMap_2400_);
lean_inc(v_vars_2399_);
lean_inc(v_negFn_2398_);
lean_inc(v_subFn_2397_);
lean_inc(v_homomulFn_x3f_2396_);
lean_inc(v_nsmulFn_x3f_2395_);
lean_inc(v_zsmulFn_x3f_2394_);
lean_inc(v_nsmulFn_2393_);
lean_inc(v_zsmulFn_2392_);
lean_inc(v_addFn_2391_);
lean_inc(v_ltFn_x3f_2390_);
lean_inc(v_leFn_x3f_2389_);
lean_inc(v_one_x3f_2388_);
lean_inc(v_ofNatZero_2387_);
lean_inc(v_zero_2386_);
lean_inc(v_charInst_x3f_2385_);
lean_inc(v_fieldInst_x3f_2384_);
lean_inc(v_orderedRingInst_x3f_2383_);
lean_inc(v_commRingInst_x3f_2382_);
lean_inc(v_ringInst_x3f_2381_);
lean_inc(v_noNatDivInst_x3f_2380_);
lean_inc(v_isLinearInst_x3f_2379_);
lean_inc(v_orderedAddInst_x3f_2378_);
lean_inc(v_isPreorderInst_x3f_2377_);
lean_inc(v_lawfulOrderLTInst_x3f_2376_);
lean_inc(v_ltInst_x3f_2375_);
lean_inc(v_leInst_x3f_2374_);
lean_inc(v_intModuleInst_2373_);
lean_inc(v_u_2372_);
lean_inc(v_type_2371_);
lean_inc(v_ringId_x3f_2370_);
lean_inc(v_id_2369_);
lean_dec(v_v_2368_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2425_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2415_; lean_object* v_xs_x27_2416_; lean_object* v___x_2417_; lean_object* v___x_2419_; 
v___x_2415_ = lean_box(0);
v_xs_x27_2416_ = lean_array_fset(v_structs_2355_, v_a_2351_, v___x_2415_);
v___x_2417_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2(v_y_2352_, v_occurs_2410_, v_x_2353_);
if (v_isShared_2414_ == 0)
{
lean_ctor_set(v___x_2413_, 40, v___x_2417_);
v___x_2419_ = v___x_2413_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_id_2369_);
lean_ctor_set(v_reuseFailAlloc_2424_, 1, v_ringId_x3f_2370_);
lean_ctor_set(v_reuseFailAlloc_2424_, 2, v_type_2371_);
lean_ctor_set(v_reuseFailAlloc_2424_, 3, v_u_2372_);
lean_ctor_set(v_reuseFailAlloc_2424_, 4, v_intModuleInst_2373_);
lean_ctor_set(v_reuseFailAlloc_2424_, 5, v_leInst_x3f_2374_);
lean_ctor_set(v_reuseFailAlloc_2424_, 6, v_ltInst_x3f_2375_);
lean_ctor_set(v_reuseFailAlloc_2424_, 7, v_lawfulOrderLTInst_x3f_2376_);
lean_ctor_set(v_reuseFailAlloc_2424_, 8, v_isPreorderInst_x3f_2377_);
lean_ctor_set(v_reuseFailAlloc_2424_, 9, v_orderedAddInst_x3f_2378_);
lean_ctor_set(v_reuseFailAlloc_2424_, 10, v_isLinearInst_x3f_2379_);
lean_ctor_set(v_reuseFailAlloc_2424_, 11, v_noNatDivInst_x3f_2380_);
lean_ctor_set(v_reuseFailAlloc_2424_, 12, v_ringInst_x3f_2381_);
lean_ctor_set(v_reuseFailAlloc_2424_, 13, v_commRingInst_x3f_2382_);
lean_ctor_set(v_reuseFailAlloc_2424_, 14, v_orderedRingInst_x3f_2383_);
lean_ctor_set(v_reuseFailAlloc_2424_, 15, v_fieldInst_x3f_2384_);
lean_ctor_set(v_reuseFailAlloc_2424_, 16, v_charInst_x3f_2385_);
lean_ctor_set(v_reuseFailAlloc_2424_, 17, v_zero_2386_);
lean_ctor_set(v_reuseFailAlloc_2424_, 18, v_ofNatZero_2387_);
lean_ctor_set(v_reuseFailAlloc_2424_, 19, v_one_x3f_2388_);
lean_ctor_set(v_reuseFailAlloc_2424_, 20, v_leFn_x3f_2389_);
lean_ctor_set(v_reuseFailAlloc_2424_, 21, v_ltFn_x3f_2390_);
lean_ctor_set(v_reuseFailAlloc_2424_, 22, v_addFn_2391_);
lean_ctor_set(v_reuseFailAlloc_2424_, 23, v_zsmulFn_2392_);
lean_ctor_set(v_reuseFailAlloc_2424_, 24, v_nsmulFn_2393_);
lean_ctor_set(v_reuseFailAlloc_2424_, 25, v_zsmulFn_x3f_2394_);
lean_ctor_set(v_reuseFailAlloc_2424_, 26, v_nsmulFn_x3f_2395_);
lean_ctor_set(v_reuseFailAlloc_2424_, 27, v_homomulFn_x3f_2396_);
lean_ctor_set(v_reuseFailAlloc_2424_, 28, v_subFn_2397_);
lean_ctor_set(v_reuseFailAlloc_2424_, 29, v_negFn_2398_);
lean_ctor_set(v_reuseFailAlloc_2424_, 30, v_vars_2399_);
lean_ctor_set(v_reuseFailAlloc_2424_, 31, v_varMap_2400_);
lean_ctor_set(v_reuseFailAlloc_2424_, 32, v_lowers_2401_);
lean_ctor_set(v_reuseFailAlloc_2424_, 33, v_uppers_2402_);
lean_ctor_set(v_reuseFailAlloc_2424_, 34, v_diseqs_2403_);
lean_ctor_set(v_reuseFailAlloc_2424_, 35, v_assignment_2404_);
lean_ctor_set(v_reuseFailAlloc_2424_, 36, v_conflict_x3f_2406_);
lean_ctor_set(v_reuseFailAlloc_2424_, 37, v_diseqSplits_2407_);
lean_ctor_set(v_reuseFailAlloc_2424_, 38, v_elimEqs_2408_);
lean_ctor_set(v_reuseFailAlloc_2424_, 39, v_elimStack_2409_);
lean_ctor_set(v_reuseFailAlloc_2424_, 40, v___x_2417_);
lean_ctor_set(v_reuseFailAlloc_2424_, 41, v_ignored_2411_);
lean_ctor_set_uint8(v_reuseFailAlloc_2424_, sizeof(void*)*42, v_caseSplits_2405_);
v___x_2419_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
lean_object* v___x_2420_; lean_object* v___x_2422_; 
v___x_2420_ = lean_array_fset(v_xs_x27_2416_, v_a_2351_, v___x_2419_);
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 0, v___x_2420_);
v___x_2422_ = v___x_2366_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v___x_2420_);
lean_ctor_set(v_reuseFailAlloc_2423_, 1, v_typeIdOf_2356_);
lean_ctor_set(v_reuseFailAlloc_2423_, 2, v_exprToStructId_2357_);
lean_ctor_set(v_reuseFailAlloc_2423_, 3, v_exprToStructIdEntries_2358_);
lean_ctor_set(v_reuseFailAlloc_2423_, 4, v_forbiddenNatModules_2359_);
lean_ctor_set(v_reuseFailAlloc_2423_, 5, v_natStructs_2360_);
lean_ctor_set(v_reuseFailAlloc_2423_, 6, v_natTypeIdOf_2361_);
lean_ctor_set(v_reuseFailAlloc_2423_, 7, v_exprToNatStructId_2362_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0___boxed(lean_object* v_a_2435_, lean_object* v_y_2436_, lean_object* v_x_2437_, lean_object* v_s_2438_){
_start:
{
lean_object* v_res_2439_; 
v_res_2439_ = l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0(v_a_2435_, v_y_2436_, v_x_2437_, v_s_2438_);
lean_dec(v_x_2437_);
lean_dec(v_a_2435_);
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc(lean_object* v_x_2440_, lean_object* v_y_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_){
_start:
{
lean_object* v___x_2454_; 
v___x_2454_ = l_Lean_Meta_Grind_Arith_Linear_getOccursOf(v_x_2440_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2467_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2457_ = v___x_2454_;
v_isShared_2458_ = v_isSharedCheck_2467_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2454_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2467_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
uint8_t v___x_2459_; 
v___x_2459_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_y_2441_, v_a_2455_);
lean_dec(v_a_2455_);
if (v___x_2459_ == 0)
{
lean_object* v___f_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
lean_del_object(v___x_2457_);
lean_inc(v_a_2442_);
v___f_2460_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2460_, 0, v_a_2442_);
lean_closure_set(v___f_2460_, 1, v_y_2441_);
lean_closure_set(v___f_2460_, 2, v_x_2440_);
v___x_2461_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2462_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2461_, v___f_2460_, v_a_2443_);
return v___x_2462_;
}
else
{
lean_object* v___x_2463_; lean_object* v___x_2465_; 
lean_dec(v_y_2441_);
lean_dec(v_x_2440_);
v___x_2463_ = lean_box(0);
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 0, v___x_2463_);
v___x_2465_ = v___x_2457_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v___x_2463_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
}
else
{
lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2475_; 
lean_dec(v_y_2441_);
lean_dec(v_x_2440_);
v_a_2468_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2470_ = v___x_2454_;
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___x_2454_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2473_; 
if (v_isShared_2471_ == 0)
{
v___x_2473_ = v___x_2470_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_a_2468_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc___boxed(lean_object* v_x_2476_, lean_object* v_y_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_){
_start:
{
lean_object* v_res_2490_; 
v_res_2490_ = l_Lean_Meta_Grind_Arith_Linear_addOcc(v_x_2476_, v_y_2477_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_);
lean_dec(v_a_2488_);
lean_dec_ref(v_a_2487_);
lean_dec(v_a_2486_);
lean_dec_ref(v_a_2485_);
lean_dec(v_a_2484_);
lean_dec_ref(v_a_2483_);
lean_dec(v_a_2482_);
lean_dec_ref(v_a_2481_);
lean_dec(v_a_2480_);
lean_dec(v_a_2479_);
lean_dec(v_a_2478_);
return v_res_2490_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0(lean_object* v_00_u03b2_2491_, lean_object* v_k_2492_, lean_object* v_t_2493_){
_start:
{
uint8_t v___x_2494_; 
v___x_2494_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_k_2492_, v_t_2493_);
return v___x_2494_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___boxed(lean_object* v_00_u03b2_2495_, lean_object* v_k_2496_, lean_object* v_t_2497_){
_start:
{
uint8_t v_res_2498_; lean_object* v_r_2499_; 
v_res_2498_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0(v_00_u03b2_2495_, v_k_2496_, v_t_2497_);
lean_dec(v_t_2497_);
lean_dec(v_k_2496_);
v_r_2499_ = lean_box(v_res_2498_);
return v_r_2499_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1(lean_object* v_00_u03b2_2500_, lean_object* v_k_2501_, lean_object* v_v_2502_, lean_object* v_t_2503_, lean_object* v_hl_2504_){
_start:
{
lean_object* v___x_2505_; 
v___x_2505_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_k_2501_, v_v_2502_, v_t_2503_);
return v___x_2505_;
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
lean_dec_ref_known(v_p_2507_, 3);
lean_inc(v_y_2506_);
v___x_2522_ = l_Lean_Meta_Grind_Arith_Linear_addOcc(v_v_2520_, v_y_2506_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_);
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_dec_ref_known(v___x_2522_, 1);
v_p_2507_ = v_p_2521_;
goto _start;
}
else
{
lean_dec(v_p_2521_);
lean_dec(v_y_2506_);
return v___x_2522_;
}
}
else
{
lean_object* v___x_2524_; lean_object* v___x_2525_; 
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
lean_dec(v_a_2528_);
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
lean_dec_ref_known(v_p_2544_, 3);
v___x_2559_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go(v_v_2557_, v_p_2558_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_);
return v___x_2559_;
}
else
{
lean_object* v___x_2560_; lean_object* v___x_2561_; 
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
lean_dec(v_a_2563_);
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
lean_dec_ref(v_elimEqs_2615_);
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
lean_dec_ref_known(v_p_2685_, 3);
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
lean_dec_ref_known(v_p_2702_, 3);
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
