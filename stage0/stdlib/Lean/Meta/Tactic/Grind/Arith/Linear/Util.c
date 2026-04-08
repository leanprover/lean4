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
size_t v_x_867__boxed_355_; lean_object* v_res_356_; 
v_x_867__boxed_355_ = lean_unbox_usize(v_x_353_);
lean_dec(v_x_353_);
v_res_356_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg(v_x_352_, v_x_867__boxed_355_, v_x_354_);
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
size_t v_x_996__boxed_436_; lean_object* v_res_437_; 
v_x_996__boxed_436_ = lean_unbox_usize(v_x_434_);
lean_dec(v_x_434_);
v_res_437_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0(v_00_u03b2_432_, v_x_433_, v_x_996__boxed_436_, v_x_435_);
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
size_t v_x_7094__boxed_593_; size_t v_x_7095__boxed_594_; lean_object* v_res_595_; 
v_x_7094__boxed_593_ = lean_unbox_usize(v_x_589_);
lean_dec(v_x_589_);
v_x_7095__boxed_594_ = lean_unbox_usize(v_x_590_);
lean_dec(v_x_590_);
v_res_595_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_x_588_, v_x_7094__boxed_593_, v_x_7095__boxed_594_, v_x_591_, v_x_592_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___lam__0(lean_object* v_e_603_, lean_object* v_a_604_, lean_object* v_s_605_){
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
lean_inc_n(v_a_604_, 2);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___lam__0___boxed(lean_object* v_e_624_, lean_object* v_a_625_, lean_object* v_s_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___lam__0(v_e_624_, v_a_625_, v_s_626_);
lean_dec(v_a_625_);
return v_res_627_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__1(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__0));
v___x_630_ = l_Lean_stringToMessageData(v___x_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg(lean_object* v_e_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_e_631_, v_a_633_, v_a_638_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v_a_645_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_a_645_);
lean_dec_ref(v___x_644_);
if (lean_obj_tag(v_a_645_) == 1)
{
lean_object* v_val_646_; uint8_t v___x_647_; 
v_val_646_ = lean_ctor_get(v_a_645_, 0);
lean_inc(v_val_646_);
lean_dec_ref(v_a_645_);
v___x_647_ = lean_nat_dec_eq(v_val_646_, v_a_632_);
lean_dec(v_val_646_);
if (v___x_647_ == 0)
{
lean_object* v___x_648_; 
v___x_648_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_634_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_object* v_a_649_; uint8_t v___x_650_; 
v_a_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_a_649_);
lean_dec_ref(v___x_648_);
v___x_650_ = lean_unbox(v_a_649_);
lean_dec(v_a_649_);
if (v___x_650_ == 0)
{
lean_dec_ref(v_e_631_);
goto v___jp_641_;
}
else
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_651_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__1);
v___x_652_ = l_Lean_indentExpr(v_e_631_);
v___x_653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_653_, 0, v___x_651_);
lean_ctor_set(v___x_653_, 1, v___x_652_);
v___x_654_ = l_Lean_Meta_Sym_reportIssue(v___x_653_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_dec_ref(v___x_654_);
goto v___jp_641_;
}
else
{
return v___x_654_;
}
}
}
else
{
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_662_; 
lean_dec_ref(v_e_631_);
v_a_655_ = lean_ctor_get(v___x_648_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_662_ == 0)
{
v___x_657_ = v___x_648_;
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_648_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_660_; 
if (v_isShared_658_ == 0)
{
v___x_660_ = v___x_657_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_a_655_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
}
else
{
lean_dec_ref(v_e_631_);
goto v___jp_641_;
}
}
else
{
lean_object* v___f_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
lean_dec(v_a_645_);
lean_inc(v_a_632_);
v___f_663_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_663_, 0, v_e_631_);
lean_closure_set(v___f_663_, 1, v_a_632_);
v___x_664_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_665_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_664_, v___f_663_, v_a_633_);
return v___x_665_;
}
}
else
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_673_; 
lean_dec_ref(v_e_631_);
v_a_666_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_673_ == 0)
{
v___x_668_ = v___x_644_;
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_644_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_666_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
v___jp_641_:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = lean_box(0);
v___x_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
return v___x_643_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___boxed(lean_object* v_e_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg(v_e_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_);
lean_dec(v_a_682_);
lean_dec_ref(v_a_681_);
lean_dec(v_a_680_);
lean_dec_ref(v_a_679_);
lean_dec(v_a_678_);
lean_dec_ref(v_a_677_);
lean_dec(v_a_676_);
lean_dec(v_a_675_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId(lean_object* v_e_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg(v_e_685_, v_a_686_, v_a_687_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___boxed(lean_object* v_e_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId(v_e_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
lean_dec(v_a_710_);
lean_dec_ref(v_a_709_);
lean_dec(v_a_708_);
lean_dec_ref(v_a_707_);
lean_dec(v_a_706_);
lean_dec_ref(v_a_705_);
lean_dec(v_a_704_);
lean_dec_ref(v_a_703_);
lean_dec(v_a_702_);
lean_dec(v_a_701_);
lean_dec(v_a_700_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0(lean_object* v_00_u03b2_713_, lean_object* v_x_714_, lean_object* v_x_715_, lean_object* v_x_716_){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0___redArg(v_x_714_, v_x_715_, v_x_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0(lean_object* v_00_u03b2_718_, lean_object* v_x_719_, size_t v_x_720_, size_t v_x_721_, lean_object* v_x_722_, lean_object* v_x_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_x_719_, v_x_720_, v_x_721_, v_x_722_, v_x_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_725_, lean_object* v_x_726_, lean_object* v_x_727_, lean_object* v_x_728_, lean_object* v_x_729_, lean_object* v_x_730_){
_start:
{
size_t v_x_7377__boxed_731_; size_t v_x_7378__boxed_732_; lean_object* v_res_733_; 
v_x_7377__boxed_731_ = lean_unbox_usize(v_x_727_);
lean_dec(v_x_727_);
v_x_7378__boxed_732_ = lean_unbox_usize(v_x_728_);
lean_dec(v_x_728_);
v_res_733_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0(v_00_u03b2_725_, v_x_726_, v_x_7377__boxed_731_, v_x_7378__boxed_732_, v_x_729_, v_x_730_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_734_, lean_object* v_n_735_, lean_object* v_k_736_, lean_object* v_v_737_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1___redArg(v_n_735_, v_k_736_, v_v_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_739_, size_t v_depth_740_, lean_object* v_keys_741_, lean_object* v_vals_742_, lean_object* v_heq_743_, lean_object* v_i_744_, lean_object* v_entries_745_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg(v_depth_740_, v_keys_741_, v_vals_742_, v_i_744_, v_entries_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_747_, lean_object* v_depth_748_, lean_object* v_keys_749_, lean_object* v_vals_750_, lean_object* v_heq_751_, lean_object* v_i_752_, lean_object* v_entries_753_){
_start:
{
size_t v_depth_boxed_754_; lean_object* v_res_755_; 
v_depth_boxed_754_ = lean_unbox_usize(v_depth_748_);
lean_dec(v_depth_748_);
v_res_755_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2(v_00_u03b2_747_, v_depth_boxed_754_, v_keys_749_, v_vals_750_, v_heq_751_, v_i_752_, v_entries_753_);
lean_dec_ref(v_vals_750_);
lean_dec_ref(v_keys_749_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_756_, lean_object* v_x_757_, lean_object* v_x_758_, lean_object* v_x_759_, lean_object* v_x_760_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_757_, v_x_758_, v_x_759_, v_x_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0(lean_object* v_msgData_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
lean_object* v___x_768_; lean_object* v_env_769_; lean_object* v___x_770_; lean_object* v_mctx_771_; lean_object* v_lctx_772_; lean_object* v_options_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_768_ = lean_st_ref_get(v___y_766_);
v_env_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc_ref(v_env_769_);
lean_dec(v___x_768_);
v___x_770_ = lean_st_ref_get(v___y_764_);
v_mctx_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc_ref(v_mctx_771_);
lean_dec(v___x_770_);
v_lctx_772_ = lean_ctor_get(v___y_763_, 2);
v_options_773_ = lean_ctor_get(v___y_765_, 2);
lean_inc_ref(v_options_773_);
lean_inc_ref(v_lctx_772_);
v___x_774_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_774_, 0, v_env_769_);
lean_ctor_set(v___x_774_, 1, v_mctx_771_);
lean_ctor_set(v___x_774_, 2, v_lctx_772_);
lean_ctor_set(v___x_774_, 3, v_options_773_);
v___x_775_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
lean_ctor_set(v___x_775_, 1, v_msgData_762_);
v___x_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0___boxed(lean_object* v_msgData_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0(v_msgData_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
lean_dec(v___y_781_);
lean_dec_ref(v___y_780_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(lean_object* v_msg_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v_ref_790_; lean_object* v___x_791_; lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_800_; 
v_ref_790_ = lean_ctor_get(v___y_787_, 5);
v___x_791_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0(v_msg_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
v_a_792_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_800_ == 0)
{
v___x_794_ = v___x_791_;
v_isShared_795_ = v_isSharedCheck_800_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_791_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_800_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_796_; lean_object* v___x_798_; 
lean_inc(v_ref_790_);
v___x_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_796_, 0, v_ref_790_);
lean_ctor_set(v___x_796_, 1, v_a_792_);
if (v_isShared_795_ == 0)
{
lean_ctor_set_tag(v___x_794_, 1);
lean_ctor_set(v___x_794_, 0, v___x_796_);
v___x_798_ = v___x_794_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v___x_796_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg___boxed(lean_object* v_msg_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v_msg_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
return v_res_807_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1(void){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__0));
v___x_810_ = l_Lean_stringToMessageData(v___x_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst(lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_835_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_835_ == 0)
{
v___x_826_ = v___x_823_;
v_isShared_827_ = v_isSharedCheck_835_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_823_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_835_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v_noNatDivInst_x3f_828_; 
v_noNatDivInst_x3f_828_ = lean_ctor_get(v_a_824_, 11);
lean_inc(v_noNatDivInst_x3f_828_);
lean_dec(v_a_824_);
if (lean_obj_tag(v_noNatDivInst_x3f_828_) == 1)
{
lean_object* v_val_829_; lean_object* v___x_831_; 
v_val_829_ = lean_ctor_get(v_noNatDivInst_x3f_828_, 0);
lean_inc(v_val_829_);
lean_dec_ref(v_noNatDivInst_x3f_828_);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v_val_829_);
v___x_831_ = v___x_826_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_val_829_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
else
{
lean_object* v___x_833_; lean_object* v___x_834_; 
lean_dec(v_noNatDivInst_x3f_828_);
lean_del_object(v___x_826_);
v___x_833_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1);
v___x_834_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_833_, v_a_818_, v_a_819_, v_a_820_, v_a_821_);
return v___x_834_;
}
}
}
else
{
lean_object* v_a_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_843_; 
v_a_836_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_843_ == 0)
{
v___x_838_ = v___x_823_;
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_a_836_);
lean_dec(v___x_823_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_841_; 
if (v_isShared_839_ == 0)
{
v___x_841_ = v___x_838_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_a_836_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___boxed(lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst(v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_);
lean_dec(v_a_854_);
lean_dec_ref(v_a_853_);
lean_dec(v_a_852_);
lean_dec_ref(v_a_851_);
lean_dec(v_a_850_);
lean_dec_ref(v_a_849_);
lean_dec(v_a_848_);
lean_dec_ref(v_a_847_);
lean_dec(v_a_846_);
lean_dec(v_a_845_);
lean_dec(v_a_844_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0(lean_object* v_00_u03b1_857_, lean_object* v_msg_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v_msg_858_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___boxed(lean_object* v_00_u03b1_872_, lean_object* v_msg_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0(v_00_u03b1_872_, v_msg_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec(v___y_876_);
lean_dec(v___y_875_);
lean_dec(v___y_874_);
return v_res_886_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1(void){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__0));
v___x_889_ = l_Lean_stringToMessageData(v___x_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLEInst(lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_914_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_914_ == 0)
{
v___x_905_ = v___x_902_;
v_isShared_906_ = v_isSharedCheck_914_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_902_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_914_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v_leInst_x3f_907_; 
v_leInst_x3f_907_ = lean_ctor_get(v_a_903_, 5);
lean_inc(v_leInst_x3f_907_);
lean_dec(v_a_903_);
if (lean_obj_tag(v_leInst_x3f_907_) == 1)
{
lean_object* v_val_908_; lean_object* v___x_910_; 
v_val_908_ = lean_ctor_get(v_leInst_x3f_907_, 0);
lean_inc(v_val_908_);
lean_dec_ref(v_leInst_x3f_907_);
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 0, v_val_908_);
v___x_910_ = v___x_905_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_val_908_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
else
{
lean_object* v___x_912_; lean_object* v___x_913_; 
lean_dec(v_leInst_x3f_907_);
lean_del_object(v___x_905_);
v___x_912_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1);
v___x_913_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_912_, v_a_897_, v_a_898_, v_a_899_, v_a_900_);
return v___x_913_;
}
}
}
else
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
v_a_915_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_922_ == 0)
{
v___x_917_ = v___x_902_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_902_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLEInst___boxed(lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Lean_Meta_Grind_Arith_Linear_getLEInst(v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_);
lean_dec(v_a_933_);
lean_dec_ref(v_a_932_);
lean_dec(v_a_931_);
lean_dec_ref(v_a_930_);
lean_dec(v_a_929_);
lean_dec_ref(v_a_928_);
lean_dec(v_a_927_);
lean_dec_ref(v_a_926_);
lean_dec(v_a_925_);
lean_dec(v_a_924_);
lean_dec(v_a_923_);
return v_res_935_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1(void){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_937_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__0));
v___x_938_ = l_Lean_stringToMessageData(v___x_937_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLTInst(lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_963_; 
v_a_952_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_963_ == 0)
{
v___x_954_ = v___x_951_;
v_isShared_955_ = v_isSharedCheck_963_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_a_952_);
lean_dec(v___x_951_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_963_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v_ltInst_x3f_956_; 
v_ltInst_x3f_956_ = lean_ctor_get(v_a_952_, 6);
lean_inc(v_ltInst_x3f_956_);
lean_dec(v_a_952_);
if (lean_obj_tag(v_ltInst_x3f_956_) == 1)
{
lean_object* v_val_957_; lean_object* v___x_959_; 
v_val_957_ = lean_ctor_get(v_ltInst_x3f_956_, 0);
lean_inc(v_val_957_);
lean_dec_ref(v_ltInst_x3f_956_);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 0, v_val_957_);
v___x_959_ = v___x_954_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_val_957_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
else
{
lean_object* v___x_961_; lean_object* v___x_962_; 
lean_dec(v_ltInst_x3f_956_);
lean_del_object(v___x_954_);
v___x_961_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1);
v___x_962_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_961_, v_a_946_, v_a_947_, v_a_948_, v_a_949_);
return v___x_962_;
}
}
}
else
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_971_; 
v_a_964_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_971_ == 0)
{
v___x_966_ = v___x_951_;
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_951_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_969_; 
if (v_isShared_967_ == 0)
{
v___x_969_ = v___x_966_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_a_964_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLTInst___boxed(lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Lean_Meta_Grind_Arith_Linear_getLTInst(v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
lean_dec(v_a_982_);
lean_dec_ref(v_a_981_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
lean_dec(v_a_978_);
lean_dec_ref(v_a_977_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
lean_dec(v_a_974_);
lean_dec(v_a_973_);
lean_dec(v_a_972_);
return v_res_984_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1(void){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__0));
v___x_987_ = l_Lean_stringToMessageData(v___x_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst(lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1012_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1003_ = v___x_1000_;
v_isShared_1004_ = v_isSharedCheck_1012_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_1000_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1012_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v_lawfulOrderLTInst_x3f_1005_; 
v_lawfulOrderLTInst_x3f_1005_ = lean_ctor_get(v_a_1001_, 7);
lean_inc(v_lawfulOrderLTInst_x3f_1005_);
lean_dec(v_a_1001_);
if (lean_obj_tag(v_lawfulOrderLTInst_x3f_1005_) == 1)
{
lean_object* v_val_1006_; lean_object* v___x_1008_; 
v_val_1006_ = lean_ctor_get(v_lawfulOrderLTInst_x3f_1005_, 0);
lean_inc(v_val_1006_);
lean_dec_ref(v_lawfulOrderLTInst_x3f_1005_);
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 0, v_val_1006_);
v___x_1008_ = v___x_1003_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_val_1006_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
else
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
lean_dec(v_lawfulOrderLTInst_x3f_1005_);
lean_del_object(v___x_1003_);
v___x_1010_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1);
v___x_1011_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1010_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
return v___x_1011_;
}
}
}
else
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
v_a_1013_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_1000_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_1000_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1013_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___boxed(lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst(v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_);
lean_dec(v_a_1031_);
lean_dec_ref(v_a_1030_);
lean_dec(v_a_1029_);
lean_dec_ref(v_a_1028_);
lean_dec(v_a_1027_);
lean_dec_ref(v_a_1026_);
lean_dec(v_a_1025_);
lean_dec_ref(v_a_1024_);
lean_dec(v_a_1023_);
lean_dec(v_a_1022_);
lean_dec(v_a_1021_);
return v_res_1033_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1(void){
_start:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__0));
v___x_1036_ = l_Lean_stringToMessageData(v___x_1035_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst(lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1061_; 
v_a_1050_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1052_ = v___x_1049_;
v_isShared_1053_ = v_isSharedCheck_1061_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_1049_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1061_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v_isPreorderInst_x3f_1054_; 
v_isPreorderInst_x3f_1054_ = lean_ctor_get(v_a_1050_, 8);
lean_inc(v_isPreorderInst_x3f_1054_);
lean_dec(v_a_1050_);
if (lean_obj_tag(v_isPreorderInst_x3f_1054_) == 1)
{
lean_object* v_val_1055_; lean_object* v___x_1057_; 
v_val_1055_ = lean_ctor_get(v_isPreorderInst_x3f_1054_, 0);
lean_inc(v_val_1055_);
lean_dec_ref(v_isPreorderInst_x3f_1054_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 0, v_val_1055_);
v___x_1057_ = v___x_1052_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_val_1055_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
else
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
lean_dec(v_isPreorderInst_x3f_1054_);
lean_del_object(v___x_1052_);
v___x_1059_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1);
v___x_1060_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1059_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_);
return v___x_1060_;
}
}
}
else
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
v_a_1062_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1064_ = v___x_1049_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1049_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___boxed(lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst(v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_);
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
lean_dec(v_a_1070_);
return v_res_1082_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1(void){
_start:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__0));
v___x_1085_ = l_Lean_stringToMessageData(v___x_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst(lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_){
_start:
{
lean_object* v___x_1098_; 
v___x_1098_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1110_; 
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1101_ = v___x_1098_;
v_isShared_1102_ = v_isSharedCheck_1110_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1098_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1110_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v_orderedAddInst_x3f_1103_; 
v_orderedAddInst_x3f_1103_ = lean_ctor_get(v_a_1099_, 9);
lean_inc(v_orderedAddInst_x3f_1103_);
lean_dec(v_a_1099_);
if (lean_obj_tag(v_orderedAddInst_x3f_1103_) == 1)
{
lean_object* v_val_1104_; lean_object* v___x_1106_; 
v_val_1104_ = lean_ctor_get(v_orderedAddInst_x3f_1103_, 0);
lean_inc(v_val_1104_);
lean_dec_ref(v_orderedAddInst_x3f_1103_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v_val_1104_);
v___x_1106_ = v___x_1101_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_val_1104_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
else
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
lean_dec(v_orderedAddInst_x3f_1103_);
lean_del_object(v___x_1101_);
v___x_1108_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1);
v___x_1109_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1108_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
return v___x_1109_;
}
}
}
else
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
v_a_1111_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1098_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1098_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___boxed(lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst(v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_);
lean_dec(v_a_1129_);
lean_dec_ref(v_a_1128_);
lean_dec(v_a_1127_);
lean_dec_ref(v_a_1126_);
lean_dec(v_a_1125_);
lean_dec_ref(v_a_1124_);
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
lean_dec(v_a_1121_);
lean_dec(v_a_1120_);
lean_dec(v_a_1119_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1160_; 
v_a_1145_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1147_ = v___x_1144_;
v_isShared_1148_ = v_isSharedCheck_1160_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1144_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1160_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v_orderedAddInst_x3f_1149_; 
v_orderedAddInst_x3f_1149_ = lean_ctor_get(v_a_1145_, 9);
lean_inc(v_orderedAddInst_x3f_1149_);
lean_dec(v_a_1145_);
if (lean_obj_tag(v_orderedAddInst_x3f_1149_) == 0)
{
uint8_t v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1153_; 
v___x_1150_ = 0;
v___x_1151_ = lean_box(v___x_1150_);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 0, v___x_1151_);
v___x_1153_ = v___x_1147_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1151_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
else
{
uint8_t v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1158_; 
lean_dec_ref(v_orderedAddInst_x3f_1149_);
v___x_1155_ = 1;
v___x_1156_ = lean_box(v___x_1155_);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 0, v___x_1156_);
v___x_1158_ = v___x_1147_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1156_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
else
{
lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1168_; 
v_a_1161_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1163_ = v___x_1144_;
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___x_1144_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1166_; 
if (v_isShared_1164_ == 0)
{
v___x_1166_ = v___x_1163_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_a_1161_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd___boxed(lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_);
lean_dec(v_a_1179_);
lean_dec_ref(v_a_1178_);
lean_dec(v_a_1177_);
lean_dec_ref(v_a_1176_);
lean_dec(v_a_1175_);
lean_dec_ref(v_a_1174_);
lean_dec(v_a_1173_);
lean_dec_ref(v_a_1172_);
lean_dec(v_a_1171_);
lean_dec(v_a_1170_);
lean_dec(v_a_1169_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg___lam__0(lean_object* v_toPure_1182_, lean_object* v_inst_1183_, lean_object* v_inst_1184_, lean_object* v_____do__lift_1185_){
_start:
{
lean_object* v_ltFn_x3f_1186_; 
v_ltFn_x3f_1186_ = lean_ctor_get(v_____do__lift_1185_, 21);
lean_inc(v_ltFn_x3f_1186_);
lean_dec_ref(v_____do__lift_1185_);
if (lean_obj_tag(v_ltFn_x3f_1186_) == 1)
{
lean_object* v_val_1187_; lean_object* v___x_1188_; 
lean_dec_ref(v_inst_1184_);
lean_dec_ref(v_inst_1183_);
v_val_1187_ = lean_ctor_get(v_ltFn_x3f_1186_, 0);
lean_inc(v_val_1187_);
lean_dec_ref(v_ltFn_x3f_1186_);
v___x_1188_ = lean_apply_2(v_toPure_1182_, lean_box(0), v_val_1187_);
return v___x_1188_;
}
else
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
lean_dec(v_ltFn_x3f_1186_);
lean_dec(v_toPure_1182_);
v___x_1189_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1);
v___x_1190_ = l_Lean_throwError___redArg(v_inst_1183_, v_inst_1184_, v___x_1189_);
return v___x_1190_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg(lean_object* v_inst_1191_, lean_object* v_inst_1192_, lean_object* v_inst_1193_){
_start:
{
lean_object* v_toApplicative_1194_; lean_object* v_toBind_1195_; lean_object* v_toPure_1196_; lean_object* v___f_1197_; lean_object* v___x_1198_; 
v_toApplicative_1194_ = lean_ctor_get(v_inst_1191_, 0);
v_toBind_1195_ = lean_ctor_get(v_inst_1191_, 1);
lean_inc(v_toBind_1195_);
v_toPure_1196_ = lean_ctor_get(v_toApplicative_1194_, 1);
lean_inc(v_toPure_1196_);
v___f_1197_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1197_, 0, v_toPure_1196_);
lean_closure_set(v___f_1197_, 1, v_inst_1191_);
lean_closure_set(v___f_1197_, 2, v_inst_1192_);
v___x_1198_ = lean_apply_4(v_toBind_1195_, lean_box(0), lean_box(0), v_inst_1193_, v___f_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn(lean_object* v_m_1199_, lean_object* v_inst_1200_, lean_object* v_inst_1201_, lean_object* v_inst_1202_){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg(v_inst_1200_, v_inst_1201_, v_inst_1202_);
return v___x_1203_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1205_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__0));
v___x_1206_ = l_Lean_stringToMessageData(v___x_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0(lean_object* v_toPure_1207_, lean_object* v_inst_1208_, lean_object* v_inst_1209_, lean_object* v_____do__lift_1210_){
_start:
{
lean_object* v_leFn_x3f_1211_; 
v_leFn_x3f_1211_ = lean_ctor_get(v_____do__lift_1210_, 20);
lean_inc(v_leFn_x3f_1211_);
lean_dec_ref(v_____do__lift_1210_);
if (lean_obj_tag(v_leFn_x3f_1211_) == 1)
{
lean_object* v_val_1212_; lean_object* v___x_1213_; 
lean_dec_ref(v_inst_1209_);
lean_dec_ref(v_inst_1208_);
v_val_1212_ = lean_ctor_get(v_leFn_x3f_1211_, 0);
lean_inc(v_val_1212_);
lean_dec_ref(v_leFn_x3f_1211_);
v___x_1213_ = lean_apply_2(v_toPure_1207_, lean_box(0), v_val_1212_);
return v___x_1213_;
}
else
{
lean_object* v___x_1214_; lean_object* v___x_1215_; 
lean_dec(v_leFn_x3f_1211_);
lean_dec(v_toPure_1207_);
v___x_1214_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1);
v___x_1215_ = l_Lean_throwError___redArg(v_inst_1208_, v_inst_1209_, v___x_1214_);
return v___x_1215_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg(lean_object* v_inst_1216_, lean_object* v_inst_1217_, lean_object* v_inst_1218_){
_start:
{
lean_object* v_toApplicative_1219_; lean_object* v_toBind_1220_; lean_object* v_toPure_1221_; lean_object* v___f_1222_; lean_object* v___x_1223_; 
v_toApplicative_1219_ = lean_ctor_get(v_inst_1216_, 0);
v_toBind_1220_ = lean_ctor_get(v_inst_1216_, 1);
lean_inc(v_toBind_1220_);
v_toPure_1221_ = lean_ctor_get(v_toApplicative_1219_, 1);
lean_inc(v_toPure_1221_);
v___f_1222_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1222_, 0, v_toPure_1221_);
lean_closure_set(v___f_1222_, 1, v_inst_1216_);
lean_closure_set(v___f_1222_, 2, v_inst_1217_);
v___x_1223_ = lean_apply_4(v_toBind_1220_, lean_box(0), lean_box(0), v_inst_1218_, v___f_1222_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn(lean_object* v_m_1224_, lean_object* v_inst_1225_, lean_object* v_inst_1226_, lean_object* v_inst_1227_){
_start:
{
lean_object* v___x_1228_; 
v___x_1228_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg(v_inst_1225_, v_inst_1226_, v_inst_1227_);
return v___x_1228_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1(void){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__0));
v___x_1231_ = l_Lean_stringToMessageData(v___x_1230_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst(lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_){
_start:
{
lean_object* v___x_1244_; 
v___x_1244_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1256_; 
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1247_ = v___x_1244_;
v_isShared_1248_ = v_isSharedCheck_1256_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1244_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1256_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v_isLinearInst_x3f_1249_; 
v_isLinearInst_x3f_1249_ = lean_ctor_get(v_a_1245_, 10);
lean_inc(v_isLinearInst_x3f_1249_);
lean_dec(v_a_1245_);
if (lean_obj_tag(v_isLinearInst_x3f_1249_) == 1)
{
lean_object* v_val_1250_; lean_object* v___x_1252_; 
v_val_1250_ = lean_ctor_get(v_isLinearInst_x3f_1249_, 0);
lean_inc(v_val_1250_);
lean_dec_ref(v_isLinearInst_x3f_1249_);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 0, v_val_1250_);
v___x_1252_ = v___x_1247_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_val_1250_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
else
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
lean_dec(v_isLinearInst_x3f_1249_);
lean_del_object(v___x_1247_);
v___x_1254_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1);
v___x_1255_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1254_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_);
return v___x_1255_;
}
}
}
else
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1264_; 
v_a_1257_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1259_ = v___x_1244_;
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1244_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___boxed(lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst(v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_);
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
lean_dec(v_a_1265_);
return v_res_1277_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1(void){
_start:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__0));
v___x_1280_ = l_Lean_stringToMessageData(v___x_1279_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRingInst(lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_){
_start:
{
lean_object* v___x_1293_; 
v___x_1293_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1305_; 
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1296_ = v___x_1293_;
v_isShared_1297_ = v_isSharedCheck_1305_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1293_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1305_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v_ringInst_x3f_1298_; 
v_ringInst_x3f_1298_ = lean_ctor_get(v_a_1294_, 12);
lean_inc(v_ringInst_x3f_1298_);
lean_dec(v_a_1294_);
if (lean_obj_tag(v_ringInst_x3f_1298_) == 1)
{
lean_object* v_val_1299_; lean_object* v___x_1301_; 
v_val_1299_ = lean_ctor_get(v_ringInst_x3f_1298_, 0);
lean_inc(v_val_1299_);
lean_dec_ref(v_ringInst_x3f_1298_);
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 0, v_val_1299_);
v___x_1301_ = v___x_1296_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_val_1299_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
else
{
lean_object* v___x_1303_; lean_object* v___x_1304_; 
lean_dec(v_ringInst_x3f_1298_);
lean_del_object(v___x_1296_);
v___x_1303_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1);
v___x_1304_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1303_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_);
return v___x_1304_;
}
}
}
else
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
v_a_1306_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1308_ = v___x_1293_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1293_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1311_; 
if (v_isShared_1309_ == 0)
{
v___x_1311_ = v___x_1308_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_a_1306_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRingInst___boxed(lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_Lean_Meta_Grind_Arith_Linear_getRingInst(v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
lean_dec(v_a_1324_);
lean_dec_ref(v_a_1323_);
lean_dec(v_a_1322_);
lean_dec_ref(v_a_1321_);
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
lean_dec(v_a_1318_);
lean_dec_ref(v_a_1317_);
lean_dec(v_a_1316_);
lean_dec(v_a_1315_);
lean_dec(v_a_1314_);
return v_res_1326_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1(void){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1328_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__0));
v___x_1329_ = l_Lean_stringToMessageData(v___x_1328_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getCommRingInst(lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1354_; 
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1345_ = v___x_1342_;
v_isShared_1346_ = v_isSharedCheck_1354_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1342_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1354_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v_commRingInst_x3f_1347_; 
v_commRingInst_x3f_1347_ = lean_ctor_get(v_a_1343_, 13);
lean_inc(v_commRingInst_x3f_1347_);
lean_dec(v_a_1343_);
if (lean_obj_tag(v_commRingInst_x3f_1347_) == 1)
{
lean_object* v_val_1348_; lean_object* v___x_1350_; 
v_val_1348_ = lean_ctor_get(v_commRingInst_x3f_1347_, 0);
lean_inc(v_val_1348_);
lean_dec_ref(v_commRingInst_x3f_1347_);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 0, v_val_1348_);
v___x_1350_ = v___x_1345_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_val_1348_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
else
{
lean_object* v___x_1352_; lean_object* v___x_1353_; 
lean_dec(v_commRingInst_x3f_1347_);
lean_del_object(v___x_1345_);
v___x_1352_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1);
v___x_1353_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1352_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_);
return v___x_1353_;
}
}
}
else
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
v_a_1355_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1357_ = v___x_1342_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1342_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___boxed(lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l_Lean_Meta_Grind_Arith_Linear_getCommRingInst(v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_);
lean_dec(v_a_1373_);
lean_dec_ref(v_a_1372_);
lean_dec(v_a_1371_);
lean_dec_ref(v_a_1370_);
lean_dec(v_a_1369_);
lean_dec_ref(v_a_1368_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec(v_a_1364_);
lean_dec(v_a_1363_);
return v_res_1375_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1(void){
_start:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1377_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__0));
v___x_1378_ = l_Lean_stringToMessageData(v___x_1377_);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst(lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_){
_start:
{
lean_object* v___x_1391_; 
v___x_1391_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1403_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1394_ = v___x_1391_;
v_isShared_1395_ = v_isSharedCheck_1403_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v___x_1391_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1403_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v_orderedRingInst_x3f_1396_; 
v_orderedRingInst_x3f_1396_ = lean_ctor_get(v_a_1392_, 14);
lean_inc(v_orderedRingInst_x3f_1396_);
lean_dec(v_a_1392_);
if (lean_obj_tag(v_orderedRingInst_x3f_1396_) == 1)
{
lean_object* v_val_1397_; lean_object* v___x_1399_; 
v_val_1397_ = lean_ctor_get(v_orderedRingInst_x3f_1396_, 0);
lean_inc(v_val_1397_);
lean_dec_ref(v_orderedRingInst_x3f_1396_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 0, v_val_1397_);
v___x_1399_ = v___x_1394_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_val_1397_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
else
{
lean_object* v___x_1401_; lean_object* v___x_1402_; 
lean_dec(v_orderedRingInst_x3f_1396_);
lean_del_object(v___x_1394_);
v___x_1401_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1);
v___x_1402_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1401_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_);
return v___x_1402_;
}
}
}
else
{
lean_object* v_a_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1411_; 
v_a_1404_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1406_ = v___x_1391_;
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_a_1404_);
lean_dec(v___x_1391_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1409_; 
if (v_isShared_1407_ == 0)
{
v___x_1409_ = v___x_1406_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_a_1404_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___boxed(lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst(v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_);
lean_dec(v_a_1422_);
lean_dec_ref(v_a_1421_);
lean_dec(v_a_1420_);
lean_dec_ref(v_a_1419_);
lean_dec(v_a_1418_);
lean_dec_ref(v_a_1417_);
lean_dec(v_a_1416_);
lean_dec_ref(v_a_1415_);
lean_dec(v_a_1414_);
lean_dec(v_a_1413_);
lean_dec(v_a_1412_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go_spec__0(lean_object* v_a_1425_){
_start:
{
lean_object* v___x_1426_; 
v___x_1426_ = l_Rat_ofInt(v_a_1425_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go(lean_object* v_a_1427_, lean_object* v_v_1428_, lean_object* v_a_1429_){
_start:
{
if (lean_obj_tag(v_a_1429_) == 0)
{
lean_object* v___x_1430_; 
v___x_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1430_, 0, v_v_1428_);
return v___x_1430_;
}
else
{
lean_object* v_k_1431_; lean_object* v_v_1432_; lean_object* v_p_1433_; lean_object* v_size_1434_; uint8_t v___x_1435_; 
v_k_1431_ = lean_ctor_get(v_a_1429_, 0);
lean_inc(v_k_1431_);
v_v_1432_ = lean_ctor_get(v_a_1429_, 1);
lean_inc(v_v_1432_);
v_p_1433_ = lean_ctor_get(v_a_1429_, 2);
lean_inc(v_p_1433_);
lean_dec_ref(v_a_1429_);
v_size_1434_ = lean_ctor_get(v_a_1427_, 2);
v___x_1435_ = lean_nat_dec_lt(v_v_1432_, v_size_1434_);
if (v___x_1435_ == 0)
{
lean_object* v___x_1436_; 
lean_dec(v_p_1433_);
lean_dec(v_v_1432_);
lean_dec(v_k_1431_);
lean_dec_ref(v_v_1428_);
v___x_1436_ = lean_box(0);
return v___x_1436_;
}
else
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1437_ = l_Rat_ofInt(v_k_1431_);
v___x_1438_ = l_instInhabitedRat;
v___x_1439_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1438_, v_a_1427_, v_v_1432_);
lean_dec(v_v_1432_);
v___x_1440_ = l_Rat_mul(v___x_1437_, v___x_1439_);
lean_dec_ref(v___x_1437_);
v___x_1441_ = l_Rat_add(v_v_1428_, v___x_1440_);
v_v_1428_ = v___x_1441_;
v_a_1429_ = v_p_1433_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go___boxed(lean_object* v_a_1443_, lean_object* v_v_1444_, lean_object* v_a_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go(v_a_1443_, v_v_1444_, v_a_1445_);
lean_dec_ref(v_a_1443_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_Linarith_Poly_eval_x3f_spec__0(lean_object* v_a_1447_){
_start:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = lean_nat_to_int(v_a_1447_);
v___x_1449_ = l_Rat_ofInt(v___x_1448_);
return v___x_1449_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0(void){
_start:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1450_ = lean_unsigned_to_nat(0u);
v___x_1451_ = l_Nat_cast___at___00Lean_Grind_Linarith_Poly_eval_x3f_spec__0(v___x_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_eval_x3f(lean_object* v_p_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_){
_start:
{
lean_object* v___x_1465_; 
v___x_1465_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1476_; 
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1468_ = v___x_1465_;
v_isShared_1469_ = v_isSharedCheck_1476_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1465_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1476_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v_assignment_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1474_; 
v_assignment_1470_ = lean_ctor_get(v_a_1466_, 35);
lean_inc_ref(v_assignment_1470_);
lean_dec(v_a_1466_);
v___x_1471_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0, &l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once, _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0);
v___x_1472_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go(v_assignment_1470_, v___x_1471_, v_p_1452_);
lean_dec_ref(v_assignment_1470_);
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 0, v___x_1472_);
v___x_1474_ = v___x_1468_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1472_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
else
{
lean_object* v_a_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1484_; 
lean_dec(v_p_1452_);
v_a_1477_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1479_ = v___x_1465_;
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_a_1477_);
lean_dec(v___x_1465_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1482_; 
if (v_isShared_1480_ == 0)
{
v___x_1482_ = v___x_1479_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_a_1477_);
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
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_eval_x3f___boxed(lean_object* v_p_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l_Lean_Grind_Linarith_Poly_eval_x3f(v_p_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_);
lean_dec(v_a_1496_);
lean_dec_ref(v_a_1495_);
lean_dec(v_a_1494_);
lean_dec_ref(v_a_1493_);
lean_dec(v_a_1492_);
lean_dec_ref(v_a_1491_);
lean_dec(v_a_1490_);
lean_dec_ref(v_a_1489_);
lean_dec(v_a_1488_);
lean_dec(v_a_1487_);
lean_dec(v_a_1486_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Lean_Grind_Linarith_Poly_eval_x3f_spec__0_spec__0(lean_object* v_a_1499_){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = lean_nat_to_int(v_a_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied(lean_object* v_c_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_){
_start:
{
lean_object* v_p_1514_; uint8_t v_strict_1515_; lean_object* v___x_1516_; 
v_p_1514_ = lean_ctor_get(v_c_1501_, 0);
lean_inc(v_p_1514_);
v_strict_1515_ = lean_ctor_get_uint8(v_c_1501_, sizeof(void*)*2);
lean_dec_ref(v_c_1501_);
v___x_1516_ = l_Lean_Grind_Linarith_Poly_eval_x3f(v_p_1514_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1542_; 
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1519_ = v___x_1516_;
v_isShared_1520_ = v_isSharedCheck_1542_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_a_1517_);
lean_dec(v___x_1516_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1542_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
if (lean_obj_tag(v_a_1517_) == 1)
{
if (v_strict_1515_ == 0)
{
lean_object* v_val_1521_; lean_object* v___x_1522_; uint8_t v___x_1523_; uint8_t v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1527_; 
v_val_1521_ = lean_ctor_get(v_a_1517_, 0);
lean_inc(v_val_1521_);
lean_dec_ref(v_a_1517_);
v___x_1522_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0, &l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once, _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0);
v___x_1523_ = l_Rat_instDecidableLe(v_val_1521_, v___x_1522_);
v___x_1524_ = l_Bool_toLBool(v___x_1523_);
v___x_1525_ = lean_box(v___x_1524_);
if (v_isShared_1520_ == 0)
{
lean_ctor_set(v___x_1519_, 0, v___x_1525_);
v___x_1527_ = v___x_1519_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1525_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
else
{
lean_object* v_val_1529_; lean_object* v___x_1530_; uint8_t v___x_1531_; uint8_t v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1535_; 
v_val_1529_ = lean_ctor_get(v_a_1517_, 0);
lean_inc(v_val_1529_);
lean_dec_ref(v_a_1517_);
v___x_1530_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0, &l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once, _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0);
v___x_1531_ = l_Rat_blt(v_val_1529_, v___x_1530_);
v___x_1532_ = l_Bool_toLBool(v___x_1531_);
v___x_1533_ = lean_box(v___x_1532_);
if (v_isShared_1520_ == 0)
{
lean_ctor_set(v___x_1519_, 0, v___x_1533_);
v___x_1535_ = v___x_1519_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1533_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
else
{
uint8_t v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1540_; 
lean_dec(v_a_1517_);
v___x_1537_ = 2;
v___x_1538_ = lean_box(v___x_1537_);
if (v_isShared_1520_ == 0)
{
lean_ctor_set(v___x_1519_, 0, v___x_1538_);
v___x_1540_ = v___x_1519_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1538_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
else
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1550_; 
v_a_1543_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1545_ = v___x_1516_;
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1516_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1548_; 
if (v_isShared_1546_ == 0)
{
v___x_1548_ = v___x_1545_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_a_1543_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied___boxed(lean_object* v_c_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied(v_c_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_);
lean_dec(v_a_1562_);
lean_dec_ref(v_a_1561_);
lean_dec(v_a_1560_);
lean_dec_ref(v_a_1559_);
lean_dec(v_a_1558_);
lean_dec_ref(v_a_1557_);
lean_dec(v_a_1556_);
lean_dec_ref(v_a_1555_);
lean_dec(v_a_1554_);
lean_dec(v_a_1553_);
lean_dec(v_a_1552_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(lean_object* v_c_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_){
_start:
{
lean_object* v_p_1578_; lean_object* v___x_1579_; 
v_p_1578_ = lean_ctor_get(v_c_1565_, 0);
lean_inc(v_p_1578_);
lean_dec_ref(v_c_1565_);
v___x_1579_ = l_Lean_Grind_Linarith_Poly_eval_x3f(v_p_1578_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1599_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1582_ = v___x_1579_;
v_isShared_1583_ = v_isSharedCheck_1599_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1579_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1599_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
uint8_t v___y_1585_; 
if (lean_obj_tag(v_a_1580_) == 1)
{
lean_object* v_val_1591_; lean_object* v___x_1592_; uint8_t v___x_1593_; 
v_val_1591_ = lean_ctor_get(v_a_1580_, 0);
lean_inc(v_val_1591_);
lean_dec_ref(v_a_1580_);
v___x_1592_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0, &l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once, _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0);
v___x_1593_ = l_instDecidableEqRat_decEq(v_val_1591_, v___x_1592_);
lean_dec(v_val_1591_);
if (v___x_1593_ == 0)
{
uint8_t v___x_1594_; 
v___x_1594_ = 1;
v___y_1585_ = v___x_1594_;
goto v___jp_1584_;
}
else
{
uint8_t v___x_1595_; 
v___x_1595_ = 0;
v___y_1585_ = v___x_1595_;
goto v___jp_1584_;
}
}
else
{
uint8_t v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
lean_del_object(v___x_1582_);
lean_dec(v_a_1580_);
v___x_1596_ = 2;
v___x_1597_ = lean_box(v___x_1596_);
v___x_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1597_);
return v___x_1598_;
}
v___jp_1584_:
{
uint8_t v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1589_; 
v___x_1586_ = l_Bool_toLBool(v___y_1585_);
v___x_1587_ = lean_box(v___x_1586_);
if (v_isShared_1583_ == 0)
{
lean_ctor_set(v___x_1582_, 0, v___x_1587_);
v___x_1589_ = v___x_1582_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1587_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
v_a_1600_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___x_1579_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1579_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied___boxed(lean_object* v_c_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(v_c_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_);
lean_dec(v_a_1619_);
lean_dec_ref(v_a_1618_);
lean_dec(v_a_1617_);
lean_dec_ref(v_a_1616_);
lean_dec(v_a_1615_);
lean_dec_ref(v_a_1614_);
lean_dec(v_a_1613_);
lean_dec_ref(v_a_1612_);
lean_dec(v_a_1611_);
lean_dec(v_a_1610_);
lean_dec(v_a_1609_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0(lean_object* v_a_1622_, lean_object* v_x_1623_, lean_object* v_s_1624_){
_start:
{
lean_object* v_structs_1625_; lean_object* v_typeIdOf_1626_; lean_object* v_exprToStructId_1627_; lean_object* v_exprToStructIdEntries_1628_; lean_object* v_forbiddenNatModules_1629_; lean_object* v_natStructs_1630_; lean_object* v_natTypeIdOf_1631_; lean_object* v_exprToNatStructId_1632_; lean_object* v___x_1633_; uint8_t v___x_1634_; 
v_structs_1625_ = lean_ctor_get(v_s_1624_, 0);
v_typeIdOf_1626_ = lean_ctor_get(v_s_1624_, 1);
v_exprToStructId_1627_ = lean_ctor_get(v_s_1624_, 2);
v_exprToStructIdEntries_1628_ = lean_ctor_get(v_s_1624_, 3);
v_forbiddenNatModules_1629_ = lean_ctor_get(v_s_1624_, 4);
v_natStructs_1630_ = lean_ctor_get(v_s_1624_, 5);
v_natTypeIdOf_1631_ = lean_ctor_get(v_s_1624_, 6);
v_exprToNatStructId_1632_ = lean_ctor_get(v_s_1624_, 7);
v___x_1633_ = lean_array_get_size(v_structs_1625_);
v___x_1634_ = lean_nat_dec_lt(v_a_1622_, v___x_1633_);
if (v___x_1634_ == 0)
{
return v_s_1624_;
}
else
{
lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1696_; 
lean_inc_ref(v_exprToNatStructId_1632_);
lean_inc_ref(v_natTypeIdOf_1631_);
lean_inc_ref(v_natStructs_1630_);
lean_inc_ref(v_forbiddenNatModules_1629_);
lean_inc_ref(v_exprToStructIdEntries_1628_);
lean_inc_ref(v_exprToStructId_1627_);
lean_inc_ref(v_typeIdOf_1626_);
lean_inc_ref(v_structs_1625_);
v_isSharedCheck_1696_ = !lean_is_exclusive(v_s_1624_);
if (v_isSharedCheck_1696_ == 0)
{
lean_object* v_unused_1697_; lean_object* v_unused_1698_; lean_object* v_unused_1699_; lean_object* v_unused_1700_; lean_object* v_unused_1701_; lean_object* v_unused_1702_; lean_object* v_unused_1703_; lean_object* v_unused_1704_; 
v_unused_1697_ = lean_ctor_get(v_s_1624_, 7);
lean_dec(v_unused_1697_);
v_unused_1698_ = lean_ctor_get(v_s_1624_, 6);
lean_dec(v_unused_1698_);
v_unused_1699_ = lean_ctor_get(v_s_1624_, 5);
lean_dec(v_unused_1699_);
v_unused_1700_ = lean_ctor_get(v_s_1624_, 4);
lean_dec(v_unused_1700_);
v_unused_1701_ = lean_ctor_get(v_s_1624_, 3);
lean_dec(v_unused_1701_);
v_unused_1702_ = lean_ctor_get(v_s_1624_, 2);
lean_dec(v_unused_1702_);
v_unused_1703_ = lean_ctor_get(v_s_1624_, 1);
lean_dec(v_unused_1703_);
v_unused_1704_ = lean_ctor_get(v_s_1624_, 0);
lean_dec(v_unused_1704_);
v___x_1636_ = v_s_1624_;
v_isShared_1637_ = v_isSharedCheck_1696_;
goto v_resetjp_1635_;
}
else
{
lean_dec(v_s_1624_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1696_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v_v_1638_; lean_object* v_id_1639_; lean_object* v_ringId_x3f_1640_; lean_object* v_type_1641_; lean_object* v_u_1642_; lean_object* v_intModuleInst_1643_; lean_object* v_leInst_x3f_1644_; lean_object* v_ltInst_x3f_1645_; lean_object* v_lawfulOrderLTInst_x3f_1646_; lean_object* v_isPreorderInst_x3f_1647_; lean_object* v_orderedAddInst_x3f_1648_; lean_object* v_isLinearInst_x3f_1649_; lean_object* v_noNatDivInst_x3f_1650_; lean_object* v_ringInst_x3f_1651_; lean_object* v_commRingInst_x3f_1652_; lean_object* v_orderedRingInst_x3f_1653_; lean_object* v_fieldInst_x3f_1654_; lean_object* v_charInst_x3f_1655_; lean_object* v_zero_1656_; lean_object* v_ofNatZero_1657_; lean_object* v_one_x3f_1658_; lean_object* v_leFn_x3f_1659_; lean_object* v_ltFn_x3f_1660_; lean_object* v_addFn_1661_; lean_object* v_zsmulFn_1662_; lean_object* v_nsmulFn_1663_; lean_object* v_zsmulFn_x3f_1664_; lean_object* v_nsmulFn_x3f_1665_; lean_object* v_homomulFn_x3f_1666_; lean_object* v_subFn_1667_; lean_object* v_negFn_1668_; lean_object* v_vars_1669_; lean_object* v_varMap_1670_; lean_object* v_lowers_1671_; lean_object* v_uppers_1672_; lean_object* v_diseqs_1673_; lean_object* v_assignment_1674_; uint8_t v_caseSplits_1675_; lean_object* v_conflict_x3f_1676_; lean_object* v_diseqSplits_1677_; lean_object* v_elimEqs_1678_; lean_object* v_elimStack_1679_; lean_object* v_occurs_1680_; lean_object* v_ignored_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1695_; 
v_v_1638_ = lean_array_fget(v_structs_1625_, v_a_1622_);
v_id_1639_ = lean_ctor_get(v_v_1638_, 0);
v_ringId_x3f_1640_ = lean_ctor_get(v_v_1638_, 1);
v_type_1641_ = lean_ctor_get(v_v_1638_, 2);
v_u_1642_ = lean_ctor_get(v_v_1638_, 3);
v_intModuleInst_1643_ = lean_ctor_get(v_v_1638_, 4);
v_leInst_x3f_1644_ = lean_ctor_get(v_v_1638_, 5);
v_ltInst_x3f_1645_ = lean_ctor_get(v_v_1638_, 6);
v_lawfulOrderLTInst_x3f_1646_ = lean_ctor_get(v_v_1638_, 7);
v_isPreorderInst_x3f_1647_ = lean_ctor_get(v_v_1638_, 8);
v_orderedAddInst_x3f_1648_ = lean_ctor_get(v_v_1638_, 9);
v_isLinearInst_x3f_1649_ = lean_ctor_get(v_v_1638_, 10);
v_noNatDivInst_x3f_1650_ = lean_ctor_get(v_v_1638_, 11);
v_ringInst_x3f_1651_ = lean_ctor_get(v_v_1638_, 12);
v_commRingInst_x3f_1652_ = lean_ctor_get(v_v_1638_, 13);
v_orderedRingInst_x3f_1653_ = lean_ctor_get(v_v_1638_, 14);
v_fieldInst_x3f_1654_ = lean_ctor_get(v_v_1638_, 15);
v_charInst_x3f_1655_ = lean_ctor_get(v_v_1638_, 16);
v_zero_1656_ = lean_ctor_get(v_v_1638_, 17);
v_ofNatZero_1657_ = lean_ctor_get(v_v_1638_, 18);
v_one_x3f_1658_ = lean_ctor_get(v_v_1638_, 19);
v_leFn_x3f_1659_ = lean_ctor_get(v_v_1638_, 20);
v_ltFn_x3f_1660_ = lean_ctor_get(v_v_1638_, 21);
v_addFn_1661_ = lean_ctor_get(v_v_1638_, 22);
v_zsmulFn_1662_ = lean_ctor_get(v_v_1638_, 23);
v_nsmulFn_1663_ = lean_ctor_get(v_v_1638_, 24);
v_zsmulFn_x3f_1664_ = lean_ctor_get(v_v_1638_, 25);
v_nsmulFn_x3f_1665_ = lean_ctor_get(v_v_1638_, 26);
v_homomulFn_x3f_1666_ = lean_ctor_get(v_v_1638_, 27);
v_subFn_1667_ = lean_ctor_get(v_v_1638_, 28);
v_negFn_1668_ = lean_ctor_get(v_v_1638_, 29);
v_vars_1669_ = lean_ctor_get(v_v_1638_, 30);
v_varMap_1670_ = lean_ctor_get(v_v_1638_, 31);
v_lowers_1671_ = lean_ctor_get(v_v_1638_, 32);
v_uppers_1672_ = lean_ctor_get(v_v_1638_, 33);
v_diseqs_1673_ = lean_ctor_get(v_v_1638_, 34);
v_assignment_1674_ = lean_ctor_get(v_v_1638_, 35);
v_caseSplits_1675_ = lean_ctor_get_uint8(v_v_1638_, sizeof(void*)*42);
v_conflict_x3f_1676_ = lean_ctor_get(v_v_1638_, 36);
v_diseqSplits_1677_ = lean_ctor_get(v_v_1638_, 37);
v_elimEqs_1678_ = lean_ctor_get(v_v_1638_, 38);
v_elimStack_1679_ = lean_ctor_get(v_v_1638_, 39);
v_occurs_1680_ = lean_ctor_get(v_v_1638_, 40);
v_ignored_1681_ = lean_ctor_get(v_v_1638_, 41);
v_isSharedCheck_1695_ = !lean_is_exclusive(v_v_1638_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1683_ = v_v_1638_;
v_isShared_1684_ = v_isSharedCheck_1695_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_ignored_1681_);
lean_inc(v_occurs_1680_);
lean_inc(v_elimStack_1679_);
lean_inc(v_elimEqs_1678_);
lean_inc(v_diseqSplits_1677_);
lean_inc(v_conflict_x3f_1676_);
lean_inc(v_assignment_1674_);
lean_inc(v_diseqs_1673_);
lean_inc(v_uppers_1672_);
lean_inc(v_lowers_1671_);
lean_inc(v_varMap_1670_);
lean_inc(v_vars_1669_);
lean_inc(v_negFn_1668_);
lean_inc(v_subFn_1667_);
lean_inc(v_homomulFn_x3f_1666_);
lean_inc(v_nsmulFn_x3f_1665_);
lean_inc(v_zsmulFn_x3f_1664_);
lean_inc(v_nsmulFn_1663_);
lean_inc(v_zsmulFn_1662_);
lean_inc(v_addFn_1661_);
lean_inc(v_ltFn_x3f_1660_);
lean_inc(v_leFn_x3f_1659_);
lean_inc(v_one_x3f_1658_);
lean_inc(v_ofNatZero_1657_);
lean_inc(v_zero_1656_);
lean_inc(v_charInst_x3f_1655_);
lean_inc(v_fieldInst_x3f_1654_);
lean_inc(v_orderedRingInst_x3f_1653_);
lean_inc(v_commRingInst_x3f_1652_);
lean_inc(v_ringInst_x3f_1651_);
lean_inc(v_noNatDivInst_x3f_1650_);
lean_inc(v_isLinearInst_x3f_1649_);
lean_inc(v_orderedAddInst_x3f_1648_);
lean_inc(v_isPreorderInst_x3f_1647_);
lean_inc(v_lawfulOrderLTInst_x3f_1646_);
lean_inc(v_ltInst_x3f_1645_);
lean_inc(v_leInst_x3f_1644_);
lean_inc(v_intModuleInst_1643_);
lean_inc(v_u_1642_);
lean_inc(v_type_1641_);
lean_inc(v_ringId_x3f_1640_);
lean_inc(v_id_1639_);
lean_dec(v_v_1638_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1695_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1685_; lean_object* v_xs_x27_1686_; lean_object* v___x_1687_; lean_object* v___x_1689_; 
v___x_1685_ = lean_box(0);
v_xs_x27_1686_ = lean_array_fset(v_structs_1625_, v_a_1622_, v___x_1685_);
v___x_1687_ = l_Lean_Meta_Grind_Arith_shrink(v_assignment_1674_, v_x_1623_);
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 35, v___x_1687_);
v___x_1689_ = v___x_1683_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_id_1639_);
lean_ctor_set(v_reuseFailAlloc_1694_, 1, v_ringId_x3f_1640_);
lean_ctor_set(v_reuseFailAlloc_1694_, 2, v_type_1641_);
lean_ctor_set(v_reuseFailAlloc_1694_, 3, v_u_1642_);
lean_ctor_set(v_reuseFailAlloc_1694_, 4, v_intModuleInst_1643_);
lean_ctor_set(v_reuseFailAlloc_1694_, 5, v_leInst_x3f_1644_);
lean_ctor_set(v_reuseFailAlloc_1694_, 6, v_ltInst_x3f_1645_);
lean_ctor_set(v_reuseFailAlloc_1694_, 7, v_lawfulOrderLTInst_x3f_1646_);
lean_ctor_set(v_reuseFailAlloc_1694_, 8, v_isPreorderInst_x3f_1647_);
lean_ctor_set(v_reuseFailAlloc_1694_, 9, v_orderedAddInst_x3f_1648_);
lean_ctor_set(v_reuseFailAlloc_1694_, 10, v_isLinearInst_x3f_1649_);
lean_ctor_set(v_reuseFailAlloc_1694_, 11, v_noNatDivInst_x3f_1650_);
lean_ctor_set(v_reuseFailAlloc_1694_, 12, v_ringInst_x3f_1651_);
lean_ctor_set(v_reuseFailAlloc_1694_, 13, v_commRingInst_x3f_1652_);
lean_ctor_set(v_reuseFailAlloc_1694_, 14, v_orderedRingInst_x3f_1653_);
lean_ctor_set(v_reuseFailAlloc_1694_, 15, v_fieldInst_x3f_1654_);
lean_ctor_set(v_reuseFailAlloc_1694_, 16, v_charInst_x3f_1655_);
lean_ctor_set(v_reuseFailAlloc_1694_, 17, v_zero_1656_);
lean_ctor_set(v_reuseFailAlloc_1694_, 18, v_ofNatZero_1657_);
lean_ctor_set(v_reuseFailAlloc_1694_, 19, v_one_x3f_1658_);
lean_ctor_set(v_reuseFailAlloc_1694_, 20, v_leFn_x3f_1659_);
lean_ctor_set(v_reuseFailAlloc_1694_, 21, v_ltFn_x3f_1660_);
lean_ctor_set(v_reuseFailAlloc_1694_, 22, v_addFn_1661_);
lean_ctor_set(v_reuseFailAlloc_1694_, 23, v_zsmulFn_1662_);
lean_ctor_set(v_reuseFailAlloc_1694_, 24, v_nsmulFn_1663_);
lean_ctor_set(v_reuseFailAlloc_1694_, 25, v_zsmulFn_x3f_1664_);
lean_ctor_set(v_reuseFailAlloc_1694_, 26, v_nsmulFn_x3f_1665_);
lean_ctor_set(v_reuseFailAlloc_1694_, 27, v_homomulFn_x3f_1666_);
lean_ctor_set(v_reuseFailAlloc_1694_, 28, v_subFn_1667_);
lean_ctor_set(v_reuseFailAlloc_1694_, 29, v_negFn_1668_);
lean_ctor_set(v_reuseFailAlloc_1694_, 30, v_vars_1669_);
lean_ctor_set(v_reuseFailAlloc_1694_, 31, v_varMap_1670_);
lean_ctor_set(v_reuseFailAlloc_1694_, 32, v_lowers_1671_);
lean_ctor_set(v_reuseFailAlloc_1694_, 33, v_uppers_1672_);
lean_ctor_set(v_reuseFailAlloc_1694_, 34, v_diseqs_1673_);
lean_ctor_set(v_reuseFailAlloc_1694_, 35, v___x_1687_);
lean_ctor_set(v_reuseFailAlloc_1694_, 36, v_conflict_x3f_1676_);
lean_ctor_set(v_reuseFailAlloc_1694_, 37, v_diseqSplits_1677_);
lean_ctor_set(v_reuseFailAlloc_1694_, 38, v_elimEqs_1678_);
lean_ctor_set(v_reuseFailAlloc_1694_, 39, v_elimStack_1679_);
lean_ctor_set(v_reuseFailAlloc_1694_, 40, v_occurs_1680_);
lean_ctor_set(v_reuseFailAlloc_1694_, 41, v_ignored_1681_);
lean_ctor_set_uint8(v_reuseFailAlloc_1694_, sizeof(void*)*42, v_caseSplits_1675_);
v___x_1689_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
lean_object* v___x_1690_; lean_object* v___x_1692_; 
v___x_1690_ = lean_array_fset(v_xs_x27_1686_, v_a_1622_, v___x_1689_);
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 0, v___x_1690_);
v___x_1692_ = v___x_1636_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1690_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v_typeIdOf_1626_);
lean_ctor_set(v_reuseFailAlloc_1693_, 2, v_exprToStructId_1627_);
lean_ctor_set(v_reuseFailAlloc_1693_, 3, v_exprToStructIdEntries_1628_);
lean_ctor_set(v_reuseFailAlloc_1693_, 4, v_forbiddenNatModules_1629_);
lean_ctor_set(v_reuseFailAlloc_1693_, 5, v_natStructs_1630_);
lean_ctor_set(v_reuseFailAlloc_1693_, 6, v_natTypeIdOf_1631_);
lean_ctor_set(v_reuseFailAlloc_1693_, 7, v_exprToNatStructId_1632_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0___boxed(lean_object* v_a_1705_, lean_object* v_x_1706_, lean_object* v_s_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0(v_a_1705_, v_x_1706_, v_s_1707_);
lean_dec(v_x_1706_);
lean_dec(v_a_1705_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(lean_object* v_x_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_){
_start:
{
lean_object* v___f_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
lean_inc(v_a_1710_);
v___f_1713_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1713_, 0, v_a_1710_);
lean_closure_set(v___f_1713_, 1, v_x_1709_);
v___x_1714_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1715_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1714_, v___f_1713_, v_a_1711_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___boxed(lean_object* v_x_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(v_x_1716_, v_a_1717_, v_a_1718_);
lean_dec(v_a_1718_);
lean_dec(v_a_1717_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom(lean_object* v_x_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_){
_start:
{
lean_object* v___x_1734_; 
v___x_1734_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(v_x_1721_, v_a_1722_, v_a_1723_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___boxed(lean_object* v_x_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom(v_x_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_);
lean_dec(v_a_1746_);
lean_dec_ref(v_a_1745_);
lean_dec(v_a_1744_);
lean_dec_ref(v_a_1743_);
lean_dec(v_a_1742_);
lean_dec_ref(v_a_1741_);
lean_dec(v_a_1740_);
lean_dec_ref(v_a_1739_);
lean_dec(v_a_1738_);
lean_dec(v_a_1737_);
lean_dec(v_a_1736_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getVar(lean_object* v_x_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1779_; 
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1765_ = v___x_1762_;
v_isShared_1766_ = v_isSharedCheck_1779_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v___x_1762_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1779_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v_vars_1767_; lean_object* v_size_1768_; lean_object* v___x_1769_; uint8_t v___x_1770_; 
v_vars_1767_ = lean_ctor_get(v_a_1763_, 30);
lean_inc_ref(v_vars_1767_);
lean_dec(v_a_1763_);
v_size_1768_ = lean_ctor_get(v_vars_1767_, 2);
v___x_1769_ = l_Lean_instInhabitedExpr;
v___x_1770_ = lean_nat_dec_lt(v_x_1749_, v_size_1768_);
if (v___x_1770_ == 0)
{
lean_object* v___x_1771_; lean_object* v___x_1773_; 
lean_dec_ref(v_vars_1767_);
v___x_1771_ = l_outOfBounds___redArg(v___x_1769_);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 0, v___x_1771_);
v___x_1773_ = v___x_1765_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v___x_1771_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
else
{
lean_object* v___x_1775_; lean_object* v___x_1777_; 
v___x_1775_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1769_, v_vars_1767_, v_x_1749_);
lean_dec_ref(v_vars_1767_);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 0, v___x_1775_);
v___x_1777_ = v___x_1765_;
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
}
}
else
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1787_; 
v_a_1780_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1782_ = v___x_1762_;
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1762_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_a_1780_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getVar___boxed(lean_object* v_x_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_){
_start:
{
lean_object* v_res_1801_; 
v_res_1801_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_x_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
lean_dec(v_a_1799_);
lean_dec_ref(v_a_1798_);
lean_dec(v_a_1797_);
lean_dec_ref(v_a_1796_);
lean_dec(v_a_1795_);
lean_dec_ref(v_a_1794_);
lean_dec(v_a_1793_);
lean_dec_ref(v_a_1792_);
lean_dec(v_a_1791_);
lean_dec(v_a_1790_);
lean_dec(v_a_1789_);
lean_dec(v_x_1788_);
return v_res_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inconsistent(lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_){
_start:
{
lean_object* v___x_1814_; 
v___x_1814_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_1803_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1815_; uint8_t v___x_1816_; 
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
lean_inc(v_a_1815_);
v___x_1816_ = lean_unbox(v_a_1815_);
if (v___x_1816_ == 0)
{
lean_object* v___x_1817_; 
lean_dec_ref(v___x_1814_);
v___x_1817_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1831_; 
v_a_1818_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1820_ = v___x_1817_;
v_isShared_1821_ = v_isSharedCheck_1831_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1817_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1831_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v_conflict_x3f_1822_; 
v_conflict_x3f_1822_ = lean_ctor_get(v_a_1818_, 36);
lean_inc(v_conflict_x3f_1822_);
lean_dec(v_a_1818_);
if (lean_obj_tag(v_conflict_x3f_1822_) == 0)
{
lean_object* v___x_1824_; 
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 0, v_a_1815_);
v___x_1824_ = v___x_1820_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_a_1815_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
else
{
uint8_t v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1829_; 
lean_dec_ref(v_conflict_x3f_1822_);
lean_dec(v_a_1815_);
v___x_1826_ = 1;
v___x_1827_ = lean_box(v___x_1826_);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 0, v___x_1827_);
v___x_1829_ = v___x_1820_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v___x_1827_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
else
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1839_; 
lean_dec(v_a_1815_);
v_a_1832_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1834_ = v___x_1817_;
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1817_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1837_; 
if (v_isShared_1835_ == 0)
{
v___x_1837_ = v___x_1834_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_a_1832_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
}
else
{
lean_dec(v_a_1815_);
return v___x_1814_;
}
}
else
{
return v___x_1814_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inconsistent___boxed(lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_);
lean_dec(v_a_1850_);
lean_dec_ref(v_a_1849_);
lean_dec(v_a_1848_);
lean_dec_ref(v_a_1847_);
lean_dec(v_a_1846_);
lean_dec_ref(v_a_1845_);
lean_dec(v_a_1844_);
lean_dec_ref(v_a_1843_);
lean_dec(v_a_1842_);
lean_dec(v_a_1841_);
lean_dec(v_a_1840_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_eliminated(lean_object* v_x_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_, v_a_1864_);
if (lean_obj_tag(v___x_1866_) == 0)
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1889_; 
v_a_1867_ = lean_ctor_get(v___x_1866_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1869_ = v___x_1866_;
v_isShared_1870_ = v_isSharedCheck_1889_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1866_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1889_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___y_1872_; lean_object* v_elimEqs_1883_; lean_object* v_size_1884_; lean_object* v___x_1885_; uint8_t v___x_1886_; 
v_elimEqs_1883_ = lean_ctor_get(v_a_1867_, 38);
lean_inc_ref(v_elimEqs_1883_);
lean_dec(v_a_1867_);
v_size_1884_ = lean_ctor_get(v_elimEqs_1883_, 2);
v___x_1885_ = lean_box(0);
v___x_1886_ = lean_nat_dec_lt(v_x_1853_, v_size_1884_);
if (v___x_1886_ == 0)
{
lean_object* v___x_1887_; 
lean_dec_ref(v_elimEqs_1883_);
v___x_1887_ = l_outOfBounds___redArg(v___x_1885_);
v___y_1872_ = v___x_1887_;
goto v___jp_1871_;
}
else
{
lean_object* v___x_1888_; 
v___x_1888_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1885_, v_elimEqs_1883_, v_x_1853_);
lean_dec_ref(v_elimEqs_1883_);
v___y_1872_ = v___x_1888_;
goto v___jp_1871_;
}
v___jp_1871_:
{
if (lean_obj_tag(v___y_1872_) == 0)
{
uint8_t v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1876_; 
v___x_1873_ = 0;
v___x_1874_ = lean_box(v___x_1873_);
if (v_isShared_1870_ == 0)
{
lean_ctor_set(v___x_1869_, 0, v___x_1874_);
v___x_1876_ = v___x_1869_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v___x_1874_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
else
{
uint8_t v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1881_; 
lean_dec_ref(v___y_1872_);
v___x_1878_ = 1;
v___x_1879_ = lean_box(v___x_1878_);
if (v_isShared_1870_ == 0)
{
lean_ctor_set(v___x_1869_, 0, v___x_1879_);
v___x_1881_ = v___x_1869_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___x_1879_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
}
}
else
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
v_a_1890_ = lean_ctor_get(v___x_1866_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1892_ = v___x_1866_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1866_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1890_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_eliminated___boxed(lean_object* v_x_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_){
_start:
{
lean_object* v_res_1911_; 
v_res_1911_ = l_Lean_Meta_Grind_Arith_Linear_eliminated(v_x_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_);
lean_dec(v_a_1909_);
lean_dec_ref(v_a_1908_);
lean_dec(v_a_1907_);
lean_dec_ref(v_a_1906_);
lean_dec(v_a_1905_);
lean_dec_ref(v_a_1904_);
lean_dec(v_a_1903_);
lean_dec_ref(v_a_1902_);
lean_dec(v_a_1901_);
lean_dec(v_a_1900_);
lean_dec(v_a_1899_);
lean_dec(v_x_1898_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOccursOf(lean_object* v_x_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_){
_start:
{
lean_object* v___x_1925_; 
v___x_1925_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1942_; 
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1928_ = v___x_1925_;
v_isShared_1929_ = v_isSharedCheck_1942_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1925_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1942_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v_occurs_1930_; lean_object* v_size_1931_; lean_object* v___x_1932_; uint8_t v___x_1933_; 
v_occurs_1930_ = lean_ctor_get(v_a_1926_, 40);
lean_inc_ref(v_occurs_1930_);
lean_dec(v_a_1926_);
v_size_1931_ = lean_ctor_get(v_occurs_1930_, 2);
v___x_1932_ = lean_box(1);
v___x_1933_ = lean_nat_dec_lt(v_x_1912_, v_size_1931_);
if (v___x_1933_ == 0)
{
lean_object* v___x_1934_; lean_object* v___x_1936_; 
lean_dec_ref(v_occurs_1930_);
v___x_1934_ = l_outOfBounds___redArg(v___x_1932_);
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 0, v___x_1934_);
v___x_1936_ = v___x_1928_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v___x_1934_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
else
{
lean_object* v___x_1938_; lean_object* v___x_1940_; 
v___x_1938_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1932_, v_occurs_1930_, v_x_1912_);
lean_dec_ref(v_occurs_1930_);
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 0, v___x_1938_);
v___x_1940_ = v___x_1928_;
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
else
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
v_a_1943_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1945_ = v___x_1925_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1925_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_a_1943_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOccursOf___boxed(lean_object* v_x_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l_Lean_Meta_Grind_Arith_Linear_getOccursOf(v_x_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_);
lean_dec(v_a_1962_);
lean_dec_ref(v_a_1961_);
lean_dec(v_a_1960_);
lean_dec_ref(v_a_1959_);
lean_dec(v_a_1958_);
lean_dec_ref(v_a_1957_);
lean_dec(v_a_1956_);
lean_dec_ref(v_a_1955_);
lean_dec(v_a_1954_);
lean_dec(v_a_1953_);
lean_dec(v_a_1952_);
lean_dec(v_x_1951_);
return v_res_1964_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(lean_object* v_k_1965_, lean_object* v_t_1966_){
_start:
{
if (lean_obj_tag(v_t_1966_) == 0)
{
lean_object* v_k_1967_; lean_object* v_l_1968_; lean_object* v_r_1969_; uint8_t v___x_1970_; 
v_k_1967_ = lean_ctor_get(v_t_1966_, 1);
v_l_1968_ = lean_ctor_get(v_t_1966_, 3);
v_r_1969_ = lean_ctor_get(v_t_1966_, 4);
v___x_1970_ = lean_nat_dec_lt(v_k_1965_, v_k_1967_);
if (v___x_1970_ == 0)
{
uint8_t v___x_1971_; 
v___x_1971_ = lean_nat_dec_eq(v_k_1965_, v_k_1967_);
if (v___x_1971_ == 0)
{
v_t_1966_ = v_r_1969_;
goto _start;
}
else
{
return v___x_1971_;
}
}
else
{
v_t_1966_ = v_l_1968_;
goto _start;
}
}
else
{
uint8_t v___x_1974_; 
v___x_1974_ = 0;
return v___x_1974_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg___boxed(lean_object* v_k_1975_, lean_object* v_t_1976_){
_start:
{
uint8_t v_res_1977_; lean_object* v_r_1978_; 
v_res_1977_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_k_1975_, v_t_1976_);
lean_dec(v_t_1976_);
lean_dec(v_k_1975_);
v_r_1978_ = lean_box(v_res_1977_);
return v_r_1978_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(lean_object* v_k_1979_, lean_object* v_v_1980_, lean_object* v_t_1981_){
_start:
{
if (lean_obj_tag(v_t_1981_) == 0)
{
lean_object* v_size_1982_; lean_object* v_k_1983_; lean_object* v_v_1984_; lean_object* v_l_1985_; lean_object* v_r_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_2267_; 
v_size_1982_ = lean_ctor_get(v_t_1981_, 0);
v_k_1983_ = lean_ctor_get(v_t_1981_, 1);
v_v_1984_ = lean_ctor_get(v_t_1981_, 2);
v_l_1985_ = lean_ctor_get(v_t_1981_, 3);
v_r_1986_ = lean_ctor_get(v_t_1981_, 4);
v_isSharedCheck_2267_ = !lean_is_exclusive(v_t_1981_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_1988_ = v_t_1981_;
v_isShared_1989_ = v_isSharedCheck_2267_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_r_1986_);
lean_inc(v_l_1985_);
lean_inc(v_v_1984_);
lean_inc(v_k_1983_);
lean_inc(v_size_1982_);
lean_dec(v_t_1981_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_2267_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
uint8_t v___x_1990_; 
v___x_1990_ = lean_nat_dec_lt(v_k_1979_, v_k_1983_);
if (v___x_1990_ == 0)
{
uint8_t v___x_1991_; 
v___x_1991_ = lean_nat_dec_eq(v_k_1979_, v_k_1983_);
if (v___x_1991_ == 0)
{
lean_object* v_impl_1992_; lean_object* v___x_1993_; 
lean_dec(v_size_1982_);
v_impl_1992_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_k_1979_, v_v_1980_, v_r_1986_);
v___x_1993_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1985_) == 0)
{
lean_object* v_size_1994_; lean_object* v_size_1995_; lean_object* v_k_1996_; lean_object* v_v_1997_; lean_object* v_l_1998_; lean_object* v_r_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; uint8_t v___x_2002_; 
v_size_1994_ = lean_ctor_get(v_l_1985_, 0);
v_size_1995_ = lean_ctor_get(v_impl_1992_, 0);
lean_inc(v_size_1995_);
v_k_1996_ = lean_ctor_get(v_impl_1992_, 1);
lean_inc(v_k_1996_);
v_v_1997_ = lean_ctor_get(v_impl_1992_, 2);
lean_inc(v_v_1997_);
v_l_1998_ = lean_ctor_get(v_impl_1992_, 3);
lean_inc(v_l_1998_);
v_r_1999_ = lean_ctor_get(v_impl_1992_, 4);
lean_inc(v_r_1999_);
v___x_2000_ = lean_unsigned_to_nat(3u);
v___x_2001_ = lean_nat_mul(v___x_2000_, v_size_1994_);
v___x_2002_ = lean_nat_dec_lt(v___x_2001_, v_size_1995_);
lean_dec(v___x_2001_);
if (v___x_2002_ == 0)
{
lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2006_; 
lean_dec(v_r_1999_);
lean_dec(v_l_1998_);
lean_dec(v_v_1997_);
lean_dec(v_k_1996_);
v___x_2003_ = lean_nat_add(v___x_1993_, v_size_1994_);
v___x_2004_ = lean_nat_add(v___x_2003_, v_size_1995_);
lean_dec(v_size_1995_);
lean_dec(v___x_2003_);
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 4, v_impl_1992_);
lean_ctor_set(v___x_1988_, 0, v___x_2004_);
v___x_2006_ = v___x_1988_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___x_2004_);
lean_ctor_set(v_reuseFailAlloc_2007_, 1, v_k_1983_);
lean_ctor_set(v_reuseFailAlloc_2007_, 2, v_v_1984_);
lean_ctor_set(v_reuseFailAlloc_2007_, 3, v_l_1985_);
lean_ctor_set(v_reuseFailAlloc_2007_, 4, v_impl_1992_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
else
{
lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2071_; 
v_isSharedCheck_2071_ = !lean_is_exclusive(v_impl_1992_);
if (v_isSharedCheck_2071_ == 0)
{
lean_object* v_unused_2072_; lean_object* v_unused_2073_; lean_object* v_unused_2074_; lean_object* v_unused_2075_; lean_object* v_unused_2076_; 
v_unused_2072_ = lean_ctor_get(v_impl_1992_, 4);
lean_dec(v_unused_2072_);
v_unused_2073_ = lean_ctor_get(v_impl_1992_, 3);
lean_dec(v_unused_2073_);
v_unused_2074_ = lean_ctor_get(v_impl_1992_, 2);
lean_dec(v_unused_2074_);
v_unused_2075_ = lean_ctor_get(v_impl_1992_, 1);
lean_dec(v_unused_2075_);
v_unused_2076_ = lean_ctor_get(v_impl_1992_, 0);
lean_dec(v_unused_2076_);
v___x_2009_ = v_impl_1992_;
v_isShared_2010_ = v_isSharedCheck_2071_;
goto v_resetjp_2008_;
}
else
{
lean_dec(v_impl_1992_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2071_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v_size_2011_; lean_object* v_k_2012_; lean_object* v_v_2013_; lean_object* v_l_2014_; lean_object* v_r_2015_; lean_object* v_size_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; uint8_t v___x_2019_; 
v_size_2011_ = lean_ctor_get(v_l_1998_, 0);
v_k_2012_ = lean_ctor_get(v_l_1998_, 1);
v_v_2013_ = lean_ctor_get(v_l_1998_, 2);
v_l_2014_ = lean_ctor_get(v_l_1998_, 3);
v_r_2015_ = lean_ctor_get(v_l_1998_, 4);
v_size_2016_ = lean_ctor_get(v_r_1999_, 0);
v___x_2017_ = lean_unsigned_to_nat(2u);
v___x_2018_ = lean_nat_mul(v___x_2017_, v_size_2016_);
v___x_2019_ = lean_nat_dec_lt(v_size_2011_, v___x_2018_);
lean_dec(v___x_2018_);
if (v___x_2019_ == 0)
{
lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2047_; 
lean_inc(v_r_2015_);
lean_inc(v_l_2014_);
lean_inc(v_v_2013_);
lean_inc(v_k_2012_);
v_isSharedCheck_2047_ = !lean_is_exclusive(v_l_1998_);
if (v_isSharedCheck_2047_ == 0)
{
lean_object* v_unused_2048_; lean_object* v_unused_2049_; lean_object* v_unused_2050_; lean_object* v_unused_2051_; lean_object* v_unused_2052_; 
v_unused_2048_ = lean_ctor_get(v_l_1998_, 4);
lean_dec(v_unused_2048_);
v_unused_2049_ = lean_ctor_get(v_l_1998_, 3);
lean_dec(v_unused_2049_);
v_unused_2050_ = lean_ctor_get(v_l_1998_, 2);
lean_dec(v_unused_2050_);
v_unused_2051_ = lean_ctor_get(v_l_1998_, 1);
lean_dec(v_unused_2051_);
v_unused_2052_ = lean_ctor_get(v_l_1998_, 0);
lean_dec(v_unused_2052_);
v___x_2021_ = v_l_1998_;
v_isShared_2022_ = v_isSharedCheck_2047_;
goto v_resetjp_2020_;
}
else
{
lean_dec(v_l_1998_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2047_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___y_2026_; lean_object* v___y_2027_; lean_object* v___y_2028_; lean_object* v___y_2037_; 
v___x_2023_ = lean_nat_add(v___x_1993_, v_size_1994_);
v___x_2024_ = lean_nat_add(v___x_2023_, v_size_1995_);
lean_dec(v_size_1995_);
if (lean_obj_tag(v_l_2014_) == 0)
{
lean_object* v_size_2045_; 
v_size_2045_ = lean_ctor_get(v_l_2014_, 0);
lean_inc(v_size_2045_);
v___y_2037_ = v_size_2045_;
goto v___jp_2036_;
}
else
{
lean_object* v___x_2046_; 
v___x_2046_ = lean_unsigned_to_nat(0u);
v___y_2037_ = v___x_2046_;
goto v___jp_2036_;
}
v___jp_2025_:
{
lean_object* v___x_2029_; lean_object* v___x_2031_; 
v___x_2029_ = lean_nat_add(v___y_2026_, v___y_2028_);
lean_dec(v___y_2028_);
lean_dec(v___y_2026_);
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 4, v_r_1999_);
lean_ctor_set(v___x_2021_, 3, v_r_2015_);
lean_ctor_set(v___x_2021_, 2, v_v_1997_);
lean_ctor_set(v___x_2021_, 1, v_k_1996_);
lean_ctor_set(v___x_2021_, 0, v___x_2029_);
v___x_2031_ = v___x_2021_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___x_2029_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v_k_1996_);
lean_ctor_set(v_reuseFailAlloc_2035_, 2, v_v_1997_);
lean_ctor_set(v_reuseFailAlloc_2035_, 3, v_r_2015_);
lean_ctor_set(v_reuseFailAlloc_2035_, 4, v_r_1999_);
v___x_2031_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
lean_object* v___x_2033_; 
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 4, v___x_2031_);
lean_ctor_set(v___x_2009_, 3, v___y_2027_);
lean_ctor_set(v___x_2009_, 2, v_v_2013_);
lean_ctor_set(v___x_2009_, 1, v_k_2012_);
lean_ctor_set(v___x_2009_, 0, v___x_2024_);
v___x_2033_ = v___x_2009_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2024_);
lean_ctor_set(v_reuseFailAlloc_2034_, 1, v_k_2012_);
lean_ctor_set(v_reuseFailAlloc_2034_, 2, v_v_2013_);
lean_ctor_set(v_reuseFailAlloc_2034_, 3, v___y_2027_);
lean_ctor_set(v_reuseFailAlloc_2034_, 4, v___x_2031_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
v___jp_2036_:
{
lean_object* v___x_2038_; lean_object* v___x_2040_; 
v___x_2038_ = lean_nat_add(v___x_2023_, v___y_2037_);
lean_dec(v___y_2037_);
lean_dec(v___x_2023_);
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 4, v_l_2014_);
lean_ctor_set(v___x_1988_, 0, v___x_2038_);
v___x_2040_ = v___x_1988_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v___x_2038_);
lean_ctor_set(v_reuseFailAlloc_2044_, 1, v_k_1983_);
lean_ctor_set(v_reuseFailAlloc_2044_, 2, v_v_1984_);
lean_ctor_set(v_reuseFailAlloc_2044_, 3, v_l_1985_);
lean_ctor_set(v_reuseFailAlloc_2044_, 4, v_l_2014_);
v___x_2040_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
lean_object* v___x_2041_; 
v___x_2041_ = lean_nat_add(v___x_1993_, v_size_2016_);
if (lean_obj_tag(v_r_2015_) == 0)
{
lean_object* v_size_2042_; 
v_size_2042_ = lean_ctor_get(v_r_2015_, 0);
lean_inc(v_size_2042_);
v___y_2026_ = v___x_2041_;
v___y_2027_ = v___x_2040_;
v___y_2028_ = v_size_2042_;
goto v___jp_2025_;
}
else
{
lean_object* v___x_2043_; 
v___x_2043_ = lean_unsigned_to_nat(0u);
v___y_2026_ = v___x_2041_;
v___y_2027_ = v___x_2040_;
v___y_2028_ = v___x_2043_;
goto v___jp_2025_;
}
}
}
}
}
else
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2057_; 
lean_del_object(v___x_1988_);
v___x_2053_ = lean_nat_add(v___x_1993_, v_size_1994_);
v___x_2054_ = lean_nat_add(v___x_2053_, v_size_1995_);
lean_dec(v_size_1995_);
v___x_2055_ = lean_nat_add(v___x_2053_, v_size_2011_);
lean_dec(v___x_2053_);
lean_inc_ref(v_l_1985_);
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 4, v_l_1998_);
lean_ctor_set(v___x_2009_, 3, v_l_1985_);
lean_ctor_set(v___x_2009_, 2, v_v_1984_);
lean_ctor_set(v___x_2009_, 1, v_k_1983_);
lean_ctor_set(v___x_2009_, 0, v___x_2055_);
v___x_2057_ = v___x_2009_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v___x_2055_);
lean_ctor_set(v_reuseFailAlloc_2070_, 1, v_k_1983_);
lean_ctor_set(v_reuseFailAlloc_2070_, 2, v_v_1984_);
lean_ctor_set(v_reuseFailAlloc_2070_, 3, v_l_1985_);
lean_ctor_set(v_reuseFailAlloc_2070_, 4, v_l_1998_);
v___x_2057_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
v_isSharedCheck_2064_ = !lean_is_exclusive(v_l_1985_);
if (v_isSharedCheck_2064_ == 0)
{
lean_object* v_unused_2065_; lean_object* v_unused_2066_; lean_object* v_unused_2067_; lean_object* v_unused_2068_; lean_object* v_unused_2069_; 
v_unused_2065_ = lean_ctor_get(v_l_1985_, 4);
lean_dec(v_unused_2065_);
v_unused_2066_ = lean_ctor_get(v_l_1985_, 3);
lean_dec(v_unused_2066_);
v_unused_2067_ = lean_ctor_get(v_l_1985_, 2);
lean_dec(v_unused_2067_);
v_unused_2068_ = lean_ctor_get(v_l_1985_, 1);
lean_dec(v_unused_2068_);
v_unused_2069_ = lean_ctor_get(v_l_1985_, 0);
lean_dec(v_unused_2069_);
v___x_2059_ = v_l_1985_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_dec(v_l_1985_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 4, v_r_1999_);
lean_ctor_set(v___x_2059_, 3, v___x_2057_);
lean_ctor_set(v___x_2059_, 2, v_v_1997_);
lean_ctor_set(v___x_2059_, 1, v_k_1996_);
lean_ctor_set(v___x_2059_, 0, v___x_2054_);
v___x_2062_ = v___x_2059_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_2054_);
lean_ctor_set(v_reuseFailAlloc_2063_, 1, v_k_1996_);
lean_ctor_set(v_reuseFailAlloc_2063_, 2, v_v_1997_);
lean_ctor_set(v_reuseFailAlloc_2063_, 3, v___x_2057_);
lean_ctor_set(v_reuseFailAlloc_2063_, 4, v_r_1999_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2077_; 
v_l_2077_ = lean_ctor_get(v_impl_1992_, 3);
lean_inc(v_l_2077_);
if (lean_obj_tag(v_l_2077_) == 0)
{
lean_object* v_r_2078_; lean_object* v_k_2079_; lean_object* v_v_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2103_; 
v_r_2078_ = lean_ctor_get(v_impl_1992_, 4);
v_k_2079_ = lean_ctor_get(v_impl_1992_, 1);
v_v_2080_ = lean_ctor_get(v_impl_1992_, 2);
v_isSharedCheck_2103_ = !lean_is_exclusive(v_impl_1992_);
if (v_isSharedCheck_2103_ == 0)
{
lean_object* v_unused_2104_; lean_object* v_unused_2105_; 
v_unused_2104_ = lean_ctor_get(v_impl_1992_, 3);
lean_dec(v_unused_2104_);
v_unused_2105_ = lean_ctor_get(v_impl_1992_, 0);
lean_dec(v_unused_2105_);
v___x_2082_ = v_impl_1992_;
v_isShared_2083_ = v_isSharedCheck_2103_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_r_2078_);
lean_inc(v_v_2080_);
lean_inc(v_k_2079_);
lean_dec(v_impl_1992_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2103_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v_k_2084_; lean_object* v_v_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2099_; 
v_k_2084_ = lean_ctor_get(v_l_2077_, 1);
v_v_2085_ = lean_ctor_get(v_l_2077_, 2);
v_isSharedCheck_2099_ = !lean_is_exclusive(v_l_2077_);
if (v_isSharedCheck_2099_ == 0)
{
lean_object* v_unused_2100_; lean_object* v_unused_2101_; lean_object* v_unused_2102_; 
v_unused_2100_ = lean_ctor_get(v_l_2077_, 4);
lean_dec(v_unused_2100_);
v_unused_2101_ = lean_ctor_get(v_l_2077_, 3);
lean_dec(v_unused_2101_);
v_unused_2102_ = lean_ctor_get(v_l_2077_, 0);
lean_dec(v_unused_2102_);
v___x_2087_ = v_l_2077_;
v_isShared_2088_ = v_isSharedCheck_2099_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_v_2085_);
lean_inc(v_k_2084_);
lean_dec(v_l_2077_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2099_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2089_; lean_object* v___x_2091_; 
v___x_2089_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2078_, 2);
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 4, v_r_2078_);
lean_ctor_set(v___x_2087_, 3, v_r_2078_);
lean_ctor_set(v___x_2087_, 2, v_v_1984_);
lean_ctor_set(v___x_2087_, 1, v_k_1983_);
lean_ctor_set(v___x_2087_, 0, v___x_1993_);
v___x_2091_ = v___x_2087_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v___x_1993_);
lean_ctor_set(v_reuseFailAlloc_2098_, 1, v_k_1983_);
lean_ctor_set(v_reuseFailAlloc_2098_, 2, v_v_1984_);
lean_ctor_set(v_reuseFailAlloc_2098_, 3, v_r_2078_);
lean_ctor_set(v_reuseFailAlloc_2098_, 4, v_r_2078_);
v___x_2091_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
lean_object* v___x_2093_; 
lean_inc(v_r_2078_);
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 3, v_r_2078_);
lean_ctor_set(v___x_2082_, 0, v___x_1993_);
v___x_2093_ = v___x_2082_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v___x_1993_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v_k_2079_);
lean_ctor_set(v_reuseFailAlloc_2097_, 2, v_v_2080_);
lean_ctor_set(v_reuseFailAlloc_2097_, 3, v_r_2078_);
lean_ctor_set(v_reuseFailAlloc_2097_, 4, v_r_2078_);
v___x_2093_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
lean_object* v___x_2095_; 
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 4, v___x_2093_);
lean_ctor_set(v___x_1988_, 3, v___x_2091_);
lean_ctor_set(v___x_1988_, 2, v_v_2085_);
lean_ctor_set(v___x_1988_, 1, v_k_2084_);
lean_ctor_set(v___x_1988_, 0, v___x_2089_);
v___x_2095_ = v___x_1988_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v___x_2089_);
lean_ctor_set(v_reuseFailAlloc_2096_, 1, v_k_2084_);
lean_ctor_set(v_reuseFailAlloc_2096_, 2, v_v_2085_);
lean_ctor_set(v_reuseFailAlloc_2096_, 3, v___x_2091_);
lean_ctor_set(v_reuseFailAlloc_2096_, 4, v___x_2093_);
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
}
else
{
lean_object* v_r_2106_; 
v_r_2106_ = lean_ctor_get(v_impl_1992_, 4);
lean_inc(v_r_2106_);
if (lean_obj_tag(v_r_2106_) == 0)
{
lean_object* v_k_2107_; lean_object* v_v_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2119_; 
v_k_2107_ = lean_ctor_get(v_impl_1992_, 1);
v_v_2108_ = lean_ctor_get(v_impl_1992_, 2);
v_isSharedCheck_2119_ = !lean_is_exclusive(v_impl_1992_);
if (v_isSharedCheck_2119_ == 0)
{
lean_object* v_unused_2120_; lean_object* v_unused_2121_; lean_object* v_unused_2122_; 
v_unused_2120_ = lean_ctor_get(v_impl_1992_, 4);
lean_dec(v_unused_2120_);
v_unused_2121_ = lean_ctor_get(v_impl_1992_, 3);
lean_dec(v_unused_2121_);
v_unused_2122_ = lean_ctor_get(v_impl_1992_, 0);
lean_dec(v_unused_2122_);
v___x_2110_ = v_impl_1992_;
v_isShared_2111_ = v_isSharedCheck_2119_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_v_2108_);
lean_inc(v_k_2107_);
lean_dec(v_impl_1992_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2119_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2112_; lean_object* v___x_2114_; 
v___x_2112_ = lean_unsigned_to_nat(3u);
if (v_isShared_2111_ == 0)
{
lean_ctor_set(v___x_2110_, 4, v_l_2077_);
lean_ctor_set(v___x_2110_, 2, v_v_1984_);
lean_ctor_set(v___x_2110_, 1, v_k_1983_);
lean_ctor_set(v___x_2110_, 0, v___x_1993_);
v___x_2114_ = v___x_2110_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v___x_1993_);
lean_ctor_set(v_reuseFailAlloc_2118_, 1, v_k_1983_);
lean_ctor_set(v_reuseFailAlloc_2118_, 2, v_v_1984_);
lean_ctor_set(v_reuseFailAlloc_2118_, 3, v_l_2077_);
lean_ctor_set(v_reuseFailAlloc_2118_, 4, v_l_2077_);
v___x_2114_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
lean_object* v___x_2116_; 
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 4, v_r_2106_);
lean_ctor_set(v___x_1988_, 3, v___x_2114_);
lean_ctor_set(v___x_1988_, 2, v_v_2108_);
lean_ctor_set(v___x_1988_, 1, v_k_2107_);
lean_ctor_set(v___x_1988_, 0, v___x_2112_);
v___x_2116_ = v___x_1988_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v___x_2112_);
lean_ctor_set(v_reuseFailAlloc_2117_, 1, v_k_2107_);
lean_ctor_set(v_reuseFailAlloc_2117_, 2, v_v_2108_);
lean_ctor_set(v_reuseFailAlloc_2117_, 3, v___x_2114_);
lean_ctor_set(v_reuseFailAlloc_2117_, 4, v_r_2106_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
}
else
{
lean_object* v___x_2123_; lean_object* v___x_2125_; 
v___x_2123_ = lean_unsigned_to_nat(2u);
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 4, v_impl_1992_);
lean_ctor_set(v___x_1988_, 3, v_r_2106_);
lean_ctor_set(v___x_1988_, 0, v___x_2123_);
v___x_2125_ = v___x_1988_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v___x_2123_);
lean_ctor_set(v_reuseFailAlloc_2126_, 1, v_k_1983_);
lean_ctor_set(v_reuseFailAlloc_2126_, 2, v_v_1984_);
lean_ctor_set(v_reuseFailAlloc_2126_, 3, v_r_2106_);
lean_ctor_set(v_reuseFailAlloc_2126_, 4, v_impl_1992_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
}
else
{
lean_object* v___x_2128_; 
lean_dec(v_v_1984_);
lean_dec(v_k_1983_);
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 2, v_v_1980_);
lean_ctor_set(v___x_1988_, 1, v_k_1979_);
v___x_2128_ = v___x_1988_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_size_1982_);
lean_ctor_set(v_reuseFailAlloc_2129_, 1, v_k_1979_);
lean_ctor_set(v_reuseFailAlloc_2129_, 2, v_v_1980_);
lean_ctor_set(v_reuseFailAlloc_2129_, 3, v_l_1985_);
lean_ctor_set(v_reuseFailAlloc_2129_, 4, v_r_1986_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
else
{
lean_object* v_impl_2130_; lean_object* v___x_2131_; 
lean_dec(v_size_1982_);
v_impl_2130_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_k_1979_, v_v_1980_, v_l_1985_);
v___x_2131_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1986_) == 0)
{
lean_object* v_size_2132_; lean_object* v_size_2133_; lean_object* v_k_2134_; lean_object* v_v_2135_; lean_object* v_l_2136_; lean_object* v_r_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; uint8_t v___x_2140_; 
v_size_2132_ = lean_ctor_get(v_r_1986_, 0);
v_size_2133_ = lean_ctor_get(v_impl_2130_, 0);
lean_inc(v_size_2133_);
v_k_2134_ = lean_ctor_get(v_impl_2130_, 1);
lean_inc(v_k_2134_);
v_v_2135_ = lean_ctor_get(v_impl_2130_, 2);
lean_inc(v_v_2135_);
v_l_2136_ = lean_ctor_get(v_impl_2130_, 3);
lean_inc(v_l_2136_);
v_r_2137_ = lean_ctor_get(v_impl_2130_, 4);
lean_inc(v_r_2137_);
v___x_2138_ = lean_unsigned_to_nat(3u);
v___x_2139_ = lean_nat_mul(v___x_2138_, v_size_2132_);
v___x_2140_ = lean_nat_dec_lt(v___x_2139_, v_size_2133_);
lean_dec(v___x_2139_);
if (v___x_2140_ == 0)
{
lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2144_; 
lean_dec(v_r_2137_);
lean_dec(v_l_2136_);
lean_dec(v_v_2135_);
lean_dec(v_k_2134_);
v___x_2141_ = lean_nat_add(v___x_2131_, v_size_2133_);
lean_dec(v_size_2133_);
v___x_2142_ = lean_nat_add(v___x_2141_, v_size_2132_);
lean_dec(v___x_2141_);
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 3, v_impl_2130_);
lean_ctor_set(v___x_1988_, 0, v___x_2142_);
v___x_2144_ = v___x_1988_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2142_);
lean_ctor_set(v_reuseFailAlloc_2145_, 1, v_k_1983_);
lean_ctor_set(v_reuseFailAlloc_2145_, 2, v_v_1984_);
lean_ctor_set(v_reuseFailAlloc_2145_, 3, v_impl_2130_);
lean_ctor_set(v_reuseFailAlloc_2145_, 4, v_r_1986_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
else
{
lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2211_; 
v_isSharedCheck_2211_ = !lean_is_exclusive(v_impl_2130_);
if (v_isSharedCheck_2211_ == 0)
{
lean_object* v_unused_2212_; lean_object* v_unused_2213_; lean_object* v_unused_2214_; lean_object* v_unused_2215_; lean_object* v_unused_2216_; 
v_unused_2212_ = lean_ctor_get(v_impl_2130_, 4);
lean_dec(v_unused_2212_);
v_unused_2213_ = lean_ctor_get(v_impl_2130_, 3);
lean_dec(v_unused_2213_);
v_unused_2214_ = lean_ctor_get(v_impl_2130_, 2);
lean_dec(v_unused_2214_);
v_unused_2215_ = lean_ctor_get(v_impl_2130_, 1);
lean_dec(v_unused_2215_);
v_unused_2216_ = lean_ctor_get(v_impl_2130_, 0);
lean_dec(v_unused_2216_);
v___x_2147_ = v_impl_2130_;
v_isShared_2148_ = v_isSharedCheck_2211_;
goto v_resetjp_2146_;
}
else
{
lean_dec(v_impl_2130_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2211_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v_size_2149_; lean_object* v_size_2150_; lean_object* v_k_2151_; lean_object* v_v_2152_; lean_object* v_l_2153_; lean_object* v_r_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; uint8_t v___x_2157_; 
v_size_2149_ = lean_ctor_get(v_l_2136_, 0);
v_size_2150_ = lean_ctor_get(v_r_2137_, 0);
v_k_2151_ = lean_ctor_get(v_r_2137_, 1);
v_v_2152_ = lean_ctor_get(v_r_2137_, 2);
v_l_2153_ = lean_ctor_get(v_r_2137_, 3);
v_r_2154_ = lean_ctor_get(v_r_2137_, 4);
v___x_2155_ = lean_unsigned_to_nat(2u);
v___x_2156_ = lean_nat_mul(v___x_2155_, v_size_2149_);
v___x_2157_ = lean_nat_dec_lt(v_size_2150_, v___x_2156_);
lean_dec(v___x_2156_);
if (v___x_2157_ == 0)
{
lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2186_; 
lean_inc(v_r_2154_);
lean_inc(v_l_2153_);
lean_inc(v_v_2152_);
lean_inc(v_k_2151_);
v_isSharedCheck_2186_ = !lean_is_exclusive(v_r_2137_);
if (v_isSharedCheck_2186_ == 0)
{
lean_object* v_unused_2187_; lean_object* v_unused_2188_; lean_object* v_unused_2189_; lean_object* v_unused_2190_; lean_object* v_unused_2191_; 
v_unused_2187_ = lean_ctor_get(v_r_2137_, 4);
lean_dec(v_unused_2187_);
v_unused_2188_ = lean_ctor_get(v_r_2137_, 3);
lean_dec(v_unused_2188_);
v_unused_2189_ = lean_ctor_get(v_r_2137_, 2);
lean_dec(v_unused_2189_);
v_unused_2190_ = lean_ctor_get(v_r_2137_, 1);
lean_dec(v_unused_2190_);
v_unused_2191_ = lean_ctor_get(v_r_2137_, 0);
lean_dec(v_unused_2191_);
v___x_2159_ = v_r_2137_;
v_isShared_2160_ = v_isSharedCheck_2186_;
goto v_resetjp_2158_;
}
else
{
lean_dec(v_r_2137_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2186_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___y_2164_; lean_object* v___y_2165_; lean_object* v___y_2166_; lean_object* v___x_2174_; lean_object* v___y_2176_; 
v___x_2161_ = lean_nat_add(v___x_2131_, v_size_2133_);
lean_dec(v_size_2133_);
v___x_2162_ = lean_nat_add(v___x_2161_, v_size_2132_);
lean_dec(v___x_2161_);
v___x_2174_ = lean_nat_add(v___x_2131_, v_size_2149_);
if (lean_obj_tag(v_l_2153_) == 0)
{
lean_object* v_size_2184_; 
v_size_2184_ = lean_ctor_get(v_l_2153_, 0);
lean_inc(v_size_2184_);
v___y_2176_ = v_size_2184_;
goto v___jp_2175_;
}
else
{
lean_object* v___x_2185_; 
v___x_2185_ = lean_unsigned_to_nat(0u);
v___y_2176_ = v___x_2185_;
goto v___jp_2175_;
}
v___jp_2163_:
{
lean_object* v___x_2167_; lean_object* v___x_2169_; 
v___x_2167_ = lean_nat_add(v___y_2165_, v___y_2166_);
lean_dec(v___y_2166_);
lean_dec(v___y_2165_);
if (v_isShared_2160_ == 0)
{
lean_ctor_set(v___x_2159_, 4, v_r_1986_);
lean_ctor_set(v___x_2159_, 3, v_r_2154_);
lean_ctor_set(v___x_2159_, 2, v_v_1984_);
lean_ctor_set(v___x_2159_, 1, v_k_1983_);
lean_ctor_set(v___x_2159_, 0, v___x_2167_);
v___x_2169_ = v___x_2159_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v___x_2167_);
lean_ctor_set(v_reuseFailAlloc_2173_, 1, v_k_1983_);
lean_ctor_set(v_reuseFailAlloc_2173_, 2, v_v_1984_);
lean_ctor_set(v_reuseFailAlloc_2173_, 3, v_r_2154_);
lean_ctor_set(v_reuseFailAlloc_2173_, 4, v_r_1986_);
v___x_2169_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
lean_object* v___x_2171_; 
if (v_isShared_2148_ == 0)
{
lean_ctor_set(v___x_2147_, 4, v___x_2169_);
lean_ctor_set(v___x_2147_, 3, v___y_2164_);
lean_ctor_set(v___x_2147_, 2, v_v_2152_);
lean_ctor_set(v___x_2147_, 1, v_k_2151_);
lean_ctor_set(v___x_2147_, 0, v___x_2162_);
v___x_2171_ = v___x_2147_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2162_);
lean_ctor_set(v_reuseFailAlloc_2172_, 1, v_k_2151_);
lean_ctor_set(v_reuseFailAlloc_2172_, 2, v_v_2152_);
lean_ctor_set(v_reuseFailAlloc_2172_, 3, v___y_2164_);
lean_ctor_set(v_reuseFailAlloc_2172_, 4, v___x_2169_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
v___jp_2175_:
{
lean_object* v___x_2177_; lean_object* v___x_2179_; 
v___x_2177_ = lean_nat_add(v___x_2174_, v___y_2176_);
lean_dec(v___y_2176_);
lean_dec(v___x_2174_);
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 4, v_l_2153_);
lean_ctor_set(v___x_1988_, 3, v_l_2136_);
lean_ctor_set(v___x_1988_, 2, v_v_2135_);
lean_ctor_set(v___x_1988_, 1, v_k_2134_);
lean_ctor_set(v___x_1988_, 0, v___x_2177_);
v___x_2179_ = v___x_1988_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v___x_2177_);
lean_ctor_set(v_reuseFailAlloc_2183_, 1, v_k_2134_);
lean_ctor_set(v_reuseFailAlloc_2183_, 2, v_v_2135_);
lean_ctor_set(v_reuseFailAlloc_2183_, 3, v_l_2136_);
lean_ctor_set(v_reuseFailAlloc_2183_, 4, v_l_2153_);
v___x_2179_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
lean_object* v___x_2180_; 
v___x_2180_ = lean_nat_add(v___x_2131_, v_size_2132_);
if (lean_obj_tag(v_r_2154_) == 0)
{
lean_object* v_size_2181_; 
v_size_2181_ = lean_ctor_get(v_r_2154_, 0);
lean_inc(v_size_2181_);
v___y_2164_ = v___x_2179_;
v___y_2165_ = v___x_2180_;
v___y_2166_ = v_size_2181_;
goto v___jp_2163_;
}
else
{
lean_object* v___x_2182_; 
v___x_2182_ = lean_unsigned_to_nat(0u);
v___y_2164_ = v___x_2179_;
v___y_2165_ = v___x_2180_;
v___y_2166_ = v___x_2182_;
goto v___jp_2163_;
}
}
}
}
}
else
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2197_; 
lean_del_object(v___x_1988_);
v___x_2192_ = lean_nat_add(v___x_2131_, v_size_2133_);
lean_dec(v_size_2133_);
v___x_2193_ = lean_nat_add(v___x_2192_, v_size_2132_);
lean_dec(v___x_2192_);
v___x_2194_ = lean_nat_add(v___x_2131_, v_size_2132_);
v___x_2195_ = lean_nat_add(v___x_2194_, v_size_2150_);
lean_dec(v___x_2194_);
lean_inc_ref(v_r_1986_);
if (v_isShared_2148_ == 0)
{
lean_ctor_set(v___x_2147_, 4, v_r_1986_);
lean_ctor_set(v___x_2147_, 3, v_r_2137_);
lean_ctor_set(v___x_2147_, 2, v_v_1984_);
lean_ctor_set(v___x_2147_, 1, v_k_1983_);
lean_ctor_set(v___x_2147_, 0, v___x_2195_);
v___x_2197_ = v___x_2147_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v___x_2195_);
lean_ctor_set(v_reuseFailAlloc_2210_, 1, v_k_1983_);
lean_ctor_set(v_reuseFailAlloc_2210_, 2, v_v_1984_);
lean_ctor_set(v_reuseFailAlloc_2210_, 3, v_r_2137_);
lean_ctor_set(v_reuseFailAlloc_2210_, 4, v_r_1986_);
v___x_2197_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2204_; 
v_isSharedCheck_2204_ = !lean_is_exclusive(v_r_1986_);
if (v_isSharedCheck_2204_ == 0)
{
lean_object* v_unused_2205_; lean_object* v_unused_2206_; lean_object* v_unused_2207_; lean_object* v_unused_2208_; lean_object* v_unused_2209_; 
v_unused_2205_ = lean_ctor_get(v_r_1986_, 4);
lean_dec(v_unused_2205_);
v_unused_2206_ = lean_ctor_get(v_r_1986_, 3);
lean_dec(v_unused_2206_);
v_unused_2207_ = lean_ctor_get(v_r_1986_, 2);
lean_dec(v_unused_2207_);
v_unused_2208_ = lean_ctor_get(v_r_1986_, 1);
lean_dec(v_unused_2208_);
v_unused_2209_ = lean_ctor_get(v_r_1986_, 0);
lean_dec(v_unused_2209_);
v___x_2199_ = v_r_1986_;
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
else
{
lean_dec(v_r_1986_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2202_; 
if (v_isShared_2200_ == 0)
{
lean_ctor_set(v___x_2199_, 4, v___x_2197_);
lean_ctor_set(v___x_2199_, 3, v_l_2136_);
lean_ctor_set(v___x_2199_, 2, v_v_2135_);
lean_ctor_set(v___x_2199_, 1, v_k_2134_);
lean_ctor_set(v___x_2199_, 0, v___x_2193_);
v___x_2202_ = v___x_2199_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v___x_2193_);
lean_ctor_set(v_reuseFailAlloc_2203_, 1, v_k_2134_);
lean_ctor_set(v_reuseFailAlloc_2203_, 2, v_v_2135_);
lean_ctor_set(v_reuseFailAlloc_2203_, 3, v_l_2136_);
lean_ctor_set(v_reuseFailAlloc_2203_, 4, v___x_2197_);
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
}
}
}
else
{
lean_object* v_l_2217_; 
v_l_2217_ = lean_ctor_get(v_impl_2130_, 3);
lean_inc(v_l_2217_);
if (lean_obj_tag(v_l_2217_) == 0)
{
lean_object* v_r_2218_; lean_object* v_k_2219_; lean_object* v_v_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2231_; 
v_r_2218_ = lean_ctor_get(v_impl_2130_, 4);
v_k_2219_ = lean_ctor_get(v_impl_2130_, 1);
v_v_2220_ = lean_ctor_get(v_impl_2130_, 2);
v_isSharedCheck_2231_ = !lean_is_exclusive(v_impl_2130_);
if (v_isSharedCheck_2231_ == 0)
{
lean_object* v_unused_2232_; lean_object* v_unused_2233_; 
v_unused_2232_ = lean_ctor_get(v_impl_2130_, 3);
lean_dec(v_unused_2232_);
v_unused_2233_ = lean_ctor_get(v_impl_2130_, 0);
lean_dec(v_unused_2233_);
v___x_2222_ = v_impl_2130_;
v_isShared_2223_ = v_isSharedCheck_2231_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_r_2218_);
lean_inc(v_v_2220_);
lean_inc(v_k_2219_);
lean_dec(v_impl_2130_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2231_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2224_; lean_object* v___x_2226_; 
v___x_2224_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2218_);
if (v_isShared_2223_ == 0)
{
lean_ctor_set(v___x_2222_, 3, v_r_2218_);
lean_ctor_set(v___x_2222_, 2, v_v_1984_);
lean_ctor_set(v___x_2222_, 1, v_k_1983_);
lean_ctor_set(v___x_2222_, 0, v___x_2131_);
v___x_2226_ = v___x_2222_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v___x_2131_);
lean_ctor_set(v_reuseFailAlloc_2230_, 1, v_k_1983_);
lean_ctor_set(v_reuseFailAlloc_2230_, 2, v_v_1984_);
lean_ctor_set(v_reuseFailAlloc_2230_, 3, v_r_2218_);
lean_ctor_set(v_reuseFailAlloc_2230_, 4, v_r_2218_);
v___x_2226_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
lean_object* v___x_2228_; 
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 4, v___x_2226_);
lean_ctor_set(v___x_1988_, 3, v_l_2217_);
lean_ctor_set(v___x_1988_, 2, v_v_2220_);
lean_ctor_set(v___x_1988_, 1, v_k_2219_);
lean_ctor_set(v___x_1988_, 0, v___x_2224_);
v___x_2228_ = v___x_1988_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v___x_2224_);
lean_ctor_set(v_reuseFailAlloc_2229_, 1, v_k_2219_);
lean_ctor_set(v_reuseFailAlloc_2229_, 2, v_v_2220_);
lean_ctor_set(v_reuseFailAlloc_2229_, 3, v_l_2217_);
lean_ctor_set(v_reuseFailAlloc_2229_, 4, v___x_2226_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
else
{
lean_object* v_r_2234_; 
v_r_2234_ = lean_ctor_get(v_impl_2130_, 4);
lean_inc(v_r_2234_);
if (lean_obj_tag(v_r_2234_) == 0)
{
lean_object* v_k_2235_; lean_object* v_v_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2259_; 
v_k_2235_ = lean_ctor_get(v_impl_2130_, 1);
v_v_2236_ = lean_ctor_get(v_impl_2130_, 2);
v_isSharedCheck_2259_ = !lean_is_exclusive(v_impl_2130_);
if (v_isSharedCheck_2259_ == 0)
{
lean_object* v_unused_2260_; lean_object* v_unused_2261_; lean_object* v_unused_2262_; 
v_unused_2260_ = lean_ctor_get(v_impl_2130_, 4);
lean_dec(v_unused_2260_);
v_unused_2261_ = lean_ctor_get(v_impl_2130_, 3);
lean_dec(v_unused_2261_);
v_unused_2262_ = lean_ctor_get(v_impl_2130_, 0);
lean_dec(v_unused_2262_);
v___x_2238_ = v_impl_2130_;
v_isShared_2239_ = v_isSharedCheck_2259_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_v_2236_);
lean_inc(v_k_2235_);
lean_dec(v_impl_2130_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2259_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v_k_2240_; lean_object* v_v_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2255_; 
v_k_2240_ = lean_ctor_get(v_r_2234_, 1);
v_v_2241_ = lean_ctor_get(v_r_2234_, 2);
v_isSharedCheck_2255_ = !lean_is_exclusive(v_r_2234_);
if (v_isSharedCheck_2255_ == 0)
{
lean_object* v_unused_2256_; lean_object* v_unused_2257_; lean_object* v_unused_2258_; 
v_unused_2256_ = lean_ctor_get(v_r_2234_, 4);
lean_dec(v_unused_2256_);
v_unused_2257_ = lean_ctor_get(v_r_2234_, 3);
lean_dec(v_unused_2257_);
v_unused_2258_ = lean_ctor_get(v_r_2234_, 0);
lean_dec(v_unused_2258_);
v___x_2243_ = v_r_2234_;
v_isShared_2244_ = v_isSharedCheck_2255_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_v_2241_);
lean_inc(v_k_2240_);
lean_dec(v_r_2234_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2255_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2245_; lean_object* v___x_2247_; 
v___x_2245_ = lean_unsigned_to_nat(3u);
if (v_isShared_2244_ == 0)
{
lean_ctor_set(v___x_2243_, 4, v_l_2217_);
lean_ctor_set(v___x_2243_, 3, v_l_2217_);
lean_ctor_set(v___x_2243_, 2, v_v_2236_);
lean_ctor_set(v___x_2243_, 1, v_k_2235_);
lean_ctor_set(v___x_2243_, 0, v___x_2131_);
v___x_2247_ = v___x_2243_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v___x_2131_);
lean_ctor_set(v_reuseFailAlloc_2254_, 1, v_k_2235_);
lean_ctor_set(v_reuseFailAlloc_2254_, 2, v_v_2236_);
lean_ctor_set(v_reuseFailAlloc_2254_, 3, v_l_2217_);
lean_ctor_set(v_reuseFailAlloc_2254_, 4, v_l_2217_);
v___x_2247_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
lean_object* v___x_2249_; 
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 4, v_l_2217_);
lean_ctor_set(v___x_2238_, 2, v_v_1984_);
lean_ctor_set(v___x_2238_, 1, v_k_1983_);
lean_ctor_set(v___x_2238_, 0, v___x_2131_);
v___x_2249_ = v___x_2238_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v___x_2131_);
lean_ctor_set(v_reuseFailAlloc_2253_, 1, v_k_1983_);
lean_ctor_set(v_reuseFailAlloc_2253_, 2, v_v_1984_);
lean_ctor_set(v_reuseFailAlloc_2253_, 3, v_l_2217_);
lean_ctor_set(v_reuseFailAlloc_2253_, 4, v_l_2217_);
v___x_2249_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
lean_object* v___x_2251_; 
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 4, v___x_2249_);
lean_ctor_set(v___x_1988_, 3, v___x_2247_);
lean_ctor_set(v___x_1988_, 2, v_v_2241_);
lean_ctor_set(v___x_1988_, 1, v_k_2240_);
lean_ctor_set(v___x_1988_, 0, v___x_2245_);
v___x_2251_ = v___x_1988_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v___x_2245_);
lean_ctor_set(v_reuseFailAlloc_2252_, 1, v_k_2240_);
lean_ctor_set(v_reuseFailAlloc_2252_, 2, v_v_2241_);
lean_ctor_set(v_reuseFailAlloc_2252_, 3, v___x_2247_);
lean_ctor_set(v_reuseFailAlloc_2252_, 4, v___x_2249_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
}
}
}
else
{
lean_object* v___x_2263_; lean_object* v___x_2265_; 
v___x_2263_ = lean_unsigned_to_nat(2u);
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 4, v_r_2234_);
lean_ctor_set(v___x_1988_, 3, v_impl_2130_);
lean_ctor_set(v___x_1988_, 0, v___x_2263_);
v___x_2265_ = v___x_1988_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v___x_2263_);
lean_ctor_set(v_reuseFailAlloc_2266_, 1, v_k_1983_);
lean_ctor_set(v_reuseFailAlloc_2266_, 2, v_v_1984_);
lean_ctor_set(v_reuseFailAlloc_2266_, 3, v_impl_2130_);
lean_ctor_set(v_reuseFailAlloc_2266_, 4, v_r_2234_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2268_ = lean_unsigned_to_nat(1u);
v___x_2269_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2268_);
lean_ctor_set(v___x_2269_, 1, v_k_1979_);
lean_ctor_set(v___x_2269_, 2, v_v_1980_);
lean_ctor_set(v___x_2269_, 3, v_t_1981_);
lean_ctor_set(v___x_2269_, 4, v_t_1981_);
return v___x_2269_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2(lean_object* v_y_2270_, lean_object* v_x_2271_, size_t v_x_2272_, size_t v_x_2273_){
_start:
{
if (lean_obj_tag(v_x_2271_) == 0)
{
lean_object* v_cs_2274_; size_t v_j_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; uint8_t v___x_2278_; 
v_cs_2274_ = lean_ctor_get(v_x_2271_, 0);
v_j_2275_ = lean_usize_shift_right(v_x_2272_, v_x_2273_);
v___x_2276_ = lean_usize_to_nat(v_j_2275_);
v___x_2277_ = lean_array_get_size(v_cs_2274_);
v___x_2278_ = lean_nat_dec_lt(v___x_2276_, v___x_2277_);
if (v___x_2278_ == 0)
{
lean_dec(v___x_2276_);
lean_dec(v_y_2270_);
return v_x_2271_;
}
else
{
lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2296_; 
lean_inc_ref(v_cs_2274_);
v_isSharedCheck_2296_ = !lean_is_exclusive(v_x_2271_);
if (v_isSharedCheck_2296_ == 0)
{
lean_object* v_unused_2297_; 
v_unused_2297_ = lean_ctor_get(v_x_2271_, 0);
lean_dec(v_unused_2297_);
v___x_2280_ = v_x_2271_;
v_isShared_2281_ = v_isSharedCheck_2296_;
goto v_resetjp_2279_;
}
else
{
lean_dec(v_x_2271_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2296_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
size_t v___x_2282_; size_t v___x_2283_; size_t v___x_2284_; size_t v_i_2285_; size_t v___x_2286_; size_t v_shift_2287_; lean_object* v_v_2288_; lean_object* v___x_2289_; lean_object* v_xs_x27_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2294_; 
v___x_2282_ = ((size_t)1ULL);
v___x_2283_ = lean_usize_shift_left(v___x_2282_, v_x_2273_);
v___x_2284_ = lean_usize_sub(v___x_2283_, v___x_2282_);
v_i_2285_ = lean_usize_land(v_x_2272_, v___x_2284_);
v___x_2286_ = ((size_t)5ULL);
v_shift_2287_ = lean_usize_sub(v_x_2273_, v___x_2286_);
v_v_2288_ = lean_array_fget(v_cs_2274_, v___x_2276_);
v___x_2289_ = lean_box(0);
v_xs_x27_2290_ = lean_array_fset(v_cs_2274_, v___x_2276_, v___x_2289_);
v___x_2291_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2(v_y_2270_, v_v_2288_, v_i_2285_, v_shift_2287_);
v___x_2292_ = lean_array_fset(v_xs_x27_2290_, v___x_2276_, v___x_2291_);
lean_dec(v___x_2276_);
if (v_isShared_2281_ == 0)
{
lean_ctor_set(v___x_2280_, 0, v___x_2292_);
v___x_2294_ = v___x_2280_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v___x_2292_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
}
}
else
{
lean_object* v_vs_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; uint8_t v___x_2301_; 
v_vs_2298_ = lean_ctor_get(v_x_2271_, 0);
v___x_2299_ = lean_usize_to_nat(v_x_2272_);
v___x_2300_ = lean_array_get_size(v_vs_2298_);
v___x_2301_ = lean_nat_dec_lt(v___x_2299_, v___x_2300_);
if (v___x_2301_ == 0)
{
lean_dec(v___x_2299_);
lean_dec(v_y_2270_);
return v_x_2271_;
}
else
{
lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2316_; 
lean_inc_ref(v_vs_2298_);
v_isSharedCheck_2316_ = !lean_is_exclusive(v_x_2271_);
if (v_isSharedCheck_2316_ == 0)
{
lean_object* v_unused_2317_; 
v_unused_2317_ = lean_ctor_get(v_x_2271_, 0);
lean_dec(v_unused_2317_);
v___x_2303_ = v_x_2271_;
v_isShared_2304_ = v_isSharedCheck_2316_;
goto v_resetjp_2302_;
}
else
{
lean_dec(v_x_2271_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2316_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v_v_2305_; lean_object* v___x_2306_; lean_object* v_xs_x27_2307_; lean_object* v___y_2309_; uint8_t v___x_2314_; 
v_v_2305_ = lean_array_fget(v_vs_2298_, v___x_2299_);
v___x_2306_ = lean_box(0);
v_xs_x27_2307_ = lean_array_fset(v_vs_2298_, v___x_2299_, v___x_2306_);
v___x_2314_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_y_2270_, v_v_2305_);
if (v___x_2314_ == 0)
{
lean_object* v___x_2315_; 
v___x_2315_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_y_2270_, v___x_2306_, v_v_2305_);
v___y_2309_ = v___x_2315_;
goto v___jp_2308_;
}
else
{
lean_dec(v_y_2270_);
v___y_2309_ = v_v_2305_;
goto v___jp_2308_;
}
v___jp_2308_:
{
lean_object* v___x_2310_; lean_object* v___x_2312_; 
v___x_2310_ = lean_array_fset(v_xs_x27_2307_, v___x_2299_, v___y_2309_);
lean_dec(v___x_2299_);
if (v_isShared_2304_ == 0)
{
lean_ctor_set(v___x_2303_, 0, v___x_2310_);
v___x_2312_ = v___x_2303_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v___x_2310_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2___boxed(lean_object* v_y_2318_, lean_object* v_x_2319_, lean_object* v_x_2320_, lean_object* v_x_2321_){
_start:
{
size_t v_x_6037__boxed_2322_; size_t v_x_6038__boxed_2323_; lean_object* v_res_2324_; 
v_x_6037__boxed_2322_ = lean_unbox_usize(v_x_2320_);
lean_dec(v_x_2320_);
v_x_6038__boxed_2323_ = lean_unbox_usize(v_x_2321_);
lean_dec(v_x_2321_);
v_res_2324_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2(v_y_2318_, v_x_2319_, v_x_6037__boxed_2322_, v_x_6038__boxed_2323_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2(lean_object* v_y_2325_, lean_object* v_t_2326_, lean_object* v_i_2327_){
_start:
{
lean_object* v_root_2328_; lean_object* v_tail_2329_; lean_object* v_size_2330_; size_t v_shift_2331_; lean_object* v_tailOff_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2359_; 
v_root_2328_ = lean_ctor_get(v_t_2326_, 0);
v_tail_2329_ = lean_ctor_get(v_t_2326_, 1);
v_size_2330_ = lean_ctor_get(v_t_2326_, 2);
v_shift_2331_ = lean_ctor_get_usize(v_t_2326_, 4);
v_tailOff_2332_ = lean_ctor_get(v_t_2326_, 3);
v_isSharedCheck_2359_ = !lean_is_exclusive(v_t_2326_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2334_ = v_t_2326_;
v_isShared_2335_ = v_isSharedCheck_2359_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_tailOff_2332_);
lean_inc(v_size_2330_);
lean_inc(v_tail_2329_);
lean_inc(v_root_2328_);
lean_dec(v_t_2326_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2359_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
uint8_t v___x_2336_; 
v___x_2336_ = lean_nat_dec_le(v_tailOff_2332_, v_i_2327_);
if (v___x_2336_ == 0)
{
size_t v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2340_; 
v___x_2337_ = lean_usize_of_nat(v_i_2327_);
v___x_2338_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2(v_y_2325_, v_root_2328_, v___x_2337_, v_shift_2331_);
if (v_isShared_2335_ == 0)
{
lean_ctor_set(v___x_2334_, 0, v___x_2338_);
v___x_2340_ = v___x_2334_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2338_);
lean_ctor_set(v_reuseFailAlloc_2341_, 1, v_tail_2329_);
lean_ctor_set(v_reuseFailAlloc_2341_, 2, v_size_2330_);
lean_ctor_set(v_reuseFailAlloc_2341_, 3, v_tailOff_2332_);
lean_ctor_set_usize(v_reuseFailAlloc_2341_, 4, v_shift_2331_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
else
{
lean_object* v___x_2342_; lean_object* v___x_2343_; uint8_t v___x_2344_; 
v___x_2342_ = lean_nat_sub(v_i_2327_, v_tailOff_2332_);
v___x_2343_ = lean_array_get_size(v_tail_2329_);
v___x_2344_ = lean_nat_dec_lt(v___x_2342_, v___x_2343_);
if (v___x_2344_ == 0)
{
lean_object* v___x_2346_; 
lean_dec(v___x_2342_);
lean_dec(v_y_2325_);
if (v_isShared_2335_ == 0)
{
v___x_2346_ = v___x_2334_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_root_2328_);
lean_ctor_set(v_reuseFailAlloc_2347_, 1, v_tail_2329_);
lean_ctor_set(v_reuseFailAlloc_2347_, 2, v_size_2330_);
lean_ctor_set(v_reuseFailAlloc_2347_, 3, v_tailOff_2332_);
lean_ctor_set_usize(v_reuseFailAlloc_2347_, 4, v_shift_2331_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
else
{
lean_object* v_v_2348_; lean_object* v___x_2349_; lean_object* v_xs_x27_2350_; lean_object* v___y_2352_; uint8_t v___x_2357_; 
v_v_2348_ = lean_array_fget(v_tail_2329_, v___x_2342_);
v___x_2349_ = lean_box(0);
v_xs_x27_2350_ = lean_array_fset(v_tail_2329_, v___x_2342_, v___x_2349_);
v___x_2357_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_y_2325_, v_v_2348_);
if (v___x_2357_ == 0)
{
lean_object* v___x_2358_; 
v___x_2358_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_y_2325_, v___x_2349_, v_v_2348_);
v___y_2352_ = v___x_2358_;
goto v___jp_2351_;
}
else
{
lean_dec(v_y_2325_);
v___y_2352_ = v_v_2348_;
goto v___jp_2351_;
}
v___jp_2351_:
{
lean_object* v___x_2353_; lean_object* v___x_2355_; 
v___x_2353_ = lean_array_fset(v_xs_x27_2350_, v___x_2342_, v___y_2352_);
lean_dec(v___x_2342_);
if (v_isShared_2335_ == 0)
{
lean_ctor_set(v___x_2334_, 1, v___x_2353_);
v___x_2355_ = v___x_2334_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_root_2328_);
lean_ctor_set(v_reuseFailAlloc_2356_, 1, v___x_2353_);
lean_ctor_set(v_reuseFailAlloc_2356_, 2, v_size_2330_);
lean_ctor_set(v_reuseFailAlloc_2356_, 3, v_tailOff_2332_);
lean_ctor_set_usize(v_reuseFailAlloc_2356_, 4, v_shift_2331_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2___boxed(lean_object* v_y_2360_, lean_object* v_t_2361_, lean_object* v_i_2362_){
_start:
{
lean_object* v_res_2363_; 
v_res_2363_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2(v_y_2360_, v_t_2361_, v_i_2362_);
lean_dec(v_i_2362_);
return v_res_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0(lean_object* v_a_2364_, lean_object* v_y_2365_, lean_object* v_x_2366_, lean_object* v_s_2367_){
_start:
{
lean_object* v_structs_2368_; lean_object* v_typeIdOf_2369_; lean_object* v_exprToStructId_2370_; lean_object* v_exprToStructIdEntries_2371_; lean_object* v_forbiddenNatModules_2372_; lean_object* v_natStructs_2373_; lean_object* v_natTypeIdOf_2374_; lean_object* v_exprToNatStructId_2375_; lean_object* v___x_2376_; uint8_t v___x_2377_; 
v_structs_2368_ = lean_ctor_get(v_s_2367_, 0);
v_typeIdOf_2369_ = lean_ctor_get(v_s_2367_, 1);
v_exprToStructId_2370_ = lean_ctor_get(v_s_2367_, 2);
v_exprToStructIdEntries_2371_ = lean_ctor_get(v_s_2367_, 3);
v_forbiddenNatModules_2372_ = lean_ctor_get(v_s_2367_, 4);
v_natStructs_2373_ = lean_ctor_get(v_s_2367_, 5);
v_natTypeIdOf_2374_ = lean_ctor_get(v_s_2367_, 6);
v_exprToNatStructId_2375_ = lean_ctor_get(v_s_2367_, 7);
v___x_2376_ = lean_array_get_size(v_structs_2368_);
v___x_2377_ = lean_nat_dec_lt(v_a_2364_, v___x_2376_);
if (v___x_2377_ == 0)
{
lean_dec(v_y_2365_);
return v_s_2367_;
}
else
{
lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2439_; 
lean_inc_ref(v_exprToNatStructId_2375_);
lean_inc_ref(v_natTypeIdOf_2374_);
lean_inc_ref(v_natStructs_2373_);
lean_inc_ref(v_forbiddenNatModules_2372_);
lean_inc_ref(v_exprToStructIdEntries_2371_);
lean_inc_ref(v_exprToStructId_2370_);
lean_inc_ref(v_typeIdOf_2369_);
lean_inc_ref(v_structs_2368_);
v_isSharedCheck_2439_ = !lean_is_exclusive(v_s_2367_);
if (v_isSharedCheck_2439_ == 0)
{
lean_object* v_unused_2440_; lean_object* v_unused_2441_; lean_object* v_unused_2442_; lean_object* v_unused_2443_; lean_object* v_unused_2444_; lean_object* v_unused_2445_; lean_object* v_unused_2446_; lean_object* v_unused_2447_; 
v_unused_2440_ = lean_ctor_get(v_s_2367_, 7);
lean_dec(v_unused_2440_);
v_unused_2441_ = lean_ctor_get(v_s_2367_, 6);
lean_dec(v_unused_2441_);
v_unused_2442_ = lean_ctor_get(v_s_2367_, 5);
lean_dec(v_unused_2442_);
v_unused_2443_ = lean_ctor_get(v_s_2367_, 4);
lean_dec(v_unused_2443_);
v_unused_2444_ = lean_ctor_get(v_s_2367_, 3);
lean_dec(v_unused_2444_);
v_unused_2445_ = lean_ctor_get(v_s_2367_, 2);
lean_dec(v_unused_2445_);
v_unused_2446_ = lean_ctor_get(v_s_2367_, 1);
lean_dec(v_unused_2446_);
v_unused_2447_ = lean_ctor_get(v_s_2367_, 0);
lean_dec(v_unused_2447_);
v___x_2379_ = v_s_2367_;
v_isShared_2380_ = v_isSharedCheck_2439_;
goto v_resetjp_2378_;
}
else
{
lean_dec(v_s_2367_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2439_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v_v_2381_; lean_object* v_id_2382_; lean_object* v_ringId_x3f_2383_; lean_object* v_type_2384_; lean_object* v_u_2385_; lean_object* v_intModuleInst_2386_; lean_object* v_leInst_x3f_2387_; lean_object* v_ltInst_x3f_2388_; lean_object* v_lawfulOrderLTInst_x3f_2389_; lean_object* v_isPreorderInst_x3f_2390_; lean_object* v_orderedAddInst_x3f_2391_; lean_object* v_isLinearInst_x3f_2392_; lean_object* v_noNatDivInst_x3f_2393_; lean_object* v_ringInst_x3f_2394_; lean_object* v_commRingInst_x3f_2395_; lean_object* v_orderedRingInst_x3f_2396_; lean_object* v_fieldInst_x3f_2397_; lean_object* v_charInst_x3f_2398_; lean_object* v_zero_2399_; lean_object* v_ofNatZero_2400_; lean_object* v_one_x3f_2401_; lean_object* v_leFn_x3f_2402_; lean_object* v_ltFn_x3f_2403_; lean_object* v_addFn_2404_; lean_object* v_zsmulFn_2405_; lean_object* v_nsmulFn_2406_; lean_object* v_zsmulFn_x3f_2407_; lean_object* v_nsmulFn_x3f_2408_; lean_object* v_homomulFn_x3f_2409_; lean_object* v_subFn_2410_; lean_object* v_negFn_2411_; lean_object* v_vars_2412_; lean_object* v_varMap_2413_; lean_object* v_lowers_2414_; lean_object* v_uppers_2415_; lean_object* v_diseqs_2416_; lean_object* v_assignment_2417_; uint8_t v_caseSplits_2418_; lean_object* v_conflict_x3f_2419_; lean_object* v_diseqSplits_2420_; lean_object* v_elimEqs_2421_; lean_object* v_elimStack_2422_; lean_object* v_occurs_2423_; lean_object* v_ignored_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2438_; 
v_v_2381_ = lean_array_fget(v_structs_2368_, v_a_2364_);
v_id_2382_ = lean_ctor_get(v_v_2381_, 0);
v_ringId_x3f_2383_ = lean_ctor_get(v_v_2381_, 1);
v_type_2384_ = lean_ctor_get(v_v_2381_, 2);
v_u_2385_ = lean_ctor_get(v_v_2381_, 3);
v_intModuleInst_2386_ = lean_ctor_get(v_v_2381_, 4);
v_leInst_x3f_2387_ = lean_ctor_get(v_v_2381_, 5);
v_ltInst_x3f_2388_ = lean_ctor_get(v_v_2381_, 6);
v_lawfulOrderLTInst_x3f_2389_ = lean_ctor_get(v_v_2381_, 7);
v_isPreorderInst_x3f_2390_ = lean_ctor_get(v_v_2381_, 8);
v_orderedAddInst_x3f_2391_ = lean_ctor_get(v_v_2381_, 9);
v_isLinearInst_x3f_2392_ = lean_ctor_get(v_v_2381_, 10);
v_noNatDivInst_x3f_2393_ = lean_ctor_get(v_v_2381_, 11);
v_ringInst_x3f_2394_ = lean_ctor_get(v_v_2381_, 12);
v_commRingInst_x3f_2395_ = lean_ctor_get(v_v_2381_, 13);
v_orderedRingInst_x3f_2396_ = lean_ctor_get(v_v_2381_, 14);
v_fieldInst_x3f_2397_ = lean_ctor_get(v_v_2381_, 15);
v_charInst_x3f_2398_ = lean_ctor_get(v_v_2381_, 16);
v_zero_2399_ = lean_ctor_get(v_v_2381_, 17);
v_ofNatZero_2400_ = lean_ctor_get(v_v_2381_, 18);
v_one_x3f_2401_ = lean_ctor_get(v_v_2381_, 19);
v_leFn_x3f_2402_ = lean_ctor_get(v_v_2381_, 20);
v_ltFn_x3f_2403_ = lean_ctor_get(v_v_2381_, 21);
v_addFn_2404_ = lean_ctor_get(v_v_2381_, 22);
v_zsmulFn_2405_ = lean_ctor_get(v_v_2381_, 23);
v_nsmulFn_2406_ = lean_ctor_get(v_v_2381_, 24);
v_zsmulFn_x3f_2407_ = lean_ctor_get(v_v_2381_, 25);
v_nsmulFn_x3f_2408_ = lean_ctor_get(v_v_2381_, 26);
v_homomulFn_x3f_2409_ = lean_ctor_get(v_v_2381_, 27);
v_subFn_2410_ = lean_ctor_get(v_v_2381_, 28);
v_negFn_2411_ = lean_ctor_get(v_v_2381_, 29);
v_vars_2412_ = lean_ctor_get(v_v_2381_, 30);
v_varMap_2413_ = lean_ctor_get(v_v_2381_, 31);
v_lowers_2414_ = lean_ctor_get(v_v_2381_, 32);
v_uppers_2415_ = lean_ctor_get(v_v_2381_, 33);
v_diseqs_2416_ = lean_ctor_get(v_v_2381_, 34);
v_assignment_2417_ = lean_ctor_get(v_v_2381_, 35);
v_caseSplits_2418_ = lean_ctor_get_uint8(v_v_2381_, sizeof(void*)*42);
v_conflict_x3f_2419_ = lean_ctor_get(v_v_2381_, 36);
v_diseqSplits_2420_ = lean_ctor_get(v_v_2381_, 37);
v_elimEqs_2421_ = lean_ctor_get(v_v_2381_, 38);
v_elimStack_2422_ = lean_ctor_get(v_v_2381_, 39);
v_occurs_2423_ = lean_ctor_get(v_v_2381_, 40);
v_ignored_2424_ = lean_ctor_get(v_v_2381_, 41);
v_isSharedCheck_2438_ = !lean_is_exclusive(v_v_2381_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2426_ = v_v_2381_;
v_isShared_2427_ = v_isSharedCheck_2438_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_ignored_2424_);
lean_inc(v_occurs_2423_);
lean_inc(v_elimStack_2422_);
lean_inc(v_elimEqs_2421_);
lean_inc(v_diseqSplits_2420_);
lean_inc(v_conflict_x3f_2419_);
lean_inc(v_assignment_2417_);
lean_inc(v_diseqs_2416_);
lean_inc(v_uppers_2415_);
lean_inc(v_lowers_2414_);
lean_inc(v_varMap_2413_);
lean_inc(v_vars_2412_);
lean_inc(v_negFn_2411_);
lean_inc(v_subFn_2410_);
lean_inc(v_homomulFn_x3f_2409_);
lean_inc(v_nsmulFn_x3f_2408_);
lean_inc(v_zsmulFn_x3f_2407_);
lean_inc(v_nsmulFn_2406_);
lean_inc(v_zsmulFn_2405_);
lean_inc(v_addFn_2404_);
lean_inc(v_ltFn_x3f_2403_);
lean_inc(v_leFn_x3f_2402_);
lean_inc(v_one_x3f_2401_);
lean_inc(v_ofNatZero_2400_);
lean_inc(v_zero_2399_);
lean_inc(v_charInst_x3f_2398_);
lean_inc(v_fieldInst_x3f_2397_);
lean_inc(v_orderedRingInst_x3f_2396_);
lean_inc(v_commRingInst_x3f_2395_);
lean_inc(v_ringInst_x3f_2394_);
lean_inc(v_noNatDivInst_x3f_2393_);
lean_inc(v_isLinearInst_x3f_2392_);
lean_inc(v_orderedAddInst_x3f_2391_);
lean_inc(v_isPreorderInst_x3f_2390_);
lean_inc(v_lawfulOrderLTInst_x3f_2389_);
lean_inc(v_ltInst_x3f_2388_);
lean_inc(v_leInst_x3f_2387_);
lean_inc(v_intModuleInst_2386_);
lean_inc(v_u_2385_);
lean_inc(v_type_2384_);
lean_inc(v_ringId_x3f_2383_);
lean_inc(v_id_2382_);
lean_dec(v_v_2381_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2438_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2428_; lean_object* v_xs_x27_2429_; lean_object* v___x_2430_; lean_object* v___x_2432_; 
v___x_2428_ = lean_box(0);
v_xs_x27_2429_ = lean_array_fset(v_structs_2368_, v_a_2364_, v___x_2428_);
v___x_2430_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2(v_y_2365_, v_occurs_2423_, v_x_2366_);
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 40, v___x_2430_);
v___x_2432_ = v___x_2426_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_id_2382_);
lean_ctor_set(v_reuseFailAlloc_2437_, 1, v_ringId_x3f_2383_);
lean_ctor_set(v_reuseFailAlloc_2437_, 2, v_type_2384_);
lean_ctor_set(v_reuseFailAlloc_2437_, 3, v_u_2385_);
lean_ctor_set(v_reuseFailAlloc_2437_, 4, v_intModuleInst_2386_);
lean_ctor_set(v_reuseFailAlloc_2437_, 5, v_leInst_x3f_2387_);
lean_ctor_set(v_reuseFailAlloc_2437_, 6, v_ltInst_x3f_2388_);
lean_ctor_set(v_reuseFailAlloc_2437_, 7, v_lawfulOrderLTInst_x3f_2389_);
lean_ctor_set(v_reuseFailAlloc_2437_, 8, v_isPreorderInst_x3f_2390_);
lean_ctor_set(v_reuseFailAlloc_2437_, 9, v_orderedAddInst_x3f_2391_);
lean_ctor_set(v_reuseFailAlloc_2437_, 10, v_isLinearInst_x3f_2392_);
lean_ctor_set(v_reuseFailAlloc_2437_, 11, v_noNatDivInst_x3f_2393_);
lean_ctor_set(v_reuseFailAlloc_2437_, 12, v_ringInst_x3f_2394_);
lean_ctor_set(v_reuseFailAlloc_2437_, 13, v_commRingInst_x3f_2395_);
lean_ctor_set(v_reuseFailAlloc_2437_, 14, v_orderedRingInst_x3f_2396_);
lean_ctor_set(v_reuseFailAlloc_2437_, 15, v_fieldInst_x3f_2397_);
lean_ctor_set(v_reuseFailAlloc_2437_, 16, v_charInst_x3f_2398_);
lean_ctor_set(v_reuseFailAlloc_2437_, 17, v_zero_2399_);
lean_ctor_set(v_reuseFailAlloc_2437_, 18, v_ofNatZero_2400_);
lean_ctor_set(v_reuseFailAlloc_2437_, 19, v_one_x3f_2401_);
lean_ctor_set(v_reuseFailAlloc_2437_, 20, v_leFn_x3f_2402_);
lean_ctor_set(v_reuseFailAlloc_2437_, 21, v_ltFn_x3f_2403_);
lean_ctor_set(v_reuseFailAlloc_2437_, 22, v_addFn_2404_);
lean_ctor_set(v_reuseFailAlloc_2437_, 23, v_zsmulFn_2405_);
lean_ctor_set(v_reuseFailAlloc_2437_, 24, v_nsmulFn_2406_);
lean_ctor_set(v_reuseFailAlloc_2437_, 25, v_zsmulFn_x3f_2407_);
lean_ctor_set(v_reuseFailAlloc_2437_, 26, v_nsmulFn_x3f_2408_);
lean_ctor_set(v_reuseFailAlloc_2437_, 27, v_homomulFn_x3f_2409_);
lean_ctor_set(v_reuseFailAlloc_2437_, 28, v_subFn_2410_);
lean_ctor_set(v_reuseFailAlloc_2437_, 29, v_negFn_2411_);
lean_ctor_set(v_reuseFailAlloc_2437_, 30, v_vars_2412_);
lean_ctor_set(v_reuseFailAlloc_2437_, 31, v_varMap_2413_);
lean_ctor_set(v_reuseFailAlloc_2437_, 32, v_lowers_2414_);
lean_ctor_set(v_reuseFailAlloc_2437_, 33, v_uppers_2415_);
lean_ctor_set(v_reuseFailAlloc_2437_, 34, v_diseqs_2416_);
lean_ctor_set(v_reuseFailAlloc_2437_, 35, v_assignment_2417_);
lean_ctor_set(v_reuseFailAlloc_2437_, 36, v_conflict_x3f_2419_);
lean_ctor_set(v_reuseFailAlloc_2437_, 37, v_diseqSplits_2420_);
lean_ctor_set(v_reuseFailAlloc_2437_, 38, v_elimEqs_2421_);
lean_ctor_set(v_reuseFailAlloc_2437_, 39, v_elimStack_2422_);
lean_ctor_set(v_reuseFailAlloc_2437_, 40, v___x_2430_);
lean_ctor_set(v_reuseFailAlloc_2437_, 41, v_ignored_2424_);
lean_ctor_set_uint8(v_reuseFailAlloc_2437_, sizeof(void*)*42, v_caseSplits_2418_);
v___x_2432_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
lean_object* v___x_2433_; lean_object* v___x_2435_; 
v___x_2433_ = lean_array_fset(v_xs_x27_2429_, v_a_2364_, v___x_2432_);
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 0, v___x_2433_);
v___x_2435_ = v___x_2379_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v___x_2433_);
lean_ctor_set(v_reuseFailAlloc_2436_, 1, v_typeIdOf_2369_);
lean_ctor_set(v_reuseFailAlloc_2436_, 2, v_exprToStructId_2370_);
lean_ctor_set(v_reuseFailAlloc_2436_, 3, v_exprToStructIdEntries_2371_);
lean_ctor_set(v_reuseFailAlloc_2436_, 4, v_forbiddenNatModules_2372_);
lean_ctor_set(v_reuseFailAlloc_2436_, 5, v_natStructs_2373_);
lean_ctor_set(v_reuseFailAlloc_2436_, 6, v_natTypeIdOf_2374_);
lean_ctor_set(v_reuseFailAlloc_2436_, 7, v_exprToNatStructId_2375_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0___boxed(lean_object* v_a_2448_, lean_object* v_y_2449_, lean_object* v_x_2450_, lean_object* v_s_2451_){
_start:
{
lean_object* v_res_2452_; 
v_res_2452_ = l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0(v_a_2448_, v_y_2449_, v_x_2450_, v_s_2451_);
lean_dec(v_x_2450_);
lean_dec(v_a_2448_);
return v_res_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc(lean_object* v_x_2453_, lean_object* v_y_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_){
_start:
{
lean_object* v___x_2467_; 
v___x_2467_ = l_Lean_Meta_Grind_Arith_Linear_getOccursOf(v_x_2453_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_);
if (lean_obj_tag(v___x_2467_) == 0)
{
lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2480_; 
v_a_2468_ = lean_ctor_get(v___x_2467_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2470_ = v___x_2467_;
v_isShared_2471_ = v_isSharedCheck_2480_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___x_2467_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2480_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
uint8_t v___x_2472_; 
v___x_2472_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_y_2454_, v_a_2468_);
lean_dec(v_a_2468_);
if (v___x_2472_ == 0)
{
lean_object* v___f_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
lean_del_object(v___x_2470_);
lean_inc(v_a_2455_);
v___f_2473_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2473_, 0, v_a_2455_);
lean_closure_set(v___f_2473_, 1, v_y_2454_);
lean_closure_set(v___f_2473_, 2, v_x_2453_);
v___x_2474_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2475_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2474_, v___f_2473_, v_a_2456_);
return v___x_2475_;
}
else
{
lean_object* v___x_2476_; lean_object* v___x_2478_; 
lean_dec(v_y_2454_);
lean_dec(v_x_2453_);
v___x_2476_ = lean_box(0);
if (v_isShared_2471_ == 0)
{
lean_ctor_set(v___x_2470_, 0, v___x_2476_);
v___x_2478_ = v___x_2470_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v___x_2476_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
}
else
{
lean_object* v_a_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2488_; 
lean_dec(v_y_2454_);
lean_dec(v_x_2453_);
v_a_2481_ = lean_ctor_get(v___x_2467_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2483_ = v___x_2467_;
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_a_2481_);
lean_dec(v___x_2467_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2486_; 
if (v_isShared_2484_ == 0)
{
v___x_2486_ = v___x_2483_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_a_2481_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
return v___x_2486_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc___boxed(lean_object* v_x_2489_, lean_object* v_y_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l_Lean_Meta_Grind_Arith_Linear_addOcc(v_x_2489_, v_y_2490_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_);
lean_dec(v_a_2501_);
lean_dec_ref(v_a_2500_);
lean_dec(v_a_2499_);
lean_dec_ref(v_a_2498_);
lean_dec(v_a_2497_);
lean_dec_ref(v_a_2496_);
lean_dec(v_a_2495_);
lean_dec_ref(v_a_2494_);
lean_dec(v_a_2493_);
lean_dec(v_a_2492_);
lean_dec(v_a_2491_);
return v_res_2503_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0(lean_object* v_00_u03b2_2504_, lean_object* v_k_2505_, lean_object* v_t_2506_){
_start:
{
uint8_t v___x_2507_; 
v___x_2507_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_k_2505_, v_t_2506_);
return v___x_2507_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___boxed(lean_object* v_00_u03b2_2508_, lean_object* v_k_2509_, lean_object* v_t_2510_){
_start:
{
uint8_t v_res_2511_; lean_object* v_r_2512_; 
v_res_2511_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0(v_00_u03b2_2508_, v_k_2509_, v_t_2510_);
lean_dec(v_t_2510_);
lean_dec(v_k_2509_);
v_r_2512_ = lean_box(v_res_2511_);
return v_r_2512_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1(lean_object* v_00_u03b2_2513_, lean_object* v_k_2514_, lean_object* v_v_2515_, lean_object* v_t_2516_, lean_object* v_hl_2517_){
_start:
{
lean_object* v___x_2518_; 
v___x_2518_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_k_2514_, v_v_2515_, v_t_2516_);
return v___x_2518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go(lean_object* v_y_2519_, lean_object* v_p_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_){
_start:
{
if (lean_obj_tag(v_p_2520_) == 1)
{
lean_object* v_v_2533_; lean_object* v_p_2534_; lean_object* v___x_2535_; 
v_v_2533_ = lean_ctor_get(v_p_2520_, 1);
lean_inc(v_v_2533_);
v_p_2534_ = lean_ctor_get(v_p_2520_, 2);
lean_inc(v_p_2534_);
lean_dec_ref(v_p_2520_);
lean_inc(v_y_2519_);
v___x_2535_ = l_Lean_Meta_Grind_Arith_Linear_addOcc(v_v_2533_, v_y_2519_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_);
if (lean_obj_tag(v___x_2535_) == 0)
{
lean_dec_ref(v___x_2535_);
v_p_2520_ = v_p_2534_;
goto _start;
}
else
{
lean_dec(v_p_2534_);
lean_dec(v_y_2519_);
return v___x_2535_;
}
}
else
{
lean_object* v___x_2537_; lean_object* v___x_2538_; 
lean_dec(v_p_2520_);
lean_dec(v_y_2519_);
v___x_2537_ = lean_box(0);
v___x_2538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2538_, 0, v___x_2537_);
return v___x_2538_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go___boxed(lean_object* v_y_2539_, lean_object* v_p_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go(v_y_2539_, v_p_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_);
lean_dec(v_a_2551_);
lean_dec_ref(v_a_2550_);
lean_dec(v_a_2549_);
lean_dec_ref(v_a_2548_);
lean_dec(v_a_2547_);
lean_dec_ref(v_a_2546_);
lean_dec(v_a_2545_);
lean_dec_ref(v_a_2544_);
lean_dec(v_a_2543_);
lean_dec(v_a_2542_);
lean_dec(v_a_2541_);
return v_res_2553_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_Poly_updateOccs___closed__1(void){
_start:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2555_ = ((lean_object*)(l_Lean_Grind_Linarith_Poly_updateOccs___closed__0));
v___x_2556_ = l_Lean_stringToMessageData(v___x_2555_);
return v___x_2556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_updateOccs(lean_object* v_p_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_){
_start:
{
if (lean_obj_tag(v_p_2557_) == 1)
{
lean_object* v_v_2570_; lean_object* v_p_2571_; lean_object* v___x_2572_; 
v_v_2570_ = lean_ctor_get(v_p_2557_, 1);
lean_inc(v_v_2570_);
v_p_2571_ = lean_ctor_get(v_p_2557_, 2);
lean_inc(v_p_2571_);
lean_dec_ref(v_p_2557_);
v___x_2572_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go(v_v_2570_, v_p_2571_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_);
return v___x_2572_;
}
else
{
lean_object* v___x_2573_; lean_object* v___x_2574_; 
lean_dec(v_p_2557_);
v___x_2573_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_updateOccs___closed__1, &l_Lean_Grind_Linarith_Poly_updateOccs___closed__1_once, _init_l_Lean_Grind_Linarith_Poly_updateOccs___closed__1);
v___x_2574_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_2573_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_);
return v___x_2574_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_updateOccs___boxed(lean_object* v_p_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_){
_start:
{
lean_object* v_res_2588_; 
v_res_2588_ = l_Lean_Grind_Linarith_Poly_updateOccs(v_p_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_);
lean_dec(v_a_2586_);
lean_dec_ref(v_a_2585_);
lean_dec(v_a_2584_);
lean_dec_ref(v_a_2583_);
lean_dec(v_a_2582_);
lean_dec_ref(v_a_2581_);
lean_dec(v_a_2580_);
lean_dec_ref(v_a_2579_);
lean_dec(v_a_2578_);
lean_dec(v_a_2577_);
lean_dec(v_a_2576_);
return v_res_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_findVarToSubst(lean_object* v_p_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_){
_start:
{
if (lean_obj_tag(v_p_2589_) == 0)
{
lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2602_ = lean_box(0);
v___x_2603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2603_, 0, v___x_2602_);
return v___x_2603_;
}
else
{
lean_object* v_k_2604_; lean_object* v_v_2605_; lean_object* v_p_2606_; lean_object* v___x_2607_; 
v_k_2604_ = lean_ctor_get(v_p_2589_, 0);
v_v_2605_ = lean_ctor_get(v_p_2589_, 1);
v_p_2606_ = lean_ctor_get(v_p_2589_, 2);
v___x_2607_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_);
if (lean_obj_tag(v___x_2607_) == 0)
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2634_; 
v_a_2608_ = lean_ctor_get(v___x_2607_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2610_ = v___x_2607_;
v_isShared_2611_ = v_isSharedCheck_2634_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___x_2607_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2634_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___y_2613_; lean_object* v_elimEqs_2628_; lean_object* v_size_2629_; lean_object* v___x_2630_; uint8_t v___x_2631_; 
v_elimEqs_2628_ = lean_ctor_get(v_a_2608_, 38);
lean_inc_ref(v_elimEqs_2628_);
lean_dec(v_a_2608_);
v_size_2629_ = lean_ctor_get(v_elimEqs_2628_, 2);
v___x_2630_ = lean_box(0);
v___x_2631_ = lean_nat_dec_lt(v_v_2605_, v_size_2629_);
if (v___x_2631_ == 0)
{
lean_object* v___x_2632_; 
lean_dec_ref(v_elimEqs_2628_);
v___x_2632_ = l_outOfBounds___redArg(v___x_2630_);
v___y_2613_ = v___x_2632_;
goto v___jp_2612_;
}
else
{
lean_object* v___x_2633_; 
v___x_2633_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2630_, v_elimEqs_2628_, v_v_2605_);
lean_dec_ref(v_elimEqs_2628_);
v___y_2613_ = v___x_2633_;
goto v___jp_2612_;
}
v___jp_2612_:
{
if (lean_obj_tag(v___y_2613_) == 1)
{
lean_object* v_val_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2626_; 
v_val_2614_ = lean_ctor_get(v___y_2613_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___y_2613_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2616_ = v___y_2613_;
v_isShared_2617_ = v_isSharedCheck_2626_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_val_2614_);
lean_dec(v___y_2613_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2626_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2621_; 
lean_inc(v_v_2605_);
v___x_2618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2618_, 0, v_v_2605_);
lean_ctor_set(v___x_2618_, 1, v_val_2614_);
lean_inc(v_k_2604_);
v___x_2619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2619_, 0, v_k_2604_);
lean_ctor_set(v___x_2619_, 1, v___x_2618_);
if (v_isShared_2617_ == 0)
{
lean_ctor_set(v___x_2616_, 0, v___x_2619_);
v___x_2621_ = v___x_2616_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v___x_2619_);
v___x_2621_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
lean_object* v___x_2623_; 
if (v_isShared_2611_ == 0)
{
lean_ctor_set(v___x_2610_, 0, v___x_2621_);
v___x_2623_ = v___x_2610_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v___x_2621_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
}
}
else
{
lean_dec(v___y_2613_);
lean_del_object(v___x_2610_);
v_p_2589_ = v_p_2606_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2642_; 
v_a_2635_ = lean_ctor_get(v___x_2607_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2637_ = v___x_2607_;
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_a_2635_);
lean_dec(v___x_2607_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2640_; 
if (v_isShared_2638_ == 0)
{
v___x_2640_ = v___x_2637_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_a_2635_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_findVarToSubst___boxed(lean_object* v_p_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l_Lean_Grind_Linarith_Poly_findVarToSubst(v_p_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_);
lean_dec(v_a_2654_);
lean_dec_ref(v_a_2653_);
lean_dec(v_a_2652_);
lean_dec_ref(v_a_2651_);
lean_dec(v_a_2650_);
lean_dec_ref(v_a_2649_);
lean_dec(v_a_2648_);
lean_dec_ref(v_a_2647_);
lean_dec(v_a_2646_);
lean_dec(v_a_2645_);
lean_dec(v_a_2644_);
lean_dec(v_p_2643_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffsAux(lean_object* v_x_2657_, lean_object* v_x_2658_){
_start:
{
if (lean_obj_tag(v_x_2657_) == 0)
{
return v_x_2658_;
}
else
{
lean_object* v_k_2659_; lean_object* v_p_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; 
v_k_2659_ = lean_ctor_get(v_x_2657_, 0);
v_p_2660_ = lean_ctor_get(v_x_2657_, 2);
v___x_2661_ = lean_nat_to_int(v_x_2658_);
v___x_2662_ = l_Int_gcd(v_k_2659_, v___x_2661_);
lean_dec(v___x_2661_);
v_x_2657_ = v_p_2660_;
v_x_2658_ = v___x_2662_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffsAux___boxed(lean_object* v_x_2664_, lean_object* v_x_2665_){
_start:
{
lean_object* v_res_2666_; 
v_res_2666_ = l_Lean_Grind_Linarith_Poly_gcdCoeffsAux(v_x_2664_, v_x_2665_);
lean_dec(v_x_2664_);
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffs(lean_object* v_p_2667_){
_start:
{
if (lean_obj_tag(v_p_2667_) == 0)
{
lean_object* v___x_2668_; 
v___x_2668_ = lean_unsigned_to_nat(1u);
return v___x_2668_;
}
else
{
lean_object* v_k_2669_; lean_object* v_p_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
v_k_2669_ = lean_ctor_get(v_p_2667_, 0);
v_p_2670_ = lean_ctor_get(v_p_2667_, 2);
v___x_2671_ = lean_nat_abs(v_k_2669_);
v___x_2672_ = l_Lean_Grind_Linarith_Poly_gcdCoeffsAux(v_p_2670_, v___x_2671_);
return v___x_2672_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffs___boxed(lean_object* v_p_2673_){
_start:
{
lean_object* v_res_2674_; 
v_res_2674_ = l_Lean_Grind_Linarith_Poly_gcdCoeffs(v_p_2673_);
lean_dec(v_p_2673_);
return v_res_2674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_div(lean_object* v_p_2675_, lean_object* v_k_2676_){
_start:
{
if (lean_obj_tag(v_p_2675_) == 0)
{
return v_p_2675_;
}
else
{
lean_object* v_k_2677_; lean_object* v_v_2678_; lean_object* v_p_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2688_; 
v_k_2677_ = lean_ctor_get(v_p_2675_, 0);
v_v_2678_ = lean_ctor_get(v_p_2675_, 1);
v_p_2679_ = lean_ctor_get(v_p_2675_, 2);
v_isSharedCheck_2688_ = !lean_is_exclusive(v_p_2675_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2681_ = v_p_2675_;
v_isShared_2682_ = v_isSharedCheck_2688_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_p_2679_);
lean_inc(v_v_2678_);
lean_inc(v_k_2677_);
lean_dec(v_p_2675_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2688_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2686_; 
v___x_2683_ = lean_int_ediv(v_k_2677_, v_k_2676_);
lean_dec(v_k_2677_);
v___x_2684_ = l_Lean_Grind_Linarith_Poly_div(v_p_2679_, v_k_2676_);
if (v_isShared_2682_ == 0)
{
lean_ctor_set(v___x_2681_, 2, v___x_2684_);
lean_ctor_set(v___x_2681_, 0, v___x_2683_);
v___x_2686_ = v___x_2681_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v___x_2683_);
lean_ctor_set(v_reuseFailAlloc_2687_, 1, v_v_2678_);
lean_ctor_set(v_reuseFailAlloc_2687_, 2, v___x_2684_);
v___x_2686_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
return v___x_2686_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_div___boxed(lean_object* v_p_2689_, lean_object* v_k_2690_){
_start:
{
lean_object* v_res_2691_; 
v_res_2691_ = l_Lean_Grind_Linarith_Poly_div(v_p_2689_, v_k_2690_);
lean_dec(v_k_2690_);
return v_res_2691_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0(void){
_start:
{
lean_object* v___x_2692_; lean_object* v___x_2693_; 
v___x_2692_ = lean_unsigned_to_nat(1u);
v___x_2693_ = lean_nat_to_int(v___x_2692_);
return v___x_2693_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__1(void){
_start:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___x_2694_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0);
v___x_2695_ = lean_int_neg(v___x_2694_);
return v___x_2695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go(lean_object* v_k_2696_, lean_object* v_x_2697_, lean_object* v_p_2698_){
_start:
{
uint8_t v___y_2700_; lean_object* v___x_2711_; uint8_t v___x_2712_; 
v___x_2711_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0);
v___x_2712_ = lean_int_dec_eq(v_k_2696_, v___x_2711_);
if (v___x_2712_ == 0)
{
lean_object* v___x_2713_; uint8_t v___x_2714_; 
v___x_2713_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__1);
v___x_2714_ = lean_int_dec_eq(v_k_2696_, v___x_2713_);
v___y_2700_ = v___x_2714_;
goto v___jp_2699_;
}
else
{
v___y_2700_ = v___x_2712_;
goto v___jp_2699_;
}
v___jp_2699_:
{
if (v___y_2700_ == 0)
{
if (lean_obj_tag(v_p_2698_) == 0)
{
lean_object* v___x_2701_; 
v___x_2701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2701_, 0, v_k_2696_);
lean_ctor_set(v___x_2701_, 1, v_x_2697_);
return v___x_2701_;
}
else
{
lean_object* v_k_2702_; lean_object* v_v_2703_; lean_object* v_p_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; uint8_t v___x_2707_; 
v_k_2702_ = lean_ctor_get(v_p_2698_, 0);
lean_inc(v_k_2702_);
v_v_2703_ = lean_ctor_get(v_p_2698_, 1);
lean_inc(v_v_2703_);
v_p_2704_ = lean_ctor_get(v_p_2698_, 2);
lean_inc(v_p_2704_);
lean_dec_ref(v_p_2698_);
v___x_2705_ = lean_nat_abs(v_k_2702_);
v___x_2706_ = lean_nat_abs(v_k_2696_);
v___x_2707_ = lean_nat_dec_lt(v___x_2705_, v___x_2706_);
lean_dec(v___x_2706_);
lean_dec(v___x_2705_);
if (v___x_2707_ == 0)
{
lean_dec(v_v_2703_);
lean_dec(v_k_2702_);
v_p_2698_ = v_p_2704_;
goto _start;
}
else
{
lean_dec(v_x_2697_);
lean_dec(v_k_2696_);
v_k_2696_ = v_k_2702_;
v_x_2697_ = v_v_2703_;
v_p_2698_ = v_p_2704_;
goto _start;
}
}
}
else
{
lean_object* v___x_2710_; 
lean_dec(v_p_2698_);
v___x_2710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2710_, 0, v_k_2696_);
lean_ctor_set(v___x_2710_, 1, v_x_2697_);
return v___x_2710_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_pickVarToElim_x3f(lean_object* v_p_2715_){
_start:
{
if (lean_obj_tag(v_p_2715_) == 0)
{
lean_object* v___x_2716_; 
v___x_2716_ = lean_box(0);
return v___x_2716_;
}
else
{
lean_object* v_k_2717_; lean_object* v_v_2718_; lean_object* v_p_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; 
v_k_2717_ = lean_ctor_get(v_p_2715_, 0);
lean_inc(v_k_2717_);
v_v_2718_ = lean_ctor_get(v_p_2715_, 1);
lean_inc(v_v_2718_);
v_p_2719_ = lean_ctor_get(v_p_2715_, 2);
lean_inc(v_p_2719_);
lean_dec_ref(v_p_2715_);
v___x_2720_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go(v_k_2717_, v_v_2718_, v_p_2719_);
v___x_2721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2721_, 0, v___x_2720_);
return v___x_2721_;
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
