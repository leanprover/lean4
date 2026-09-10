// Lean compiler output
// Module: Std.Sat.AIG.CNF
// Imports: public import Std.Sat.CNF public import Std.Sat.AIG.Lemmas import Init.ByCases import Init.Omega
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_byte_array_push(lean_object*, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_ByteArray_empty;
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Bool_toNat(uint8_t);
lean_object* lean_nat_lxor(lean_object*, lean_object*);
uint8_t l_Std_Sat_CNF_eval___redArg(lean_object*, lean_object*);
uint8_t l_Std_Sat_AIG_denote_go___redArg(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__0 = (const lean_object*)&l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__0_value;
static lean_once_cell_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF(lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF___redArg___closed__0;
static lean_once_cell_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF___redArg___closed__1;
static lean_once_cell_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_mixAssigns(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_mixAssigns___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectRightAssign(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectRightAssign___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___boxed(lean_object**);
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_match__4_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_match__4_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go_match__103_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go_match__103_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go_match__81_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go_match__81_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__52_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__52_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__52_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__50_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__50_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__50_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__48_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__48_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__48_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__45_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__45_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__45_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__56_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__56_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__56_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__54_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__54_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__54_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_Sat_AIG_toCNF___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Sat_AIG_toCNF___closed__0 = (const lean_object*)&l_Std_Sat_AIG_toCNF___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF(lean_object*);
static lean_object* _init_l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__1(void){
_start:
{
uint8_t v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_3_ = 0;
v___x_4_ = l_ByteArray_empty;
v___x_5_ = lean_byte_array_push(v___x_4_, v___x_3_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg(lean_object* v_output_6_){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_7_ = ((lean_object*)(l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__0));
v___x_8_ = lean_array_push(v___x_7_, v_output_6_);
v___x_9_ = lean_obj_once(&l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__1, &l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__1_once, _init_l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__1);
v___x_10_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_10_, 0, v___x_8_);
lean_ctor_set(v___x_10_, 1, v___x_9_);
v___x_11_ = lean_array_push(v___x_7_, v___x_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF(lean_object* v_00_u03b1_12_, lean_object* v_output_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg(v_output_13_);
return v___x_14_;
}
}
static lean_object* _init_l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF___redArg___closed__0(void){
_start:
{
uint8_t v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_15_ = 1;
v___x_16_ = l_ByteArray_empty;
v___x_17_ = lean_byte_array_push(v___x_16_, v___x_15_);
return v___x_17_;
}
}
static lean_object* _init_l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF___redArg___closed__1(void){
_start:
{
uint8_t v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_18_ = 0;
v___x_19_ = lean_obj_once(&l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF___redArg___closed__0, &l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF___redArg___closed__0_once, _init_l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF___redArg___closed__0);
v___x_20_ = lean_byte_array_push(v___x_19_, v___x_18_);
return v___x_20_;
}
}
static lean_object* _init_l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF___redArg___closed__2(void){
_start:
{
uint8_t v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_21_ = 1;
v___x_22_ = lean_obj_once(&l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__1, &l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__1_once, _init_l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__1);
v___x_23_ = lean_byte_array_push(v___x_22_, v___x_21_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF___redArg(lean_object* v_output_24_, lean_object* v_atom_25_){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_26_ = ((lean_object*)(l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__0));
v___x_27_ = lean_array_push(v___x_26_, v_output_24_);
v___x_28_ = lean_array_push(v___x_27_, v_atom_25_);
v___x_29_ = lean_obj_once(&l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF___redArg___closed__1, &l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF___redArg___closed__1_once, _init_l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF___redArg___closed__1);
lean_inc_ref(v___x_28_);
v___x_30_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_30_, 0, v___x_28_);
lean_ctor_set(v___x_30_, 1, v___x_29_);
v___x_31_ = lean_array_push(v___x_26_, v___x_30_);
v___x_32_ = lean_obj_once(&l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF___redArg___closed__2, &l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF___redArg___closed__2_once, _init_l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF___redArg___closed__2);
v___x_33_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_33_, 0, v___x_28_);
lean_ctor_set(v___x_33_, 1, v___x_32_);
v___x_34_ = lean_array_push(v___x_31_, v___x_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF(lean_object* v_00_u03b1_35_, lean_object* v_output_36_, lean_object* v_atom_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF___redArg(v_output_36_, v_atom_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg(lean_object* v_output_39_, lean_object* v_lhs_40_, lean_object* v_rhs_41_, uint8_t v_linv_42_, uint8_t v_rinv_43_){
_start:
{
lean_object* v___y_45_; lean_object* v___y_46_; lean_object* v___y_47_; uint8_t v___y_48_; lean_object* v___x_52_; lean_object* v___x_53_; uint8_t v___x_54_; lean_object* v___y_56_; lean_object* v___y_57_; uint8_t v___y_58_; lean_object* v___y_59_; uint8_t v___y_60_; lean_object* v___x_63_; lean_object* v___y_65_; lean_object* v___y_66_; lean_object* v___y_67_; uint8_t v___y_68_; lean_object* v___y_75_; uint8_t v___y_76_; 
v___x_52_ = ((lean_object*)(l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__0));
v___x_53_ = lean_array_push(v___x_52_, v_output_39_);
v___x_54_ = 0;
v___x_63_ = lean_obj_once(&l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__1, &l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__1_once, _init_l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__1);
if (v_linv_42_ == 0)
{
lean_object* v___x_83_; uint8_t v___x_84_; 
lean_inc_ref(v___x_53_);
v___x_83_ = lean_array_push(v___x_53_, v_lhs_40_);
v___x_84_ = 1;
v___y_75_ = v___x_83_;
v___y_76_ = v___x_84_;
goto v___jp_74_;
}
else
{
lean_object* v___x_85_; 
lean_inc_ref(v___x_53_);
v___x_85_ = lean_array_push(v___x_53_, v_lhs_40_);
v___y_75_ = v___x_85_;
v___y_76_ = v___x_54_;
goto v___jp_74_;
}
v___jp_44_:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = lean_byte_array_push(v___y_45_, v___y_48_);
v___x_50_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_50_, 0, v___y_47_);
lean_ctor_set(v___x_50_, 1, v___x_49_);
v___x_51_ = lean_array_push(v___y_46_, v___x_50_);
return v___x_51_;
}
v___jp_55_:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
lean_inc_ref(v___y_56_);
v___x_61_ = lean_byte_array_push(v___y_56_, v___y_60_);
v___x_62_ = lean_array_push(v___y_59_, v_rhs_41_);
if (v_rinv_43_ == 0)
{
v___y_45_ = v___x_61_;
v___y_46_ = v___y_57_;
v___y_47_ = v___x_62_;
v___y_48_ = v___x_54_;
goto v___jp_44_;
}
else
{
v___y_45_ = v___x_61_;
v___y_46_ = v___y_57_;
v___y_47_ = v___x_62_;
v___y_48_ = v___y_58_;
goto v___jp_44_;
}
}
v___jp_64_:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; uint8_t v___x_72_; lean_object* v___x_73_; 
v___x_69_ = lean_byte_array_push(v___x_63_, v___y_68_);
v___x_70_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_70_, 0, v___y_65_);
lean_ctor_set(v___x_70_, 1, v___x_69_);
v___x_71_ = lean_array_push(v___y_67_, v___x_70_);
v___x_72_ = 1;
v___x_73_ = lean_obj_once(&l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF___redArg___closed__0, &l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF___redArg___closed__0_once, _init_l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF___redArg___closed__0);
if (v_linv_42_ == 0)
{
v___y_56_ = v___x_73_;
v___y_57_ = v___x_71_;
v___y_58_ = v___x_72_;
v___y_59_ = v___y_66_;
v___y_60_ = v___x_54_;
goto v___jp_55_;
}
else
{
v___y_56_ = v___x_73_;
v___y_57_ = v___x_71_;
v___y_58_ = v___x_72_;
v___y_59_ = v___y_66_;
v___y_60_ = v___x_72_;
goto v___jp_55_;
}
}
v___jp_74_:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_77_ = lean_byte_array_push(v___x_63_, v___y_76_);
lean_inc_ref(v___y_75_);
v___x_78_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_78_, 0, v___y_75_);
lean_ctor_set(v___x_78_, 1, v___x_77_);
v___x_79_ = lean_array_push(v___x_52_, v___x_78_);
if (v_rinv_43_ == 0)
{
lean_object* v___x_80_; uint8_t v___x_81_; 
lean_inc(v_rhs_41_);
v___x_80_ = lean_array_push(v___x_53_, v_rhs_41_);
v___x_81_ = 1;
v___y_65_ = v___x_80_;
v___y_66_ = v___y_75_;
v___y_67_ = v___x_79_;
v___y_68_ = v___x_81_;
goto v___jp_64_;
}
else
{
lean_object* v___x_82_; 
lean_inc(v_rhs_41_);
v___x_82_ = lean_array_push(v___x_53_, v_rhs_41_);
v___y_65_ = v___x_82_;
v___y_66_ = v___y_75_;
v___y_67_ = v___x_79_;
v___y_68_ = v___x_54_;
goto v___jp_64_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg___boxed(lean_object* v_output_86_, lean_object* v_lhs_87_, lean_object* v_rhs_88_, lean_object* v_linv_89_, lean_object* v_rinv_90_){
_start:
{
uint8_t v_linv_boxed_91_; uint8_t v_rinv_boxed_92_; lean_object* v_res_93_; 
v_linv_boxed_91_ = lean_unbox(v_linv_89_);
v_rinv_boxed_92_ = lean_unbox(v_rinv_90_);
v_res_93_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg(v_output_86_, v_lhs_87_, v_rhs_88_, v_linv_boxed_91_, v_rinv_boxed_92_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF(lean_object* v_00_u03b1_94_, lean_object* v_output_95_, lean_object* v_lhs_96_, lean_object* v_rhs_97_, uint8_t v_linv_98_, uint8_t v_rinv_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg(v_output_95_, v_lhs_96_, v_rhs_97_, v_linv_98_, v_rinv_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___boxed(lean_object* v_00_u03b1_101_, lean_object* v_output_102_, lean_object* v_lhs_103_, lean_object* v_rhs_104_, lean_object* v_linv_105_, lean_object* v_rinv_106_){
_start:
{
uint8_t v_linv_boxed_107_; uint8_t v_rinv_boxed_108_; lean_object* v_res_109_; 
v_linv_boxed_107_ = lean_unbox(v_linv_105_);
v_rinv_boxed_108_ = lean_unbox(v_rinv_106_);
v_res_109_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF(v_00_u03b1_101_, v_output_102_, v_lhs_103_, v_rhs_104_, v_linv_boxed_107_, v_rinv_boxed_108_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF___redArg(lean_object* v_output_110_, lean_object* v_cond_111_, lean_object* v_ifTrue_112_, lean_object* v_ifFalse_113_, uint8_t v_cinv_114_, uint8_t v_tinv_115_, uint8_t v_finv_116_){
_start:
{
uint8_t v___y_118_; lean_object* v___y_119_; lean_object* v___y_120_; lean_object* v___y_121_; uint8_t v___y_122_; uint8_t v___y_128_; lean_object* v___y_129_; lean_object* v___y_130_; uint8_t v___y_131_; lean_object* v___y_132_; uint8_t v___y_133_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; uint8_t v___y_143_; lean_object* v___y_144_; uint8_t v___y_145_; uint8_t v___y_146_; lean_object* v___y_150_; lean_object* v___y_151_; uint8_t v___y_152_; lean_object* v___y_153_; uint8_t v___y_154_; lean_object* v___y_161_; lean_object* v___y_162_; uint8_t v___y_163_; uint8_t v___y_172_; 
v___x_139_ = ((lean_object*)(l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__0));
v___x_140_ = l_ByteArray_empty;
v___x_141_ = lean_array_push(v___x_139_, v_cond_111_);
if (v_cinv_114_ == 0)
{
uint8_t v___x_177_; 
v___x_177_ = 0;
v___y_172_ = v___x_177_;
goto v___jp_171_;
}
else
{
uint8_t v___x_178_; 
v___x_178_ = 1;
v___y_172_ = v___x_178_;
goto v___jp_171_;
}
v___jp_117_:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_123_ = lean_byte_array_push(v___y_121_, v___y_122_);
v___x_124_ = lean_byte_array_push(v___x_123_, v___y_118_);
v___x_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_125_, 0, v___y_119_);
lean_ctor_set(v___x_125_, 1, v___x_124_);
v___x_126_ = lean_array_push(v___y_120_, v___x_125_);
return v___x_126_;
}
v___jp_127_:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
lean_inc_ref(v___y_132_);
v___x_134_ = lean_byte_array_push(v___y_132_, v___y_133_);
v___x_135_ = lean_array_push(v___y_129_, v_output_110_);
v___x_136_ = lean_byte_array_push(v___x_134_, v___y_131_);
lean_inc_ref(v___x_135_);
v___x_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_135_);
lean_ctor_set(v___x_137_, 1, v___x_136_);
v___x_138_ = lean_array_push(v___y_130_, v___x_137_);
if (v_finv_116_ == 0)
{
v___y_118_ = v___y_128_;
v___y_119_ = v___x_135_;
v___y_120_ = v___x_138_;
v___y_121_ = v___y_132_;
v___y_122_ = v___y_131_;
goto v___jp_117_;
}
else
{
v___y_118_ = v___y_128_;
v___y_119_ = v___x_135_;
v___y_120_ = v___x_138_;
v___y_121_ = v___y_132_;
v___y_122_ = v___y_128_;
goto v___jp_117_;
}
}
v___jp_142_:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = lean_byte_array_push(v___x_140_, v___y_146_);
v___x_148_ = lean_array_push(v___x_141_, v_ifFalse_113_);
if (v_finv_116_ == 0)
{
v___y_128_ = v___y_143_;
v___y_129_ = v___x_148_;
v___y_130_ = v___y_144_;
v___y_131_ = v___y_145_;
v___y_132_ = v___x_147_;
v___y_133_ = v___y_143_;
goto v___jp_127_;
}
else
{
v___y_128_ = v___y_143_;
v___y_129_ = v___x_148_;
v___y_130_ = v___y_144_;
v___y_131_ = v___y_145_;
v___y_132_ = v___x_147_;
v___y_133_ = v___y_145_;
goto v___jp_127_;
}
}
v___jp_149_:
{
lean_object* v___x_155_; uint8_t v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_155_ = lean_byte_array_push(v___y_153_, v___y_154_);
v___x_156_ = 0;
v___x_157_ = lean_byte_array_push(v___x_155_, v___x_156_);
v___x_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_158_, 0, v___y_151_);
lean_ctor_set(v___x_158_, 1, v___x_157_);
v___x_159_ = lean_array_push(v___y_150_, v___x_158_);
if (v_cinv_114_ == 0)
{
v___y_143_ = v___x_156_;
v___y_144_ = v___x_159_;
v___y_145_ = v___y_152_;
v___y_146_ = v___y_152_;
goto v___jp_142_;
}
else
{
v___y_143_ = v___x_156_;
v___y_144_ = v___x_159_;
v___y_145_ = v___y_152_;
v___y_146_ = v___x_156_;
goto v___jp_142_;
}
}
v___jp_160_:
{
lean_object* v___x_164_; lean_object* v___x_165_; uint8_t v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
lean_inc_ref(v___y_162_);
v___x_164_ = lean_byte_array_push(v___y_162_, v___y_163_);
lean_inc(v_output_110_);
v___x_165_ = lean_array_push(v___y_161_, v_output_110_);
v___x_166_ = 1;
v___x_167_ = lean_byte_array_push(v___x_164_, v___x_166_);
lean_inc_ref(v___x_165_);
v___x_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_165_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
v___x_169_ = lean_array_push(v___x_139_, v___x_168_);
if (v_tinv_115_ == 0)
{
v___y_150_ = v___x_169_;
v___y_151_ = v___x_165_;
v___y_152_ = v___x_166_;
v___y_153_ = v___y_162_;
v___y_154_ = v___x_166_;
goto v___jp_149_;
}
else
{
uint8_t v___x_170_; 
v___x_170_ = 0;
v___y_150_ = v___x_169_;
v___y_151_ = v___x_165_;
v___y_152_ = v___x_166_;
v___y_153_ = v___y_162_;
v___y_154_ = v___x_170_;
goto v___jp_149_;
}
}
v___jp_171_:
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = lean_byte_array_push(v___x_140_, v___y_172_);
lean_inc_ref(v___x_141_);
v___x_174_ = lean_array_push(v___x_141_, v_ifTrue_112_);
if (v_tinv_115_ == 0)
{
uint8_t v___x_175_; 
v___x_175_ = 0;
v___y_161_ = v___x_174_;
v___y_162_ = v___x_173_;
v___y_163_ = v___x_175_;
goto v___jp_160_;
}
else
{
uint8_t v___x_176_; 
v___x_176_ = 1;
v___y_161_ = v___x_174_;
v___y_162_ = v___x_173_;
v___y_163_ = v___x_176_;
goto v___jp_160_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF___redArg___boxed(lean_object* v_output_179_, lean_object* v_cond_180_, lean_object* v_ifTrue_181_, lean_object* v_ifFalse_182_, lean_object* v_cinv_183_, lean_object* v_tinv_184_, lean_object* v_finv_185_){
_start:
{
uint8_t v_cinv_boxed_186_; uint8_t v_tinv_boxed_187_; uint8_t v_finv_boxed_188_; lean_object* v_res_189_; 
v_cinv_boxed_186_ = lean_unbox(v_cinv_183_);
v_tinv_boxed_187_ = lean_unbox(v_tinv_184_);
v_finv_boxed_188_ = lean_unbox(v_finv_185_);
v_res_189_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF___redArg(v_output_179_, v_cond_180_, v_ifTrue_181_, v_ifFalse_182_, v_cinv_boxed_186_, v_tinv_boxed_187_, v_finv_boxed_188_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF(lean_object* v_00_u03b1_190_, lean_object* v_output_191_, lean_object* v_cond_192_, lean_object* v_ifTrue_193_, lean_object* v_ifFalse_194_, uint8_t v_cinv_195_, uint8_t v_tinv_196_, uint8_t v_finv_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF___redArg(v_output_191_, v_cond_192_, v_ifTrue_193_, v_ifFalse_194_, v_cinv_195_, v_tinv_196_, v_finv_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF___boxed(lean_object* v_00_u03b1_199_, lean_object* v_output_200_, lean_object* v_cond_201_, lean_object* v_ifTrue_202_, lean_object* v_ifFalse_203_, lean_object* v_cinv_204_, lean_object* v_tinv_205_, lean_object* v_finv_206_){
_start:
{
uint8_t v_cinv_boxed_207_; uint8_t v_tinv_boxed_208_; uint8_t v_finv_boxed_209_; lean_object* v_res_210_; 
v_cinv_boxed_207_ = lean_unbox(v_cinv_204_);
v_tinv_boxed_208_ = lean_unbox(v_tinv_205_);
v_finv_boxed_209_ = lean_unbox(v_finv_206_);
v_res_210_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF(v_00_u03b1_199_, v_output_200_, v_cond_201_, v_ifTrue_202_, v_ifFalse_203_, v_cinv_boxed_207_, v_tinv_boxed_208_, v_finv_boxed_209_);
return v_res_210_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_mixAssigns(lean_object* v_aig_211_, lean_object* v_assign1_212_, lean_object* v_assign2_213_, lean_object* v_var_214_){
_start:
{
lean_object* v_decls_215_; lean_object* v___x_216_; uint8_t v___x_217_; 
v_decls_215_ = lean_ctor_get(v_aig_211_, 0);
v___x_216_ = lean_array_get_size(v_decls_215_);
v___x_217_ = lean_nat_dec_lt(v_var_214_, v___x_216_);
if (v___x_217_ == 0)
{
lean_object* v___x_218_; lean_object* v___x_219_; uint8_t v___x_220_; 
lean_dec_ref(v_assign2_213_);
v___x_218_ = lean_nat_sub(v_var_214_, v___x_216_);
lean_dec(v_var_214_);
v___x_219_ = lean_apply_1(v_assign1_212_, v___x_218_);
v___x_220_ = lean_unbox(v___x_219_);
return v___x_220_;
}
else
{
lean_object* v___x_221_; uint8_t v___x_222_; 
lean_dec_ref(v_assign1_212_);
v___x_221_ = lean_apply_1(v_assign2_213_, v_var_214_);
v___x_222_ = lean_unbox(v___x_221_);
return v___x_222_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_mixAssigns___boxed(lean_object* v_aig_223_, lean_object* v_assign1_224_, lean_object* v_assign2_225_, lean_object* v_var_226_){
_start:
{
uint8_t v_res_227_; lean_object* v_r_228_; 
v_res_227_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_mixAssigns(v_aig_223_, v_assign1_224_, v_assign2_225_, v_var_226_);
lean_dec_ref(v_aig_223_);
v_r_228_ = lean_box(v_res_227_);
return v_r_228_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign(lean_object* v_aig_229_, lean_object* v_assign_230_, lean_object* v_var_231_){
_start:
{
lean_object* v_decls_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; uint8_t v___x_236_; 
v_decls_232_ = lean_ctor_get(v_aig_229_, 0);
v___x_233_ = lean_array_get_size(v_decls_232_);
v___x_234_ = lean_nat_add(v_var_231_, v___x_233_);
v___x_235_ = lean_apply_1(v_assign_230_, v___x_234_);
v___x_236_ = lean_unbox(v___x_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign___boxed(lean_object* v_aig_237_, lean_object* v_assign_238_, lean_object* v_var_239_){
_start:
{
uint8_t v_res_240_; lean_object* v_r_241_; 
v_res_240_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign(v_aig_237_, v_assign_238_, v_var_239_);
lean_dec(v_var_239_);
lean_dec_ref(v_aig_237_);
v_r_241_ = lean_box(v_res_240_);
return v_r_241_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectRightAssign(lean_object* v_assign_242_, lean_object* v_idx_243_){
_start:
{
lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_244_ = lean_apply_1(v_assign_242_, v_idx_243_);
v___x_245_ = lean_unbox(v___x_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectRightAssign___boxed(lean_object* v_assign_246_, lean_object* v_idx_247_){
_start:
{
uint8_t v_res_248_; lean_object* v_r_249_; 
v_res_248_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectRightAssign(v_assign_246_, v_idx_247_);
v_r_249_ = lean_box(v_res_248_);
return v_r_249_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment_spec__0(lean_object* v_assign_250_, lean_object* v_entry_251_){
_start:
{
lean_object* v_ref_252_; lean_object* v_aig_253_; lean_object* v_gate_254_; uint8_t v_invert_255_; lean_object* v_decls_256_; uint8_t v___x_257_; 
v_ref_252_ = lean_ctor_get(v_entry_251_, 1);
v_aig_253_ = lean_ctor_get(v_entry_251_, 0);
v_gate_254_ = lean_ctor_get(v_ref_252_, 0);
v_invert_255_ = lean_ctor_get_uint8(v_ref_252_, sizeof(void*)*1);
v_decls_256_ = lean_ctor_get(v_aig_253_, 0);
v___x_257_ = l_Std_Sat_AIG_denote_go___redArg(v_gate_254_, v_decls_256_, v_assign_250_);
if (v_invert_255_ == 0)
{
return v___x_257_;
}
else
{
if (v___x_257_ == 0)
{
return v_invert_255_;
}
else
{
uint8_t v___x_258_; 
v___x_258_ = 0;
return v___x_258_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment_spec__0___boxed(lean_object* v_assign_259_, lean_object* v_entry_260_){
_start:
{
uint8_t v_res_261_; lean_object* v_r_262_; 
v_res_261_ = l_Std_Sat_AIG_denote___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment_spec__0(v_assign_259_, v_entry_260_);
lean_dec_ref(v_entry_260_);
v_r_262_ = lean_box(v_res_261_);
return v_r_262_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___lam__0(lean_object* v_aig_263_, lean_object* v_assign1_264_, lean_object* v_idx_265_){
_start:
{
uint8_t v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_266_ = 0;
v___x_267_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_267_, 0, v_idx_265_);
lean_ctor_set_uint8(v___x_267_, sizeof(void*)*1, v___x_266_);
v___x_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_268_, 0, v_aig_263_);
lean_ctor_set(v___x_268_, 1, v___x_267_);
v___x_269_ = l_Std_Sat_AIG_denote___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment_spec__0(v_assign1_264_, v___x_268_);
lean_dec_ref_known(v___x_268_, 2);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___lam__0___boxed(lean_object* v_aig_270_, lean_object* v_assign1_271_, lean_object* v_idx_272_){
_start:
{
uint8_t v_res_273_; lean_object* v_r_274_; 
v_res_273_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___lam__0(v_aig_270_, v_assign1_271_, v_idx_272_);
v_r_274_ = lean_box(v_res_273_);
return v_r_274_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment(lean_object* v_aig_275_, lean_object* v_assign1_276_, lean_object* v_var_277_){
_start:
{
lean_object* v___f_278_; uint8_t v___x_279_; 
lean_inc_ref(v_assign1_276_);
lean_inc_ref(v_aig_275_);
v___f_278_ = lean_alloc_closure((void*)(l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___lam__0___boxed), 3, 2);
lean_closure_set(v___f_278_, 0, v_aig_275_);
lean_closure_set(v___f_278_, 1, v_assign1_276_);
v___x_279_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_mixAssigns(v_aig_275_, v_assign1_276_, v___f_278_, v_var_277_);
lean_dec_ref(v_aig_275_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___boxed(lean_object* v_aig_280_, lean_object* v_assign1_281_, lean_object* v_var_282_){
_start:
{
uint8_t v_res_283_; lean_object* v_r_284_; 
v_res_283_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment(v_aig_280_, v_assign1_281_, v_var_282_);
v_r_284_ = lean_box(v_res_283_);
return v_r_284_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init(lean_object* v_aig_285_){
_start:
{
lean_object* v_decls_286_; lean_object* v___x_287_; uint8_t v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v_decls_286_ = lean_ctor_get(v_aig_285_, 0);
v___x_287_ = lean_array_get_size(v_decls_286_);
v___x_288_ = 0;
v___x_289_ = lean_box(v___x_288_);
v___x_290_ = lean_mk_array(v___x_287_, v___x_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___boxed(lean_object* v_aig_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init(v_aig_291_);
lean_dec_ref(v_aig_291_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg(lean_object* v_cache_293_, lean_object* v_idx_294_){
_start:
{
uint8_t v___x_295_; lean_object* v___x_296_; lean_object* v_out_297_; 
v___x_295_ = 1;
v___x_296_ = lean_box(v___x_295_);
v_out_297_ = lean_array_fset(v_cache_293_, v_idx_294_, v___x_296_);
return v_out_297_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg___boxed(lean_object* v_cache_298_, lean_object* v_idx_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg(v_cache_298_, v_idx_299_);
lean_dec(v_idx_299_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse(lean_object* v_aig_301_, lean_object* v_cnf_302_, lean_object* v_cache_303_, lean_object* v_idx_304_, lean_object* v_h_305_, lean_object* v_htip_306_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg(v_cache_303_, v_idx_304_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___boxed(lean_object* v_aig_308_, lean_object* v_cnf_309_, lean_object* v_cache_310_, lean_object* v_idx_311_, lean_object* v_h_312_, lean_object* v_htip_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse(v_aig_308_, v_cnf_309_, v_cache_310_, v_idx_311_, v_h_312_, v_htip_313_);
lean_dec(v_idx_311_);
lean_dec_ref(v_cnf_309_);
lean_dec_ref(v_aig_308_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg(lean_object* v_cache_315_, lean_object* v_idx_316_){
_start:
{
uint8_t v___x_317_; lean_object* v___x_318_; lean_object* v_out_319_; 
v___x_317_ = 1;
v___x_318_ = lean_box(v___x_317_);
v_out_319_ = lean_array_fset(v_cache_315_, v_idx_316_, v___x_318_);
return v_out_319_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg___boxed(lean_object* v_cache_320_, lean_object* v_idx_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg(v_cache_320_, v_idx_321_);
lean_dec(v_idx_321_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom(lean_object* v_aig_323_, lean_object* v_cnf_324_, lean_object* v_a_325_, lean_object* v_cache_326_, lean_object* v_idx_327_, lean_object* v_h_328_, lean_object* v_htip_329_){
_start:
{
lean_object* v___x_330_; 
v___x_330_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg(v_cache_326_, v_idx_327_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___boxed(lean_object* v_aig_331_, lean_object* v_cnf_332_, lean_object* v_a_333_, lean_object* v_cache_334_, lean_object* v_idx_335_, lean_object* v_h_336_, lean_object* v_htip_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom(v_aig_331_, v_cnf_332_, v_a_333_, v_cache_334_, v_idx_335_, v_h_336_, v_htip_337_);
lean_dec(v_idx_335_);
lean_dec(v_a_333_);
lean_dec_ref(v_cnf_332_);
lean_dec_ref(v_aig_331_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg(lean_object* v_lhs_339_, lean_object* v_rhs_340_, lean_object* v_cache_341_, lean_object* v_idx_342_){
_start:
{
uint8_t v___x_343_; lean_object* v___x_344_; lean_object* v_out_345_; 
v___x_343_ = 1;
v___x_344_ = lean_box(v___x_343_);
v_out_345_ = lean_array_fset(v_cache_341_, v_idx_342_, v___x_344_);
return v_out_345_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg___boxed(lean_object* v_lhs_346_, lean_object* v_rhs_347_, lean_object* v_cache_348_, lean_object* v_idx_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg(v_lhs_346_, v_rhs_347_, v_cache_348_, v_idx_349_);
lean_dec(v_idx_349_);
lean_dec(v_rhs_347_);
lean_dec(v_lhs_346_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate(lean_object* v_aig_351_, lean_object* v_cnf_352_, lean_object* v_lhs_353_, lean_object* v_rhs_354_, lean_object* v_cache_355_, lean_object* v_hlb_356_, lean_object* v_hrb_357_, lean_object* v_idx_358_, lean_object* v_h_359_, lean_object* v_htip_360_, lean_object* v_hl_361_, lean_object* v_hr_362_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg(v_lhs_353_, v_rhs_354_, v_cache_355_, v_idx_358_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___boxed(lean_object* v_aig_364_, lean_object* v_cnf_365_, lean_object* v_lhs_366_, lean_object* v_rhs_367_, lean_object* v_cache_368_, lean_object* v_hlb_369_, lean_object* v_hrb_370_, lean_object* v_idx_371_, lean_object* v_h_372_, lean_object* v_htip_373_, lean_object* v_hl_374_, lean_object* v_hr_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate(v_aig_364_, v_cnf_365_, v_lhs_366_, v_rhs_367_, v_cache_368_, v_hlb_369_, v_hrb_370_, v_idx_371_, v_h_372_, v_htip_373_, v_hl_374_, v_hr_375_);
lean_dec(v_idx_371_);
lean_dec(v_rhs_367_);
lean_dec(v_lhs_366_);
lean_dec_ref(v_cnf_365_);
lean_dec_ref(v_aig_364_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___redArg(lean_object* v_cache_377_, lean_object* v_cond_378_, lean_object* v_ifTrue_379_, lean_object* v_ifFalse_380_, lean_object* v_idx_381_){
_start:
{
uint8_t v___x_382_; lean_object* v___x_383_; lean_object* v_out_384_; 
v___x_382_ = 1;
v___x_383_ = lean_box(v___x_382_);
v_out_384_ = lean_array_fset(v_cache_377_, v_idx_381_, v___x_383_);
return v_out_384_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___redArg___boxed(lean_object* v_cache_385_, lean_object* v_cond_386_, lean_object* v_ifTrue_387_, lean_object* v_ifFalse_388_, lean_object* v_idx_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___redArg(v_cache_385_, v_cond_386_, v_ifTrue_387_, v_ifFalse_388_, v_idx_389_);
lean_dec(v_idx_389_);
lean_dec(v_ifFalse_388_);
lean_dec(v_ifTrue_387_);
lean_dec(v_cond_386_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte(lean_object* v_aig_391_, lean_object* v_cnf_392_, lean_object* v_cache_393_, lean_object* v_cond_394_, lean_object* v_ifTrue_395_, lean_object* v_ifFalse_396_, lean_object* v_idx_397_, lean_object* v_hcb_398_, lean_object* v_htb_399_, lean_object* v_hfb_400_, lean_object* v_h_401_, lean_object* v_hltc_402_, lean_object* v_hltt_403_, lean_object* v_hltf_404_, lean_object* v_hc_405_, lean_object* v_ht_406_, lean_object* v_hf_407_, lean_object* v_hdenote_408_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___redArg(v_cache_393_, v_cond_394_, v_ifTrue_395_, v_ifFalse_396_, v_idx_397_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___boxed(lean_object** _args){
lean_object* v_aig_410_ = _args[0];
lean_object* v_cnf_411_ = _args[1];
lean_object* v_cache_412_ = _args[2];
lean_object* v_cond_413_ = _args[3];
lean_object* v_ifTrue_414_ = _args[4];
lean_object* v_ifFalse_415_ = _args[5];
lean_object* v_idx_416_ = _args[6];
lean_object* v_hcb_417_ = _args[7];
lean_object* v_htb_418_ = _args[8];
lean_object* v_hfb_419_ = _args[9];
lean_object* v_h_420_ = _args[10];
lean_object* v_hltc_421_ = _args[11];
lean_object* v_hltt_422_ = _args[12];
lean_object* v_hltf_423_ = _args[13];
lean_object* v_hc_424_ = _args[14];
lean_object* v_ht_425_ = _args[15];
lean_object* v_hf_426_ = _args[16];
lean_object* v_hdenote_427_ = _args[17];
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte(v_aig_410_, v_cnf_411_, v_cache_412_, v_cond_413_, v_ifTrue_414_, v_ifFalse_415_, v_idx_416_, v_hcb_417_, v_htb_418_, v_hfb_419_, v_h_420_, v_hltc_421_, v_hltt_422_, v_hltf_423_, v_hc_424_, v_ht_425_, v_hf_426_, v_hdenote_427_);
lean_dec(v_idx_416_);
lean_dec(v_ifFalse_415_);
lean_dec(v_ifTrue_414_);
lean_dec(v_cond_413_);
lean_dec_ref(v_cnf_411_);
lean_dec_ref(v_aig_410_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty(lean_object* v_aig_429_){
_start:
{
lean_object* v_decls_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_442_; 
v_decls_430_ = lean_ctor_get(v_aig_429_, 0);
v___x_431_ = lean_array_get_size(v_decls_430_);
v___x_432_ = lean_unsigned_to_nat(2u);
v___x_433_ = lean_nat_mul(v___x_431_, v___x_432_);
v___x_434_ = lean_mk_empty_array_with_capacity(v___x_433_);
lean_dec(v___x_433_);
v___x_435_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init(v_aig_429_);
v_isSharedCheck_442_ = !lean_is_exclusive(v_aig_429_);
if (v_isSharedCheck_442_ == 0)
{
lean_object* v_unused_443_; lean_object* v_unused_444_; 
v_unused_443_ = lean_ctor_get(v_aig_429_, 1);
lean_dec(v_unused_443_);
v_unused_444_ = lean_ctor_get(v_aig_429_, 0);
lean_dec(v_unused_444_);
v___x_437_ = v_aig_429_;
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
else
{
lean_dec(v_aig_429_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_440_; 
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 1, v___x_435_);
lean_ctor_set(v___x_437_, 0, v___x_434_);
v___x_440_ = v___x_437_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v___x_434_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v___x_435_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___redArg(lean_object* v_state_445_, lean_object* v_idx_446_){
_start:
{
lean_object* v_cnf_447_; lean_object* v_cache_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_458_; 
v_cnf_447_ = lean_ctor_get(v_state_445_, 0);
v_cache_448_ = lean_ctor_get(v_state_445_, 1);
v_isSharedCheck_458_ = !lean_is_exclusive(v_state_445_);
if (v_isSharedCheck_458_ == 0)
{
v___x_450_ = v_state_445_;
v_isShared_451_ = v_isSharedCheck_458_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_cache_448_);
lean_inc(v_cnf_447_);
lean_dec(v_state_445_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_458_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v_val_452_; lean_object* v_newCnf_453_; lean_object* v___x_454_; lean_object* v___x_456_; 
v_val_452_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg(v_cache_448_, v_idx_446_);
v_newCnf_453_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg(v_idx_446_);
v___x_454_ = l_Array_append___redArg(v_cnf_447_, v_newCnf_453_);
lean_dec_ref(v_newCnf_453_);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 1, v_val_452_);
lean_ctor_set(v___x_450_, 0, v___x_454_);
v___x_456_ = v___x_450_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_454_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v_val_452_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse(lean_object* v_aig_459_, lean_object* v_state_460_, lean_object* v_idx_461_, lean_object* v_h_462_, lean_object* v_htip_463_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___redArg(v_state_460_, v_idx_461_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___boxed(lean_object* v_aig_465_, lean_object* v_state_466_, lean_object* v_idx_467_, lean_object* v_h_468_, lean_object* v_htip_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse(v_aig_465_, v_state_466_, v_idx_467_, v_h_468_, v_htip_469_);
lean_dec_ref(v_aig_465_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg(lean_object* v_aig_471_, lean_object* v_a_472_, lean_object* v_state_473_, lean_object* v_idx_474_){
_start:
{
lean_object* v_cnf_475_; lean_object* v_cache_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_489_; 
v_cnf_475_ = lean_ctor_get(v_state_473_, 0);
v_cache_476_ = lean_ctor_get(v_state_473_, 1);
v_isSharedCheck_489_ = !lean_is_exclusive(v_state_473_);
if (v_isSharedCheck_489_ == 0)
{
v___x_478_ = v_state_473_;
v_isShared_479_ = v_isSharedCheck_489_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_cache_476_);
lean_inc(v_cnf_475_);
lean_dec(v_state_473_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_489_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v_decls_480_; lean_object* v_val_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v_newCnf_484_; lean_object* v___x_485_; lean_object* v___x_487_; 
v_decls_480_ = lean_ctor_get(v_aig_471_, 0);
v_val_481_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg(v_cache_476_, v_idx_474_);
v___x_482_ = lean_array_get_size(v_decls_480_);
v___x_483_ = lean_nat_add(v_a_472_, v___x_482_);
v_newCnf_484_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF___redArg(v_idx_474_, v___x_483_);
v___x_485_ = l_Array_append___redArg(v_cnf_475_, v_newCnf_484_);
lean_dec_ref(v_newCnf_484_);
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 1, v_val_481_);
lean_ctor_set(v___x_478_, 0, v___x_485_);
v___x_487_ = v___x_478_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v___x_485_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v_val_481_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg___boxed(lean_object* v_aig_490_, lean_object* v_a_491_, lean_object* v_state_492_, lean_object* v_idx_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg(v_aig_490_, v_a_491_, v_state_492_, v_idx_493_);
lean_dec(v_a_491_);
lean_dec_ref(v_aig_490_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom(lean_object* v_aig_495_, lean_object* v_a_496_, lean_object* v_state_497_, lean_object* v_idx_498_, lean_object* v_h_499_, lean_object* v_htip_500_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg(v_aig_495_, v_a_496_, v_state_497_, v_idx_498_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___boxed(lean_object* v_aig_502_, lean_object* v_a_503_, lean_object* v_state_504_, lean_object* v_idx_505_, lean_object* v_h_506_, lean_object* v_htip_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom(v_aig_502_, v_a_503_, v_state_504_, v_idx_505_, v_h_506_, v_htip_507_);
lean_dec(v_a_503_);
lean_dec_ref(v_aig_502_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg(lean_object* v_lhs_509_, lean_object* v_rhs_510_, lean_object* v_state_511_, lean_object* v_idx_512_){
_start:
{
lean_object* v_cnf_513_; lean_object* v_cache_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_542_; 
v_cnf_513_ = lean_ctor_get(v_state_511_, 0);
v_cache_514_ = lean_ctor_get(v_state_511_, 1);
v_isSharedCheck_542_ = !lean_is_exclusive(v_state_511_);
if (v_isSharedCheck_542_ == 0)
{
v___x_516_ = v_state_511_;
v_isShared_517_ = v_isSharedCheck_542_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_cache_514_);
lean_inc(v_cnf_513_);
lean_dec(v_state_511_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_542_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; uint8_t v___y_522_; uint8_t v___y_523_; uint8_t v___y_531_; lean_object* v___x_537_; lean_object* v___x_538_; uint8_t v___x_539_; 
v___x_518_ = lean_unsigned_to_nat(1u);
v___x_519_ = lean_nat_shiftr(v_lhs_509_, v___x_518_);
v___x_520_ = lean_nat_shiftr(v_rhs_510_, v___x_518_);
v___x_537_ = lean_nat_land(v___x_518_, v_lhs_509_);
v___x_538_ = lean_unsigned_to_nat(0u);
v___x_539_ = lean_nat_dec_eq(v___x_537_, v___x_538_);
lean_dec(v___x_537_);
if (v___x_539_ == 0)
{
uint8_t v___x_540_; 
v___x_540_ = 1;
v___y_531_ = v___x_540_;
goto v___jp_530_;
}
else
{
uint8_t v___x_541_; 
v___x_541_ = 0;
v___y_531_ = v___x_541_;
goto v___jp_530_;
}
v___jp_521_:
{
lean_object* v_val_524_; lean_object* v_newCnf_525_; lean_object* v___x_526_; lean_object* v___x_528_; 
v_val_524_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg(v_lhs_509_, v_rhs_510_, v_cache_514_, v_idx_512_);
v_newCnf_525_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg(v_idx_512_, v___x_519_, v___x_520_, v___y_522_, v___y_523_);
v___x_526_ = l_Array_append___redArg(v_cnf_513_, v_newCnf_525_);
lean_dec_ref(v_newCnf_525_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 1, v_val_524_);
lean_ctor_set(v___x_516_, 0, v___x_526_);
v___x_528_ = v___x_516_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_526_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v_val_524_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
v___jp_530_:
{
lean_object* v___x_532_; lean_object* v___x_533_; uint8_t v___x_534_; 
v___x_532_ = lean_nat_land(v___x_518_, v_rhs_510_);
v___x_533_ = lean_unsigned_to_nat(0u);
v___x_534_ = lean_nat_dec_eq(v___x_532_, v___x_533_);
lean_dec(v___x_532_);
if (v___x_534_ == 0)
{
uint8_t v___x_535_; 
v___x_535_ = 1;
v___y_522_ = v___y_531_;
v___y_523_ = v___x_535_;
goto v___jp_521_;
}
else
{
uint8_t v___x_536_; 
v___x_536_ = 0;
v___y_522_ = v___y_531_;
v___y_523_ = v___x_536_;
goto v___jp_521_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg___boxed(lean_object* v_lhs_543_, lean_object* v_rhs_544_, lean_object* v_state_545_, lean_object* v_idx_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg(v_lhs_543_, v_rhs_544_, v_state_545_, v_idx_546_);
lean_dec(v_rhs_544_);
lean_dec(v_lhs_543_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate(lean_object* v_aig_548_, lean_object* v_lhs_549_, lean_object* v_rhs_550_, lean_object* v_state_551_, lean_object* v_hlb_552_, lean_object* v_hrb_553_, lean_object* v_idx_554_, lean_object* v_h_555_, lean_object* v_htip_556_, lean_object* v_hl_557_, lean_object* v_hr_558_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg(v_lhs_549_, v_rhs_550_, v_state_551_, v_idx_554_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___boxed(lean_object* v_aig_560_, lean_object* v_lhs_561_, lean_object* v_rhs_562_, lean_object* v_state_563_, lean_object* v_hlb_564_, lean_object* v_hrb_565_, lean_object* v_idx_566_, lean_object* v_h_567_, lean_object* v_htip_568_, lean_object* v_hl_569_, lean_object* v_hr_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate(v_aig_560_, v_lhs_561_, v_rhs_562_, v_state_563_, v_hlb_564_, v_hrb_565_, v_idx_566_, v_h_567_, v_htip_568_, v_hl_569_, v_hr_570_);
lean_dec(v_rhs_562_);
lean_dec(v_lhs_561_);
lean_dec_ref(v_aig_560_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___redArg(lean_object* v_state_572_, lean_object* v_cond_573_, lean_object* v_ifTrue_574_, lean_object* v_ifFalse_575_, lean_object* v_idx_576_){
_start:
{
lean_object* v_cnf_577_; lean_object* v_cache_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_616_; 
v_cnf_577_ = lean_ctor_get(v_state_572_, 0);
v_cache_578_ = lean_ctor_get(v_state_572_, 1);
v_isSharedCheck_616_ = !lean_is_exclusive(v_state_572_);
if (v_isSharedCheck_616_ == 0)
{
v___x_580_ = v_state_572_;
v_isShared_581_ = v_isSharedCheck_616_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_cache_578_);
lean_inc(v_cnf_577_);
lean_dec(v_state_572_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_616_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; uint8_t v___y_587_; uint8_t v___y_588_; uint8_t v___y_589_; uint8_t v___y_597_; uint8_t v___y_598_; uint8_t v___y_605_; lean_object* v___x_611_; lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_582_ = lean_unsigned_to_nat(1u);
v___x_583_ = lean_nat_shiftr(v_cond_573_, v___x_582_);
v___x_584_ = lean_nat_shiftr(v_ifTrue_574_, v___x_582_);
v___x_585_ = lean_nat_shiftr(v_ifFalse_575_, v___x_582_);
v___x_611_ = lean_nat_land(v___x_582_, v_cond_573_);
v___x_612_ = lean_unsigned_to_nat(0u);
v___x_613_ = lean_nat_dec_eq(v___x_611_, v___x_612_);
lean_dec(v___x_611_);
if (v___x_613_ == 0)
{
uint8_t v___x_614_; 
v___x_614_ = 1;
v___y_605_ = v___x_614_;
goto v___jp_604_;
}
else
{
uint8_t v___x_615_; 
v___x_615_ = 0;
v___y_605_ = v___x_615_;
goto v___jp_604_;
}
v___jp_586_:
{
lean_object* v_val_590_; lean_object* v_newCnf_591_; lean_object* v___x_592_; lean_object* v___x_594_; 
v_val_590_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___redArg(v_cache_578_, v_cond_573_, v_ifTrue_574_, v_ifFalse_575_, v_idx_576_);
v_newCnf_591_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF___redArg(v_idx_576_, v___x_583_, v___x_584_, v___x_585_, v___y_588_, v___y_587_, v___y_589_);
v___x_592_ = l_Array_append___redArg(v_cnf_577_, v_newCnf_591_);
lean_dec_ref(v_newCnf_591_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 1, v_val_590_);
lean_ctor_set(v___x_580_, 0, v___x_592_);
v___x_594_ = v___x_580_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_592_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v_val_590_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
v___jp_596_:
{
lean_object* v___x_599_; lean_object* v___x_600_; uint8_t v___x_601_; 
v___x_599_ = lean_nat_land(v___x_582_, v_ifFalse_575_);
v___x_600_ = lean_unsigned_to_nat(0u);
v___x_601_ = lean_nat_dec_eq(v___x_599_, v___x_600_);
lean_dec(v___x_599_);
if (v___x_601_ == 0)
{
uint8_t v___x_602_; 
v___x_602_ = 1;
v___y_587_ = v___y_598_;
v___y_588_ = v___y_597_;
v___y_589_ = v___x_602_;
goto v___jp_586_;
}
else
{
uint8_t v___x_603_; 
v___x_603_ = 0;
v___y_587_ = v___y_598_;
v___y_588_ = v___y_597_;
v___y_589_ = v___x_603_;
goto v___jp_586_;
}
}
v___jp_604_:
{
lean_object* v___x_606_; lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_606_ = lean_nat_land(v___x_582_, v_ifTrue_574_);
v___x_607_ = lean_unsigned_to_nat(0u);
v___x_608_ = lean_nat_dec_eq(v___x_606_, v___x_607_);
lean_dec(v___x_606_);
if (v___x_608_ == 0)
{
uint8_t v___x_609_; 
v___x_609_ = 1;
v___y_597_ = v___y_605_;
v___y_598_ = v___x_609_;
goto v___jp_596_;
}
else
{
uint8_t v___x_610_; 
v___x_610_ = 0;
v___y_597_ = v___y_605_;
v___y_598_ = v___x_610_;
goto v___jp_596_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___redArg___boxed(lean_object* v_state_617_, lean_object* v_cond_618_, lean_object* v_ifTrue_619_, lean_object* v_ifFalse_620_, lean_object* v_idx_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___redArg(v_state_617_, v_cond_618_, v_ifTrue_619_, v_ifFalse_620_, v_idx_621_);
lean_dec(v_ifFalse_620_);
lean_dec(v_ifTrue_619_);
lean_dec(v_cond_618_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte(lean_object* v_aig_623_, lean_object* v_state_624_, lean_object* v_cond_625_, lean_object* v_ifTrue_626_, lean_object* v_ifFalse_627_, lean_object* v_idx_628_, lean_object* v_hcb_629_, lean_object* v_htb_630_, lean_object* v_hfb_631_, lean_object* v_h_632_, lean_object* v_hltc_633_, lean_object* v_hltt_634_, lean_object* v_hltf_635_, lean_object* v_hc_636_, lean_object* v_ht_637_, lean_object* v_hf_638_, lean_object* v_hdenote_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___redArg(v_state_624_, v_cond_625_, v_ifTrue_626_, v_ifFalse_627_, v_idx_628_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___boxed(lean_object** _args){
lean_object* v_aig_641_ = _args[0];
lean_object* v_state_642_ = _args[1];
lean_object* v_cond_643_ = _args[2];
lean_object* v_ifTrue_644_ = _args[3];
lean_object* v_ifFalse_645_ = _args[4];
lean_object* v_idx_646_ = _args[5];
lean_object* v_hcb_647_ = _args[6];
lean_object* v_htb_648_ = _args[7];
lean_object* v_hfb_649_ = _args[8];
lean_object* v_h_650_ = _args[9];
lean_object* v_hltc_651_ = _args[10];
lean_object* v_hltt_652_ = _args[11];
lean_object* v_hltf_653_ = _args[12];
lean_object* v_hc_654_ = _args[13];
lean_object* v_ht_655_ = _args[14];
lean_object* v_hf_656_ = _args[15];
lean_object* v_hdenote_657_ = _args[16];
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte(v_aig_641_, v_state_642_, v_cond_643_, v_ifTrue_644_, v_ifFalse_645_, v_idx_646_, v_hcb_647_, v_htb_648_, v_hfb_649_, v_h_650_, v_hltc_651_, v_hltt_652_, v_hltf_653_, v_hc_654_, v_ht_655_, v_hf_656_, v_hdenote_657_);
lean_dec(v_ifFalse_645_);
lean_dec(v_ifTrue_644_);
lean_dec(v_cond_643_);
lean_dec_ref(v_aig_641_);
return v_res_658_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg(lean_object* v_assign_659_, lean_object* v_state_660_){
_start:
{
lean_object* v_cnf_661_; uint8_t v___x_662_; 
v_cnf_661_ = lean_ctor_get(v_state_660_, 0);
v___x_662_ = l_Std_Sat_CNF_eval___redArg(v_assign_659_, v_cnf_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg___boxed(lean_object* v_assign_663_, lean_object* v_state_664_){
_start:
{
uint8_t v_res_665_; lean_object* v_r_666_; 
v_res_665_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg(v_assign_663_, v_state_664_);
lean_dec_ref(v_state_664_);
v_r_666_ = lean_box(v_res_665_);
return v_r_666_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval(lean_object* v_aig_667_, lean_object* v_assign_668_, lean_object* v_state_669_){
_start:
{
uint8_t v___x_670_; 
v___x_670_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg(v_assign_668_, v_state_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___boxed(lean_object* v_aig_671_, lean_object* v_assign_672_, lean_object* v_state_673_){
_start:
{
uint8_t v_res_674_; lean_object* v_r_675_; 
v_res_674_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval(v_aig_671_, v_assign_672_, v_state_673_);
lean_dec_ref(v_state_673_);
lean_dec_ref(v_aig_671_);
v_r_675_ = lean_box(v_res_674_);
return v_r_675_;
}
}
static lean_object* _init_l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg___closed__0(void){
_start:
{
uint8_t v___x_676_; lean_object* v___x_677_; 
v___x_676_ = 1;
v___x_677_ = l_Bool_toNat(v___x_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg(lean_object* v_l0_678_, lean_object* v_l1_679_, lean_object* v_r0_680_, lean_object* v_r1_681_){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; uint8_t v___x_684_; 
v___x_682_ = lean_obj_once(&l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg___closed__0, &l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg___closed__0_once, _init_l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg___closed__0);
v___x_683_ = lean_nat_lxor(v_r0_680_, v___x_682_);
v___x_684_ = lean_nat_dec_eq(v_l0_678_, v___x_683_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; uint8_t v___x_686_; 
v___x_685_ = lean_nat_lxor(v_r1_681_, v___x_682_);
v___x_686_ = lean_nat_dec_eq(v_l0_678_, v___x_685_);
if (v___x_686_ == 0)
{
uint8_t v___x_687_; 
v___x_687_ = lean_nat_dec_eq(v_l1_679_, v___x_683_);
if (v___x_687_ == 0)
{
uint8_t v___x_688_; 
v___x_688_ = lean_nat_dec_eq(v_l1_679_, v___x_685_);
lean_dec(v___x_685_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; 
lean_dec(v___x_683_);
lean_dec(v_l1_679_);
lean_dec(v_l0_678_);
v___x_689_ = lean_box(0);
return v___x_689_;
}
else
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_690_ = lean_nat_lxor(v_l0_678_, v___x_682_);
lean_dec(v_l0_678_);
v___x_691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
lean_ctor_set(v___x_691_, 1, v___x_683_);
v___x_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_692_, 0, v_l1_679_);
lean_ctor_set(v___x_692_, 1, v___x_691_);
v___x_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
return v___x_693_;
}
}
else
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
lean_dec(v___x_683_);
v___x_694_ = lean_nat_lxor(v_l0_678_, v___x_682_);
lean_dec(v_l0_678_);
v___x_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
lean_ctor_set(v___x_695_, 1, v___x_685_);
v___x_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_696_, 0, v_l1_679_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
v___x_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
return v___x_697_;
}
}
else
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
lean_dec(v___x_685_);
v___x_698_ = lean_nat_lxor(v_l1_679_, v___x_682_);
lean_dec(v_l1_679_);
v___x_699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
lean_ctor_set(v___x_699_, 1, v___x_683_);
v___x_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_700_, 0, v_l0_678_);
lean_ctor_set(v___x_700_, 1, v___x_699_);
v___x_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_701_, 0, v___x_700_);
return v___x_701_;
}
}
else
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
lean_dec(v___x_683_);
v___x_702_ = lean_nat_lxor(v_l1_679_, v___x_682_);
lean_dec(v_l1_679_);
v___x_703_ = lean_nat_lxor(v_r1_681_, v___x_682_);
v___x_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_702_);
lean_ctor_set(v___x_704_, 1, v___x_703_);
v___x_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_705_, 0, v_l0_678_);
lean_ctor_set(v___x_705_, 1, v___x_704_);
v___x_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
return v___x_706_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg___boxed(lean_object* v_l0_707_, lean_object* v_l1_708_, lean_object* v_r0_709_, lean_object* v_r1_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg(v_l0_707_, v_l1_708_, v_r0_709_, v_r1_710_);
lean_dec(v_r1_710_);
lean_dec(v_r0_709_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go(lean_object* v_l_712_, lean_object* v_r_713_, lean_object* v_l0_714_, lean_object* v_l1_715_, lean_object* v_r0_716_, lean_object* v_r1_717_){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg(v_l0_714_, v_l1_715_, v_r0_716_, v_r1_717_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___boxed(lean_object* v_l_719_, lean_object* v_r_720_, lean_object* v_l0_721_, lean_object* v_l1_722_, lean_object* v_r0_723_, lean_object* v_r1_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go(v_l_719_, v_r_720_, v_l0_721_, v_l1_722_, v_r0_723_, v_r1_724_);
lean_dec(v_r1_724_);
lean_dec(v_r0_723_);
lean_dec(v_r_720_);
lean_dec(v_l_719_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___redArg(lean_object* v_aig_726_, lean_object* v_root_727_){
_start:
{
lean_object* v_decls_728_; lean_object* v___x_729_; 
v_decls_728_ = lean_ctor_get(v_aig_726_, 0);
v___x_729_ = lean_array_fget_borrowed(v_decls_728_, v_root_727_);
if (lean_obj_tag(v___x_729_) == 2)
{
lean_object* v_l_730_; lean_object* v_r_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; uint8_t v___x_735_; 
v_l_730_ = lean_ctor_get(v___x_729_, 0);
v_r_731_ = lean_ctor_get(v___x_729_, 1);
v___x_732_ = lean_unsigned_to_nat(1u);
v___x_733_ = lean_nat_land(v___x_732_, v_l_730_);
v___x_734_ = lean_unsigned_to_nat(0u);
v___x_735_ = lean_nat_dec_eq(v___x_733_, v___x_734_);
lean_dec(v___x_733_);
if (v___x_735_ == 0)
{
lean_object* v___x_736_; uint8_t v___x_737_; 
v___x_736_ = lean_nat_land(v___x_732_, v_r_731_);
v___x_737_ = lean_nat_dec_eq(v___x_736_, v___x_734_);
lean_dec(v___x_736_);
if (v___x_737_ == 0)
{
lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_738_ = lean_nat_shiftr(v_l_730_, v___x_732_);
v___x_739_ = lean_array_fget_borrowed(v_decls_728_, v___x_738_);
lean_dec(v___x_738_);
if (lean_obj_tag(v___x_739_) == 2)
{
lean_object* v_l_740_; lean_object* v_r_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v_l_740_ = lean_ctor_get(v___x_739_, 0);
v_r_741_ = lean_ctor_get(v___x_739_, 1);
v___x_742_ = lean_nat_shiftr(v_r_731_, v___x_732_);
v___x_743_ = lean_array_fget_borrowed(v_decls_728_, v___x_742_);
lean_dec(v___x_742_);
if (lean_obj_tag(v___x_743_) == 2)
{
lean_object* v_l_744_; lean_object* v_r_745_; lean_object* v___x_746_; 
v_l_744_ = lean_ctor_get(v___x_743_, 0);
v_r_745_ = lean_ctor_get(v___x_743_, 1);
lean_inc(v_r_741_);
lean_inc(v_l_740_);
v___x_746_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg(v_l_740_, v_r_741_, v_l_744_, v_r_745_);
return v___x_746_;
}
else
{
lean_object* v___x_747_; 
v___x_747_ = lean_box(0);
return v___x_747_;
}
}
else
{
lean_object* v___x_748_; 
v___x_748_ = lean_box(0);
return v___x_748_;
}
}
else
{
lean_object* v___x_749_; 
v___x_749_ = lean_box(0);
return v___x_749_;
}
}
else
{
lean_object* v___x_750_; 
v___x_750_ = lean_box(0);
return v___x_750_;
}
}
else
{
lean_object* v___x_751_; 
v___x_751_ = lean_box(0);
return v___x_751_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___redArg___boxed(lean_object* v_aig_752_, lean_object* v_root_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___redArg(v_aig_752_, v_root_753_);
lean_dec(v_root_753_);
lean_dec_ref(v_aig_752_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte(lean_object* v_aig_755_, lean_object* v_root_756_, lean_object* v_h_757_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___redArg(v_aig_755_, v_root_756_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___boxed(lean_object* v_aig_759_, lean_object* v_root_760_, lean_object* v_h_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte(v_aig_759_, v_root_760_, v_h_761_);
lean_dec(v_root_760_);
lean_dec_ref(v_aig_759_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_match__4_splitter___redArg(lean_object* v_x_763_, lean_object* v_h__1_764_, lean_object* v_h__2_765_){
_start:
{
if (lean_obj_tag(v_x_763_) == 2)
{
lean_object* v_l_766_; lean_object* v_r_767_; lean_object* v___x_768_; 
lean_dec(v_h__2_765_);
v_l_766_ = lean_ctor_get(v_x_763_, 0);
lean_inc(v_l_766_);
v_r_767_ = lean_ctor_get(v_x_763_, 1);
lean_inc(v_r_767_);
lean_dec_ref_known(v_x_763_, 2);
v___x_768_ = lean_apply_3(v_h__1_764_, v_l_766_, v_r_767_, lean_box(0));
return v___x_768_;
}
else
{
lean_object* v___x_769_; 
lean_dec(v_h__1_764_);
v___x_769_ = lean_apply_3(v_h__2_765_, v_x_763_, lean_box(0), lean_box(0));
return v___x_769_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_match__4_splitter(lean_object* v_motive_770_, lean_object* v_x_771_, lean_object* v_h__1_772_, lean_object* v_h__2_773_){
_start:
{
if (lean_obj_tag(v_x_771_) == 2)
{
lean_object* v_l_774_; lean_object* v_r_775_; lean_object* v___x_776_; 
lean_dec(v_h__2_773_);
v_l_774_ = lean_ctor_get(v_x_771_, 0);
lean_inc(v_l_774_);
v_r_775_ = lean_ctor_get(v_x_771_, 1);
lean_inc(v_r_775_);
lean_dec_ref_known(v_x_771_, 2);
v___x_776_ = lean_apply_3(v_h__1_772_, v_l_774_, v_r_775_, lean_box(0));
return v___x_776_;
}
else
{
lean_object* v___x_777_; 
lean_dec(v_h__1_772_);
v___x_777_ = lean_apply_3(v_h__2_773_, v_x_771_, lean_box(0), lean_box(0));
return v___x_777_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_match__1_splitter___redArg(lean_object* v_x_778_, lean_object* v_x_779_, lean_object* v_h__1_780_, lean_object* v_h__2_781_){
_start:
{
if (lean_obj_tag(v_x_778_) == 2)
{
if (lean_obj_tag(v_x_779_) == 2)
{
lean_object* v_l_782_; lean_object* v_r_783_; lean_object* v_l_784_; lean_object* v_r_785_; lean_object* v___x_786_; 
lean_dec(v_h__2_781_);
v_l_782_ = lean_ctor_get(v_x_778_, 0);
lean_inc(v_l_782_);
v_r_783_ = lean_ctor_get(v_x_778_, 1);
lean_inc(v_r_783_);
lean_dec_ref_known(v_x_778_, 2);
v_l_784_ = lean_ctor_get(v_x_779_, 0);
lean_inc(v_l_784_);
v_r_785_ = lean_ctor_get(v_x_779_, 1);
lean_inc(v_r_785_);
lean_dec_ref_known(v_x_779_, 2);
v___x_786_ = lean_apply_6(v_h__1_780_, v_l_782_, v_r_783_, v_l_784_, v_r_785_, lean_box(0), lean_box(0));
return v___x_786_;
}
else
{
lean_object* v___x_787_; 
lean_dec(v_h__1_780_);
v___x_787_ = lean_apply_5(v_h__2_781_, v_x_778_, v_x_779_, lean_box(0), lean_box(0), lean_box(0));
return v___x_787_;
}
}
else
{
lean_object* v___x_788_; 
lean_dec(v_h__1_780_);
v___x_788_ = lean_apply_5(v_h__2_781_, v_x_778_, v_x_779_, lean_box(0), lean_box(0), lean_box(0));
return v___x_788_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_match__1_splitter(lean_object* v_motive_789_, lean_object* v_x_790_, lean_object* v_x_791_, lean_object* v_h__1_792_, lean_object* v_h__2_793_){
_start:
{
if (lean_obj_tag(v_x_790_) == 2)
{
if (lean_obj_tag(v_x_791_) == 2)
{
lean_object* v_l_794_; lean_object* v_r_795_; lean_object* v_l_796_; lean_object* v_r_797_; lean_object* v___x_798_; 
lean_dec(v_h__2_793_);
v_l_794_ = lean_ctor_get(v_x_790_, 0);
lean_inc(v_l_794_);
v_r_795_ = lean_ctor_get(v_x_790_, 1);
lean_inc(v_r_795_);
lean_dec_ref_known(v_x_790_, 2);
v_l_796_ = lean_ctor_get(v_x_791_, 0);
lean_inc(v_l_796_);
v_r_797_ = lean_ctor_get(v_x_791_, 1);
lean_inc(v_r_797_);
lean_dec_ref_known(v_x_791_, 2);
v___x_798_ = lean_apply_6(v_h__1_792_, v_l_794_, v_r_795_, v_l_796_, v_r_797_, lean_box(0), lean_box(0));
return v___x_798_;
}
else
{
lean_object* v___x_799_; 
lean_dec(v_h__1_792_);
v___x_799_ = lean_apply_5(v_h__2_793_, v_x_790_, v_x_791_, lean_box(0), lean_box(0), lean_box(0));
return v___x_799_;
}
}
else
{
lean_object* v___x_800_; 
lean_dec(v_h__1_792_);
v___x_800_ = lean_apply_5(v_h__2_793_, v_x_790_, v_x_791_, lean_box(0), lean_box(0), lean_box(0));
return v___x_800_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(lean_object* v_aig_801_, lean_object* v_upper_802_, lean_object* v_state_803_){
_start:
{
lean_object* v_cache_804_; lean_object* v___x_805_; uint8_t v___x_806_; 
v_cache_804_ = lean_ctor_get(v_state_803_, 1);
v___x_805_ = lean_array_fget_borrowed(v_cache_804_, v_upper_802_);
v___x_806_ = lean_unbox(v___x_805_);
if (v___x_806_ == 0)
{
lean_object* v_decls_807_; lean_object* v_decl_808_; 
v_decls_807_ = lean_ctor_get(v_aig_801_, 0);
v_decl_808_ = lean_array_fget_borrowed(v_decls_807_, v_upper_802_);
switch(lean_obj_tag(v_decl_808_))
{
case 0:
{
lean_object* v___x_809_; 
v___x_809_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___redArg(v_state_803_, v_upper_802_);
return v___x_809_;
}
case 1:
{
lean_object* v_idx_810_; lean_object* v___x_811_; 
v_idx_810_ = lean_ctor_get(v_decl_808_, 0);
v___x_811_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg(v_aig_801_, v_idx_810_, v_state_803_, v_upper_802_);
return v___x_811_;
}
default: 
{
lean_object* v_l_812_; lean_object* v_r_813_; lean_object* v___x_814_; 
v_l_812_ = lean_ctor_get(v_decl_808_, 0);
v_r_813_ = lean_ctor_get(v_decl_808_, 1);
v___x_814_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___redArg(v_aig_801_, v_upper_802_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v_val_817_; lean_object* v___x_818_; lean_object* v_val_819_; lean_object* v_val_820_; 
v___x_815_ = lean_unsigned_to_nat(1u);
v___x_816_ = lean_nat_shiftr(v_l_812_, v___x_815_);
v_val_817_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(v_aig_801_, v___x_816_, v_state_803_);
v___x_818_ = lean_nat_shiftr(v_r_813_, v___x_815_);
v_val_819_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(v_aig_801_, v___x_818_, v_val_817_);
v_val_820_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg(v_l_812_, v_r_813_, v_val_819_, v_upper_802_);
return v_val_820_;
}
else
{
lean_object* v_val_821_; lean_object* v_snd_822_; lean_object* v_fst_823_; lean_object* v_fst_824_; lean_object* v_snd_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v_val_828_; lean_object* v___x_829_; lean_object* v_val_830_; lean_object* v___x_831_; lean_object* v_val_832_; lean_object* v_val_833_; 
v_val_821_ = lean_ctor_get(v___x_814_, 0);
lean_inc(v_val_821_);
lean_dec_ref_known(v___x_814_, 1);
v_snd_822_ = lean_ctor_get(v_val_821_, 1);
lean_inc(v_snd_822_);
v_fst_823_ = lean_ctor_get(v_val_821_, 0);
lean_inc(v_fst_823_);
lean_dec(v_val_821_);
v_fst_824_ = lean_ctor_get(v_snd_822_, 0);
lean_inc(v_fst_824_);
v_snd_825_ = lean_ctor_get(v_snd_822_, 1);
lean_inc(v_snd_825_);
lean_dec(v_snd_822_);
v___x_826_ = lean_unsigned_to_nat(1u);
v___x_827_ = lean_nat_shiftr(v_fst_823_, v___x_826_);
v_val_828_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(v_aig_801_, v___x_827_, v_state_803_);
v___x_829_ = lean_nat_shiftr(v_fst_824_, v___x_826_);
v_val_830_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(v_aig_801_, v___x_829_, v_val_828_);
v___x_831_ = lean_nat_shiftr(v_snd_825_, v___x_826_);
v_val_832_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(v_aig_801_, v___x_831_, v_val_830_);
v_val_833_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___redArg(v_val_832_, v_fst_823_, v_fst_824_, v_snd_825_, v_upper_802_);
lean_dec(v_snd_825_);
lean_dec(v_fst_824_);
lean_dec(v_fst_823_);
return v_val_833_;
}
}
}
}
else
{
lean_dec(v_upper_802_);
return v_state_803_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg___boxed(lean_object* v_aig_834_, lean_object* v_upper_835_, lean_object* v_state_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(v_aig_834_, v_upper_835_, v_state_836_);
lean_dec_ref(v_aig_834_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go(lean_object* v_aig_838_, lean_object* v_upper_839_, lean_object* v_h_840_, lean_object* v_state_841_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(v_aig_838_, v_upper_839_, v_state_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___boxed(lean_object* v_aig_843_, lean_object* v_upper_844_, lean_object* v_h_845_, lean_object* v_state_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go(v_aig_843_, v_upper_844_, v_h_845_, v_state_846_);
lean_dec_ref(v_aig_843_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go_match__103_splitter___redArg(lean_object* v_decl_848_, lean_object* v_h__1_849_, lean_object* v_h__2_850_, lean_object* v_h__3_851_){
_start:
{
switch(lean_obj_tag(v_decl_848_))
{
case 0:
{
lean_object* v___x_852_; 
lean_dec(v_h__3_851_);
lean_dec(v_h__2_850_);
v___x_852_ = lean_apply_1(v_h__1_849_, lean_box(0));
return v___x_852_;
}
case 1:
{
lean_object* v_idx_853_; lean_object* v___x_854_; 
lean_dec(v_h__3_851_);
lean_dec(v_h__1_849_);
v_idx_853_ = lean_ctor_get(v_decl_848_, 0);
lean_inc(v_idx_853_);
lean_dec_ref_known(v_decl_848_, 1);
v___x_854_ = lean_apply_2(v_h__2_850_, v_idx_853_, lean_box(0));
return v___x_854_;
}
default: 
{
lean_object* v_l_855_; lean_object* v_r_856_; lean_object* v___x_857_; 
lean_dec(v_h__2_850_);
lean_dec(v_h__1_849_);
v_l_855_ = lean_ctor_get(v_decl_848_, 0);
lean_inc(v_l_855_);
v_r_856_ = lean_ctor_get(v_decl_848_, 1);
lean_inc(v_r_856_);
lean_dec_ref_known(v_decl_848_, 2);
v___x_857_ = lean_apply_3(v_h__3_851_, v_l_855_, v_r_856_, lean_box(0));
return v___x_857_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go_match__103_splitter(lean_object* v_motive_858_, lean_object* v_decl_859_, lean_object* v_h__1_860_, lean_object* v_h__2_861_, lean_object* v_h__3_862_){
_start:
{
switch(lean_obj_tag(v_decl_859_))
{
case 0:
{
lean_object* v___x_863_; 
lean_dec(v_h__3_862_);
lean_dec(v_h__2_861_);
v___x_863_ = lean_apply_1(v_h__1_860_, lean_box(0));
return v___x_863_;
}
case 1:
{
lean_object* v_idx_864_; lean_object* v___x_865_; 
lean_dec(v_h__3_862_);
lean_dec(v_h__1_860_);
v_idx_864_ = lean_ctor_get(v_decl_859_, 0);
lean_inc(v_idx_864_);
lean_dec_ref_known(v_decl_859_, 1);
v___x_865_ = lean_apply_2(v_h__2_861_, v_idx_864_, lean_box(0));
return v___x_865_;
}
default: 
{
lean_object* v_l_866_; lean_object* v_r_867_; lean_object* v___x_868_; 
lean_dec(v_h__2_861_);
lean_dec(v_h__1_860_);
v_l_866_ = lean_ctor_get(v_decl_859_, 0);
lean_inc(v_l_866_);
v_r_867_ = lean_ctor_get(v_decl_859_, 1);
lean_inc(v_r_867_);
lean_dec_ref_known(v_decl_859_, 2);
v___x_868_ = lean_apply_3(v_h__3_862_, v_l_866_, v_r_867_, lean_box(0));
return v___x_868_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go_match__81_splitter___redArg(lean_object* v_x_869_, lean_object* v_h__1_870_, lean_object* v_h__2_871_){
_start:
{
if (lean_obj_tag(v_x_869_) == 0)
{
lean_object* v___x_872_; 
lean_dec(v_h__1_870_);
v___x_872_ = lean_apply_1(v_h__2_871_, lean_box(0));
return v___x_872_;
}
else
{
lean_object* v_val_873_; lean_object* v_snd_874_; lean_object* v_fst_875_; lean_object* v_fst_876_; lean_object* v_snd_877_; lean_object* v___x_878_; 
lean_dec(v_h__2_871_);
v_val_873_ = lean_ctor_get(v_x_869_, 0);
lean_inc(v_val_873_);
lean_dec_ref_known(v_x_869_, 1);
v_snd_874_ = lean_ctor_get(v_val_873_, 1);
lean_inc(v_snd_874_);
v_fst_875_ = lean_ctor_get(v_val_873_, 0);
lean_inc(v_fst_875_);
lean_dec(v_val_873_);
v_fst_876_ = lean_ctor_get(v_snd_874_, 0);
lean_inc(v_fst_876_);
v_snd_877_ = lean_ctor_get(v_snd_874_, 1);
lean_inc(v_snd_877_);
lean_dec(v_snd_874_);
v___x_878_ = lean_apply_4(v_h__1_870_, v_fst_875_, v_fst_876_, v_snd_877_, lean_box(0));
return v___x_878_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go_match__81_splitter(lean_object* v_motive_879_, lean_object* v_x_880_, lean_object* v_h__1_881_, lean_object* v_h__2_882_){
_start:
{
if (lean_obj_tag(v_x_880_) == 0)
{
lean_object* v___x_883_; 
lean_dec(v_h__1_881_);
v___x_883_ = lean_apply_1(v_h__2_882_, lean_box(0));
return v___x_883_;
}
else
{
lean_object* v_val_884_; lean_object* v_snd_885_; lean_object* v_fst_886_; lean_object* v_fst_887_; lean_object* v_snd_888_; lean_object* v___x_889_; 
lean_dec(v_h__2_882_);
v_val_884_ = lean_ctor_get(v_x_880_, 0);
lean_inc(v_val_884_);
lean_dec_ref_known(v_x_880_, 1);
v_snd_885_ = lean_ctor_get(v_val_884_, 1);
lean_inc(v_snd_885_);
v_fst_886_ = lean_ctor_get(v_val_884_, 0);
lean_inc(v_fst_886_);
lean_dec(v_val_884_);
v_fst_887_ = lean_ctor_get(v_snd_885_, 0);
lean_inc(v_fst_887_);
v_snd_888_ = lean_ctor_get(v_snd_885_, 1);
lean_inc(v_snd_888_);
lean_dec(v_snd_885_);
v___x_889_ = lean_apply_4(v_h__1_881_, v_fst_886_, v_fst_887_, v_snd_888_, lean_box(0));
return v___x_889_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__52_splitter___redArg(lean_object* v_x_890_, lean_object* v_h__1_891_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = lean_apply_2(v_h__1_891_, v_x_890_, lean_box(0));
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__52_splitter(lean_object* v_aig_893_, lean_object* v_upper_894_, lean_object* v_h_895_, lean_object* v_state_896_, lean_object* v_cond_897_, lean_object* v_ifTrue_898_, lean_object* v_ifFalse_899_, lean_object* v_hltc_900_, lean_object* v_motive_901_, lean_object* v_x_902_, lean_object* v_h__1_903_){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = lean_apply_2(v_h__1_903_, v_x_902_, lean_box(0));
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__52_splitter___boxed(lean_object* v_aig_905_, lean_object* v_upper_906_, lean_object* v_h_907_, lean_object* v_state_908_, lean_object* v_cond_909_, lean_object* v_ifTrue_910_, lean_object* v_ifFalse_911_, lean_object* v_hltc_912_, lean_object* v_motive_913_, lean_object* v_x_914_, lean_object* v_h__1_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__52_splitter(v_aig_905_, v_upper_906_, v_h_907_, v_state_908_, v_cond_909_, v_ifTrue_910_, v_ifFalse_911_, v_hltc_912_, v_motive_913_, v_x_914_, v_h__1_915_);
lean_dec(v_ifFalse_911_);
lean_dec(v_ifTrue_910_);
lean_dec(v_cond_909_);
lean_dec_ref(v_state_908_);
lean_dec(v_upper_906_);
lean_dec_ref(v_aig_905_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__50_splitter___redArg(lean_object* v_x_917_, lean_object* v_h__1_918_){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = lean_apply_2(v_h__1_918_, v_x_917_, lean_box(0));
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__50_splitter(lean_object* v_aig_920_, lean_object* v_upper_921_, lean_object* v_h_922_, lean_object* v_cond_923_, lean_object* v_ifTrue_924_, lean_object* v_ifFalse_925_, lean_object* v_hltt_926_, lean_object* v_cstate_927_, lean_object* v_motive_928_, lean_object* v_x_929_, lean_object* v_h__1_930_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = lean_apply_2(v_h__1_930_, v_x_929_, lean_box(0));
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__50_splitter___boxed(lean_object* v_aig_932_, lean_object* v_upper_933_, lean_object* v_h_934_, lean_object* v_cond_935_, lean_object* v_ifTrue_936_, lean_object* v_ifFalse_937_, lean_object* v_hltt_938_, lean_object* v_cstate_939_, lean_object* v_motive_940_, lean_object* v_x_941_, lean_object* v_h__1_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__50_splitter(v_aig_932_, v_upper_933_, v_h_934_, v_cond_935_, v_ifTrue_936_, v_ifFalse_937_, v_hltt_938_, v_cstate_939_, v_motive_940_, v_x_941_, v_h__1_942_);
lean_dec_ref(v_cstate_939_);
lean_dec(v_ifFalse_937_);
lean_dec(v_ifTrue_936_);
lean_dec(v_cond_935_);
lean_dec(v_upper_933_);
lean_dec_ref(v_aig_932_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__48_splitter___redArg(lean_object* v_x_944_, lean_object* v_h__1_945_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = lean_apply_2(v_h__1_945_, v_x_944_, lean_box(0));
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__48_splitter(lean_object* v_aig_947_, lean_object* v_upper_948_, lean_object* v_h_949_, lean_object* v_cond_950_, lean_object* v_ifTrue_951_, lean_object* v_ifFalse_952_, lean_object* v_hltf_953_, lean_object* v_tstate_954_, lean_object* v_motive_955_, lean_object* v_x_956_, lean_object* v_h__1_957_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = lean_apply_2(v_h__1_957_, v_x_956_, lean_box(0));
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__48_splitter___boxed(lean_object* v_aig_959_, lean_object* v_upper_960_, lean_object* v_h_961_, lean_object* v_cond_962_, lean_object* v_ifTrue_963_, lean_object* v_ifFalse_964_, lean_object* v_hltf_965_, lean_object* v_tstate_966_, lean_object* v_motive_967_, lean_object* v_x_968_, lean_object* v_h__1_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__48_splitter(v_aig_959_, v_upper_960_, v_h_961_, v_cond_962_, v_ifTrue_963_, v_ifFalse_964_, v_hltf_965_, v_tstate_966_, v_motive_967_, v_x_968_, v_h__1_969_);
lean_dec_ref(v_tstate_966_);
lean_dec(v_ifFalse_964_);
lean_dec(v_ifTrue_963_);
lean_dec(v_cond_962_);
lean_dec(v_upper_960_);
lean_dec_ref(v_aig_959_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__45_splitter___redArg(lean_object* v_x_971_, lean_object* v_h__1_972_){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = lean_apply_2(v_h__1_972_, v_x_971_, lean_box(0));
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__45_splitter(lean_object* v_aig_974_, lean_object* v_upper_975_, lean_object* v_h_976_, lean_object* v_fstate_977_, lean_object* v_motive_978_, lean_object* v_x_979_, lean_object* v_h__1_980_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = lean_apply_2(v_h__1_980_, v_x_979_, lean_box(0));
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__45_splitter___boxed(lean_object* v_aig_982_, lean_object* v_upper_983_, lean_object* v_h_984_, lean_object* v_fstate_985_, lean_object* v_motive_986_, lean_object* v_x_987_, lean_object* v_h__1_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__45_splitter(v_aig_982_, v_upper_983_, v_h_984_, v_fstate_985_, v_motive_986_, v_x_987_, v_h__1_988_);
lean_dec_ref(v_fstate_985_);
lean_dec(v_upper_983_);
lean_dec_ref(v_aig_982_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__56_splitter___redArg(lean_object* v_x_990_, lean_object* v_h__1_991_){
_start:
{
lean_object* v___x_992_; 
v___x_992_ = lean_apply_2(v_h__1_991_, v_x_990_, lean_box(0));
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__56_splitter(lean_object* v_aig_993_, lean_object* v_upper_994_, lean_object* v_h_995_, lean_object* v_state_996_, lean_object* v_lhs_997_, lean_object* v_rhs_998_, lean_object* v_this_999_, lean_object* v_motive_1000_, lean_object* v_x_1001_, lean_object* v_h__1_1002_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = lean_apply_2(v_h__1_1002_, v_x_1001_, lean_box(0));
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__56_splitter___boxed(lean_object* v_aig_1004_, lean_object* v_upper_1005_, lean_object* v_h_1006_, lean_object* v_state_1007_, lean_object* v_lhs_1008_, lean_object* v_rhs_1009_, lean_object* v_this_1010_, lean_object* v_motive_1011_, lean_object* v_x_1012_, lean_object* v_h__1_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__56_splitter(v_aig_1004_, v_upper_1005_, v_h_1006_, v_state_1007_, v_lhs_1008_, v_rhs_1009_, v_this_1010_, v_motive_1011_, v_x_1012_, v_h__1_1013_);
lean_dec(v_rhs_1009_);
lean_dec(v_lhs_1008_);
lean_dec_ref(v_state_1007_);
lean_dec(v_upper_1005_);
lean_dec_ref(v_aig_1004_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__54_splitter___redArg(lean_object* v_x_1015_, lean_object* v_h__1_1016_){
_start:
{
lean_object* v___x_1017_; 
v___x_1017_ = lean_apply_2(v_h__1_1016_, v_x_1015_, lean_box(0));
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__54_splitter(lean_object* v_aig_1018_, lean_object* v_upper_1019_, lean_object* v_h_1020_, lean_object* v_lhs_1021_, lean_object* v_rhs_1022_, lean_object* v_this_1023_, lean_object* v_lstate_1024_, lean_object* v_motive_1025_, lean_object* v_x_1026_, lean_object* v_h__1_1027_){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = lean_apply_2(v_h__1_1027_, v_x_1026_, lean_box(0));
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__54_splitter___boxed(lean_object* v_aig_1029_, lean_object* v_upper_1030_, lean_object* v_h_1031_, lean_object* v_lhs_1032_, lean_object* v_rhs_1033_, lean_object* v_this_1034_, lean_object* v_lstate_1035_, lean_object* v_motive_1036_, lean_object* v_x_1037_, lean_object* v_h__1_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__54_splitter(v_aig_1029_, v_upper_1030_, v_h_1031_, v_lhs_1032_, v_rhs_1033_, v_this_1034_, v_lstate_1035_, v_motive_1036_, v_x_1037_, v_h__1_1038_);
lean_dec_ref(v_lstate_1035_);
lean_dec(v_rhs_1033_);
lean_dec(v_lhs_1032_);
lean_dec(v_upper_1030_);
lean_dec_ref(v_aig_1029_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF(lean_object* v_entry_1042_){
_start:
{
lean_object* v_ref_1043_; lean_object* v_aig_1044_; lean_object* v_gate_1045_; uint8_t v_invert_1046_; lean_object* v___x_1047_; lean_object* v_val_1048_; lean_object* v_cnf_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1067_; 
v_ref_1043_ = lean_ctor_get(v_entry_1042_, 1);
lean_inc_ref(v_ref_1043_);
v_aig_1044_ = lean_ctor_get(v_entry_1042_, 0);
lean_inc_ref_n(v_aig_1044_, 2);
lean_dec_ref(v_entry_1042_);
v_gate_1045_ = lean_ctor_get(v_ref_1043_, 0);
lean_inc_n(v_gate_1045_, 2);
v_invert_1046_ = lean_ctor_get_uint8(v_ref_1043_, sizeof(void*)*1);
lean_dec_ref(v_ref_1043_);
v___x_1047_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty(v_aig_1044_);
v_val_1048_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(v_aig_1044_, v_gate_1045_, v___x_1047_);
lean_dec_ref(v_aig_1044_);
v_cnf_1049_ = lean_ctor_get(v_val_1048_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v_val_1048_);
if (v_isSharedCheck_1067_ == 0)
{
lean_object* v_unused_1068_; 
v_unused_1068_ = lean_ctor_get(v_val_1048_, 1);
lean_dec(v_unused_1068_);
v___x_1051_ = v_val_1048_;
v_isShared_1052_ = v_isSharedCheck_1067_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_cnf_1049_);
lean_dec(v_val_1048_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1067_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___y_1056_; uint8_t v___y_1057_; 
v___x_1053_ = ((lean_object*)(l_Std_Sat_AIG_toCNF___closed__0));
v___x_1054_ = l_ByteArray_empty;
if (v_invert_1046_ == 0)
{
lean_object* v___x_1063_; uint8_t v___x_1064_; 
v___x_1063_ = lean_array_push(v___x_1053_, v_gate_1045_);
v___x_1064_ = 1;
v___y_1056_ = v___x_1063_;
v___y_1057_ = v___x_1064_;
goto v___jp_1055_;
}
else
{
lean_object* v___x_1065_; uint8_t v___x_1066_; 
v___x_1065_ = lean_array_push(v___x_1053_, v_gate_1045_);
v___x_1066_ = 0;
v___y_1056_ = v___x_1065_;
v___y_1057_ = v___x_1066_;
goto v___jp_1055_;
}
v___jp_1055_:
{
lean_object* v___x_1058_; lean_object* v___x_1060_; 
v___x_1058_ = lean_byte_array_push(v___x_1054_, v___y_1057_);
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 1, v___x_1058_);
lean_ctor_set(v___x_1051_, 0, v___y_1056_);
v___x_1060_ = v___x_1051_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___y_1056_);
lean_ctor_set(v_reuseFailAlloc_1062_, 1, v___x_1058_);
v___x_1060_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
lean_object* v___x_1061_; 
v___x_1061_ = lean_array_push(v_cnf_1049_, v___x_1060_);
return v___x_1061_;
}
}
}
}
}
lean_object* runtime_initialize_Std_Sat_CNF(uint8_t builtin);
lean_object* runtime_initialize_Std_Sat_AIG_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sat_AIG_CNF(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Sat_CNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_AIG_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Sat_AIG_CNF(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Sat_CNF(uint8_t builtin);
lean_object* initialize_Std_Sat_AIG_Lemmas(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_AIG_CNF(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_CNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_AIG_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_AIG_CNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sat_AIG_CNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sat_AIG_CNF(builtin);
}
#ifdef __cplusplus
}
#endif
