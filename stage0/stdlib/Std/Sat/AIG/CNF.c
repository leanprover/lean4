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
lean_object* lean_array_push(lean_object*, lean_object*);
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
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Bool_toNat(uint8_t);
lean_object* lean_nat_lxor(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
uint8_t l_Std_Sat_CNF_eval___redArg(lean_object*, lean_object*);
uint8_t l_Std_Sat_AIG_denote_go___redArg(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__0 = (const lean_object*)&l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg(lean_object* v_output_3_){
_start:
{
uint8_t v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_4_ = 0;
v___x_5_ = lean_box(v___x_4_);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v_output_3_);
lean_ctor_set(v___x_6_, 1, v___x_5_);
v___x_7_ = lean_box(0);
v___x_8_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_8_, 0, v___x_6_);
lean_ctor_set(v___x_8_, 1, v___x_7_);
v___x_9_ = ((lean_object*)(l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__0));
v___x_10_ = lean_array_push(v___x_9_, v___x_8_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF(lean_object* v_00_u03b1_11_, lean_object* v_output_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg(v_output_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF___redArg(lean_object* v_output_14_, lean_object* v_atom_15_){
_start:
{
uint8_t v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; uint8_t v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_16_ = 0;
v___x_17_ = lean_box(v___x_16_);
lean_inc(v_output_14_);
v___x_18_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_18_, 0, v_output_14_);
lean_ctor_set(v___x_18_, 1, v___x_17_);
v___x_19_ = 1;
v___x_20_ = lean_box(v___x_19_);
lean_inc(v_atom_15_);
v___x_21_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_21_, 0, v_atom_15_);
lean_ctor_set(v___x_21_, 1, v___x_20_);
v___x_22_ = lean_box(0);
v___x_23_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_23_, 0, v___x_21_);
lean_ctor_set(v___x_23_, 1, v___x_22_);
v___x_24_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_24_, 0, v___x_18_);
lean_ctor_set(v___x_24_, 1, v___x_23_);
v___x_25_ = lean_box(v___x_19_);
v___x_26_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_26_, 0, v_output_14_);
lean_ctor_set(v___x_26_, 1, v___x_25_);
v___x_27_ = lean_box(v___x_16_);
v___x_28_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_28_, 0, v_atom_15_);
lean_ctor_set(v___x_28_, 1, v___x_27_);
v___x_29_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
lean_ctor_set(v___x_29_, 1, v___x_22_);
v___x_30_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_30_, 0, v___x_26_);
lean_ctor_set(v___x_30_, 1, v___x_29_);
v___x_31_ = ((lean_object*)(l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__0));
v___x_32_ = lean_array_push(v___x_31_, v___x_30_);
v___x_33_ = lean_array_push(v___x_32_, v___x_24_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF(lean_object* v_00_u03b1_34_, lean_object* v_output_35_, lean_object* v_atom_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF___redArg(v_output_35_, v_atom_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg(lean_object* v_output_38_, lean_object* v_lhs_39_, lean_object* v_rhs_40_, uint8_t v_linv_41_, uint8_t v_rinv_42_){
_start:
{
uint8_t v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; uint8_t v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___y_58_; uint8_t v___y_59_; uint8_t v___y_69_; 
v___x_43_ = 1;
v___x_44_ = lean_box(v___x_43_);
lean_inc(v_output_38_);
v___x_45_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_45_, 0, v_output_38_);
lean_ctor_set(v___x_45_, 1, v___x_44_);
v___x_46_ = lean_box(v_linv_41_);
lean_inc(v_lhs_39_);
v___x_47_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_47_, 0, v_lhs_39_);
lean_ctor_set(v___x_47_, 1, v___x_46_);
v___x_48_ = lean_box(v_rinv_42_);
lean_inc(v_rhs_40_);
v___x_49_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_49_, 0, v_rhs_40_);
lean_ctor_set(v___x_49_, 1, v___x_48_);
v___x_50_ = lean_box(0);
v___x_51_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_51_, 0, v___x_49_);
lean_ctor_set(v___x_51_, 1, v___x_50_);
v___x_52_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_52_, 0, v___x_47_);
lean_ctor_set(v___x_52_, 1, v___x_51_);
v___x_53_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_53_, 0, v___x_45_);
lean_ctor_set(v___x_53_, 1, v___x_52_);
v___x_54_ = 0;
v___x_55_ = lean_box(v___x_54_);
v___x_56_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_56_, 0, v_output_38_);
lean_ctor_set(v___x_56_, 1, v___x_55_);
if (v_rinv_42_ == 0)
{
v___y_69_ = v___x_43_;
goto v___jp_68_;
}
else
{
v___y_69_ = v___x_54_;
goto v___jp_68_;
}
v___jp_57_:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_60_ = lean_box(v___y_59_);
v___x_61_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_61_, 0, v_lhs_39_);
lean_ctor_set(v___x_61_, 1, v___x_60_);
v___x_62_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v___x_50_);
v___x_63_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_63_, 0, v___x_56_);
lean_ctor_set(v___x_63_, 1, v___x_62_);
v___x_64_ = ((lean_object*)(l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__0));
v___x_65_ = lean_array_push(v___x_64_, v___x_63_);
v___x_66_ = lean_array_push(v___x_65_, v___y_58_);
v___x_67_ = lean_array_push(v___x_66_, v___x_53_);
return v___x_67_;
}
v___jp_68_:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_70_ = lean_box(v___y_69_);
v___x_71_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_71_, 0, v_rhs_40_);
lean_ctor_set(v___x_71_, 1, v___x_70_);
v___x_72_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
lean_ctor_set(v___x_72_, 1, v___x_50_);
lean_inc_ref(v___x_56_);
v___x_73_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_56_);
lean_ctor_set(v___x_73_, 1, v___x_72_);
if (v_linv_41_ == 0)
{
v___y_58_ = v___x_73_;
v___y_59_ = v___x_43_;
goto v___jp_57_;
}
else
{
v___y_58_ = v___x_73_;
v___y_59_ = v___x_54_;
goto v___jp_57_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg___boxed(lean_object* v_output_74_, lean_object* v_lhs_75_, lean_object* v_rhs_76_, lean_object* v_linv_77_, lean_object* v_rinv_78_){
_start:
{
uint8_t v_linv_boxed_79_; uint8_t v_rinv_boxed_80_; lean_object* v_res_81_; 
v_linv_boxed_79_ = lean_unbox(v_linv_77_);
v_rinv_boxed_80_ = lean_unbox(v_rinv_78_);
v_res_81_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg(v_output_74_, v_lhs_75_, v_rhs_76_, v_linv_boxed_79_, v_rinv_boxed_80_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF(lean_object* v_00_u03b1_82_, lean_object* v_output_83_, lean_object* v_lhs_84_, lean_object* v_rhs_85_, uint8_t v_linv_86_, uint8_t v_rinv_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg(v_output_83_, v_lhs_84_, v_rhs_85_, v_linv_86_, v_rinv_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___boxed(lean_object* v_00_u03b1_89_, lean_object* v_output_90_, lean_object* v_lhs_91_, lean_object* v_rhs_92_, lean_object* v_linv_93_, lean_object* v_rinv_94_){
_start:
{
uint8_t v_linv_boxed_95_; uint8_t v_rinv_boxed_96_; lean_object* v_res_97_; 
v_linv_boxed_95_ = lean_unbox(v_linv_93_);
v_rinv_boxed_96_ = lean_unbox(v_rinv_94_);
v_res_97_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF(v_00_u03b1_89_, v_output_90_, v_lhs_91_, v_rhs_92_, v_linv_boxed_95_, v_rinv_boxed_96_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF___redArg(lean_object* v_output_98_, lean_object* v_cond_99_, lean_object* v_ifTrue_100_, lean_object* v_ifFalse_101_, uint8_t v_cinv_102_, uint8_t v_tinv_103_, uint8_t v_finv_104_){
_start:
{
lean_object* v___y_106_; lean_object* v___y_107_; lean_object* v___y_108_; lean_object* v___y_109_; lean_object* v___y_110_; uint8_t v___y_111_; lean_object* v___y_126_; uint8_t v___y_127_; uint8_t v___y_148_; 
if (v_cinv_102_ == 0)
{
uint8_t v___x_153_; 
v___x_153_ = 1;
v___y_148_ = v___x_153_;
goto v___jp_147_;
}
else
{
uint8_t v___x_154_; 
v___x_154_ = 0;
v___y_148_ = v___x_154_;
goto v___jp_147_;
}
v___jp_105_:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_112_ = lean_box(v___y_111_);
lean_inc(v_ifTrue_100_);
v___x_113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_113_, 0, v_ifTrue_100_);
lean_ctor_set(v___x_113_, 1, v___x_112_);
v___x_114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v___y_110_);
lean_inc_ref(v___y_107_);
v___x_115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_115_, 0, v___y_107_);
lean_ctor_set(v___x_115_, 1, v___x_114_);
v___x_116_ = lean_box(v_tinv_103_);
v___x_117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_117_, 0, v_ifTrue_100_);
lean_ctor_set(v___x_117_, 1, v___x_116_);
v___x_118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
lean_ctor_set(v___x_118_, 1, v___y_106_);
v___x_119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_119_, 0, v___y_107_);
lean_ctor_set(v___x_119_, 1, v___x_118_);
v___x_120_ = ((lean_object*)(l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__0));
v___x_121_ = lean_array_push(v___x_120_, v___x_119_);
v___x_122_ = lean_array_push(v___x_121_, v___x_115_);
v___x_123_ = lean_array_push(v___x_122_, v___y_109_);
v___x_124_ = lean_array_push(v___x_123_, v___y_108_);
return v___x_124_;
}
v___jp_125_:
{
lean_object* v___x_128_; lean_object* v___x_129_; uint8_t v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_128_ = lean_box(v___y_127_);
lean_inc(v_ifFalse_101_);
v___x_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_129_, 0, v_ifFalse_101_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
v___x_130_ = 0;
v___x_131_ = lean_box(v___x_130_);
lean_inc(v_output_98_);
v___x_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_132_, 0, v_output_98_);
lean_ctor_set(v___x_132_, 1, v___x_131_);
v___x_133_ = lean_box(0);
v___x_134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_132_);
lean_ctor_set(v___x_134_, 1, v___x_133_);
lean_inc_ref(v___x_134_);
v___x_135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_129_);
lean_ctor_set(v___x_135_, 1, v___x_134_);
lean_inc_ref(v___y_126_);
v___x_136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_136_, 0, v___y_126_);
lean_ctor_set(v___x_136_, 1, v___x_135_);
v___x_137_ = lean_box(v_finv_104_);
v___x_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_138_, 0, v_ifFalse_101_);
lean_ctor_set(v___x_138_, 1, v___x_137_);
v___x_139_ = 1;
v___x_140_ = lean_box(v___x_139_);
v___x_141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_141_, 0, v_output_98_);
lean_ctor_set(v___x_141_, 1, v___x_140_);
v___x_142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
lean_ctor_set(v___x_142_, 1, v___x_133_);
lean_inc_ref(v___x_142_);
v___x_143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_143_, 0, v___x_138_);
lean_ctor_set(v___x_143_, 1, v___x_142_);
v___x_144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_144_, 0, v___y_126_);
lean_ctor_set(v___x_144_, 1, v___x_143_);
v___x_145_ = lean_box(v_cinv_102_);
v___x_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_146_, 0, v_cond_99_);
lean_ctor_set(v___x_146_, 1, v___x_145_);
if (v_tinv_103_ == 0)
{
v___y_106_ = v___x_142_;
v___y_107_ = v___x_146_;
v___y_108_ = v___x_136_;
v___y_109_ = v___x_144_;
v___y_110_ = v___x_134_;
v___y_111_ = v___x_139_;
goto v___jp_105_;
}
else
{
v___y_106_ = v___x_142_;
v___y_107_ = v___x_146_;
v___y_108_ = v___x_136_;
v___y_109_ = v___x_144_;
v___y_110_ = v___x_134_;
v___y_111_ = v___x_130_;
goto v___jp_105_;
}
}
v___jp_147_:
{
lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_149_ = lean_box(v___y_148_);
lean_inc(v_cond_99_);
v___x_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_150_, 0, v_cond_99_);
lean_ctor_set(v___x_150_, 1, v___x_149_);
if (v_finv_104_ == 0)
{
uint8_t v___x_151_; 
v___x_151_ = 1;
v___y_126_ = v___x_150_;
v___y_127_ = v___x_151_;
goto v___jp_125_;
}
else
{
uint8_t v___x_152_; 
v___x_152_ = 0;
v___y_126_ = v___x_150_;
v___y_127_ = v___x_152_;
goto v___jp_125_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF___redArg___boxed(lean_object* v_output_155_, lean_object* v_cond_156_, lean_object* v_ifTrue_157_, lean_object* v_ifFalse_158_, lean_object* v_cinv_159_, lean_object* v_tinv_160_, lean_object* v_finv_161_){
_start:
{
uint8_t v_cinv_boxed_162_; uint8_t v_tinv_boxed_163_; uint8_t v_finv_boxed_164_; lean_object* v_res_165_; 
v_cinv_boxed_162_ = lean_unbox(v_cinv_159_);
v_tinv_boxed_163_ = lean_unbox(v_tinv_160_);
v_finv_boxed_164_ = lean_unbox(v_finv_161_);
v_res_165_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF___redArg(v_output_155_, v_cond_156_, v_ifTrue_157_, v_ifFalse_158_, v_cinv_boxed_162_, v_tinv_boxed_163_, v_finv_boxed_164_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF(lean_object* v_00_u03b1_166_, lean_object* v_output_167_, lean_object* v_cond_168_, lean_object* v_ifTrue_169_, lean_object* v_ifFalse_170_, uint8_t v_cinv_171_, uint8_t v_tinv_172_, uint8_t v_finv_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF___redArg(v_output_167_, v_cond_168_, v_ifTrue_169_, v_ifFalse_170_, v_cinv_171_, v_tinv_172_, v_finv_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF___boxed(lean_object* v_00_u03b1_175_, lean_object* v_output_176_, lean_object* v_cond_177_, lean_object* v_ifTrue_178_, lean_object* v_ifFalse_179_, lean_object* v_cinv_180_, lean_object* v_tinv_181_, lean_object* v_finv_182_){
_start:
{
uint8_t v_cinv_boxed_183_; uint8_t v_tinv_boxed_184_; uint8_t v_finv_boxed_185_; lean_object* v_res_186_; 
v_cinv_boxed_183_ = lean_unbox(v_cinv_180_);
v_tinv_boxed_184_ = lean_unbox(v_tinv_181_);
v_finv_boxed_185_ = lean_unbox(v_finv_182_);
v_res_186_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF(v_00_u03b1_175_, v_output_176_, v_cond_177_, v_ifTrue_178_, v_ifFalse_179_, v_cinv_boxed_183_, v_tinv_boxed_184_, v_finv_boxed_185_);
return v_res_186_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_mixAssigns(lean_object* v_aig_187_, lean_object* v_assign1_188_, lean_object* v_assign2_189_, lean_object* v_var_190_){
_start:
{
lean_object* v_decls_191_; lean_object* v___x_192_; uint8_t v___x_193_; 
v_decls_191_ = lean_ctor_get(v_aig_187_, 0);
v___x_192_ = lean_array_get_size(v_decls_191_);
v___x_193_ = lean_nat_dec_lt(v_var_190_, v___x_192_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; lean_object* v___x_195_; uint8_t v___x_196_; 
lean_dec_ref(v_assign2_189_);
v___x_194_ = lean_nat_sub(v_var_190_, v___x_192_);
lean_dec(v_var_190_);
v___x_195_ = lean_apply_1(v_assign1_188_, v___x_194_);
v___x_196_ = lean_unbox(v___x_195_);
return v___x_196_;
}
else
{
lean_object* v___x_197_; uint8_t v___x_198_; 
lean_dec_ref(v_assign1_188_);
v___x_197_ = lean_apply_1(v_assign2_189_, v_var_190_);
v___x_198_ = lean_unbox(v___x_197_);
return v___x_198_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_mixAssigns___boxed(lean_object* v_aig_199_, lean_object* v_assign1_200_, lean_object* v_assign2_201_, lean_object* v_var_202_){
_start:
{
uint8_t v_res_203_; lean_object* v_r_204_; 
v_res_203_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_mixAssigns(v_aig_199_, v_assign1_200_, v_assign2_201_, v_var_202_);
lean_dec_ref(v_aig_199_);
v_r_204_ = lean_box(v_res_203_);
return v_r_204_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign(lean_object* v_aig_205_, lean_object* v_assign_206_, lean_object* v_var_207_){
_start:
{
lean_object* v_decls_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; uint8_t v___x_212_; 
v_decls_208_ = lean_ctor_get(v_aig_205_, 0);
v___x_209_ = lean_array_get_size(v_decls_208_);
v___x_210_ = lean_nat_add(v_var_207_, v___x_209_);
v___x_211_ = lean_apply_1(v_assign_206_, v___x_210_);
v___x_212_ = lean_unbox(v___x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign___boxed(lean_object* v_aig_213_, lean_object* v_assign_214_, lean_object* v_var_215_){
_start:
{
uint8_t v_res_216_; lean_object* v_r_217_; 
v_res_216_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign(v_aig_213_, v_assign_214_, v_var_215_);
lean_dec(v_var_215_);
lean_dec_ref(v_aig_213_);
v_r_217_ = lean_box(v_res_216_);
return v_r_217_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectRightAssign(lean_object* v_assign_218_, lean_object* v_idx_219_){
_start:
{
lean_object* v___x_220_; uint8_t v___x_221_; 
v___x_220_ = lean_apply_1(v_assign_218_, v_idx_219_);
v___x_221_ = lean_unbox(v___x_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectRightAssign___boxed(lean_object* v_assign_222_, lean_object* v_idx_223_){
_start:
{
uint8_t v_res_224_; lean_object* v_r_225_; 
v_res_224_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectRightAssign(v_assign_222_, v_idx_223_);
v_r_225_ = lean_box(v_res_224_);
return v_r_225_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment_spec__0(lean_object* v_assign_226_, lean_object* v_entry_227_){
_start:
{
uint8_t v___y_229_; lean_object* v_ref_232_; lean_object* v_aig_233_; lean_object* v_gate_234_; uint8_t v_invert_235_; lean_object* v_decls_236_; uint8_t v___x_237_; 
v_ref_232_ = lean_ctor_get(v_entry_227_, 1);
v_aig_233_ = lean_ctor_get(v_entry_227_, 0);
v_gate_234_ = lean_ctor_get(v_ref_232_, 0);
v_invert_235_ = lean_ctor_get_uint8(v_ref_232_, sizeof(void*)*1);
v_decls_236_ = lean_ctor_get(v_aig_233_, 0);
v___x_237_ = l_Std_Sat_AIG_denote_go___redArg(v_gate_234_, v_decls_236_, v_assign_226_);
if (v___x_237_ == 0)
{
if (v_invert_235_ == 0)
{
return v_invert_235_;
}
else
{
v___y_229_ = v___x_237_;
goto v___jp_228_;
}
}
else
{
v___y_229_ = v_invert_235_;
goto v___jp_228_;
}
v___jp_228_:
{
if (v___y_229_ == 0)
{
uint8_t v___x_230_; 
v___x_230_ = 1;
return v___x_230_;
}
else
{
uint8_t v___x_231_; 
v___x_231_ = 0;
return v___x_231_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment_spec__0___boxed(lean_object* v_assign_238_, lean_object* v_entry_239_){
_start:
{
uint8_t v_res_240_; lean_object* v_r_241_; 
v_res_240_ = l_Std_Sat_AIG_denote___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment_spec__0(v_assign_238_, v_entry_239_);
lean_dec_ref(v_entry_239_);
v_r_241_ = lean_box(v_res_240_);
return v_r_241_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___lam__0(lean_object* v_aig_242_, lean_object* v_assign1_243_, lean_object* v_idx_244_){
_start:
{
uint8_t v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v___x_245_ = 0;
v___x_246_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_246_, 0, v_idx_244_);
lean_ctor_set_uint8(v___x_246_, sizeof(void*)*1, v___x_245_);
v___x_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_247_, 0, v_aig_242_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
v___x_248_ = l_Std_Sat_AIG_denote___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment_spec__0(v_assign1_243_, v___x_247_);
lean_dec_ref_known(v___x_247_, 2);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___lam__0___boxed(lean_object* v_aig_249_, lean_object* v_assign1_250_, lean_object* v_idx_251_){
_start:
{
uint8_t v_res_252_; lean_object* v_r_253_; 
v_res_252_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___lam__0(v_aig_249_, v_assign1_250_, v_idx_251_);
v_r_253_ = lean_box(v_res_252_);
return v_r_253_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment(lean_object* v_aig_254_, lean_object* v_assign1_255_, lean_object* v_var_256_){
_start:
{
lean_object* v___f_257_; uint8_t v___x_258_; 
lean_inc_ref(v_assign1_255_);
lean_inc_ref(v_aig_254_);
v___f_257_ = lean_alloc_closure((void*)(l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___lam__0___boxed), 3, 2);
lean_closure_set(v___f_257_, 0, v_aig_254_);
lean_closure_set(v___f_257_, 1, v_assign1_255_);
v___x_258_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_mixAssigns(v_aig_254_, v_assign1_255_, v___f_257_, v_var_256_);
lean_dec_ref(v_aig_254_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___boxed(lean_object* v_aig_259_, lean_object* v_assign1_260_, lean_object* v_var_261_){
_start:
{
uint8_t v_res_262_; lean_object* v_r_263_; 
v_res_262_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment(v_aig_259_, v_assign1_260_, v_var_261_);
v_r_263_ = lean_box(v_res_262_);
return v_r_263_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init(lean_object* v_aig_264_){
_start:
{
lean_object* v_decls_265_; lean_object* v___x_266_; uint8_t v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v_decls_265_ = lean_ctor_get(v_aig_264_, 0);
v___x_266_ = lean_array_get_size(v_decls_265_);
v___x_267_ = 0;
v___x_268_ = lean_box(v___x_267_);
v___x_269_ = lean_mk_array(v___x_266_, v___x_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___boxed(lean_object* v_aig_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init(v_aig_270_);
lean_dec_ref(v_aig_270_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg(lean_object* v_cache_272_, lean_object* v_idx_273_){
_start:
{
uint8_t v___x_274_; lean_object* v___x_275_; lean_object* v_out_276_; 
v___x_274_ = 1;
v___x_275_ = lean_box(v___x_274_);
v_out_276_ = lean_array_fset(v_cache_272_, v_idx_273_, v___x_275_);
return v_out_276_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg___boxed(lean_object* v_cache_277_, lean_object* v_idx_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg(v_cache_277_, v_idx_278_);
lean_dec(v_idx_278_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse(lean_object* v_aig_280_, lean_object* v_cnf_281_, lean_object* v_cache_282_, lean_object* v_idx_283_, lean_object* v_h_284_, lean_object* v_htip_285_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg(v_cache_282_, v_idx_283_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___boxed(lean_object* v_aig_287_, lean_object* v_cnf_288_, lean_object* v_cache_289_, lean_object* v_idx_290_, lean_object* v_h_291_, lean_object* v_htip_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse(v_aig_287_, v_cnf_288_, v_cache_289_, v_idx_290_, v_h_291_, v_htip_292_);
lean_dec(v_idx_290_);
lean_dec_ref(v_cnf_288_);
lean_dec_ref(v_aig_287_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg(lean_object* v_cache_294_, lean_object* v_idx_295_){
_start:
{
uint8_t v___x_296_; lean_object* v___x_297_; lean_object* v_out_298_; 
v___x_296_ = 1;
v___x_297_ = lean_box(v___x_296_);
v_out_298_ = lean_array_fset(v_cache_294_, v_idx_295_, v___x_297_);
return v_out_298_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg___boxed(lean_object* v_cache_299_, lean_object* v_idx_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg(v_cache_299_, v_idx_300_);
lean_dec(v_idx_300_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom(lean_object* v_aig_302_, lean_object* v_cnf_303_, lean_object* v_a_304_, lean_object* v_cache_305_, lean_object* v_idx_306_, lean_object* v_h_307_, lean_object* v_htip_308_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg(v_cache_305_, v_idx_306_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___boxed(lean_object* v_aig_310_, lean_object* v_cnf_311_, lean_object* v_a_312_, lean_object* v_cache_313_, lean_object* v_idx_314_, lean_object* v_h_315_, lean_object* v_htip_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom(v_aig_310_, v_cnf_311_, v_a_312_, v_cache_313_, v_idx_314_, v_h_315_, v_htip_316_);
lean_dec(v_idx_314_);
lean_dec(v_a_312_);
lean_dec_ref(v_cnf_311_);
lean_dec_ref(v_aig_310_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg(lean_object* v_lhs_318_, lean_object* v_rhs_319_, lean_object* v_cache_320_, lean_object* v_idx_321_){
_start:
{
uint8_t v___x_322_; lean_object* v___x_323_; lean_object* v_out_324_; 
v___x_322_ = 1;
v___x_323_ = lean_box(v___x_322_);
v_out_324_ = lean_array_fset(v_cache_320_, v_idx_321_, v___x_323_);
return v_out_324_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg___boxed(lean_object* v_lhs_325_, lean_object* v_rhs_326_, lean_object* v_cache_327_, lean_object* v_idx_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg(v_lhs_325_, v_rhs_326_, v_cache_327_, v_idx_328_);
lean_dec(v_idx_328_);
lean_dec(v_rhs_326_);
lean_dec(v_lhs_325_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate(lean_object* v_aig_330_, lean_object* v_cnf_331_, lean_object* v_lhs_332_, lean_object* v_rhs_333_, lean_object* v_cache_334_, lean_object* v_hlb_335_, lean_object* v_hrb_336_, lean_object* v_idx_337_, lean_object* v_h_338_, lean_object* v_htip_339_, lean_object* v_hl_340_, lean_object* v_hr_341_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg(v_lhs_332_, v_rhs_333_, v_cache_334_, v_idx_337_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___boxed(lean_object* v_aig_343_, lean_object* v_cnf_344_, lean_object* v_lhs_345_, lean_object* v_rhs_346_, lean_object* v_cache_347_, lean_object* v_hlb_348_, lean_object* v_hrb_349_, lean_object* v_idx_350_, lean_object* v_h_351_, lean_object* v_htip_352_, lean_object* v_hl_353_, lean_object* v_hr_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate(v_aig_343_, v_cnf_344_, v_lhs_345_, v_rhs_346_, v_cache_347_, v_hlb_348_, v_hrb_349_, v_idx_350_, v_h_351_, v_htip_352_, v_hl_353_, v_hr_354_);
lean_dec(v_idx_350_);
lean_dec(v_rhs_346_);
lean_dec(v_lhs_345_);
lean_dec_ref(v_cnf_344_);
lean_dec_ref(v_aig_343_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___redArg(lean_object* v_cache_356_, lean_object* v_cond_357_, lean_object* v_ifTrue_358_, lean_object* v_ifFalse_359_, lean_object* v_idx_360_){
_start:
{
uint8_t v___x_361_; lean_object* v___x_362_; lean_object* v_out_363_; 
v___x_361_ = 1;
v___x_362_ = lean_box(v___x_361_);
v_out_363_ = lean_array_fset(v_cache_356_, v_idx_360_, v___x_362_);
return v_out_363_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___redArg___boxed(lean_object* v_cache_364_, lean_object* v_cond_365_, lean_object* v_ifTrue_366_, lean_object* v_ifFalse_367_, lean_object* v_idx_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___redArg(v_cache_364_, v_cond_365_, v_ifTrue_366_, v_ifFalse_367_, v_idx_368_);
lean_dec(v_idx_368_);
lean_dec(v_ifFalse_367_);
lean_dec(v_ifTrue_366_);
lean_dec(v_cond_365_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte(lean_object* v_aig_370_, lean_object* v_cnf_371_, lean_object* v_cache_372_, lean_object* v_cond_373_, lean_object* v_ifTrue_374_, lean_object* v_ifFalse_375_, lean_object* v_idx_376_, lean_object* v_hcb_377_, lean_object* v_htb_378_, lean_object* v_hfb_379_, lean_object* v_h_380_, lean_object* v_hltc_381_, lean_object* v_hltt_382_, lean_object* v_hltf_383_, lean_object* v_hc_384_, lean_object* v_ht_385_, lean_object* v_hf_386_, lean_object* v_hdenote_387_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___redArg(v_cache_372_, v_cond_373_, v_ifTrue_374_, v_ifFalse_375_, v_idx_376_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___boxed(lean_object** _args){
lean_object* v_aig_389_ = _args[0];
lean_object* v_cnf_390_ = _args[1];
lean_object* v_cache_391_ = _args[2];
lean_object* v_cond_392_ = _args[3];
lean_object* v_ifTrue_393_ = _args[4];
lean_object* v_ifFalse_394_ = _args[5];
lean_object* v_idx_395_ = _args[6];
lean_object* v_hcb_396_ = _args[7];
lean_object* v_htb_397_ = _args[8];
lean_object* v_hfb_398_ = _args[9];
lean_object* v_h_399_ = _args[10];
lean_object* v_hltc_400_ = _args[11];
lean_object* v_hltt_401_ = _args[12];
lean_object* v_hltf_402_ = _args[13];
lean_object* v_hc_403_ = _args[14];
lean_object* v_ht_404_ = _args[15];
lean_object* v_hf_405_ = _args[16];
lean_object* v_hdenote_406_ = _args[17];
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte(v_aig_389_, v_cnf_390_, v_cache_391_, v_cond_392_, v_ifTrue_393_, v_ifFalse_394_, v_idx_395_, v_hcb_396_, v_htb_397_, v_hfb_398_, v_h_399_, v_hltc_400_, v_hltt_401_, v_hltf_402_, v_hc_403_, v_ht_404_, v_hf_405_, v_hdenote_406_);
lean_dec(v_idx_395_);
lean_dec(v_ifFalse_394_);
lean_dec(v_ifTrue_393_);
lean_dec(v_cond_392_);
lean_dec_ref(v_cnf_390_);
lean_dec_ref(v_aig_389_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty(lean_object* v_aig_408_){
_start:
{
lean_object* v_decls_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
v_decls_409_ = lean_ctor_get(v_aig_408_, 0);
v___x_410_ = lean_array_get_size(v_decls_409_);
v___x_411_ = lean_unsigned_to_nat(2u);
v___x_412_ = lean_nat_mul(v___x_410_, v___x_411_);
v___x_413_ = lean_mk_empty_array_with_capacity(v___x_412_);
lean_dec(v___x_412_);
v___x_414_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init(v_aig_408_);
v_isSharedCheck_421_ = !lean_is_exclusive(v_aig_408_);
if (v_isSharedCheck_421_ == 0)
{
lean_object* v_unused_422_; lean_object* v_unused_423_; 
v_unused_422_ = lean_ctor_get(v_aig_408_, 1);
lean_dec(v_unused_422_);
v_unused_423_ = lean_ctor_get(v_aig_408_, 0);
lean_dec(v_unused_423_);
v___x_416_ = v_aig_408_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_dec(v_aig_408_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 1, v___x_414_);
lean_ctor_set(v___x_416_, 0, v___x_413_);
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_413_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v___x_414_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___redArg(lean_object* v_state_424_, lean_object* v_idx_425_){
_start:
{
lean_object* v_cnf_426_; lean_object* v_cache_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_437_; 
v_cnf_426_ = lean_ctor_get(v_state_424_, 0);
v_cache_427_ = lean_ctor_get(v_state_424_, 1);
v_isSharedCheck_437_ = !lean_is_exclusive(v_state_424_);
if (v_isSharedCheck_437_ == 0)
{
v___x_429_ = v_state_424_;
v_isShared_430_ = v_isSharedCheck_437_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_cache_427_);
lean_inc(v_cnf_426_);
lean_dec(v_state_424_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_437_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v_val_431_; lean_object* v_newCnf_432_; lean_object* v___x_433_; lean_object* v___x_435_; 
v_val_431_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg(v_cache_427_, v_idx_425_);
v_newCnf_432_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg(v_idx_425_);
v___x_433_ = l_Array_append___redArg(v_cnf_426_, v_newCnf_432_);
lean_dec_ref(v_newCnf_432_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 1, v_val_431_);
lean_ctor_set(v___x_429_, 0, v___x_433_);
v___x_435_ = v___x_429_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v_val_431_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse(lean_object* v_aig_438_, lean_object* v_state_439_, lean_object* v_idx_440_, lean_object* v_h_441_, lean_object* v_htip_442_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___redArg(v_state_439_, v_idx_440_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___boxed(lean_object* v_aig_444_, lean_object* v_state_445_, lean_object* v_idx_446_, lean_object* v_h_447_, lean_object* v_htip_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse(v_aig_444_, v_state_445_, v_idx_446_, v_h_447_, v_htip_448_);
lean_dec_ref(v_aig_444_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg(lean_object* v_aig_450_, lean_object* v_a_451_, lean_object* v_state_452_, lean_object* v_idx_453_){
_start:
{
lean_object* v_cnf_454_; lean_object* v_cache_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_468_; 
v_cnf_454_ = lean_ctor_get(v_state_452_, 0);
v_cache_455_ = lean_ctor_get(v_state_452_, 1);
v_isSharedCheck_468_ = !lean_is_exclusive(v_state_452_);
if (v_isSharedCheck_468_ == 0)
{
v___x_457_ = v_state_452_;
v_isShared_458_ = v_isSharedCheck_468_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_cache_455_);
lean_inc(v_cnf_454_);
lean_dec(v_state_452_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_468_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v_decls_459_; lean_object* v_val_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v_newCnf_463_; lean_object* v___x_464_; lean_object* v___x_466_; 
v_decls_459_ = lean_ctor_get(v_aig_450_, 0);
v_val_460_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg(v_cache_455_, v_idx_453_);
v___x_461_ = lean_array_get_size(v_decls_459_);
v___x_462_ = lean_nat_add(v_a_451_, v___x_461_);
v_newCnf_463_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF___redArg(v_idx_453_, v___x_462_);
v___x_464_ = l_Array_append___redArg(v_cnf_454_, v_newCnf_463_);
lean_dec_ref(v_newCnf_463_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 1, v_val_460_);
lean_ctor_set(v___x_457_, 0, v___x_464_);
v___x_466_ = v___x_457_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_464_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v_val_460_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg___boxed(lean_object* v_aig_469_, lean_object* v_a_470_, lean_object* v_state_471_, lean_object* v_idx_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg(v_aig_469_, v_a_470_, v_state_471_, v_idx_472_);
lean_dec(v_a_470_);
lean_dec_ref(v_aig_469_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom(lean_object* v_aig_474_, lean_object* v_a_475_, lean_object* v_state_476_, lean_object* v_idx_477_, lean_object* v_h_478_, lean_object* v_htip_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg(v_aig_474_, v_a_475_, v_state_476_, v_idx_477_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___boxed(lean_object* v_aig_481_, lean_object* v_a_482_, lean_object* v_state_483_, lean_object* v_idx_484_, lean_object* v_h_485_, lean_object* v_htip_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom(v_aig_481_, v_a_482_, v_state_483_, v_idx_484_, v_h_485_, v_htip_486_);
lean_dec(v_a_482_);
lean_dec_ref(v_aig_481_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg(lean_object* v_lhs_488_, lean_object* v_rhs_489_, lean_object* v_state_490_, lean_object* v_idx_491_){
_start:
{
lean_object* v_cnf_492_; lean_object* v_cache_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_521_; 
v_cnf_492_ = lean_ctor_get(v_state_490_, 0);
v_cache_493_ = lean_ctor_get(v_state_490_, 1);
v_isSharedCheck_521_ = !lean_is_exclusive(v_state_490_);
if (v_isSharedCheck_521_ == 0)
{
v___x_495_ = v_state_490_;
v_isShared_496_ = v_isSharedCheck_521_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_cache_493_);
lean_inc(v_cnf_492_);
lean_dec(v_state_490_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_521_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; uint8_t v___y_501_; uint8_t v___y_502_; uint8_t v___y_510_; lean_object* v___x_516_; lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_497_ = lean_unsigned_to_nat(1u);
v___x_498_ = lean_nat_shiftr(v_lhs_488_, v___x_497_);
v___x_499_ = lean_nat_shiftr(v_rhs_489_, v___x_497_);
v___x_516_ = lean_nat_land(v___x_497_, v_lhs_488_);
v___x_517_ = lean_unsigned_to_nat(0u);
v___x_518_ = lean_nat_dec_eq(v___x_516_, v___x_517_);
lean_dec(v___x_516_);
if (v___x_518_ == 0)
{
uint8_t v___x_519_; 
v___x_519_ = 1;
v___y_510_ = v___x_519_;
goto v___jp_509_;
}
else
{
uint8_t v___x_520_; 
v___x_520_ = 0;
v___y_510_ = v___x_520_;
goto v___jp_509_;
}
v___jp_500_:
{
lean_object* v_val_503_; lean_object* v_newCnf_504_; lean_object* v___x_505_; lean_object* v___x_507_; 
v_val_503_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg(v_lhs_488_, v_rhs_489_, v_cache_493_, v_idx_491_);
v_newCnf_504_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg(v_idx_491_, v___x_498_, v___x_499_, v___y_501_, v___y_502_);
v___x_505_ = l_Array_append___redArg(v_cnf_492_, v_newCnf_504_);
lean_dec_ref(v_newCnf_504_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 1, v_val_503_);
lean_ctor_set(v___x_495_, 0, v___x_505_);
v___x_507_ = v___x_495_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_505_);
lean_ctor_set(v_reuseFailAlloc_508_, 1, v_val_503_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
v___jp_509_:
{
lean_object* v___x_511_; lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_511_ = lean_nat_land(v___x_497_, v_rhs_489_);
v___x_512_ = lean_unsigned_to_nat(0u);
v___x_513_ = lean_nat_dec_eq(v___x_511_, v___x_512_);
lean_dec(v___x_511_);
if (v___x_513_ == 0)
{
uint8_t v___x_514_; 
v___x_514_ = 1;
v___y_501_ = v___y_510_;
v___y_502_ = v___x_514_;
goto v___jp_500_;
}
else
{
uint8_t v___x_515_; 
v___x_515_ = 0;
v___y_501_ = v___y_510_;
v___y_502_ = v___x_515_;
goto v___jp_500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg___boxed(lean_object* v_lhs_522_, lean_object* v_rhs_523_, lean_object* v_state_524_, lean_object* v_idx_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg(v_lhs_522_, v_rhs_523_, v_state_524_, v_idx_525_);
lean_dec(v_rhs_523_);
lean_dec(v_lhs_522_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate(lean_object* v_aig_527_, lean_object* v_lhs_528_, lean_object* v_rhs_529_, lean_object* v_state_530_, lean_object* v_hlb_531_, lean_object* v_hrb_532_, lean_object* v_idx_533_, lean_object* v_h_534_, lean_object* v_htip_535_, lean_object* v_hl_536_, lean_object* v_hr_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg(v_lhs_528_, v_rhs_529_, v_state_530_, v_idx_533_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___boxed(lean_object* v_aig_539_, lean_object* v_lhs_540_, lean_object* v_rhs_541_, lean_object* v_state_542_, lean_object* v_hlb_543_, lean_object* v_hrb_544_, lean_object* v_idx_545_, lean_object* v_h_546_, lean_object* v_htip_547_, lean_object* v_hl_548_, lean_object* v_hr_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate(v_aig_539_, v_lhs_540_, v_rhs_541_, v_state_542_, v_hlb_543_, v_hrb_544_, v_idx_545_, v_h_546_, v_htip_547_, v_hl_548_, v_hr_549_);
lean_dec(v_rhs_541_);
lean_dec(v_lhs_540_);
lean_dec_ref(v_aig_539_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___redArg(lean_object* v_state_551_, lean_object* v_cond_552_, lean_object* v_ifTrue_553_, lean_object* v_ifFalse_554_, lean_object* v_idx_555_){
_start:
{
lean_object* v_cnf_556_; lean_object* v_cache_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_595_; 
v_cnf_556_ = lean_ctor_get(v_state_551_, 0);
v_cache_557_ = lean_ctor_get(v_state_551_, 1);
v_isSharedCheck_595_ = !lean_is_exclusive(v_state_551_);
if (v_isSharedCheck_595_ == 0)
{
v___x_559_ = v_state_551_;
v_isShared_560_ = v_isSharedCheck_595_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_cache_557_);
lean_inc(v_cnf_556_);
lean_dec(v_state_551_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_595_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; uint8_t v___y_566_; uint8_t v___y_567_; uint8_t v___y_568_; uint8_t v___y_576_; uint8_t v___y_577_; uint8_t v___y_584_; lean_object* v___x_590_; lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_561_ = lean_unsigned_to_nat(1u);
v___x_562_ = lean_nat_shiftr(v_cond_552_, v___x_561_);
v___x_563_ = lean_nat_shiftr(v_ifTrue_553_, v___x_561_);
v___x_564_ = lean_nat_shiftr(v_ifFalse_554_, v___x_561_);
v___x_590_ = lean_nat_land(v___x_561_, v_cond_552_);
v___x_591_ = lean_unsigned_to_nat(0u);
v___x_592_ = lean_nat_dec_eq(v___x_590_, v___x_591_);
lean_dec(v___x_590_);
if (v___x_592_ == 0)
{
uint8_t v___x_593_; 
v___x_593_ = 1;
v___y_584_ = v___x_593_;
goto v___jp_583_;
}
else
{
uint8_t v___x_594_; 
v___x_594_ = 0;
v___y_584_ = v___x_594_;
goto v___jp_583_;
}
v___jp_565_:
{
lean_object* v_val_569_; lean_object* v_newCnf_570_; lean_object* v___x_571_; lean_object* v___x_573_; 
v_val_569_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___redArg(v_cache_557_, v_cond_552_, v_ifTrue_553_, v_ifFalse_554_, v_idx_555_);
v_newCnf_570_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF___redArg(v_idx_555_, v___x_562_, v___x_563_, v___x_564_, v___y_567_, v___y_566_, v___y_568_);
v___x_571_ = l_Array_append___redArg(v_cnf_556_, v_newCnf_570_);
lean_dec_ref(v_newCnf_570_);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 1, v_val_569_);
lean_ctor_set(v___x_559_, 0, v___x_571_);
v___x_573_ = v___x_559_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_571_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v_val_569_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
v___jp_575_:
{
lean_object* v___x_578_; lean_object* v___x_579_; uint8_t v___x_580_; 
v___x_578_ = lean_nat_land(v___x_561_, v_ifFalse_554_);
v___x_579_ = lean_unsigned_to_nat(0u);
v___x_580_ = lean_nat_dec_eq(v___x_578_, v___x_579_);
lean_dec(v___x_578_);
if (v___x_580_ == 0)
{
uint8_t v___x_581_; 
v___x_581_ = 1;
v___y_566_ = v___y_577_;
v___y_567_ = v___y_576_;
v___y_568_ = v___x_581_;
goto v___jp_565_;
}
else
{
uint8_t v___x_582_; 
v___x_582_ = 0;
v___y_566_ = v___y_577_;
v___y_567_ = v___y_576_;
v___y_568_ = v___x_582_;
goto v___jp_565_;
}
}
v___jp_583_:
{
lean_object* v___x_585_; lean_object* v___x_586_; uint8_t v___x_587_; 
v___x_585_ = lean_nat_land(v___x_561_, v_ifTrue_553_);
v___x_586_ = lean_unsigned_to_nat(0u);
v___x_587_ = lean_nat_dec_eq(v___x_585_, v___x_586_);
lean_dec(v___x_585_);
if (v___x_587_ == 0)
{
uint8_t v___x_588_; 
v___x_588_ = 1;
v___y_576_ = v___y_584_;
v___y_577_ = v___x_588_;
goto v___jp_575_;
}
else
{
uint8_t v___x_589_; 
v___x_589_ = 0;
v___y_576_ = v___y_584_;
v___y_577_ = v___x_589_;
goto v___jp_575_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___redArg___boxed(lean_object* v_state_596_, lean_object* v_cond_597_, lean_object* v_ifTrue_598_, lean_object* v_ifFalse_599_, lean_object* v_idx_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___redArg(v_state_596_, v_cond_597_, v_ifTrue_598_, v_ifFalse_599_, v_idx_600_);
lean_dec(v_ifFalse_599_);
lean_dec(v_ifTrue_598_);
lean_dec(v_cond_597_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte(lean_object* v_aig_602_, lean_object* v_state_603_, lean_object* v_cond_604_, lean_object* v_ifTrue_605_, lean_object* v_ifFalse_606_, lean_object* v_idx_607_, lean_object* v_hcb_608_, lean_object* v_htb_609_, lean_object* v_hfb_610_, lean_object* v_h_611_, lean_object* v_hltc_612_, lean_object* v_hltt_613_, lean_object* v_hltf_614_, lean_object* v_hc_615_, lean_object* v_ht_616_, lean_object* v_hf_617_, lean_object* v_hdenote_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___redArg(v_state_603_, v_cond_604_, v_ifTrue_605_, v_ifFalse_606_, v_idx_607_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___boxed(lean_object** _args){
lean_object* v_aig_620_ = _args[0];
lean_object* v_state_621_ = _args[1];
lean_object* v_cond_622_ = _args[2];
lean_object* v_ifTrue_623_ = _args[3];
lean_object* v_ifFalse_624_ = _args[4];
lean_object* v_idx_625_ = _args[5];
lean_object* v_hcb_626_ = _args[6];
lean_object* v_htb_627_ = _args[7];
lean_object* v_hfb_628_ = _args[8];
lean_object* v_h_629_ = _args[9];
lean_object* v_hltc_630_ = _args[10];
lean_object* v_hltt_631_ = _args[11];
lean_object* v_hltf_632_ = _args[12];
lean_object* v_hc_633_ = _args[13];
lean_object* v_ht_634_ = _args[14];
lean_object* v_hf_635_ = _args[15];
lean_object* v_hdenote_636_ = _args[16];
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte(v_aig_620_, v_state_621_, v_cond_622_, v_ifTrue_623_, v_ifFalse_624_, v_idx_625_, v_hcb_626_, v_htb_627_, v_hfb_628_, v_h_629_, v_hltc_630_, v_hltt_631_, v_hltf_632_, v_hc_633_, v_ht_634_, v_hf_635_, v_hdenote_636_);
lean_dec(v_ifFalse_624_);
lean_dec(v_ifTrue_623_);
lean_dec(v_cond_622_);
lean_dec_ref(v_aig_620_);
return v_res_637_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg(lean_object* v_assign_638_, lean_object* v_state_639_){
_start:
{
lean_object* v_cnf_640_; uint8_t v___x_641_; 
v_cnf_640_ = lean_ctor_get(v_state_639_, 0);
v___x_641_ = l_Std_Sat_CNF_eval___redArg(v_assign_638_, v_cnf_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg___boxed(lean_object* v_assign_642_, lean_object* v_state_643_){
_start:
{
uint8_t v_res_644_; lean_object* v_r_645_; 
v_res_644_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg(v_assign_642_, v_state_643_);
lean_dec_ref(v_state_643_);
v_r_645_ = lean_box(v_res_644_);
return v_r_645_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval(lean_object* v_aig_646_, lean_object* v_assign_647_, lean_object* v_state_648_){
_start:
{
uint8_t v___x_649_; 
v___x_649_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg(v_assign_647_, v_state_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___boxed(lean_object* v_aig_650_, lean_object* v_assign_651_, lean_object* v_state_652_){
_start:
{
uint8_t v_res_653_; lean_object* v_r_654_; 
v_res_653_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval(v_aig_650_, v_assign_651_, v_state_652_);
lean_dec_ref(v_state_652_);
lean_dec_ref(v_aig_650_);
v_r_654_ = lean_box(v_res_653_);
return v_r_654_;
}
}
static lean_object* _init_l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg___closed__0(void){
_start:
{
uint8_t v___x_655_; lean_object* v___x_656_; 
v___x_655_ = 1;
v___x_656_ = l_Bool_toNat(v___x_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg(lean_object* v_l0_657_, lean_object* v_l1_658_, lean_object* v_r0_659_, lean_object* v_r1_660_){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_661_ = lean_obj_once(&l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg___closed__0, &l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg___closed__0_once, _init_l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg___closed__0);
v___x_662_ = lean_nat_lxor(v_r0_659_, v___x_661_);
v___x_663_ = lean_nat_dec_eq(v_l0_657_, v___x_662_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_664_ = lean_nat_lxor(v_r1_660_, v___x_661_);
v___x_665_ = lean_nat_dec_eq(v_l0_657_, v___x_664_);
if (v___x_665_ == 0)
{
uint8_t v___x_666_; 
v___x_666_ = lean_nat_dec_eq(v_l1_658_, v___x_662_);
if (v___x_666_ == 0)
{
uint8_t v___x_667_; 
v___x_667_ = lean_nat_dec_eq(v_l1_658_, v___x_664_);
lean_dec(v___x_664_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; 
lean_dec(v___x_662_);
lean_dec(v_l1_658_);
lean_dec(v_l0_657_);
v___x_668_ = lean_box(0);
return v___x_668_;
}
else
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_669_ = lean_nat_lxor(v_l0_657_, v___x_661_);
lean_dec(v_l0_657_);
v___x_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
lean_ctor_set(v___x_670_, 1, v___x_662_);
v___x_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_671_, 0, v_l1_658_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
v___x_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
return v___x_672_;
}
}
else
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
lean_dec(v___x_662_);
v___x_673_ = lean_nat_lxor(v_l0_657_, v___x_661_);
lean_dec(v_l0_657_);
v___x_674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
lean_ctor_set(v___x_674_, 1, v___x_664_);
v___x_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_675_, 0, v_l1_658_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
v___x_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
return v___x_676_;
}
}
else
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
lean_dec(v___x_664_);
v___x_677_ = lean_nat_lxor(v_l1_658_, v___x_661_);
lean_dec(v_l1_658_);
v___x_678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
lean_ctor_set(v___x_678_, 1, v___x_662_);
v___x_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_679_, 0, v_l0_657_);
lean_ctor_set(v___x_679_, 1, v___x_678_);
v___x_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
return v___x_680_;
}
}
else
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
lean_dec(v___x_662_);
v___x_681_ = lean_nat_lxor(v_l1_658_, v___x_661_);
lean_dec(v_l1_658_);
v___x_682_ = lean_nat_lxor(v_r1_660_, v___x_661_);
v___x_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_683_, 0, v___x_681_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
v___x_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_684_, 0, v_l0_657_);
lean_ctor_set(v___x_684_, 1, v___x_683_);
v___x_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_685_, 0, v___x_684_);
return v___x_685_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg___boxed(lean_object* v_l0_686_, lean_object* v_l1_687_, lean_object* v_r0_688_, lean_object* v_r1_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg(v_l0_686_, v_l1_687_, v_r0_688_, v_r1_689_);
lean_dec(v_r1_689_);
lean_dec(v_r0_688_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go(lean_object* v_l_691_, lean_object* v_r_692_, lean_object* v_l0_693_, lean_object* v_l1_694_, lean_object* v_r0_695_, lean_object* v_r1_696_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg(v_l0_693_, v_l1_694_, v_r0_695_, v_r1_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___boxed(lean_object* v_l_698_, lean_object* v_r_699_, lean_object* v_l0_700_, lean_object* v_l1_701_, lean_object* v_r0_702_, lean_object* v_r1_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go(v_l_698_, v_r_699_, v_l0_700_, v_l1_701_, v_r0_702_, v_r1_703_);
lean_dec(v_r1_703_);
lean_dec(v_r0_702_);
lean_dec(v_r_699_);
lean_dec(v_l_698_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___redArg(lean_object* v_aig_705_, lean_object* v_root_706_){
_start:
{
lean_object* v_decls_707_; lean_object* v___x_708_; 
v_decls_707_ = lean_ctor_get(v_aig_705_, 0);
v___x_708_ = lean_array_fget_borrowed(v_decls_707_, v_root_706_);
if (lean_obj_tag(v___x_708_) == 2)
{
lean_object* v_l_709_; lean_object* v_r_710_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; uint8_t v___x_727_; 
v_l_709_ = lean_ctor_get(v___x_708_, 0);
v_r_710_ = lean_ctor_get(v___x_708_, 1);
v___x_724_ = lean_unsigned_to_nat(1u);
v___x_725_ = lean_nat_land(v___x_724_, v_l_709_);
v___x_726_ = lean_unsigned_to_nat(0u);
v___x_727_ = lean_nat_dec_eq(v___x_725_, v___x_726_);
lean_dec(v___x_725_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_728_ = lean_nat_land(v___x_724_, v_r_710_);
v___x_729_ = lean_nat_dec_eq(v___x_728_, v___x_726_);
lean_dec(v___x_728_);
if (v___x_729_ == 0)
{
goto v___jp_711_;
}
else
{
if (v___x_729_ == 0)
{
goto v___jp_711_;
}
else
{
lean_object* v___x_730_; 
v___x_730_ = lean_box(0);
return v___x_730_;
}
}
}
else
{
lean_object* v___x_731_; 
v___x_731_ = lean_box(0);
return v___x_731_;
}
v___jp_711_:
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_712_ = lean_unsigned_to_nat(1u);
v___x_713_ = lean_nat_shiftr(v_l_709_, v___x_712_);
v___x_714_ = lean_array_fget_borrowed(v_decls_707_, v___x_713_);
lean_dec(v___x_713_);
if (lean_obj_tag(v___x_714_) == 2)
{
lean_object* v_l_715_; lean_object* v_r_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v_l_715_ = lean_ctor_get(v___x_714_, 0);
v_r_716_ = lean_ctor_get(v___x_714_, 1);
v___x_717_ = lean_nat_shiftr(v_r_710_, v___x_712_);
v___x_718_ = lean_array_fget_borrowed(v_decls_707_, v___x_717_);
lean_dec(v___x_717_);
if (lean_obj_tag(v___x_718_) == 2)
{
lean_object* v_l_719_; lean_object* v_r_720_; lean_object* v___x_721_; 
v_l_719_ = lean_ctor_get(v___x_718_, 0);
v_r_720_ = lean_ctor_get(v___x_718_, 1);
lean_inc(v_r_716_);
lean_inc(v_l_715_);
v___x_721_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg(v_l_715_, v_r_716_, v_l_719_, v_r_720_);
return v___x_721_;
}
else
{
lean_object* v___x_722_; 
v___x_722_ = lean_box(0);
return v___x_722_;
}
}
else
{
lean_object* v___x_723_; 
v___x_723_ = lean_box(0);
return v___x_723_;
}
}
}
else
{
lean_object* v___x_732_; 
v___x_732_ = lean_box(0);
return v___x_732_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___redArg___boxed(lean_object* v_aig_733_, lean_object* v_root_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___redArg(v_aig_733_, v_root_734_);
lean_dec(v_root_734_);
lean_dec_ref(v_aig_733_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte(lean_object* v_aig_736_, lean_object* v_root_737_, lean_object* v_h_738_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___redArg(v_aig_736_, v_root_737_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___boxed(lean_object* v_aig_740_, lean_object* v_root_741_, lean_object* v_h_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte(v_aig_740_, v_root_741_, v_h_742_);
lean_dec(v_root_741_);
lean_dec_ref(v_aig_740_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_match__4_splitter___redArg(lean_object* v_x_744_, lean_object* v_h__1_745_, lean_object* v_h__2_746_){
_start:
{
if (lean_obj_tag(v_x_744_) == 2)
{
lean_object* v_l_747_; lean_object* v_r_748_; lean_object* v___x_749_; 
lean_dec(v_h__2_746_);
v_l_747_ = lean_ctor_get(v_x_744_, 0);
lean_inc(v_l_747_);
v_r_748_ = lean_ctor_get(v_x_744_, 1);
lean_inc(v_r_748_);
lean_dec_ref_known(v_x_744_, 2);
v___x_749_ = lean_apply_3(v_h__1_745_, v_l_747_, v_r_748_, lean_box(0));
return v___x_749_;
}
else
{
lean_object* v___x_750_; 
lean_dec(v_h__1_745_);
v___x_750_ = lean_apply_3(v_h__2_746_, v_x_744_, lean_box(0), lean_box(0));
return v___x_750_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_match__4_splitter(lean_object* v_motive_751_, lean_object* v_x_752_, lean_object* v_h__1_753_, lean_object* v_h__2_754_){
_start:
{
if (lean_obj_tag(v_x_752_) == 2)
{
lean_object* v_l_755_; lean_object* v_r_756_; lean_object* v___x_757_; 
lean_dec(v_h__2_754_);
v_l_755_ = lean_ctor_get(v_x_752_, 0);
lean_inc(v_l_755_);
v_r_756_ = lean_ctor_get(v_x_752_, 1);
lean_inc(v_r_756_);
lean_dec_ref_known(v_x_752_, 2);
v___x_757_ = lean_apply_3(v_h__1_753_, v_l_755_, v_r_756_, lean_box(0));
return v___x_757_;
}
else
{
lean_object* v___x_758_; 
lean_dec(v_h__1_753_);
v___x_758_ = lean_apply_3(v_h__2_754_, v_x_752_, lean_box(0), lean_box(0));
return v___x_758_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_match__1_splitter___redArg(lean_object* v_x_759_, lean_object* v_x_760_, lean_object* v_h__1_761_, lean_object* v_h__2_762_){
_start:
{
if (lean_obj_tag(v_x_759_) == 2)
{
if (lean_obj_tag(v_x_760_) == 2)
{
lean_object* v_l_763_; lean_object* v_r_764_; lean_object* v_l_765_; lean_object* v_r_766_; lean_object* v___x_767_; 
lean_dec(v_h__2_762_);
v_l_763_ = lean_ctor_get(v_x_759_, 0);
lean_inc(v_l_763_);
v_r_764_ = lean_ctor_get(v_x_759_, 1);
lean_inc(v_r_764_);
lean_dec_ref_known(v_x_759_, 2);
v_l_765_ = lean_ctor_get(v_x_760_, 0);
lean_inc(v_l_765_);
v_r_766_ = lean_ctor_get(v_x_760_, 1);
lean_inc(v_r_766_);
lean_dec_ref_known(v_x_760_, 2);
v___x_767_ = lean_apply_6(v_h__1_761_, v_l_763_, v_r_764_, v_l_765_, v_r_766_, lean_box(0), lean_box(0));
return v___x_767_;
}
else
{
lean_object* v___x_768_; 
lean_dec(v_h__1_761_);
v___x_768_ = lean_apply_5(v_h__2_762_, v_x_759_, v_x_760_, lean_box(0), lean_box(0), lean_box(0));
return v___x_768_;
}
}
else
{
lean_object* v___x_769_; 
lean_dec(v_h__1_761_);
v___x_769_ = lean_apply_5(v_h__2_762_, v_x_759_, v_x_760_, lean_box(0), lean_box(0), lean_box(0));
return v___x_769_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_match__1_splitter(lean_object* v_motive_770_, lean_object* v_x_771_, lean_object* v_x_772_, lean_object* v_h__1_773_, lean_object* v_h__2_774_){
_start:
{
if (lean_obj_tag(v_x_771_) == 2)
{
if (lean_obj_tag(v_x_772_) == 2)
{
lean_object* v_l_775_; lean_object* v_r_776_; lean_object* v_l_777_; lean_object* v_r_778_; lean_object* v___x_779_; 
lean_dec(v_h__2_774_);
v_l_775_ = lean_ctor_get(v_x_771_, 0);
lean_inc(v_l_775_);
v_r_776_ = lean_ctor_get(v_x_771_, 1);
lean_inc(v_r_776_);
lean_dec_ref_known(v_x_771_, 2);
v_l_777_ = lean_ctor_get(v_x_772_, 0);
lean_inc(v_l_777_);
v_r_778_ = lean_ctor_get(v_x_772_, 1);
lean_inc(v_r_778_);
lean_dec_ref_known(v_x_772_, 2);
v___x_779_ = lean_apply_6(v_h__1_773_, v_l_775_, v_r_776_, v_l_777_, v_r_778_, lean_box(0), lean_box(0));
return v___x_779_;
}
else
{
lean_object* v___x_780_; 
lean_dec(v_h__1_773_);
v___x_780_ = lean_apply_5(v_h__2_774_, v_x_771_, v_x_772_, lean_box(0), lean_box(0), lean_box(0));
return v___x_780_;
}
}
else
{
lean_object* v___x_781_; 
lean_dec(v_h__1_773_);
v___x_781_ = lean_apply_5(v_h__2_774_, v_x_771_, v_x_772_, lean_box(0), lean_box(0), lean_box(0));
return v___x_781_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(lean_object* v_aig_782_, lean_object* v_upper_783_, lean_object* v_state_784_){
_start:
{
lean_object* v_cache_785_; lean_object* v___x_786_; uint8_t v___x_787_; 
v_cache_785_ = lean_ctor_get(v_state_784_, 1);
v___x_786_ = lean_array_fget_borrowed(v_cache_785_, v_upper_783_);
v___x_787_ = lean_unbox(v___x_786_);
if (v___x_787_ == 0)
{
lean_object* v_decls_788_; lean_object* v_decl_789_; 
v_decls_788_ = lean_ctor_get(v_aig_782_, 0);
v_decl_789_ = lean_array_fget_borrowed(v_decls_788_, v_upper_783_);
switch(lean_obj_tag(v_decl_789_))
{
case 0:
{
lean_object* v___x_790_; 
v___x_790_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___redArg(v_state_784_, v_upper_783_);
return v___x_790_;
}
case 1:
{
lean_object* v_idx_791_; lean_object* v___x_792_; 
v_idx_791_ = lean_ctor_get(v_decl_789_, 0);
v___x_792_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg(v_aig_782_, v_idx_791_, v_state_784_, v_upper_783_);
return v___x_792_;
}
default: 
{
lean_object* v_l_793_; lean_object* v_r_794_; lean_object* v___x_795_; 
v_l_793_ = lean_ctor_get(v_decl_789_, 0);
v_r_794_ = lean_ctor_get(v_decl_789_, 1);
v___x_795_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___redArg(v_aig_782_, v_upper_783_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v_val_798_; lean_object* v___x_799_; lean_object* v_val_800_; lean_object* v_val_801_; 
v___x_796_ = lean_unsigned_to_nat(1u);
v___x_797_ = lean_nat_shiftr(v_l_793_, v___x_796_);
v_val_798_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(v_aig_782_, v___x_797_, v_state_784_);
v___x_799_ = lean_nat_shiftr(v_r_794_, v___x_796_);
v_val_800_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(v_aig_782_, v___x_799_, v_val_798_);
v_val_801_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg(v_l_793_, v_r_794_, v_val_800_, v_upper_783_);
return v_val_801_;
}
else
{
lean_object* v_val_802_; lean_object* v_snd_803_; lean_object* v_fst_804_; lean_object* v_fst_805_; lean_object* v_snd_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v_val_809_; lean_object* v___x_810_; lean_object* v_val_811_; lean_object* v___x_812_; lean_object* v_val_813_; lean_object* v_val_814_; 
v_val_802_ = lean_ctor_get(v___x_795_, 0);
lean_inc(v_val_802_);
lean_dec_ref_known(v___x_795_, 1);
v_snd_803_ = lean_ctor_get(v_val_802_, 1);
lean_inc(v_snd_803_);
v_fst_804_ = lean_ctor_get(v_val_802_, 0);
lean_inc(v_fst_804_);
lean_dec(v_val_802_);
v_fst_805_ = lean_ctor_get(v_snd_803_, 0);
lean_inc(v_fst_805_);
v_snd_806_ = lean_ctor_get(v_snd_803_, 1);
lean_inc(v_snd_806_);
lean_dec(v_snd_803_);
v___x_807_ = lean_unsigned_to_nat(1u);
v___x_808_ = lean_nat_shiftr(v_fst_804_, v___x_807_);
v_val_809_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(v_aig_782_, v___x_808_, v_state_784_);
v___x_810_ = lean_nat_shiftr(v_fst_805_, v___x_807_);
v_val_811_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(v_aig_782_, v___x_810_, v_val_809_);
v___x_812_ = lean_nat_shiftr(v_snd_806_, v___x_807_);
v_val_813_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(v_aig_782_, v___x_812_, v_val_811_);
v_val_814_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___redArg(v_val_813_, v_fst_804_, v_fst_805_, v_snd_806_, v_upper_783_);
lean_dec(v_snd_806_);
lean_dec(v_fst_805_);
lean_dec(v_fst_804_);
return v_val_814_;
}
}
}
}
else
{
lean_dec(v_upper_783_);
return v_state_784_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg___boxed(lean_object* v_aig_815_, lean_object* v_upper_816_, lean_object* v_state_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(v_aig_815_, v_upper_816_, v_state_817_);
lean_dec_ref(v_aig_815_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go(lean_object* v_aig_819_, lean_object* v_upper_820_, lean_object* v_h_821_, lean_object* v_state_822_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(v_aig_819_, v_upper_820_, v_state_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___boxed(lean_object* v_aig_824_, lean_object* v_upper_825_, lean_object* v_h_826_, lean_object* v_state_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go(v_aig_824_, v_upper_825_, v_h_826_, v_state_827_);
lean_dec_ref(v_aig_824_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go_match__103_splitter___redArg(lean_object* v_decl_829_, lean_object* v_h__1_830_, lean_object* v_h__2_831_, lean_object* v_h__3_832_){
_start:
{
switch(lean_obj_tag(v_decl_829_))
{
case 0:
{
lean_object* v___x_833_; 
lean_dec(v_h__3_832_);
lean_dec(v_h__2_831_);
v___x_833_ = lean_apply_1(v_h__1_830_, lean_box(0));
return v___x_833_;
}
case 1:
{
lean_object* v_idx_834_; lean_object* v___x_835_; 
lean_dec(v_h__3_832_);
lean_dec(v_h__1_830_);
v_idx_834_ = lean_ctor_get(v_decl_829_, 0);
lean_inc(v_idx_834_);
lean_dec_ref_known(v_decl_829_, 1);
v___x_835_ = lean_apply_2(v_h__2_831_, v_idx_834_, lean_box(0));
return v___x_835_;
}
default: 
{
lean_object* v_l_836_; lean_object* v_r_837_; lean_object* v___x_838_; 
lean_dec(v_h__2_831_);
lean_dec(v_h__1_830_);
v_l_836_ = lean_ctor_get(v_decl_829_, 0);
lean_inc(v_l_836_);
v_r_837_ = lean_ctor_get(v_decl_829_, 1);
lean_inc(v_r_837_);
lean_dec_ref_known(v_decl_829_, 2);
v___x_838_ = lean_apply_3(v_h__3_832_, v_l_836_, v_r_837_, lean_box(0));
return v___x_838_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go_match__103_splitter(lean_object* v_motive_839_, lean_object* v_decl_840_, lean_object* v_h__1_841_, lean_object* v_h__2_842_, lean_object* v_h__3_843_){
_start:
{
switch(lean_obj_tag(v_decl_840_))
{
case 0:
{
lean_object* v___x_844_; 
lean_dec(v_h__3_843_);
lean_dec(v_h__2_842_);
v___x_844_ = lean_apply_1(v_h__1_841_, lean_box(0));
return v___x_844_;
}
case 1:
{
lean_object* v_idx_845_; lean_object* v___x_846_; 
lean_dec(v_h__3_843_);
lean_dec(v_h__1_841_);
v_idx_845_ = lean_ctor_get(v_decl_840_, 0);
lean_inc(v_idx_845_);
lean_dec_ref_known(v_decl_840_, 1);
v___x_846_ = lean_apply_2(v_h__2_842_, v_idx_845_, lean_box(0));
return v___x_846_;
}
default: 
{
lean_object* v_l_847_; lean_object* v_r_848_; lean_object* v___x_849_; 
lean_dec(v_h__2_842_);
lean_dec(v_h__1_841_);
v_l_847_ = lean_ctor_get(v_decl_840_, 0);
lean_inc(v_l_847_);
v_r_848_ = lean_ctor_get(v_decl_840_, 1);
lean_inc(v_r_848_);
lean_dec_ref_known(v_decl_840_, 2);
v___x_849_ = lean_apply_3(v_h__3_843_, v_l_847_, v_r_848_, lean_box(0));
return v___x_849_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go_match__81_splitter___redArg(lean_object* v_x_850_, lean_object* v_h__1_851_, lean_object* v_h__2_852_){
_start:
{
if (lean_obj_tag(v_x_850_) == 0)
{
lean_object* v___x_853_; 
lean_dec(v_h__1_851_);
v___x_853_ = lean_apply_1(v_h__2_852_, lean_box(0));
return v___x_853_;
}
else
{
lean_object* v_val_854_; lean_object* v_snd_855_; lean_object* v_fst_856_; lean_object* v_fst_857_; lean_object* v_snd_858_; lean_object* v___x_859_; 
lean_dec(v_h__2_852_);
v_val_854_ = lean_ctor_get(v_x_850_, 0);
lean_inc(v_val_854_);
lean_dec_ref_known(v_x_850_, 1);
v_snd_855_ = lean_ctor_get(v_val_854_, 1);
lean_inc(v_snd_855_);
v_fst_856_ = lean_ctor_get(v_val_854_, 0);
lean_inc(v_fst_856_);
lean_dec(v_val_854_);
v_fst_857_ = lean_ctor_get(v_snd_855_, 0);
lean_inc(v_fst_857_);
v_snd_858_ = lean_ctor_get(v_snd_855_, 1);
lean_inc(v_snd_858_);
lean_dec(v_snd_855_);
v___x_859_ = lean_apply_4(v_h__1_851_, v_fst_856_, v_fst_857_, v_snd_858_, lean_box(0));
return v___x_859_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go_match__81_splitter(lean_object* v_motive_860_, lean_object* v_x_861_, lean_object* v_h__1_862_, lean_object* v_h__2_863_){
_start:
{
if (lean_obj_tag(v_x_861_) == 0)
{
lean_object* v___x_864_; 
lean_dec(v_h__1_862_);
v___x_864_ = lean_apply_1(v_h__2_863_, lean_box(0));
return v___x_864_;
}
else
{
lean_object* v_val_865_; lean_object* v_snd_866_; lean_object* v_fst_867_; lean_object* v_fst_868_; lean_object* v_snd_869_; lean_object* v___x_870_; 
lean_dec(v_h__2_863_);
v_val_865_ = lean_ctor_get(v_x_861_, 0);
lean_inc(v_val_865_);
lean_dec_ref_known(v_x_861_, 1);
v_snd_866_ = lean_ctor_get(v_val_865_, 1);
lean_inc(v_snd_866_);
v_fst_867_ = lean_ctor_get(v_val_865_, 0);
lean_inc(v_fst_867_);
lean_dec(v_val_865_);
v_fst_868_ = lean_ctor_get(v_snd_866_, 0);
lean_inc(v_fst_868_);
v_snd_869_ = lean_ctor_get(v_snd_866_, 1);
lean_inc(v_snd_869_);
lean_dec(v_snd_866_);
v___x_870_ = lean_apply_4(v_h__1_862_, v_fst_867_, v_fst_868_, v_snd_869_, lean_box(0));
return v___x_870_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__52_splitter___redArg(lean_object* v_x_871_, lean_object* v_h__1_872_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = lean_apply_2(v_h__1_872_, v_x_871_, lean_box(0));
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__52_splitter(lean_object* v_aig_874_, lean_object* v_upper_875_, lean_object* v_h_876_, lean_object* v_state_877_, lean_object* v_cond_878_, lean_object* v_ifTrue_879_, lean_object* v_ifFalse_880_, lean_object* v_hltc_881_, lean_object* v_motive_882_, lean_object* v_x_883_, lean_object* v_h__1_884_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = lean_apply_2(v_h__1_884_, v_x_883_, lean_box(0));
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__52_splitter___boxed(lean_object* v_aig_886_, lean_object* v_upper_887_, lean_object* v_h_888_, lean_object* v_state_889_, lean_object* v_cond_890_, lean_object* v_ifTrue_891_, lean_object* v_ifFalse_892_, lean_object* v_hltc_893_, lean_object* v_motive_894_, lean_object* v_x_895_, lean_object* v_h__1_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__52_splitter(v_aig_886_, v_upper_887_, v_h_888_, v_state_889_, v_cond_890_, v_ifTrue_891_, v_ifFalse_892_, v_hltc_893_, v_motive_894_, v_x_895_, v_h__1_896_);
lean_dec(v_ifFalse_892_);
lean_dec(v_ifTrue_891_);
lean_dec(v_cond_890_);
lean_dec_ref(v_state_889_);
lean_dec(v_upper_887_);
lean_dec_ref(v_aig_886_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__50_splitter___redArg(lean_object* v_x_898_, lean_object* v_h__1_899_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = lean_apply_2(v_h__1_899_, v_x_898_, lean_box(0));
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__50_splitter(lean_object* v_aig_901_, lean_object* v_upper_902_, lean_object* v_h_903_, lean_object* v_cond_904_, lean_object* v_ifTrue_905_, lean_object* v_ifFalse_906_, lean_object* v_hltt_907_, lean_object* v_cstate_908_, lean_object* v_motive_909_, lean_object* v_x_910_, lean_object* v_h__1_911_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = lean_apply_2(v_h__1_911_, v_x_910_, lean_box(0));
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__50_splitter___boxed(lean_object* v_aig_913_, lean_object* v_upper_914_, lean_object* v_h_915_, lean_object* v_cond_916_, lean_object* v_ifTrue_917_, lean_object* v_ifFalse_918_, lean_object* v_hltt_919_, lean_object* v_cstate_920_, lean_object* v_motive_921_, lean_object* v_x_922_, lean_object* v_h__1_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__50_splitter(v_aig_913_, v_upper_914_, v_h_915_, v_cond_916_, v_ifTrue_917_, v_ifFalse_918_, v_hltt_919_, v_cstate_920_, v_motive_921_, v_x_922_, v_h__1_923_);
lean_dec_ref(v_cstate_920_);
lean_dec(v_ifFalse_918_);
lean_dec(v_ifTrue_917_);
lean_dec(v_cond_916_);
lean_dec(v_upper_914_);
lean_dec_ref(v_aig_913_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__48_splitter___redArg(lean_object* v_x_925_, lean_object* v_h__1_926_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = lean_apply_2(v_h__1_926_, v_x_925_, lean_box(0));
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__48_splitter(lean_object* v_aig_928_, lean_object* v_upper_929_, lean_object* v_h_930_, lean_object* v_cond_931_, lean_object* v_ifTrue_932_, lean_object* v_ifFalse_933_, lean_object* v_hltf_934_, lean_object* v_tstate_935_, lean_object* v_motive_936_, lean_object* v_x_937_, lean_object* v_h__1_938_){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = lean_apply_2(v_h__1_938_, v_x_937_, lean_box(0));
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__48_splitter___boxed(lean_object* v_aig_940_, lean_object* v_upper_941_, lean_object* v_h_942_, lean_object* v_cond_943_, lean_object* v_ifTrue_944_, lean_object* v_ifFalse_945_, lean_object* v_hltf_946_, lean_object* v_tstate_947_, lean_object* v_motive_948_, lean_object* v_x_949_, lean_object* v_h__1_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__48_splitter(v_aig_940_, v_upper_941_, v_h_942_, v_cond_943_, v_ifTrue_944_, v_ifFalse_945_, v_hltf_946_, v_tstate_947_, v_motive_948_, v_x_949_, v_h__1_950_);
lean_dec_ref(v_tstate_947_);
lean_dec(v_ifFalse_945_);
lean_dec(v_ifTrue_944_);
lean_dec(v_cond_943_);
lean_dec(v_upper_941_);
lean_dec_ref(v_aig_940_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__45_splitter___redArg(lean_object* v_x_952_, lean_object* v_h__1_953_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = lean_apply_2(v_h__1_953_, v_x_952_, lean_box(0));
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__45_splitter(lean_object* v_aig_955_, lean_object* v_upper_956_, lean_object* v_h_957_, lean_object* v_fstate_958_, lean_object* v_motive_959_, lean_object* v_x_960_, lean_object* v_h__1_961_){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = lean_apply_2(v_h__1_961_, v_x_960_, lean_box(0));
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__45_splitter___boxed(lean_object* v_aig_963_, lean_object* v_upper_964_, lean_object* v_h_965_, lean_object* v_fstate_966_, lean_object* v_motive_967_, lean_object* v_x_968_, lean_object* v_h__1_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__45_splitter(v_aig_963_, v_upper_964_, v_h_965_, v_fstate_966_, v_motive_967_, v_x_968_, v_h__1_969_);
lean_dec_ref(v_fstate_966_);
lean_dec(v_upper_964_);
lean_dec_ref(v_aig_963_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__56_splitter___redArg(lean_object* v_x_971_, lean_object* v_h__1_972_){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = lean_apply_2(v_h__1_972_, v_x_971_, lean_box(0));
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__56_splitter(lean_object* v_aig_974_, lean_object* v_upper_975_, lean_object* v_h_976_, lean_object* v_state_977_, lean_object* v_lhs_978_, lean_object* v_rhs_979_, lean_object* v_this_980_, lean_object* v_motive_981_, lean_object* v_x_982_, lean_object* v_h__1_983_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = lean_apply_2(v_h__1_983_, v_x_982_, lean_box(0));
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__56_splitter___boxed(lean_object* v_aig_985_, lean_object* v_upper_986_, lean_object* v_h_987_, lean_object* v_state_988_, lean_object* v_lhs_989_, lean_object* v_rhs_990_, lean_object* v_this_991_, lean_object* v_motive_992_, lean_object* v_x_993_, lean_object* v_h__1_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__56_splitter(v_aig_985_, v_upper_986_, v_h_987_, v_state_988_, v_lhs_989_, v_rhs_990_, v_this_991_, v_motive_992_, v_x_993_, v_h__1_994_);
lean_dec(v_rhs_990_);
lean_dec(v_lhs_989_);
lean_dec_ref(v_state_988_);
lean_dec(v_upper_986_);
lean_dec_ref(v_aig_985_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__54_splitter___redArg(lean_object* v_x_996_, lean_object* v_h__1_997_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = lean_apply_2(v_h__1_997_, v_x_996_, lean_box(0));
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__54_splitter(lean_object* v_aig_999_, lean_object* v_upper_1000_, lean_object* v_h_1001_, lean_object* v_lhs_1002_, lean_object* v_rhs_1003_, lean_object* v_this_1004_, lean_object* v_lstate_1005_, lean_object* v_motive_1006_, lean_object* v_x_1007_, lean_object* v_h__1_1008_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = lean_apply_2(v_h__1_1008_, v_x_1007_, lean_box(0));
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__54_splitter___boxed(lean_object* v_aig_1010_, lean_object* v_upper_1011_, lean_object* v_h_1012_, lean_object* v_lhs_1013_, lean_object* v_rhs_1014_, lean_object* v_this_1015_, lean_object* v_lstate_1016_, lean_object* v_motive_1017_, lean_object* v_x_1018_, lean_object* v_h__1_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__54_splitter(v_aig_1010_, v_upper_1011_, v_h_1012_, v_lhs_1013_, v_rhs_1014_, v_this_1015_, v_lstate_1016_, v_motive_1017_, v_x_1018_, v_h__1_1019_);
lean_dec_ref(v_lstate_1016_);
lean_dec(v_rhs_1014_);
lean_dec(v_lhs_1013_);
lean_dec(v_upper_1011_);
lean_dec_ref(v_aig_1010_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF(lean_object* v_entry_1021_){
_start:
{
lean_object* v_ref_1022_; lean_object* v_aig_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1050_; 
v_ref_1022_ = lean_ctor_get(v_entry_1021_, 1);
v_aig_1023_ = lean_ctor_get(v_entry_1021_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v_entry_1021_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1025_ = v_entry_1021_;
v_isShared_1026_ = v_isSharedCheck_1050_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_ref_1022_);
lean_inc(v_aig_1023_);
lean_dec(v_entry_1021_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1050_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v_gate_1027_; uint8_t v_invert_1028_; lean_object* v___x_1029_; lean_object* v_val_1030_; uint8_t v___y_1032_; 
v_gate_1027_ = lean_ctor_get(v_ref_1022_, 0);
lean_inc_n(v_gate_1027_, 2);
v_invert_1028_ = lean_ctor_get_uint8(v_ref_1022_, sizeof(void*)*1);
lean_dec_ref(v_ref_1022_);
lean_inc_ref(v_aig_1023_);
v___x_1029_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty(v_aig_1023_);
v_val_1030_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(v_aig_1023_, v_gate_1027_, v___x_1029_);
lean_dec_ref(v_aig_1023_);
if (v_invert_1028_ == 0)
{
uint8_t v___x_1048_; 
v___x_1048_ = 1;
v___y_1032_ = v___x_1048_;
goto v___jp_1031_;
}
else
{
uint8_t v___x_1049_; 
v___x_1049_ = 0;
v___y_1032_ = v___x_1049_;
goto v___jp_1031_;
}
v___jp_1031_:
{
lean_object* v_cnf_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1046_; 
v_cnf_1033_ = lean_ctor_get(v_val_1030_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v_val_1030_);
if (v_isSharedCheck_1046_ == 0)
{
lean_object* v_unused_1047_; 
v_unused_1047_ = lean_ctor_get(v_val_1030_, 1);
lean_dec(v_unused_1047_);
v___x_1035_ = v_val_1030_;
v_isShared_1036_ = v_isSharedCheck_1046_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_cnf_1033_);
lean_dec(v_val_1030_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1046_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1037_; lean_object* v___x_1039_; 
v___x_1037_ = lean_box(v___y_1032_);
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 1, v___x_1037_);
lean_ctor_set(v___x_1035_, 0, v_gate_1027_);
v___x_1039_ = v___x_1035_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_gate_1027_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v___x_1037_);
v___x_1039_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
lean_object* v___x_1040_; lean_object* v___x_1042_; 
v___x_1040_ = lean_box(0);
if (v_isShared_1026_ == 0)
{
lean_ctor_set_tag(v___x_1025_, 1);
lean_ctor_set(v___x_1025_, 1, v___x_1040_);
lean_ctor_set(v___x_1025_, 0, v___x_1039_);
v___x_1042_ = v___x_1025_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1039_);
lean_ctor_set(v_reuseFailAlloc_1044_, 1, v___x_1040_);
v___x_1042_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
lean_object* v___x_1043_; 
v___x_1043_ = lean_array_push(v_cnf_1033_, v___x_1042_);
return v___x_1043_;
}
}
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
