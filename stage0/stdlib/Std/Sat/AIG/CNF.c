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
lean_object* lean_nat_land(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Bool_toNat(uint8_t);
lean_object* lean_nat_lxor(lean_object*, lean_object*);
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
lean_object* v_ref_228_; lean_object* v_aig_229_; lean_object* v_gate_230_; uint8_t v_invert_231_; lean_object* v_decls_232_; uint8_t v___x_233_; 
v_ref_228_ = lean_ctor_get(v_entry_227_, 1);
v_aig_229_ = lean_ctor_get(v_entry_227_, 0);
v_gate_230_ = lean_ctor_get(v_ref_228_, 0);
v_invert_231_ = lean_ctor_get_uint8(v_ref_228_, sizeof(void*)*1);
v_decls_232_ = lean_ctor_get(v_aig_229_, 0);
v___x_233_ = l_Std_Sat_AIG_denote_go___redArg(v_gate_230_, v_decls_232_, v_assign_226_);
if (v_invert_231_ == 0)
{
return v___x_233_;
}
else
{
if (v___x_233_ == 0)
{
return v_invert_231_;
}
else
{
uint8_t v___x_234_; 
v___x_234_ = 0;
return v___x_234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment_spec__0___boxed(lean_object* v_assign_235_, lean_object* v_entry_236_){
_start:
{
uint8_t v_res_237_; lean_object* v_r_238_; 
v_res_237_ = l_Std_Sat_AIG_denote___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment_spec__0(v_assign_235_, v_entry_236_);
lean_dec_ref(v_entry_236_);
v_r_238_ = lean_box(v_res_237_);
return v_r_238_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___lam__0(lean_object* v_aig_239_, lean_object* v_assign1_240_, lean_object* v_idx_241_){
_start:
{
uint8_t v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_242_ = 0;
v___x_243_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_243_, 0, v_idx_241_);
lean_ctor_set_uint8(v___x_243_, sizeof(void*)*1, v___x_242_);
v___x_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_244_, 0, v_aig_239_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
v___x_245_ = l_Std_Sat_AIG_denote___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment_spec__0(v_assign1_240_, v___x_244_);
lean_dec_ref_known(v___x_244_, 2);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___lam__0___boxed(lean_object* v_aig_246_, lean_object* v_assign1_247_, lean_object* v_idx_248_){
_start:
{
uint8_t v_res_249_; lean_object* v_r_250_; 
v_res_249_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___lam__0(v_aig_246_, v_assign1_247_, v_idx_248_);
v_r_250_ = lean_box(v_res_249_);
return v_r_250_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment(lean_object* v_aig_251_, lean_object* v_assign1_252_, lean_object* v_var_253_){
_start:
{
lean_object* v___f_254_; uint8_t v___x_255_; 
lean_inc_ref(v_assign1_252_);
lean_inc_ref(v_aig_251_);
v___f_254_ = lean_alloc_closure((void*)(l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___lam__0___boxed), 3, 2);
lean_closure_set(v___f_254_, 0, v_aig_251_);
lean_closure_set(v___f_254_, 1, v_assign1_252_);
v___x_255_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_mixAssigns(v_aig_251_, v_assign1_252_, v___f_254_, v_var_253_);
lean_dec_ref(v_aig_251_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___boxed(lean_object* v_aig_256_, lean_object* v_assign1_257_, lean_object* v_var_258_){
_start:
{
uint8_t v_res_259_; lean_object* v_r_260_; 
v_res_259_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment(v_aig_256_, v_assign1_257_, v_var_258_);
v_r_260_ = lean_box(v_res_259_);
return v_r_260_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init(lean_object* v_aig_261_){
_start:
{
lean_object* v_decls_262_; lean_object* v___x_263_; uint8_t v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v_decls_262_ = lean_ctor_get(v_aig_261_, 0);
v___x_263_ = lean_array_get_size(v_decls_262_);
v___x_264_ = 0;
v___x_265_ = lean_box(v___x_264_);
v___x_266_ = lean_mk_array(v___x_263_, v___x_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___boxed(lean_object* v_aig_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init(v_aig_267_);
lean_dec_ref(v_aig_267_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg(lean_object* v_cache_269_, lean_object* v_idx_270_){
_start:
{
uint8_t v___x_271_; lean_object* v___x_272_; lean_object* v_out_273_; 
v___x_271_ = 1;
v___x_272_ = lean_box(v___x_271_);
v_out_273_ = lean_array_fset(v_cache_269_, v_idx_270_, v___x_272_);
return v_out_273_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg___boxed(lean_object* v_cache_274_, lean_object* v_idx_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg(v_cache_274_, v_idx_275_);
lean_dec(v_idx_275_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse(lean_object* v_aig_277_, lean_object* v_cnf_278_, lean_object* v_cache_279_, lean_object* v_idx_280_, lean_object* v_h_281_, lean_object* v_htip_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg(v_cache_279_, v_idx_280_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___boxed(lean_object* v_aig_284_, lean_object* v_cnf_285_, lean_object* v_cache_286_, lean_object* v_idx_287_, lean_object* v_h_288_, lean_object* v_htip_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse(v_aig_284_, v_cnf_285_, v_cache_286_, v_idx_287_, v_h_288_, v_htip_289_);
lean_dec(v_idx_287_);
lean_dec_ref(v_cnf_285_);
lean_dec_ref(v_aig_284_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg(lean_object* v_cache_291_, lean_object* v_idx_292_){
_start:
{
uint8_t v___x_293_; lean_object* v___x_294_; lean_object* v_out_295_; 
v___x_293_ = 1;
v___x_294_ = lean_box(v___x_293_);
v_out_295_ = lean_array_fset(v_cache_291_, v_idx_292_, v___x_294_);
return v_out_295_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg___boxed(lean_object* v_cache_296_, lean_object* v_idx_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg(v_cache_296_, v_idx_297_);
lean_dec(v_idx_297_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom(lean_object* v_aig_299_, lean_object* v_cnf_300_, lean_object* v_a_301_, lean_object* v_cache_302_, lean_object* v_idx_303_, lean_object* v_h_304_, lean_object* v_htip_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg(v_cache_302_, v_idx_303_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___boxed(lean_object* v_aig_307_, lean_object* v_cnf_308_, lean_object* v_a_309_, lean_object* v_cache_310_, lean_object* v_idx_311_, lean_object* v_h_312_, lean_object* v_htip_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom(v_aig_307_, v_cnf_308_, v_a_309_, v_cache_310_, v_idx_311_, v_h_312_, v_htip_313_);
lean_dec(v_idx_311_);
lean_dec(v_a_309_);
lean_dec_ref(v_cnf_308_);
lean_dec_ref(v_aig_307_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg(lean_object* v_lhs_315_, lean_object* v_rhs_316_, lean_object* v_cache_317_, lean_object* v_idx_318_){
_start:
{
uint8_t v___x_319_; lean_object* v___x_320_; lean_object* v_out_321_; 
v___x_319_ = 1;
v___x_320_ = lean_box(v___x_319_);
v_out_321_ = lean_array_fset(v_cache_317_, v_idx_318_, v___x_320_);
return v_out_321_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg___boxed(lean_object* v_lhs_322_, lean_object* v_rhs_323_, lean_object* v_cache_324_, lean_object* v_idx_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg(v_lhs_322_, v_rhs_323_, v_cache_324_, v_idx_325_);
lean_dec(v_idx_325_);
lean_dec(v_rhs_323_);
lean_dec(v_lhs_322_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate(lean_object* v_aig_327_, lean_object* v_cnf_328_, lean_object* v_lhs_329_, lean_object* v_rhs_330_, lean_object* v_cache_331_, lean_object* v_hlb_332_, lean_object* v_hrb_333_, lean_object* v_idx_334_, lean_object* v_h_335_, lean_object* v_htip_336_, lean_object* v_hl_337_, lean_object* v_hr_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg(v_lhs_329_, v_rhs_330_, v_cache_331_, v_idx_334_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___boxed(lean_object* v_aig_340_, lean_object* v_cnf_341_, lean_object* v_lhs_342_, lean_object* v_rhs_343_, lean_object* v_cache_344_, lean_object* v_hlb_345_, lean_object* v_hrb_346_, lean_object* v_idx_347_, lean_object* v_h_348_, lean_object* v_htip_349_, lean_object* v_hl_350_, lean_object* v_hr_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate(v_aig_340_, v_cnf_341_, v_lhs_342_, v_rhs_343_, v_cache_344_, v_hlb_345_, v_hrb_346_, v_idx_347_, v_h_348_, v_htip_349_, v_hl_350_, v_hr_351_);
lean_dec(v_idx_347_);
lean_dec(v_rhs_343_);
lean_dec(v_lhs_342_);
lean_dec_ref(v_cnf_341_);
lean_dec_ref(v_aig_340_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___redArg(lean_object* v_cache_353_, lean_object* v_cond_354_, lean_object* v_ifTrue_355_, lean_object* v_ifFalse_356_, lean_object* v_idx_357_){
_start:
{
uint8_t v___x_358_; lean_object* v___x_359_; lean_object* v_out_360_; 
v___x_358_ = 1;
v___x_359_ = lean_box(v___x_358_);
v_out_360_ = lean_array_fset(v_cache_353_, v_idx_357_, v___x_359_);
return v_out_360_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___redArg___boxed(lean_object* v_cache_361_, lean_object* v_cond_362_, lean_object* v_ifTrue_363_, lean_object* v_ifFalse_364_, lean_object* v_idx_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___redArg(v_cache_361_, v_cond_362_, v_ifTrue_363_, v_ifFalse_364_, v_idx_365_);
lean_dec(v_idx_365_);
lean_dec(v_ifFalse_364_);
lean_dec(v_ifTrue_363_);
lean_dec(v_cond_362_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte(lean_object* v_aig_367_, lean_object* v_cnf_368_, lean_object* v_cache_369_, lean_object* v_cond_370_, lean_object* v_ifTrue_371_, lean_object* v_ifFalse_372_, lean_object* v_idx_373_, lean_object* v_hcb_374_, lean_object* v_htb_375_, lean_object* v_hfb_376_, lean_object* v_h_377_, lean_object* v_hltc_378_, lean_object* v_hltt_379_, lean_object* v_hltf_380_, lean_object* v_hc_381_, lean_object* v_ht_382_, lean_object* v_hf_383_, lean_object* v_hdenote_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___redArg(v_cache_369_, v_cond_370_, v_ifTrue_371_, v_ifFalse_372_, v_idx_373_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___boxed(lean_object** _args){
lean_object* v_aig_386_ = _args[0];
lean_object* v_cnf_387_ = _args[1];
lean_object* v_cache_388_ = _args[2];
lean_object* v_cond_389_ = _args[3];
lean_object* v_ifTrue_390_ = _args[4];
lean_object* v_ifFalse_391_ = _args[5];
lean_object* v_idx_392_ = _args[6];
lean_object* v_hcb_393_ = _args[7];
lean_object* v_htb_394_ = _args[8];
lean_object* v_hfb_395_ = _args[9];
lean_object* v_h_396_ = _args[10];
lean_object* v_hltc_397_ = _args[11];
lean_object* v_hltt_398_ = _args[12];
lean_object* v_hltf_399_ = _args[13];
lean_object* v_hc_400_ = _args[14];
lean_object* v_ht_401_ = _args[15];
lean_object* v_hf_402_ = _args[16];
lean_object* v_hdenote_403_ = _args[17];
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte(v_aig_386_, v_cnf_387_, v_cache_388_, v_cond_389_, v_ifTrue_390_, v_ifFalse_391_, v_idx_392_, v_hcb_393_, v_htb_394_, v_hfb_395_, v_h_396_, v_hltc_397_, v_hltt_398_, v_hltf_399_, v_hc_400_, v_ht_401_, v_hf_402_, v_hdenote_403_);
lean_dec(v_idx_392_);
lean_dec(v_ifFalse_391_);
lean_dec(v_ifTrue_390_);
lean_dec(v_cond_389_);
lean_dec_ref(v_cnf_387_);
lean_dec_ref(v_aig_386_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty(lean_object* v_aig_405_){
_start:
{
lean_object* v_decls_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_418_; 
v_decls_406_ = lean_ctor_get(v_aig_405_, 0);
v___x_407_ = lean_array_get_size(v_decls_406_);
v___x_408_ = lean_unsigned_to_nat(2u);
v___x_409_ = lean_nat_mul(v___x_407_, v___x_408_);
v___x_410_ = lean_mk_empty_array_with_capacity(v___x_409_);
lean_dec(v___x_409_);
v___x_411_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init(v_aig_405_);
v_isSharedCheck_418_ = !lean_is_exclusive(v_aig_405_);
if (v_isSharedCheck_418_ == 0)
{
lean_object* v_unused_419_; lean_object* v_unused_420_; 
v_unused_419_ = lean_ctor_get(v_aig_405_, 1);
lean_dec(v_unused_419_);
v_unused_420_ = lean_ctor_get(v_aig_405_, 0);
lean_dec(v_unused_420_);
v___x_413_ = v_aig_405_;
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
else
{
lean_dec(v_aig_405_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_416_; 
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 1, v___x_411_);
lean_ctor_set(v___x_413_, 0, v___x_410_);
v___x_416_ = v___x_413_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_410_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v___x_411_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___redArg(lean_object* v_state_421_, lean_object* v_idx_422_){
_start:
{
lean_object* v_cnf_423_; lean_object* v_cache_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_434_; 
v_cnf_423_ = lean_ctor_get(v_state_421_, 0);
v_cache_424_ = lean_ctor_get(v_state_421_, 1);
v_isSharedCheck_434_ = !lean_is_exclusive(v_state_421_);
if (v_isSharedCheck_434_ == 0)
{
v___x_426_ = v_state_421_;
v_isShared_427_ = v_isSharedCheck_434_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_cache_424_);
lean_inc(v_cnf_423_);
lean_dec(v_state_421_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_434_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v_val_428_; lean_object* v_newCnf_429_; lean_object* v___x_430_; lean_object* v___x_432_; 
v_val_428_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg(v_cache_424_, v_idx_422_);
v_newCnf_429_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg(v_idx_422_);
v___x_430_ = l_Array_append___redArg(v_cnf_423_, v_newCnf_429_);
lean_dec_ref(v_newCnf_429_);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 1, v_val_428_);
lean_ctor_set(v___x_426_, 0, v___x_430_);
v___x_432_ = v___x_426_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v_val_428_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse(lean_object* v_aig_435_, lean_object* v_state_436_, lean_object* v_idx_437_, lean_object* v_h_438_, lean_object* v_htip_439_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___redArg(v_state_436_, v_idx_437_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___boxed(lean_object* v_aig_441_, lean_object* v_state_442_, lean_object* v_idx_443_, lean_object* v_h_444_, lean_object* v_htip_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse(v_aig_441_, v_state_442_, v_idx_443_, v_h_444_, v_htip_445_);
lean_dec_ref(v_aig_441_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg(lean_object* v_aig_447_, lean_object* v_a_448_, lean_object* v_state_449_, lean_object* v_idx_450_){
_start:
{
lean_object* v_cnf_451_; lean_object* v_cache_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_465_; 
v_cnf_451_ = lean_ctor_get(v_state_449_, 0);
v_cache_452_ = lean_ctor_get(v_state_449_, 1);
v_isSharedCheck_465_ = !lean_is_exclusive(v_state_449_);
if (v_isSharedCheck_465_ == 0)
{
v___x_454_ = v_state_449_;
v_isShared_455_ = v_isSharedCheck_465_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_cache_452_);
lean_inc(v_cnf_451_);
lean_dec(v_state_449_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_465_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v_decls_456_; lean_object* v_val_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v_newCnf_460_; lean_object* v___x_461_; lean_object* v___x_463_; 
v_decls_456_ = lean_ctor_get(v_aig_447_, 0);
v_val_457_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg(v_cache_452_, v_idx_450_);
v___x_458_ = lean_array_get_size(v_decls_456_);
v___x_459_ = lean_nat_add(v_a_448_, v___x_458_);
v_newCnf_460_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF___redArg(v_idx_450_, v___x_459_);
v___x_461_ = l_Array_append___redArg(v_cnf_451_, v_newCnf_460_);
lean_dec_ref(v_newCnf_460_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 1, v_val_457_);
lean_ctor_set(v___x_454_, 0, v___x_461_);
v___x_463_ = v___x_454_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_461_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v_val_457_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg___boxed(lean_object* v_aig_466_, lean_object* v_a_467_, lean_object* v_state_468_, lean_object* v_idx_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg(v_aig_466_, v_a_467_, v_state_468_, v_idx_469_);
lean_dec(v_a_467_);
lean_dec_ref(v_aig_466_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom(lean_object* v_aig_471_, lean_object* v_a_472_, lean_object* v_state_473_, lean_object* v_idx_474_, lean_object* v_h_475_, lean_object* v_htip_476_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg(v_aig_471_, v_a_472_, v_state_473_, v_idx_474_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___boxed(lean_object* v_aig_478_, lean_object* v_a_479_, lean_object* v_state_480_, lean_object* v_idx_481_, lean_object* v_h_482_, lean_object* v_htip_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom(v_aig_478_, v_a_479_, v_state_480_, v_idx_481_, v_h_482_, v_htip_483_);
lean_dec(v_a_479_);
lean_dec_ref(v_aig_478_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg(lean_object* v_lhs_485_, lean_object* v_rhs_486_, lean_object* v_state_487_, lean_object* v_idx_488_){
_start:
{
lean_object* v_cnf_489_; lean_object* v_cache_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_518_; 
v_cnf_489_ = lean_ctor_get(v_state_487_, 0);
v_cache_490_ = lean_ctor_get(v_state_487_, 1);
v_isSharedCheck_518_ = !lean_is_exclusive(v_state_487_);
if (v_isSharedCheck_518_ == 0)
{
v___x_492_ = v_state_487_;
v_isShared_493_ = v_isSharedCheck_518_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_cache_490_);
lean_inc(v_cnf_489_);
lean_dec(v_state_487_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_518_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; uint8_t v___y_498_; uint8_t v___y_499_; uint8_t v___y_507_; lean_object* v___x_513_; lean_object* v___x_514_; uint8_t v___x_515_; 
v___x_494_ = lean_unsigned_to_nat(1u);
v___x_495_ = lean_nat_shiftr(v_lhs_485_, v___x_494_);
v___x_496_ = lean_nat_shiftr(v_rhs_486_, v___x_494_);
v___x_513_ = lean_nat_land(v___x_494_, v_lhs_485_);
v___x_514_ = lean_unsigned_to_nat(0u);
v___x_515_ = lean_nat_dec_eq(v___x_513_, v___x_514_);
lean_dec(v___x_513_);
if (v___x_515_ == 0)
{
uint8_t v___x_516_; 
v___x_516_ = 1;
v___y_507_ = v___x_516_;
goto v___jp_506_;
}
else
{
uint8_t v___x_517_; 
v___x_517_ = 0;
v___y_507_ = v___x_517_;
goto v___jp_506_;
}
v___jp_497_:
{
lean_object* v_val_500_; lean_object* v_newCnf_501_; lean_object* v___x_502_; lean_object* v___x_504_; 
v_val_500_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg(v_lhs_485_, v_rhs_486_, v_cache_490_, v_idx_488_);
v_newCnf_501_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg(v_idx_488_, v___x_495_, v___x_496_, v___y_498_, v___y_499_);
v___x_502_ = l_Array_append___redArg(v_cnf_489_, v_newCnf_501_);
lean_dec_ref(v_newCnf_501_);
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 1, v_val_500_);
lean_ctor_set(v___x_492_, 0, v___x_502_);
v___x_504_ = v___x_492_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_502_);
lean_ctor_set(v_reuseFailAlloc_505_, 1, v_val_500_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
v___jp_506_:
{
lean_object* v___x_508_; lean_object* v___x_509_; uint8_t v___x_510_; 
v___x_508_ = lean_nat_land(v___x_494_, v_rhs_486_);
v___x_509_ = lean_unsigned_to_nat(0u);
v___x_510_ = lean_nat_dec_eq(v___x_508_, v___x_509_);
lean_dec(v___x_508_);
if (v___x_510_ == 0)
{
uint8_t v___x_511_; 
v___x_511_ = 1;
v___y_498_ = v___y_507_;
v___y_499_ = v___x_511_;
goto v___jp_497_;
}
else
{
uint8_t v___x_512_; 
v___x_512_ = 0;
v___y_498_ = v___y_507_;
v___y_499_ = v___x_512_;
goto v___jp_497_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg___boxed(lean_object* v_lhs_519_, lean_object* v_rhs_520_, lean_object* v_state_521_, lean_object* v_idx_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg(v_lhs_519_, v_rhs_520_, v_state_521_, v_idx_522_);
lean_dec(v_rhs_520_);
lean_dec(v_lhs_519_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate(lean_object* v_aig_524_, lean_object* v_lhs_525_, lean_object* v_rhs_526_, lean_object* v_state_527_, lean_object* v_hlb_528_, lean_object* v_hrb_529_, lean_object* v_idx_530_, lean_object* v_h_531_, lean_object* v_htip_532_, lean_object* v_hl_533_, lean_object* v_hr_534_){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg(v_lhs_525_, v_rhs_526_, v_state_527_, v_idx_530_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___boxed(lean_object* v_aig_536_, lean_object* v_lhs_537_, lean_object* v_rhs_538_, lean_object* v_state_539_, lean_object* v_hlb_540_, lean_object* v_hrb_541_, lean_object* v_idx_542_, lean_object* v_h_543_, lean_object* v_htip_544_, lean_object* v_hl_545_, lean_object* v_hr_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate(v_aig_536_, v_lhs_537_, v_rhs_538_, v_state_539_, v_hlb_540_, v_hrb_541_, v_idx_542_, v_h_543_, v_htip_544_, v_hl_545_, v_hr_546_);
lean_dec(v_rhs_538_);
lean_dec(v_lhs_537_);
lean_dec_ref(v_aig_536_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___redArg(lean_object* v_state_548_, lean_object* v_cond_549_, lean_object* v_ifTrue_550_, lean_object* v_ifFalse_551_, lean_object* v_idx_552_){
_start:
{
lean_object* v_cnf_553_; lean_object* v_cache_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_592_; 
v_cnf_553_ = lean_ctor_get(v_state_548_, 0);
v_cache_554_ = lean_ctor_get(v_state_548_, 1);
v_isSharedCheck_592_ = !lean_is_exclusive(v_state_548_);
if (v_isSharedCheck_592_ == 0)
{
v___x_556_ = v_state_548_;
v_isShared_557_ = v_isSharedCheck_592_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_cache_554_);
lean_inc(v_cnf_553_);
lean_dec(v_state_548_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_592_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; uint8_t v___y_563_; uint8_t v___y_564_; uint8_t v___y_565_; uint8_t v___y_573_; uint8_t v___y_574_; uint8_t v___y_581_; lean_object* v___x_587_; lean_object* v___x_588_; uint8_t v___x_589_; 
v___x_558_ = lean_unsigned_to_nat(1u);
v___x_559_ = lean_nat_shiftr(v_cond_549_, v___x_558_);
v___x_560_ = lean_nat_shiftr(v_ifTrue_550_, v___x_558_);
v___x_561_ = lean_nat_shiftr(v_ifFalse_551_, v___x_558_);
v___x_587_ = lean_nat_land(v___x_558_, v_cond_549_);
v___x_588_ = lean_unsigned_to_nat(0u);
v___x_589_ = lean_nat_dec_eq(v___x_587_, v___x_588_);
lean_dec(v___x_587_);
if (v___x_589_ == 0)
{
uint8_t v___x_590_; 
v___x_590_ = 1;
v___y_581_ = v___x_590_;
goto v___jp_580_;
}
else
{
uint8_t v___x_591_; 
v___x_591_ = 0;
v___y_581_ = v___x_591_;
goto v___jp_580_;
}
v___jp_562_:
{
lean_object* v_val_566_; lean_object* v_newCnf_567_; lean_object* v___x_568_; lean_object* v___x_570_; 
v_val_566_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___redArg(v_cache_554_, v_cond_549_, v_ifTrue_550_, v_ifFalse_551_, v_idx_552_);
v_newCnf_567_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF___redArg(v_idx_552_, v___x_559_, v___x_560_, v___x_561_, v___y_563_, v___y_564_, v___y_565_);
v___x_568_ = l_Array_append___redArg(v_cnf_553_, v_newCnf_567_);
lean_dec_ref(v_newCnf_567_);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 1, v_val_566_);
lean_ctor_set(v___x_556_, 0, v___x_568_);
v___x_570_ = v___x_556_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_568_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_val_566_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
v___jp_572_:
{
lean_object* v___x_575_; lean_object* v___x_576_; uint8_t v___x_577_; 
v___x_575_ = lean_nat_land(v___x_558_, v_ifFalse_551_);
v___x_576_ = lean_unsigned_to_nat(0u);
v___x_577_ = lean_nat_dec_eq(v___x_575_, v___x_576_);
lean_dec(v___x_575_);
if (v___x_577_ == 0)
{
uint8_t v___x_578_; 
v___x_578_ = 1;
v___y_563_ = v___y_573_;
v___y_564_ = v___y_574_;
v___y_565_ = v___x_578_;
goto v___jp_562_;
}
else
{
uint8_t v___x_579_; 
v___x_579_ = 0;
v___y_563_ = v___y_573_;
v___y_564_ = v___y_574_;
v___y_565_ = v___x_579_;
goto v___jp_562_;
}
}
v___jp_580_:
{
lean_object* v___x_582_; lean_object* v___x_583_; uint8_t v___x_584_; 
v___x_582_ = lean_nat_land(v___x_558_, v_ifTrue_550_);
v___x_583_ = lean_unsigned_to_nat(0u);
v___x_584_ = lean_nat_dec_eq(v___x_582_, v___x_583_);
lean_dec(v___x_582_);
if (v___x_584_ == 0)
{
uint8_t v___x_585_; 
v___x_585_ = 1;
v___y_573_ = v___y_581_;
v___y_574_ = v___x_585_;
goto v___jp_572_;
}
else
{
uint8_t v___x_586_; 
v___x_586_ = 0;
v___y_573_ = v___y_581_;
v___y_574_ = v___x_586_;
goto v___jp_572_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___redArg___boxed(lean_object* v_state_593_, lean_object* v_cond_594_, lean_object* v_ifTrue_595_, lean_object* v_ifFalse_596_, lean_object* v_idx_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___redArg(v_state_593_, v_cond_594_, v_ifTrue_595_, v_ifFalse_596_, v_idx_597_);
lean_dec(v_ifFalse_596_);
lean_dec(v_ifTrue_595_);
lean_dec(v_cond_594_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte(lean_object* v_aig_599_, lean_object* v_state_600_, lean_object* v_cond_601_, lean_object* v_ifTrue_602_, lean_object* v_ifFalse_603_, lean_object* v_idx_604_, lean_object* v_hcb_605_, lean_object* v_htb_606_, lean_object* v_hfb_607_, lean_object* v_h_608_, lean_object* v_hltc_609_, lean_object* v_hltt_610_, lean_object* v_hltf_611_, lean_object* v_hc_612_, lean_object* v_ht_613_, lean_object* v_hf_614_, lean_object* v_hdenote_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___redArg(v_state_600_, v_cond_601_, v_ifTrue_602_, v_ifFalse_603_, v_idx_604_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___boxed(lean_object** _args){
lean_object* v_aig_617_ = _args[0];
lean_object* v_state_618_ = _args[1];
lean_object* v_cond_619_ = _args[2];
lean_object* v_ifTrue_620_ = _args[3];
lean_object* v_ifFalse_621_ = _args[4];
lean_object* v_idx_622_ = _args[5];
lean_object* v_hcb_623_ = _args[6];
lean_object* v_htb_624_ = _args[7];
lean_object* v_hfb_625_ = _args[8];
lean_object* v_h_626_ = _args[9];
lean_object* v_hltc_627_ = _args[10];
lean_object* v_hltt_628_ = _args[11];
lean_object* v_hltf_629_ = _args[12];
lean_object* v_hc_630_ = _args[13];
lean_object* v_ht_631_ = _args[14];
lean_object* v_hf_632_ = _args[15];
lean_object* v_hdenote_633_ = _args[16];
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte(v_aig_617_, v_state_618_, v_cond_619_, v_ifTrue_620_, v_ifFalse_621_, v_idx_622_, v_hcb_623_, v_htb_624_, v_hfb_625_, v_h_626_, v_hltc_627_, v_hltt_628_, v_hltf_629_, v_hc_630_, v_ht_631_, v_hf_632_, v_hdenote_633_);
lean_dec(v_ifFalse_621_);
lean_dec(v_ifTrue_620_);
lean_dec(v_cond_619_);
lean_dec_ref(v_aig_617_);
return v_res_634_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg(lean_object* v_assign_635_, lean_object* v_state_636_){
_start:
{
lean_object* v_cnf_637_; uint8_t v___x_638_; 
v_cnf_637_ = lean_ctor_get(v_state_636_, 0);
v___x_638_ = l_Std_Sat_CNF_eval___redArg(v_assign_635_, v_cnf_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg___boxed(lean_object* v_assign_639_, lean_object* v_state_640_){
_start:
{
uint8_t v_res_641_; lean_object* v_r_642_; 
v_res_641_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg(v_assign_639_, v_state_640_);
lean_dec_ref(v_state_640_);
v_r_642_ = lean_box(v_res_641_);
return v_r_642_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval(lean_object* v_aig_643_, lean_object* v_assign_644_, lean_object* v_state_645_){
_start:
{
uint8_t v___x_646_; 
v___x_646_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg(v_assign_644_, v_state_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___boxed(lean_object* v_aig_647_, lean_object* v_assign_648_, lean_object* v_state_649_){
_start:
{
uint8_t v_res_650_; lean_object* v_r_651_; 
v_res_650_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval(v_aig_647_, v_assign_648_, v_state_649_);
lean_dec_ref(v_state_649_);
lean_dec_ref(v_aig_647_);
v_r_651_ = lean_box(v_res_650_);
return v_r_651_;
}
}
static lean_object* _init_l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg___closed__0(void){
_start:
{
uint8_t v___x_652_; lean_object* v___x_653_; 
v___x_652_ = 1;
v___x_653_ = l_Bool_toNat(v___x_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg(lean_object* v_l0_654_, lean_object* v_l1_655_, lean_object* v_r0_656_, lean_object* v_r1_657_){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; uint8_t v___x_660_; 
v___x_658_ = lean_obj_once(&l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg___closed__0, &l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg___closed__0_once, _init_l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg___closed__0);
v___x_659_ = lean_nat_lxor(v_r0_656_, v___x_658_);
v___x_660_ = lean_nat_dec_eq(v_l0_654_, v___x_659_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; uint8_t v___x_662_; 
v___x_661_ = lean_nat_lxor(v_r1_657_, v___x_658_);
v___x_662_ = lean_nat_dec_eq(v_l0_654_, v___x_661_);
if (v___x_662_ == 0)
{
uint8_t v___x_663_; 
v___x_663_ = lean_nat_dec_eq(v_l1_655_, v___x_659_);
if (v___x_663_ == 0)
{
uint8_t v___x_664_; 
v___x_664_ = lean_nat_dec_eq(v_l1_655_, v___x_661_);
lean_dec(v___x_661_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; 
lean_dec(v___x_659_);
lean_dec(v_l1_655_);
lean_dec(v_l0_654_);
v___x_665_ = lean_box(0);
return v___x_665_;
}
else
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_666_ = lean_nat_lxor(v_l0_654_, v___x_658_);
lean_dec(v_l0_654_);
v___x_667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_666_);
lean_ctor_set(v___x_667_, 1, v___x_659_);
v___x_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_668_, 0, v_l1_655_);
lean_ctor_set(v___x_668_, 1, v___x_667_);
v___x_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
return v___x_669_;
}
}
else
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
lean_dec(v___x_659_);
v___x_670_ = lean_nat_lxor(v_l0_654_, v___x_658_);
lean_dec(v_l0_654_);
v___x_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
lean_ctor_set(v___x_671_, 1, v___x_661_);
v___x_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_672_, 0, v_l1_655_);
lean_ctor_set(v___x_672_, 1, v___x_671_);
v___x_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
return v___x_673_;
}
}
else
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
lean_dec(v___x_661_);
v___x_674_ = lean_nat_lxor(v_l1_655_, v___x_658_);
lean_dec(v_l1_655_);
v___x_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
lean_ctor_set(v___x_675_, 1, v___x_659_);
v___x_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_676_, 0, v_l0_654_);
lean_ctor_set(v___x_676_, 1, v___x_675_);
v___x_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
return v___x_677_;
}
}
else
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
lean_dec(v___x_659_);
v___x_678_ = lean_nat_lxor(v_l1_655_, v___x_658_);
lean_dec(v_l1_655_);
v___x_679_ = lean_nat_lxor(v_r1_657_, v___x_658_);
v___x_680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_680_, 0, v___x_678_);
lean_ctor_set(v___x_680_, 1, v___x_679_);
v___x_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_681_, 0, v_l0_654_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
v___x_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
return v___x_682_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg___boxed(lean_object* v_l0_683_, lean_object* v_l1_684_, lean_object* v_r0_685_, lean_object* v_r1_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg(v_l0_683_, v_l1_684_, v_r0_685_, v_r1_686_);
lean_dec(v_r1_686_);
lean_dec(v_r0_685_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go(lean_object* v_l_688_, lean_object* v_r_689_, lean_object* v_l0_690_, lean_object* v_l1_691_, lean_object* v_r0_692_, lean_object* v_r1_693_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg(v_l0_690_, v_l1_691_, v_r0_692_, v_r1_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___boxed(lean_object* v_l_695_, lean_object* v_r_696_, lean_object* v_l0_697_, lean_object* v_l1_698_, lean_object* v_r0_699_, lean_object* v_r1_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go(v_l_695_, v_r_696_, v_l0_697_, v_l1_698_, v_r0_699_, v_r1_700_);
lean_dec(v_r1_700_);
lean_dec(v_r0_699_);
lean_dec(v_r_696_);
lean_dec(v_l_695_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___redArg(lean_object* v_aig_702_, lean_object* v_root_703_){
_start:
{
lean_object* v_decls_704_; lean_object* v___x_705_; 
v_decls_704_ = lean_ctor_get(v_aig_702_, 0);
v___x_705_ = lean_array_fget_borrowed(v_decls_704_, v_root_703_);
if (lean_obj_tag(v___x_705_) == 2)
{
lean_object* v_l_706_; lean_object* v_r_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
v_l_706_ = lean_ctor_get(v___x_705_, 0);
v_r_707_ = lean_ctor_get(v___x_705_, 1);
v___x_708_ = lean_unsigned_to_nat(1u);
v___x_709_ = lean_nat_land(v___x_708_, v_l_706_);
v___x_710_ = lean_unsigned_to_nat(0u);
v___x_711_ = lean_nat_dec_eq(v___x_709_, v___x_710_);
lean_dec(v___x_709_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; uint8_t v___x_713_; 
v___x_712_ = lean_nat_land(v___x_708_, v_r_707_);
v___x_713_ = lean_nat_dec_eq(v___x_712_, v___x_710_);
lean_dec(v___x_712_);
if (v___x_713_ == 0)
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = lean_nat_shiftr(v_l_706_, v___x_708_);
v___x_715_ = lean_array_fget_borrowed(v_decls_704_, v___x_714_);
lean_dec(v___x_714_);
if (lean_obj_tag(v___x_715_) == 2)
{
lean_object* v_l_716_; lean_object* v_r_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v_l_716_ = lean_ctor_get(v___x_715_, 0);
v_r_717_ = lean_ctor_get(v___x_715_, 1);
v___x_718_ = lean_nat_shiftr(v_r_707_, v___x_708_);
v___x_719_ = lean_array_fget_borrowed(v_decls_704_, v___x_718_);
lean_dec(v___x_718_);
if (lean_obj_tag(v___x_719_) == 2)
{
lean_object* v_l_720_; lean_object* v_r_721_; lean_object* v___x_722_; 
v_l_720_ = lean_ctor_get(v___x_719_, 0);
v_r_721_ = lean_ctor_get(v___x_719_, 1);
lean_inc(v_r_717_);
lean_inc(v_l_716_);
v___x_722_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg(v_l_716_, v_r_717_, v_l_720_, v_r_721_);
return v___x_722_;
}
else
{
lean_object* v___x_723_; 
v___x_723_ = lean_box(0);
return v___x_723_;
}
}
else
{
lean_object* v___x_724_; 
v___x_724_ = lean_box(0);
return v___x_724_;
}
}
else
{
lean_object* v___x_725_; 
v___x_725_ = lean_box(0);
return v___x_725_;
}
}
else
{
lean_object* v___x_726_; 
v___x_726_ = lean_box(0);
return v___x_726_;
}
}
else
{
lean_object* v___x_727_; 
v___x_727_ = lean_box(0);
return v___x_727_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___redArg___boxed(lean_object* v_aig_728_, lean_object* v_root_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___redArg(v_aig_728_, v_root_729_);
lean_dec(v_root_729_);
lean_dec_ref(v_aig_728_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte(lean_object* v_aig_731_, lean_object* v_root_732_, lean_object* v_h_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___redArg(v_aig_731_, v_root_732_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___boxed(lean_object* v_aig_735_, lean_object* v_root_736_, lean_object* v_h_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte(v_aig_735_, v_root_736_, v_h_737_);
lean_dec(v_root_736_);
lean_dec_ref(v_aig_735_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_match__4_splitter___redArg(lean_object* v_x_739_, lean_object* v_h__1_740_, lean_object* v_h__2_741_){
_start:
{
if (lean_obj_tag(v_x_739_) == 2)
{
lean_object* v_l_742_; lean_object* v_r_743_; lean_object* v___x_744_; 
lean_dec(v_h__2_741_);
v_l_742_ = lean_ctor_get(v_x_739_, 0);
lean_inc(v_l_742_);
v_r_743_ = lean_ctor_get(v_x_739_, 1);
lean_inc(v_r_743_);
lean_dec_ref_known(v_x_739_, 2);
v___x_744_ = lean_apply_3(v_h__1_740_, v_l_742_, v_r_743_, lean_box(0));
return v___x_744_;
}
else
{
lean_object* v___x_745_; 
lean_dec(v_h__1_740_);
v___x_745_ = lean_apply_3(v_h__2_741_, v_x_739_, lean_box(0), lean_box(0));
return v___x_745_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_match__4_splitter(lean_object* v_motive_746_, lean_object* v_x_747_, lean_object* v_h__1_748_, lean_object* v_h__2_749_){
_start:
{
if (lean_obj_tag(v_x_747_) == 2)
{
lean_object* v_l_750_; lean_object* v_r_751_; lean_object* v___x_752_; 
lean_dec(v_h__2_749_);
v_l_750_ = lean_ctor_get(v_x_747_, 0);
lean_inc(v_l_750_);
v_r_751_ = lean_ctor_get(v_x_747_, 1);
lean_inc(v_r_751_);
lean_dec_ref_known(v_x_747_, 2);
v___x_752_ = lean_apply_3(v_h__1_748_, v_l_750_, v_r_751_, lean_box(0));
return v___x_752_;
}
else
{
lean_object* v___x_753_; 
lean_dec(v_h__1_748_);
v___x_753_ = lean_apply_3(v_h__2_749_, v_x_747_, lean_box(0), lean_box(0));
return v___x_753_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_match__1_splitter___redArg(lean_object* v_x_754_, lean_object* v_x_755_, lean_object* v_h__1_756_, lean_object* v_h__2_757_){
_start:
{
if (lean_obj_tag(v_x_754_) == 2)
{
if (lean_obj_tag(v_x_755_) == 2)
{
lean_object* v_l_758_; lean_object* v_r_759_; lean_object* v_l_760_; lean_object* v_r_761_; lean_object* v___x_762_; 
lean_dec(v_h__2_757_);
v_l_758_ = lean_ctor_get(v_x_754_, 0);
lean_inc(v_l_758_);
v_r_759_ = lean_ctor_get(v_x_754_, 1);
lean_inc(v_r_759_);
lean_dec_ref_known(v_x_754_, 2);
v_l_760_ = lean_ctor_get(v_x_755_, 0);
lean_inc(v_l_760_);
v_r_761_ = lean_ctor_get(v_x_755_, 1);
lean_inc(v_r_761_);
lean_dec_ref_known(v_x_755_, 2);
v___x_762_ = lean_apply_6(v_h__1_756_, v_l_758_, v_r_759_, v_l_760_, v_r_761_, lean_box(0), lean_box(0));
return v___x_762_;
}
else
{
lean_object* v___x_763_; 
lean_dec(v_h__1_756_);
v___x_763_ = lean_apply_5(v_h__2_757_, v_x_754_, v_x_755_, lean_box(0), lean_box(0), lean_box(0));
return v___x_763_;
}
}
else
{
lean_object* v___x_764_; 
lean_dec(v_h__1_756_);
v___x_764_ = lean_apply_5(v_h__2_757_, v_x_754_, v_x_755_, lean_box(0), lean_box(0), lean_box(0));
return v___x_764_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_match__1_splitter(lean_object* v_motive_765_, lean_object* v_x_766_, lean_object* v_x_767_, lean_object* v_h__1_768_, lean_object* v_h__2_769_){
_start:
{
if (lean_obj_tag(v_x_766_) == 2)
{
if (lean_obj_tag(v_x_767_) == 2)
{
lean_object* v_l_770_; lean_object* v_r_771_; lean_object* v_l_772_; lean_object* v_r_773_; lean_object* v___x_774_; 
lean_dec(v_h__2_769_);
v_l_770_ = lean_ctor_get(v_x_766_, 0);
lean_inc(v_l_770_);
v_r_771_ = lean_ctor_get(v_x_766_, 1);
lean_inc(v_r_771_);
lean_dec_ref_known(v_x_766_, 2);
v_l_772_ = lean_ctor_get(v_x_767_, 0);
lean_inc(v_l_772_);
v_r_773_ = lean_ctor_get(v_x_767_, 1);
lean_inc(v_r_773_);
lean_dec_ref_known(v_x_767_, 2);
v___x_774_ = lean_apply_6(v_h__1_768_, v_l_770_, v_r_771_, v_l_772_, v_r_773_, lean_box(0), lean_box(0));
return v___x_774_;
}
else
{
lean_object* v___x_775_; 
lean_dec(v_h__1_768_);
v___x_775_ = lean_apply_5(v_h__2_769_, v_x_766_, v_x_767_, lean_box(0), lean_box(0), lean_box(0));
return v___x_775_;
}
}
else
{
lean_object* v___x_776_; 
lean_dec(v_h__1_768_);
v___x_776_ = lean_apply_5(v_h__2_769_, v_x_766_, v_x_767_, lean_box(0), lean_box(0), lean_box(0));
return v___x_776_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(lean_object* v_aig_777_, lean_object* v_upper_778_, lean_object* v_state_779_){
_start:
{
lean_object* v_cache_780_; lean_object* v___x_781_; uint8_t v___x_782_; 
v_cache_780_ = lean_ctor_get(v_state_779_, 1);
v___x_781_ = lean_array_fget_borrowed(v_cache_780_, v_upper_778_);
v___x_782_ = lean_unbox(v___x_781_);
if (v___x_782_ == 0)
{
lean_object* v_decls_783_; lean_object* v_decl_784_; 
v_decls_783_ = lean_ctor_get(v_aig_777_, 0);
v_decl_784_ = lean_array_fget_borrowed(v_decls_783_, v_upper_778_);
switch(lean_obj_tag(v_decl_784_))
{
case 0:
{
lean_object* v___x_785_; 
v___x_785_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___redArg(v_state_779_, v_upper_778_);
return v___x_785_;
}
case 1:
{
lean_object* v_idx_786_; lean_object* v___x_787_; 
v_idx_786_ = lean_ctor_get(v_decl_784_, 0);
v___x_787_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg(v_aig_777_, v_idx_786_, v_state_779_, v_upper_778_);
return v___x_787_;
}
default: 
{
lean_object* v_l_788_; lean_object* v_r_789_; lean_object* v___x_790_; 
v_l_788_ = lean_ctor_get(v_decl_784_, 0);
v_r_789_ = lean_ctor_get(v_decl_784_, 1);
v___x_790_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___redArg(v_aig_777_, v_upper_778_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v_val_793_; lean_object* v___x_794_; lean_object* v_val_795_; lean_object* v_val_796_; 
v___x_791_ = lean_unsigned_to_nat(1u);
v___x_792_ = lean_nat_shiftr(v_l_788_, v___x_791_);
v_val_793_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(v_aig_777_, v___x_792_, v_state_779_);
v___x_794_ = lean_nat_shiftr(v_r_789_, v___x_791_);
v_val_795_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(v_aig_777_, v___x_794_, v_val_793_);
v_val_796_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg(v_l_788_, v_r_789_, v_val_795_, v_upper_778_);
return v_val_796_;
}
else
{
lean_object* v_val_797_; lean_object* v_snd_798_; lean_object* v_fst_799_; lean_object* v_fst_800_; lean_object* v_snd_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v_val_804_; lean_object* v___x_805_; lean_object* v_val_806_; lean_object* v___x_807_; lean_object* v_val_808_; lean_object* v_val_809_; 
v_val_797_ = lean_ctor_get(v___x_790_, 0);
lean_inc(v_val_797_);
lean_dec_ref_known(v___x_790_, 1);
v_snd_798_ = lean_ctor_get(v_val_797_, 1);
lean_inc(v_snd_798_);
v_fst_799_ = lean_ctor_get(v_val_797_, 0);
lean_inc(v_fst_799_);
lean_dec(v_val_797_);
v_fst_800_ = lean_ctor_get(v_snd_798_, 0);
lean_inc(v_fst_800_);
v_snd_801_ = lean_ctor_get(v_snd_798_, 1);
lean_inc(v_snd_801_);
lean_dec(v_snd_798_);
v___x_802_ = lean_unsigned_to_nat(1u);
v___x_803_ = lean_nat_shiftr(v_fst_799_, v___x_802_);
v_val_804_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(v_aig_777_, v___x_803_, v_state_779_);
v___x_805_ = lean_nat_shiftr(v_fst_800_, v___x_802_);
v_val_806_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(v_aig_777_, v___x_805_, v_val_804_);
v___x_807_ = lean_nat_shiftr(v_snd_801_, v___x_802_);
v_val_808_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(v_aig_777_, v___x_807_, v_val_806_);
v_val_809_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___redArg(v_val_808_, v_fst_799_, v_fst_800_, v_snd_801_, v_upper_778_);
lean_dec(v_snd_801_);
lean_dec(v_fst_800_);
lean_dec(v_fst_799_);
return v_val_809_;
}
}
}
}
else
{
lean_dec(v_upper_778_);
return v_state_779_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg___boxed(lean_object* v_aig_810_, lean_object* v_upper_811_, lean_object* v_state_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(v_aig_810_, v_upper_811_, v_state_812_);
lean_dec_ref(v_aig_810_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go(lean_object* v_aig_814_, lean_object* v_upper_815_, lean_object* v_h_816_, lean_object* v_state_817_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(v_aig_814_, v_upper_815_, v_state_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___boxed(lean_object* v_aig_819_, lean_object* v_upper_820_, lean_object* v_h_821_, lean_object* v_state_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go(v_aig_819_, v_upper_820_, v_h_821_, v_state_822_);
lean_dec_ref(v_aig_819_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go_match__103_splitter___redArg(lean_object* v_decl_824_, lean_object* v_h__1_825_, lean_object* v_h__2_826_, lean_object* v_h__3_827_){
_start:
{
switch(lean_obj_tag(v_decl_824_))
{
case 0:
{
lean_object* v___x_828_; 
lean_dec(v_h__3_827_);
lean_dec(v_h__2_826_);
v___x_828_ = lean_apply_1(v_h__1_825_, lean_box(0));
return v___x_828_;
}
case 1:
{
lean_object* v_idx_829_; lean_object* v___x_830_; 
lean_dec(v_h__3_827_);
lean_dec(v_h__1_825_);
v_idx_829_ = lean_ctor_get(v_decl_824_, 0);
lean_inc(v_idx_829_);
lean_dec_ref_known(v_decl_824_, 1);
v___x_830_ = lean_apply_2(v_h__2_826_, v_idx_829_, lean_box(0));
return v___x_830_;
}
default: 
{
lean_object* v_l_831_; lean_object* v_r_832_; lean_object* v___x_833_; 
lean_dec(v_h__2_826_);
lean_dec(v_h__1_825_);
v_l_831_ = lean_ctor_get(v_decl_824_, 0);
lean_inc(v_l_831_);
v_r_832_ = lean_ctor_get(v_decl_824_, 1);
lean_inc(v_r_832_);
lean_dec_ref_known(v_decl_824_, 2);
v___x_833_ = lean_apply_3(v_h__3_827_, v_l_831_, v_r_832_, lean_box(0));
return v___x_833_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go_match__103_splitter(lean_object* v_motive_834_, lean_object* v_decl_835_, lean_object* v_h__1_836_, lean_object* v_h__2_837_, lean_object* v_h__3_838_){
_start:
{
switch(lean_obj_tag(v_decl_835_))
{
case 0:
{
lean_object* v___x_839_; 
lean_dec(v_h__3_838_);
lean_dec(v_h__2_837_);
v___x_839_ = lean_apply_1(v_h__1_836_, lean_box(0));
return v___x_839_;
}
case 1:
{
lean_object* v_idx_840_; lean_object* v___x_841_; 
lean_dec(v_h__3_838_);
lean_dec(v_h__1_836_);
v_idx_840_ = lean_ctor_get(v_decl_835_, 0);
lean_inc(v_idx_840_);
lean_dec_ref_known(v_decl_835_, 1);
v___x_841_ = lean_apply_2(v_h__2_837_, v_idx_840_, lean_box(0));
return v___x_841_;
}
default: 
{
lean_object* v_l_842_; lean_object* v_r_843_; lean_object* v___x_844_; 
lean_dec(v_h__2_837_);
lean_dec(v_h__1_836_);
v_l_842_ = lean_ctor_get(v_decl_835_, 0);
lean_inc(v_l_842_);
v_r_843_ = lean_ctor_get(v_decl_835_, 1);
lean_inc(v_r_843_);
lean_dec_ref_known(v_decl_835_, 2);
v___x_844_ = lean_apply_3(v_h__3_838_, v_l_842_, v_r_843_, lean_box(0));
return v___x_844_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go_match__81_splitter___redArg(lean_object* v_x_845_, lean_object* v_h__1_846_, lean_object* v_h__2_847_){
_start:
{
if (lean_obj_tag(v_x_845_) == 0)
{
lean_object* v___x_848_; 
lean_dec(v_h__1_846_);
v___x_848_ = lean_apply_1(v_h__2_847_, lean_box(0));
return v___x_848_;
}
else
{
lean_object* v_val_849_; lean_object* v_snd_850_; lean_object* v_fst_851_; lean_object* v_fst_852_; lean_object* v_snd_853_; lean_object* v___x_854_; 
lean_dec(v_h__2_847_);
v_val_849_ = lean_ctor_get(v_x_845_, 0);
lean_inc(v_val_849_);
lean_dec_ref_known(v_x_845_, 1);
v_snd_850_ = lean_ctor_get(v_val_849_, 1);
lean_inc(v_snd_850_);
v_fst_851_ = lean_ctor_get(v_val_849_, 0);
lean_inc(v_fst_851_);
lean_dec(v_val_849_);
v_fst_852_ = lean_ctor_get(v_snd_850_, 0);
lean_inc(v_fst_852_);
v_snd_853_ = lean_ctor_get(v_snd_850_, 1);
lean_inc(v_snd_853_);
lean_dec(v_snd_850_);
v___x_854_ = lean_apply_4(v_h__1_846_, v_fst_851_, v_fst_852_, v_snd_853_, lean_box(0));
return v___x_854_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go_match__81_splitter(lean_object* v_motive_855_, lean_object* v_x_856_, lean_object* v_h__1_857_, lean_object* v_h__2_858_){
_start:
{
if (lean_obj_tag(v_x_856_) == 0)
{
lean_object* v___x_859_; 
lean_dec(v_h__1_857_);
v___x_859_ = lean_apply_1(v_h__2_858_, lean_box(0));
return v___x_859_;
}
else
{
lean_object* v_val_860_; lean_object* v_snd_861_; lean_object* v_fst_862_; lean_object* v_fst_863_; lean_object* v_snd_864_; lean_object* v___x_865_; 
lean_dec(v_h__2_858_);
v_val_860_ = lean_ctor_get(v_x_856_, 0);
lean_inc(v_val_860_);
lean_dec_ref_known(v_x_856_, 1);
v_snd_861_ = lean_ctor_get(v_val_860_, 1);
lean_inc(v_snd_861_);
v_fst_862_ = lean_ctor_get(v_val_860_, 0);
lean_inc(v_fst_862_);
lean_dec(v_val_860_);
v_fst_863_ = lean_ctor_get(v_snd_861_, 0);
lean_inc(v_fst_863_);
v_snd_864_ = lean_ctor_get(v_snd_861_, 1);
lean_inc(v_snd_864_);
lean_dec(v_snd_861_);
v___x_865_ = lean_apply_4(v_h__1_857_, v_fst_862_, v_fst_863_, v_snd_864_, lean_box(0));
return v___x_865_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__52_splitter___redArg(lean_object* v_x_866_, lean_object* v_h__1_867_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = lean_apply_2(v_h__1_867_, v_x_866_, lean_box(0));
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__52_splitter(lean_object* v_aig_869_, lean_object* v_upper_870_, lean_object* v_h_871_, lean_object* v_state_872_, lean_object* v_cond_873_, lean_object* v_ifTrue_874_, lean_object* v_ifFalse_875_, lean_object* v_hltc_876_, lean_object* v_motive_877_, lean_object* v_x_878_, lean_object* v_h__1_879_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = lean_apply_2(v_h__1_879_, v_x_878_, lean_box(0));
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__52_splitter___boxed(lean_object* v_aig_881_, lean_object* v_upper_882_, lean_object* v_h_883_, lean_object* v_state_884_, lean_object* v_cond_885_, lean_object* v_ifTrue_886_, lean_object* v_ifFalse_887_, lean_object* v_hltc_888_, lean_object* v_motive_889_, lean_object* v_x_890_, lean_object* v_h__1_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__52_splitter(v_aig_881_, v_upper_882_, v_h_883_, v_state_884_, v_cond_885_, v_ifTrue_886_, v_ifFalse_887_, v_hltc_888_, v_motive_889_, v_x_890_, v_h__1_891_);
lean_dec(v_ifFalse_887_);
lean_dec(v_ifTrue_886_);
lean_dec(v_cond_885_);
lean_dec_ref(v_state_884_);
lean_dec(v_upper_882_);
lean_dec_ref(v_aig_881_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__50_splitter___redArg(lean_object* v_x_893_, lean_object* v_h__1_894_){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = lean_apply_2(v_h__1_894_, v_x_893_, lean_box(0));
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__50_splitter(lean_object* v_aig_896_, lean_object* v_upper_897_, lean_object* v_h_898_, lean_object* v_cond_899_, lean_object* v_ifTrue_900_, lean_object* v_ifFalse_901_, lean_object* v_hltt_902_, lean_object* v_cstate_903_, lean_object* v_motive_904_, lean_object* v_x_905_, lean_object* v_h__1_906_){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = lean_apply_2(v_h__1_906_, v_x_905_, lean_box(0));
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__50_splitter___boxed(lean_object* v_aig_908_, lean_object* v_upper_909_, lean_object* v_h_910_, lean_object* v_cond_911_, lean_object* v_ifTrue_912_, lean_object* v_ifFalse_913_, lean_object* v_hltt_914_, lean_object* v_cstate_915_, lean_object* v_motive_916_, lean_object* v_x_917_, lean_object* v_h__1_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__50_splitter(v_aig_908_, v_upper_909_, v_h_910_, v_cond_911_, v_ifTrue_912_, v_ifFalse_913_, v_hltt_914_, v_cstate_915_, v_motive_916_, v_x_917_, v_h__1_918_);
lean_dec_ref(v_cstate_915_);
lean_dec(v_ifFalse_913_);
lean_dec(v_ifTrue_912_);
lean_dec(v_cond_911_);
lean_dec(v_upper_909_);
lean_dec_ref(v_aig_908_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__48_splitter___redArg(lean_object* v_x_920_, lean_object* v_h__1_921_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = lean_apply_2(v_h__1_921_, v_x_920_, lean_box(0));
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__48_splitter(lean_object* v_aig_923_, lean_object* v_upper_924_, lean_object* v_h_925_, lean_object* v_cond_926_, lean_object* v_ifTrue_927_, lean_object* v_ifFalse_928_, lean_object* v_hltf_929_, lean_object* v_tstate_930_, lean_object* v_motive_931_, lean_object* v_x_932_, lean_object* v_h__1_933_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = lean_apply_2(v_h__1_933_, v_x_932_, lean_box(0));
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__48_splitter___boxed(lean_object* v_aig_935_, lean_object* v_upper_936_, lean_object* v_h_937_, lean_object* v_cond_938_, lean_object* v_ifTrue_939_, lean_object* v_ifFalse_940_, lean_object* v_hltf_941_, lean_object* v_tstate_942_, lean_object* v_motive_943_, lean_object* v_x_944_, lean_object* v_h__1_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__48_splitter(v_aig_935_, v_upper_936_, v_h_937_, v_cond_938_, v_ifTrue_939_, v_ifFalse_940_, v_hltf_941_, v_tstate_942_, v_motive_943_, v_x_944_, v_h__1_945_);
lean_dec_ref(v_tstate_942_);
lean_dec(v_ifFalse_940_);
lean_dec(v_ifTrue_939_);
lean_dec(v_cond_938_);
lean_dec(v_upper_936_);
lean_dec_ref(v_aig_935_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__45_splitter___redArg(lean_object* v_x_947_, lean_object* v_h__1_948_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = lean_apply_2(v_h__1_948_, v_x_947_, lean_box(0));
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__45_splitter(lean_object* v_aig_950_, lean_object* v_upper_951_, lean_object* v_h_952_, lean_object* v_fstate_953_, lean_object* v_motive_954_, lean_object* v_x_955_, lean_object* v_h__1_956_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = lean_apply_2(v_h__1_956_, v_x_955_, lean_box(0));
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__45_splitter___boxed(lean_object* v_aig_958_, lean_object* v_upper_959_, lean_object* v_h_960_, lean_object* v_fstate_961_, lean_object* v_motive_962_, lean_object* v_x_963_, lean_object* v_h__1_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__45_splitter(v_aig_958_, v_upper_959_, v_h_960_, v_fstate_961_, v_motive_962_, v_x_963_, v_h__1_964_);
lean_dec_ref(v_fstate_961_);
lean_dec(v_upper_959_);
lean_dec_ref(v_aig_958_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__56_splitter___redArg(lean_object* v_x_966_, lean_object* v_h__1_967_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = lean_apply_2(v_h__1_967_, v_x_966_, lean_box(0));
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__56_splitter(lean_object* v_aig_969_, lean_object* v_upper_970_, lean_object* v_h_971_, lean_object* v_state_972_, lean_object* v_lhs_973_, lean_object* v_rhs_974_, lean_object* v_this_975_, lean_object* v_motive_976_, lean_object* v_x_977_, lean_object* v_h__1_978_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = lean_apply_2(v_h__1_978_, v_x_977_, lean_box(0));
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__56_splitter___boxed(lean_object* v_aig_980_, lean_object* v_upper_981_, lean_object* v_h_982_, lean_object* v_state_983_, lean_object* v_lhs_984_, lean_object* v_rhs_985_, lean_object* v_this_986_, lean_object* v_motive_987_, lean_object* v_x_988_, lean_object* v_h__1_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__56_splitter(v_aig_980_, v_upper_981_, v_h_982_, v_state_983_, v_lhs_984_, v_rhs_985_, v_this_986_, v_motive_987_, v_x_988_, v_h__1_989_);
lean_dec(v_rhs_985_);
lean_dec(v_lhs_984_);
lean_dec_ref(v_state_983_);
lean_dec(v_upper_981_);
lean_dec_ref(v_aig_980_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__54_splitter___redArg(lean_object* v_x_991_, lean_object* v_h__1_992_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = lean_apply_2(v_h__1_992_, v_x_991_, lean_box(0));
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__54_splitter(lean_object* v_aig_994_, lean_object* v_upper_995_, lean_object* v_h_996_, lean_object* v_lhs_997_, lean_object* v_rhs_998_, lean_object* v_this_999_, lean_object* v_lstate_1000_, lean_object* v_motive_1001_, lean_object* v_x_1002_, lean_object* v_h__1_1003_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = lean_apply_2(v_h__1_1003_, v_x_1002_, lean_box(0));
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__54_splitter___boxed(lean_object* v_aig_1005_, lean_object* v_upper_1006_, lean_object* v_h_1007_, lean_object* v_lhs_1008_, lean_object* v_rhs_1009_, lean_object* v_this_1010_, lean_object* v_lstate_1011_, lean_object* v_motive_1012_, lean_object* v_x_1013_, lean_object* v_h__1_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__54_splitter(v_aig_1005_, v_upper_1006_, v_h_1007_, v_lhs_1008_, v_rhs_1009_, v_this_1010_, v_lstate_1011_, v_motive_1012_, v_x_1013_, v_h__1_1014_);
lean_dec_ref(v_lstate_1011_);
lean_dec(v_rhs_1009_);
lean_dec(v_lhs_1008_);
lean_dec(v_upper_1006_);
lean_dec_ref(v_aig_1005_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF(lean_object* v_entry_1016_){
_start:
{
lean_object* v_ref_1017_; lean_object* v_aig_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1045_; 
v_ref_1017_ = lean_ctor_get(v_entry_1016_, 1);
v_aig_1018_ = lean_ctor_get(v_entry_1016_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v_entry_1016_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1020_ = v_entry_1016_;
v_isShared_1021_ = v_isSharedCheck_1045_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_ref_1017_);
lean_inc(v_aig_1018_);
lean_dec(v_entry_1016_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1045_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v_gate_1022_; uint8_t v_invert_1023_; lean_object* v___x_1024_; lean_object* v_val_1025_; uint8_t v___y_1027_; 
v_gate_1022_ = lean_ctor_get(v_ref_1017_, 0);
lean_inc_n(v_gate_1022_, 2);
v_invert_1023_ = lean_ctor_get_uint8(v_ref_1017_, sizeof(void*)*1);
lean_dec_ref(v_ref_1017_);
lean_inc_ref(v_aig_1018_);
v___x_1024_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty(v_aig_1018_);
v_val_1025_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(v_aig_1018_, v_gate_1022_, v___x_1024_);
lean_dec_ref(v_aig_1018_);
if (v_invert_1023_ == 0)
{
uint8_t v___x_1043_; 
v___x_1043_ = 1;
v___y_1027_ = v___x_1043_;
goto v___jp_1026_;
}
else
{
uint8_t v___x_1044_; 
v___x_1044_ = 0;
v___y_1027_ = v___x_1044_;
goto v___jp_1026_;
}
v___jp_1026_:
{
lean_object* v_cnf_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1041_; 
v_cnf_1028_ = lean_ctor_get(v_val_1025_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v_val_1025_);
if (v_isSharedCheck_1041_ == 0)
{
lean_object* v_unused_1042_; 
v_unused_1042_ = lean_ctor_get(v_val_1025_, 1);
lean_dec(v_unused_1042_);
v___x_1030_ = v_val_1025_;
v_isShared_1031_ = v_isSharedCheck_1041_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_cnf_1028_);
lean_dec(v_val_1025_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1041_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1032_; lean_object* v___x_1034_; 
v___x_1032_ = lean_box(v___y_1027_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 1, v___x_1032_);
lean_ctor_set(v___x_1030_, 0, v_gate_1022_);
v___x_1034_ = v___x_1030_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_gate_1022_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v___x_1032_);
v___x_1034_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
lean_object* v___x_1035_; lean_object* v___x_1037_; 
v___x_1035_ = lean_box(0);
if (v_isShared_1021_ == 0)
{
lean_ctor_set_tag(v___x_1020_, 1);
lean_ctor_set(v___x_1020_, 1, v___x_1035_);
lean_ctor_set(v___x_1020_, 0, v___x_1034_);
v___x_1037_ = v___x_1020_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1034_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v___x_1035_);
v___x_1037_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
lean_object* v___x_1038_; 
v___x_1038_ = lean_array_push(v_cnf_1028_, v___x_1037_);
return v___x_1038_;
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
