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
lean_object* lean_byte_array_push(lean_object*, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_ByteArray_empty;
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_lxor(lean_object*, lean_object*);
uint8_t l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_instHashableDecl_hash___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Std_Sat_CNF_eval___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Std_Sat_AIG_denote___redArg(lean_object*, lean_object*);
static const lean_array_object l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__0 = (const lean_object*)&l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__0_value;
static lean_once_cell_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF(lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_cast___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_cast___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_cast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_cast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_cast___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_cast___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_cast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_cast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___boxed(lean_object**);
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_match__4_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_match__4_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go_match__103_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go_match__103_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go_match__81_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go_match__81_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__52_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__52_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__52_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__50_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__50_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__50_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__48_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__48_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__48_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__45_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__45_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__45_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__56_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__56_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__56_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__54_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__54_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__54_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__6_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty___at___00Std_Sat_AIG_toCNF_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty___at___00Std_Sat_AIG_toCNF_spec__0_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty___at___00Std_Sat_AIG_toCNF_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty___at___00Std_Sat_AIG_toCNF_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_Sat_AIG_toCNF___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Sat_AIG_toCNF___redArg___closed__0 = (const lean_object*)&l_Std_Sat_AIG_toCNF___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty___at___00Std_Sat_AIG_toCNF_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty___at___00Std_Sat_AIG_toCNF_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty___at___00Std_Sat_AIG_toCNF_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty___at___00Std_Sat_AIG_toCNF_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__6_spec__10___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__6___boxed(lean_object**);
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
static lean_object* _init_l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg___closed__0(void){
_start:
{
uint8_t v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_15_ = 1;
v___x_16_ = l_ByteArray_empty;
v___x_17_ = lean_byte_array_push(v___x_16_, v___x_15_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg(lean_object* v_output_18_, lean_object* v_lhs_19_, lean_object* v_rhs_20_, uint8_t v_linv_21_, uint8_t v_rinv_22_){
_start:
{
lean_object* v___y_24_; lean_object* v___y_25_; lean_object* v___y_26_; uint8_t v___y_27_; lean_object* v___x_31_; lean_object* v___x_32_; uint8_t v___x_33_; lean_object* v___y_35_; lean_object* v___y_36_; uint8_t v___y_37_; lean_object* v___y_38_; uint8_t v___y_39_; lean_object* v___x_42_; lean_object* v___y_44_; lean_object* v___y_45_; lean_object* v___y_46_; uint8_t v___y_47_; lean_object* v___y_54_; uint8_t v___y_55_; 
v___x_31_ = ((lean_object*)(l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__0));
v___x_32_ = lean_array_push(v___x_31_, v_output_18_);
v___x_33_ = 0;
v___x_42_ = lean_obj_once(&l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__1, &l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__1_once, _init_l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__1);
if (v_linv_21_ == 0)
{
lean_object* v___x_62_; uint8_t v___x_63_; 
lean_inc_ref(v___x_32_);
v___x_62_ = lean_array_push(v___x_32_, v_lhs_19_);
v___x_63_ = 1;
v___y_54_ = v___x_62_;
v___y_55_ = v___x_63_;
goto v___jp_53_;
}
else
{
lean_object* v___x_64_; 
lean_inc_ref(v___x_32_);
v___x_64_ = lean_array_push(v___x_32_, v_lhs_19_);
v___y_54_ = v___x_64_;
v___y_55_ = v___x_33_;
goto v___jp_53_;
}
v___jp_23_:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_28_ = lean_byte_array_push(v___y_26_, v___y_27_);
v___x_29_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_29_, 0, v___y_25_);
lean_ctor_set(v___x_29_, 1, v___x_28_);
v___x_30_ = lean_array_push(v___y_24_, v___x_29_);
return v___x_30_;
}
v___jp_34_:
{
lean_object* v___x_40_; lean_object* v___x_41_; 
lean_inc_ref(v___y_36_);
v___x_40_ = lean_byte_array_push(v___y_36_, v___y_39_);
v___x_41_ = lean_array_push(v___y_38_, v_rhs_20_);
if (v_rinv_22_ == 0)
{
v___y_24_ = v___y_35_;
v___y_25_ = v___x_41_;
v___y_26_ = v___x_40_;
v___y_27_ = v___x_33_;
goto v___jp_23_;
}
else
{
v___y_24_ = v___y_35_;
v___y_25_ = v___x_41_;
v___y_26_ = v___x_40_;
v___y_27_ = v___y_37_;
goto v___jp_23_;
}
}
v___jp_43_:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; uint8_t v___x_51_; lean_object* v___x_52_; 
v___x_48_ = lean_byte_array_push(v___x_42_, v___y_47_);
v___x_49_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_49_, 0, v___y_45_);
lean_ctor_set(v___x_49_, 1, v___x_48_);
v___x_50_ = lean_array_push(v___y_44_, v___x_49_);
v___x_51_ = 1;
v___x_52_ = lean_obj_once(&l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg___closed__0, &l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg___closed__0_once, _init_l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg___closed__0);
if (v_linv_21_ == 0)
{
v___y_35_ = v___x_50_;
v___y_36_ = v___x_52_;
v___y_37_ = v___x_51_;
v___y_38_ = v___y_46_;
v___y_39_ = v___x_33_;
goto v___jp_34_;
}
else
{
v___y_35_ = v___x_50_;
v___y_36_ = v___x_52_;
v___y_37_ = v___x_51_;
v___y_38_ = v___y_46_;
v___y_39_ = v___x_51_;
goto v___jp_34_;
}
}
v___jp_53_:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_56_ = lean_byte_array_push(v___x_42_, v___y_55_);
lean_inc_ref(v___y_54_);
v___x_57_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_57_, 0, v___y_54_);
lean_ctor_set(v___x_57_, 1, v___x_56_);
v___x_58_ = lean_array_push(v___x_31_, v___x_57_);
if (v_rinv_22_ == 0)
{
lean_object* v___x_59_; uint8_t v___x_60_; 
lean_inc(v_rhs_20_);
v___x_59_ = lean_array_push(v___x_32_, v_rhs_20_);
v___x_60_ = 1;
v___y_44_ = v___x_58_;
v___y_45_ = v___x_59_;
v___y_46_ = v___y_54_;
v___y_47_ = v___x_60_;
goto v___jp_43_;
}
else
{
lean_object* v___x_61_; 
lean_inc(v_rhs_20_);
v___x_61_ = lean_array_push(v___x_32_, v_rhs_20_);
v___y_44_ = v___x_58_;
v___y_45_ = v___x_61_;
v___y_46_ = v___y_54_;
v___y_47_ = v___x_33_;
goto v___jp_43_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg___boxed(lean_object* v_output_65_, lean_object* v_lhs_66_, lean_object* v_rhs_67_, lean_object* v_linv_68_, lean_object* v_rinv_69_){
_start:
{
uint8_t v_linv_boxed_70_; uint8_t v_rinv_boxed_71_; lean_object* v_res_72_; 
v_linv_boxed_70_ = lean_unbox(v_linv_68_);
v_rinv_boxed_71_ = lean_unbox(v_rinv_69_);
v_res_72_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg(v_output_65_, v_lhs_66_, v_rhs_67_, v_linv_boxed_70_, v_rinv_boxed_71_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF(lean_object* v_00_u03b1_73_, lean_object* v_output_74_, lean_object* v_lhs_75_, lean_object* v_rhs_76_, uint8_t v_linv_77_, uint8_t v_rinv_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg(v_output_74_, v_lhs_75_, v_rhs_76_, v_linv_77_, v_rinv_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___boxed(lean_object* v_00_u03b1_80_, lean_object* v_output_81_, lean_object* v_lhs_82_, lean_object* v_rhs_83_, lean_object* v_linv_84_, lean_object* v_rinv_85_){
_start:
{
uint8_t v_linv_boxed_86_; uint8_t v_rinv_boxed_87_; lean_object* v_res_88_; 
v_linv_boxed_86_ = lean_unbox(v_linv_84_);
v_rinv_boxed_87_ = lean_unbox(v_rinv_85_);
v_res_88_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF(v_00_u03b1_80_, v_output_81_, v_lhs_82_, v_rhs_83_, v_linv_boxed_86_, v_rinv_boxed_87_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF___redArg(lean_object* v_output_89_, lean_object* v_cond_90_, lean_object* v_ifTrue_91_, lean_object* v_ifFalse_92_, uint8_t v_cinv_93_, uint8_t v_tinv_94_, uint8_t v_finv_95_){
_start:
{
lean_object* v___y_97_; uint8_t v___y_98_; lean_object* v___y_99_; lean_object* v___y_100_; uint8_t v___y_101_; lean_object* v___y_107_; uint8_t v___y_108_; uint8_t v___y_109_; lean_object* v___y_110_; lean_object* v___y_111_; uint8_t v___y_112_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; uint8_t v___y_122_; uint8_t v___y_123_; lean_object* v___y_124_; uint8_t v___y_125_; uint8_t v___y_129_; lean_object* v___y_130_; lean_object* v___y_131_; lean_object* v___y_132_; uint8_t v___y_133_; lean_object* v___y_140_; lean_object* v___y_141_; uint8_t v___y_142_; uint8_t v___y_151_; 
v___x_118_ = ((lean_object*)(l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__0));
v___x_119_ = l_ByteArray_empty;
v___x_120_ = lean_array_push(v___x_118_, v_cond_90_);
if (v_cinv_93_ == 0)
{
uint8_t v___x_156_; 
v___x_156_ = 0;
v___y_151_ = v___x_156_;
goto v___jp_150_;
}
else
{
uint8_t v___x_157_; 
v___x_157_ = 1;
v___y_151_ = v___x_157_;
goto v___jp_150_;
}
v___jp_96_:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_102_ = lean_byte_array_push(v___y_97_, v___y_101_);
v___x_103_ = lean_byte_array_push(v___x_102_, v___y_98_);
v___x_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_104_, 0, v___y_99_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
v___x_105_ = lean_array_push(v___y_100_, v___x_104_);
return v___x_105_;
}
v___jp_106_:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
lean_inc_ref(v___y_107_);
v___x_113_ = lean_byte_array_push(v___y_107_, v___y_112_);
v___x_114_ = lean_array_push(v___y_111_, v_output_89_);
v___x_115_ = lean_byte_array_push(v___x_113_, v___y_109_);
lean_inc_ref(v___x_114_);
v___x_116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_116_, 0, v___x_114_);
lean_ctor_set(v___x_116_, 1, v___x_115_);
v___x_117_ = lean_array_push(v___y_110_, v___x_116_);
if (v_finv_95_ == 0)
{
v___y_97_ = v___y_107_;
v___y_98_ = v___y_108_;
v___y_99_ = v___x_114_;
v___y_100_ = v___x_117_;
v___y_101_ = v___y_109_;
goto v___jp_96_;
}
else
{
v___y_97_ = v___y_107_;
v___y_98_ = v___y_108_;
v___y_99_ = v___x_114_;
v___y_100_ = v___x_117_;
v___y_101_ = v___y_108_;
goto v___jp_96_;
}
}
v___jp_121_:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = lean_byte_array_push(v___x_119_, v___y_125_);
v___x_127_ = lean_array_push(v___x_120_, v_ifFalse_92_);
if (v_finv_95_ == 0)
{
v___y_107_ = v___x_126_;
v___y_108_ = v___y_123_;
v___y_109_ = v___y_122_;
v___y_110_ = v___y_124_;
v___y_111_ = v___x_127_;
v___y_112_ = v___y_123_;
goto v___jp_106_;
}
else
{
v___y_107_ = v___x_126_;
v___y_108_ = v___y_123_;
v___y_109_ = v___y_122_;
v___y_110_ = v___y_124_;
v___y_111_ = v___x_127_;
v___y_112_ = v___y_122_;
goto v___jp_106_;
}
}
v___jp_128_:
{
lean_object* v___x_134_; uint8_t v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_134_ = lean_byte_array_push(v___y_131_, v___y_133_);
v___x_135_ = 0;
v___x_136_ = lean_byte_array_push(v___x_134_, v___x_135_);
v___x_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_137_, 0, v___y_130_);
lean_ctor_set(v___x_137_, 1, v___x_136_);
v___x_138_ = lean_array_push(v___y_132_, v___x_137_);
if (v_cinv_93_ == 0)
{
v___y_122_ = v___y_129_;
v___y_123_ = v___x_135_;
v___y_124_ = v___x_138_;
v___y_125_ = v___y_129_;
goto v___jp_121_;
}
else
{
v___y_122_ = v___y_129_;
v___y_123_ = v___x_135_;
v___y_124_ = v___x_138_;
v___y_125_ = v___x_135_;
goto v___jp_121_;
}
}
v___jp_139_:
{
lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
lean_inc_ref(v___y_141_);
v___x_143_ = lean_byte_array_push(v___y_141_, v___y_142_);
lean_inc(v_output_89_);
v___x_144_ = lean_array_push(v___y_140_, v_output_89_);
v___x_145_ = 1;
v___x_146_ = lean_byte_array_push(v___x_143_, v___x_145_);
lean_inc_ref(v___x_144_);
v___x_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_144_);
lean_ctor_set(v___x_147_, 1, v___x_146_);
v___x_148_ = lean_array_push(v___x_118_, v___x_147_);
if (v_tinv_94_ == 0)
{
v___y_129_ = v___x_145_;
v___y_130_ = v___x_144_;
v___y_131_ = v___y_141_;
v___y_132_ = v___x_148_;
v___y_133_ = v___x_145_;
goto v___jp_128_;
}
else
{
uint8_t v___x_149_; 
v___x_149_ = 0;
v___y_129_ = v___x_145_;
v___y_130_ = v___x_144_;
v___y_131_ = v___y_141_;
v___y_132_ = v___x_148_;
v___y_133_ = v___x_149_;
goto v___jp_128_;
}
}
v___jp_150_:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = lean_byte_array_push(v___x_119_, v___y_151_);
lean_inc_ref(v___x_120_);
v___x_153_ = lean_array_push(v___x_120_, v_ifTrue_91_);
if (v_tinv_94_ == 0)
{
uint8_t v___x_154_; 
v___x_154_ = 0;
v___y_140_ = v___x_153_;
v___y_141_ = v___x_152_;
v___y_142_ = v___x_154_;
goto v___jp_139_;
}
else
{
uint8_t v___x_155_; 
v___x_155_ = 1;
v___y_140_ = v___x_153_;
v___y_141_ = v___x_152_;
v___y_142_ = v___x_155_;
goto v___jp_139_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF___redArg___boxed(lean_object* v_output_158_, lean_object* v_cond_159_, lean_object* v_ifTrue_160_, lean_object* v_ifFalse_161_, lean_object* v_cinv_162_, lean_object* v_tinv_163_, lean_object* v_finv_164_){
_start:
{
uint8_t v_cinv_boxed_165_; uint8_t v_tinv_boxed_166_; uint8_t v_finv_boxed_167_; lean_object* v_res_168_; 
v_cinv_boxed_165_ = lean_unbox(v_cinv_162_);
v_tinv_boxed_166_ = lean_unbox(v_tinv_163_);
v_finv_boxed_167_ = lean_unbox(v_finv_164_);
v_res_168_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF___redArg(v_output_158_, v_cond_159_, v_ifTrue_160_, v_ifFalse_161_, v_cinv_boxed_165_, v_tinv_boxed_166_, v_finv_boxed_167_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF(lean_object* v_00_u03b1_169_, lean_object* v_output_170_, lean_object* v_cond_171_, lean_object* v_ifTrue_172_, lean_object* v_ifFalse_173_, uint8_t v_cinv_174_, uint8_t v_tinv_175_, uint8_t v_finv_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF___redArg(v_output_170_, v_cond_171_, v_ifTrue_172_, v_ifFalse_173_, v_cinv_174_, v_tinv_175_, v_finv_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF___boxed(lean_object* v_00_u03b1_178_, lean_object* v_output_179_, lean_object* v_cond_180_, lean_object* v_ifTrue_181_, lean_object* v_ifFalse_182_, lean_object* v_cinv_183_, lean_object* v_tinv_184_, lean_object* v_finv_185_){
_start:
{
uint8_t v_cinv_boxed_186_; uint8_t v_tinv_boxed_187_; uint8_t v_finv_boxed_188_; lean_object* v_res_189_; 
v_cinv_boxed_186_ = lean_unbox(v_cinv_183_);
v_tinv_boxed_187_ = lean_unbox(v_tinv_184_);
v_finv_boxed_188_ = lean_unbox(v_finv_185_);
v_res_189_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF(v_00_u03b1_178_, v_output_179_, v_cond_180_, v_ifTrue_181_, v_ifFalse_182_, v_cinv_boxed_186_, v_tinv_boxed_187_, v_finv_boxed_188_);
return v_res_189_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign___redArg___lam__0(lean_object* v_inst_190_, lean_object* v_a_191_, lean_object* v_b_192_){
_start:
{
uint8_t v___x_193_; 
v___x_193_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v_inst_190_, v_a_191_, v_b_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign___redArg___lam__0___boxed(lean_object* v_inst_194_, lean_object* v_a_195_, lean_object* v_b_196_){
_start:
{
uint8_t v_res_197_; lean_object* v_r_198_; 
v_res_197_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign___redArg___lam__0(v_inst_194_, v_a_195_, v_b_196_);
v_r_198_ = lean_box(v_res_197_);
return v_r_198_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign___redArg(lean_object* v_inst_199_, lean_object* v_inst_200_, lean_object* v_aig_201_, lean_object* v_assign_202_, lean_object* v_a_203_){
_start:
{
lean_object* v_cache_204_; lean_object* v___f_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___f_208_; lean_object* v___x_209_; 
v_cache_204_ = lean_ctor_get(v_aig_201_, 1);
v___f_205_ = lean_alloc_closure((void*)(l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_205_, 0, v_inst_200_);
v___x_206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_206_, 0, v_a_203_);
v___x_207_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_207_, 0, lean_box(0));
lean_closure_set(v___x_207_, 1, v_inst_199_);
v___f_208_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_208_, 0, v___f_205_);
v___x_209_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_208_, v___x_207_, v_cache_204_, v___x_206_);
if (lean_obj_tag(v___x_209_) == 0)
{
uint8_t v___x_210_; 
lean_dec_ref(v_assign_202_);
v___x_210_ = 0;
return v___x_210_;
}
else
{
lean_object* v_val_211_; lean_object* v___x_212_; uint8_t v___x_213_; 
v_val_211_ = lean_ctor_get(v___x_209_, 0);
lean_inc(v_val_211_);
lean_dec_ref_known(v___x_209_, 1);
v___x_212_ = lean_apply_1(v_assign_202_, v_val_211_);
v___x_213_ = lean_unbox(v___x_212_);
return v___x_213_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign___redArg___boxed(lean_object* v_inst_214_, lean_object* v_inst_215_, lean_object* v_aig_216_, lean_object* v_assign_217_, lean_object* v_a_218_){
_start:
{
uint8_t v_res_219_; lean_object* v_r_220_; 
v_res_219_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign___redArg(v_inst_214_, v_inst_215_, v_aig_216_, v_assign_217_, v_a_218_);
lean_dec_ref(v_aig_216_);
v_r_220_ = lean_box(v_res_219_);
return v_r_220_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign(lean_object* v_00_u03b1_221_, lean_object* v_inst_222_, lean_object* v_inst_223_, lean_object* v_aig_224_, lean_object* v_assign_225_, lean_object* v_a_226_){
_start:
{
uint8_t v___x_227_; 
v___x_227_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign___redArg(v_inst_222_, v_inst_223_, v_aig_224_, v_assign_225_, v_a_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign___boxed(lean_object* v_00_u03b1_228_, lean_object* v_inst_229_, lean_object* v_inst_230_, lean_object* v_aig_231_, lean_object* v_assign_232_, lean_object* v_a_233_){
_start:
{
uint8_t v_res_234_; lean_object* v_r_235_; 
v_res_234_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign(v_00_u03b1_228_, v_inst_229_, v_inst_230_, v_aig_231_, v_assign_232_, v_a_233_);
lean_dec_ref(v_aig_231_);
v_r_235_ = lean_box(v_res_234_);
return v_r_235_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___redArg(lean_object* v_aig_236_, lean_object* v_assign1_237_, lean_object* v_idx_238_){
_start:
{
lean_object* v_decls_239_; lean_object* v___x_240_; uint8_t v___x_241_; 
v_decls_239_ = lean_ctor_get(v_aig_236_, 0);
v___x_240_ = lean_array_get_size(v_decls_239_);
v___x_241_ = lean_nat_dec_lt(v_idx_238_, v___x_240_);
if (v___x_241_ == 0)
{
lean_dec(v_idx_238_);
lean_dec_ref(v_assign1_237_);
lean_dec_ref(v_aig_236_);
return v___x_241_;
}
else
{
uint8_t v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_242_ = 0;
v___x_243_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_243_, 0, v_idx_238_);
lean_ctor_set_uint8(v___x_243_, sizeof(void*)*1, v___x_242_);
v___x_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_244_, 0, v_aig_236_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
v___x_245_ = l_Std_Sat_AIG_denote___redArg(v_assign1_237_, v___x_244_);
lean_dec_ref_known(v___x_244_, 2);
return v___x_245_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___redArg___boxed(lean_object* v_aig_246_, lean_object* v_assign1_247_, lean_object* v_idx_248_){
_start:
{
uint8_t v_res_249_; lean_object* v_r_250_; 
v_res_249_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___redArg(v_aig_246_, v_assign1_247_, v_idx_248_);
v_r_250_ = lean_box(v_res_249_);
return v_r_250_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment(lean_object* v_00_u03b1_251_, lean_object* v_inst_252_, lean_object* v_inst_253_, lean_object* v_aig_254_, lean_object* v_assign1_255_, lean_object* v_idx_256_){
_start:
{
uint8_t v___x_257_; 
v___x_257_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___redArg(v_aig_254_, v_assign1_255_, v_idx_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___boxed(lean_object* v_00_u03b1_258_, lean_object* v_inst_259_, lean_object* v_inst_260_, lean_object* v_aig_261_, lean_object* v_assign1_262_, lean_object* v_idx_263_){
_start:
{
uint8_t v_res_264_; lean_object* v_r_265_; 
v_res_264_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment(v_00_u03b1_258_, v_inst_259_, v_inst_260_, v_aig_261_, v_assign1_262_, v_idx_263_);
lean_dec_ref(v_inst_260_);
lean_dec_ref(v_inst_259_);
v_r_265_ = lean_box(v_res_264_);
return v_r_265_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___redArg(lean_object* v_aig_266_){
_start:
{
lean_object* v_decls_267_; lean_object* v___x_268_; uint8_t v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v_decls_267_ = lean_ctor_get(v_aig_266_, 0);
v___x_268_ = lean_array_get_size(v_decls_267_);
v___x_269_ = 0;
v___x_270_ = lean_box(v___x_269_);
v___x_271_ = lean_mk_array(v___x_268_, v___x_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___redArg___boxed(lean_object* v_aig_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___redArg(v_aig_272_);
lean_dec_ref(v_aig_272_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init(lean_object* v_00_u03b1_274_, lean_object* v_inst_275_, lean_object* v_inst_276_, lean_object* v_aig_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___redArg(v_aig_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___boxed(lean_object* v_00_u03b1_279_, lean_object* v_inst_280_, lean_object* v_inst_281_, lean_object* v_aig_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init(v_00_u03b1_279_, v_inst_280_, v_inst_281_, v_aig_282_);
lean_dec_ref(v_aig_282_);
lean_dec_ref(v_inst_281_);
lean_dec_ref(v_inst_280_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_cast___redArg(lean_object* v_aig2_284_, lean_object* v_cache_285_){
_start:
{
lean_object* v_decls_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v_decls_286_ = lean_ctor_get(v_aig2_284_, 0);
v___x_287_ = lean_array_get_size(v_decls_286_);
v___x_288_ = lean_array_get_size(v_cache_285_);
v___x_289_ = lean_nat_sub(v___x_287_, v___x_288_);
v___x_290_ = 0;
v___x_291_ = lean_box(v___x_290_);
v___x_292_ = lean_mk_array(v___x_289_, v___x_291_);
v___x_293_ = l_Array_append___redArg(v_cache_285_, v___x_292_);
lean_dec_ref(v___x_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_cast___redArg___boxed(lean_object* v_aig2_294_, lean_object* v_cache_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_cast___redArg(v_aig2_294_, v_cache_295_);
lean_dec_ref(v_aig2_294_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_cast(lean_object* v_00_u03b1_297_, lean_object* v_inst_298_, lean_object* v_inst_299_, lean_object* v_cnf_300_, lean_object* v_aig1_301_, lean_object* v_aig2_302_, lean_object* v_cache_303_, lean_object* v_hprefix_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_cast___redArg(v_aig2_302_, v_cache_303_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_cast___boxed(lean_object* v_00_u03b1_306_, lean_object* v_inst_307_, lean_object* v_inst_308_, lean_object* v_cnf_309_, lean_object* v_aig1_310_, lean_object* v_aig2_311_, lean_object* v_cache_312_, lean_object* v_hprefix_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_cast(v_00_u03b1_306_, v_inst_307_, v_inst_308_, v_cnf_309_, v_aig1_310_, v_aig2_311_, v_cache_312_, v_hprefix_313_);
lean_dec_ref(v_aig2_311_);
lean_dec_ref(v_aig1_310_);
lean_dec_ref(v_cnf_309_);
lean_dec_ref(v_inst_308_);
lean_dec_ref(v_inst_307_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg(lean_object* v_cache_315_, lean_object* v_idx_316_){
_start:
{
uint8_t v___x_317_; lean_object* v___x_318_; lean_object* v_out_319_; 
v___x_317_ = 1;
v___x_318_ = lean_box(v___x_317_);
v_out_319_ = lean_array_fset(v_cache_315_, v_idx_316_, v___x_318_);
return v_out_319_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg___boxed(lean_object* v_cache_320_, lean_object* v_idx_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg(v_cache_320_, v_idx_321_);
lean_dec(v_idx_321_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse(lean_object* v_00_u03b1_323_, lean_object* v_inst_324_, lean_object* v_inst_325_, lean_object* v_aig_326_, lean_object* v_cnf_327_, lean_object* v_cache_328_, lean_object* v_idx_329_, lean_object* v_h_330_, lean_object* v_htip_331_){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg(v_cache_328_, v_idx_329_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___boxed(lean_object* v_00_u03b1_333_, lean_object* v_inst_334_, lean_object* v_inst_335_, lean_object* v_aig_336_, lean_object* v_cnf_337_, lean_object* v_cache_338_, lean_object* v_idx_339_, lean_object* v_h_340_, lean_object* v_htip_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse(v_00_u03b1_333_, v_inst_334_, v_inst_335_, v_aig_336_, v_cnf_337_, v_cache_338_, v_idx_339_, v_h_340_, v_htip_341_);
lean_dec(v_idx_339_);
lean_dec_ref(v_cnf_337_);
lean_dec_ref(v_aig_336_);
lean_dec_ref(v_inst_335_);
lean_dec_ref(v_inst_334_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg(lean_object* v_cache_343_, lean_object* v_idx_344_){
_start:
{
uint8_t v___x_345_; lean_object* v___x_346_; lean_object* v_out_347_; 
v___x_345_ = 1;
v___x_346_ = lean_box(v___x_345_);
v_out_347_ = lean_array_fset(v_cache_343_, v_idx_344_, v___x_346_);
return v_out_347_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg___boxed(lean_object* v_cache_348_, lean_object* v_idx_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg(v_cache_348_, v_idx_349_);
lean_dec(v_idx_349_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom(lean_object* v_00_u03b1_351_, lean_object* v_inst_352_, lean_object* v_inst_353_, lean_object* v_aig_354_, lean_object* v_cnf_355_, lean_object* v_a_356_, lean_object* v_cache_357_, lean_object* v_idx_358_, lean_object* v_h_359_, lean_object* v_htip_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg(v_cache_357_, v_idx_358_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___boxed(lean_object* v_00_u03b1_362_, lean_object* v_inst_363_, lean_object* v_inst_364_, lean_object* v_aig_365_, lean_object* v_cnf_366_, lean_object* v_a_367_, lean_object* v_cache_368_, lean_object* v_idx_369_, lean_object* v_h_370_, lean_object* v_htip_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom(v_00_u03b1_362_, v_inst_363_, v_inst_364_, v_aig_365_, v_cnf_366_, v_a_367_, v_cache_368_, v_idx_369_, v_h_370_, v_htip_371_);
lean_dec(v_idx_369_);
lean_dec(v_a_367_);
lean_dec_ref(v_cnf_366_);
lean_dec_ref(v_aig_365_);
lean_dec_ref(v_inst_364_);
lean_dec_ref(v_inst_363_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg(lean_object* v_lhs_373_, lean_object* v_rhs_374_, lean_object* v_cache_375_, lean_object* v_idx_376_){
_start:
{
uint8_t v___x_377_; lean_object* v___x_378_; lean_object* v_out_379_; 
v___x_377_ = 1;
v___x_378_ = lean_box(v___x_377_);
v_out_379_ = lean_array_fset(v_cache_375_, v_idx_376_, v___x_378_);
return v_out_379_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg___boxed(lean_object* v_lhs_380_, lean_object* v_rhs_381_, lean_object* v_cache_382_, lean_object* v_idx_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg(v_lhs_380_, v_rhs_381_, v_cache_382_, v_idx_383_);
lean_dec(v_idx_383_);
lean_dec(v_rhs_381_);
lean_dec(v_lhs_380_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate(lean_object* v_00_u03b1_385_, lean_object* v_inst_386_, lean_object* v_inst_387_, lean_object* v_aig_388_, lean_object* v_cnf_389_, lean_object* v_lhs_390_, lean_object* v_rhs_391_, lean_object* v_cache_392_, lean_object* v_hlb_393_, lean_object* v_hrb_394_, lean_object* v_idx_395_, lean_object* v_h_396_, lean_object* v_htip_397_, lean_object* v_hl_398_, lean_object* v_hr_399_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg(v_lhs_390_, v_rhs_391_, v_cache_392_, v_idx_395_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___boxed(lean_object* v_00_u03b1_401_, lean_object* v_inst_402_, lean_object* v_inst_403_, lean_object* v_aig_404_, lean_object* v_cnf_405_, lean_object* v_lhs_406_, lean_object* v_rhs_407_, lean_object* v_cache_408_, lean_object* v_hlb_409_, lean_object* v_hrb_410_, lean_object* v_idx_411_, lean_object* v_h_412_, lean_object* v_htip_413_, lean_object* v_hl_414_, lean_object* v_hr_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate(v_00_u03b1_401_, v_inst_402_, v_inst_403_, v_aig_404_, v_cnf_405_, v_lhs_406_, v_rhs_407_, v_cache_408_, v_hlb_409_, v_hrb_410_, v_idx_411_, v_h_412_, v_htip_413_, v_hl_414_, v_hr_415_);
lean_dec(v_idx_411_);
lean_dec(v_rhs_407_);
lean_dec(v_lhs_406_);
lean_dec_ref(v_cnf_405_);
lean_dec_ref(v_aig_404_);
lean_dec_ref(v_inst_403_);
lean_dec_ref(v_inst_402_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___redArg(lean_object* v_cache_417_, lean_object* v_cond_418_, lean_object* v_ifTrue_419_, lean_object* v_ifFalse_420_, lean_object* v_idx_421_){
_start:
{
uint8_t v___x_422_; lean_object* v___x_423_; lean_object* v_out_424_; 
v___x_422_ = 1;
v___x_423_ = lean_box(v___x_422_);
v_out_424_ = lean_array_fset(v_cache_417_, v_idx_421_, v___x_423_);
return v_out_424_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___redArg___boxed(lean_object* v_cache_425_, lean_object* v_cond_426_, lean_object* v_ifTrue_427_, lean_object* v_ifFalse_428_, lean_object* v_idx_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___redArg(v_cache_425_, v_cond_426_, v_ifTrue_427_, v_ifFalse_428_, v_idx_429_);
lean_dec(v_idx_429_);
lean_dec(v_ifFalse_428_);
lean_dec(v_ifTrue_427_);
lean_dec(v_cond_426_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte(lean_object* v_00_u03b1_431_, lean_object* v_inst_432_, lean_object* v_inst_433_, lean_object* v_aig_434_, lean_object* v_cnf_435_, lean_object* v_cache_436_, lean_object* v_cond_437_, lean_object* v_ifTrue_438_, lean_object* v_ifFalse_439_, lean_object* v_idx_440_, lean_object* v_hcb_441_, lean_object* v_htb_442_, lean_object* v_hfb_443_, lean_object* v_h_444_, lean_object* v_hltc_445_, lean_object* v_hltt_446_, lean_object* v_hltf_447_, lean_object* v_hc_448_, lean_object* v_ht_449_, lean_object* v_hf_450_, lean_object* v_hdenote_451_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___redArg(v_cache_436_, v_cond_437_, v_ifTrue_438_, v_ifFalse_439_, v_idx_440_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___boxed(lean_object** _args){
lean_object* v_00_u03b1_453_ = _args[0];
lean_object* v_inst_454_ = _args[1];
lean_object* v_inst_455_ = _args[2];
lean_object* v_aig_456_ = _args[3];
lean_object* v_cnf_457_ = _args[4];
lean_object* v_cache_458_ = _args[5];
lean_object* v_cond_459_ = _args[6];
lean_object* v_ifTrue_460_ = _args[7];
lean_object* v_ifFalse_461_ = _args[8];
lean_object* v_idx_462_ = _args[9];
lean_object* v_hcb_463_ = _args[10];
lean_object* v_htb_464_ = _args[11];
lean_object* v_hfb_465_ = _args[12];
lean_object* v_h_466_ = _args[13];
lean_object* v_hltc_467_ = _args[14];
lean_object* v_hltt_468_ = _args[15];
lean_object* v_hltf_469_ = _args[16];
lean_object* v_hc_470_ = _args[17];
lean_object* v_ht_471_ = _args[18];
lean_object* v_hf_472_ = _args[19];
lean_object* v_hdenote_473_ = _args[20];
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte(v_00_u03b1_453_, v_inst_454_, v_inst_455_, v_aig_456_, v_cnf_457_, v_cache_458_, v_cond_459_, v_ifTrue_460_, v_ifFalse_461_, v_idx_462_, v_hcb_463_, v_htb_464_, v_hfb_465_, v_h_466_, v_hltc_467_, v_hltt_468_, v_hltf_469_, v_hc_470_, v_ht_471_, v_hf_472_, v_hdenote_473_);
lean_dec(v_idx_462_);
lean_dec(v_ifFalse_461_);
lean_dec(v_ifTrue_460_);
lean_dec(v_cond_459_);
lean_dec_ref(v_cnf_457_);
lean_dec_ref(v_aig_456_);
lean_dec_ref(v_inst_455_);
lean_dec_ref(v_inst_454_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty___redArg(lean_object* v_aig_475_){
_start:
{
lean_object* v_decls_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_488_; 
v_decls_476_ = lean_ctor_get(v_aig_475_, 0);
v___x_477_ = lean_array_get_size(v_decls_476_);
v___x_478_ = lean_unsigned_to_nat(2u);
v___x_479_ = lean_nat_mul(v___x_477_, v___x_478_);
v___x_480_ = lean_mk_empty_array_with_capacity(v___x_479_);
lean_dec(v___x_479_);
v___x_481_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___redArg(v_aig_475_);
v_isSharedCheck_488_ = !lean_is_exclusive(v_aig_475_);
if (v_isSharedCheck_488_ == 0)
{
lean_object* v_unused_489_; lean_object* v_unused_490_; 
v_unused_489_ = lean_ctor_get(v_aig_475_, 1);
lean_dec(v_unused_489_);
v_unused_490_ = lean_ctor_get(v_aig_475_, 0);
lean_dec(v_unused_490_);
v___x_483_ = v_aig_475_;
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
else
{
lean_dec(v_aig_475_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_486_; 
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 1, v___x_481_);
lean_ctor_set(v___x_483_, 0, v___x_480_);
v___x_486_ = v___x_483_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_480_);
lean_ctor_set(v_reuseFailAlloc_487_, 1, v___x_481_);
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
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty(lean_object* v_00_u03b1_491_, lean_object* v_inst_492_, lean_object* v_inst_493_, lean_object* v_aig_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty___redArg(v_aig_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty___boxed(lean_object* v_00_u03b1_496_, lean_object* v_inst_497_, lean_object* v_inst_498_, lean_object* v_aig_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty(v_00_u03b1_496_, v_inst_497_, v_inst_498_, v_aig_499_);
lean_dec_ref(v_inst_498_);
lean_dec_ref(v_inst_497_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_cast___redArg(lean_object* v_aig2_501_, lean_object* v_state_502_){
_start:
{
lean_object* v_cnf_503_; lean_object* v_cache_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_512_; 
v_cnf_503_ = lean_ctor_get(v_state_502_, 0);
v_cache_504_ = lean_ctor_get(v_state_502_, 1);
v_isSharedCheck_512_ = !lean_is_exclusive(v_state_502_);
if (v_isSharedCheck_512_ == 0)
{
v___x_506_ = v_state_502_;
v_isShared_507_ = v_isSharedCheck_512_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_cache_504_);
lean_inc(v_cnf_503_);
lean_dec(v_state_502_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_512_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_508_; lean_object* v___x_510_; 
v___x_508_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_cast___redArg(v_aig2_501_, v_cache_504_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 1, v___x_508_);
v___x_510_ = v___x_506_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_cnf_503_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v___x_508_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_cast___redArg___boxed(lean_object* v_aig2_513_, lean_object* v_state_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_cast___redArg(v_aig2_513_, v_state_514_);
lean_dec_ref(v_aig2_513_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_cast(lean_object* v_00_u03b1_516_, lean_object* v_inst_517_, lean_object* v_inst_518_, lean_object* v_aig1_519_, lean_object* v_aig2_520_, lean_object* v_state_521_, lean_object* v_hprefix_522_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_cast___redArg(v_aig2_520_, v_state_521_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_cast___boxed(lean_object* v_00_u03b1_524_, lean_object* v_inst_525_, lean_object* v_inst_526_, lean_object* v_aig1_527_, lean_object* v_aig2_528_, lean_object* v_state_529_, lean_object* v_hprefix_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_cast(v_00_u03b1_524_, v_inst_525_, v_inst_526_, v_aig1_527_, v_aig2_528_, v_state_529_, v_hprefix_530_);
lean_dec_ref(v_aig2_528_);
lean_dec_ref(v_aig1_527_);
lean_dec_ref(v_inst_526_);
lean_dec_ref(v_inst_525_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___redArg(lean_object* v_state_532_, lean_object* v_idx_533_){
_start:
{
lean_object* v_cnf_534_; lean_object* v_cache_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_545_; 
v_cnf_534_ = lean_ctor_get(v_state_532_, 0);
v_cache_535_ = lean_ctor_get(v_state_532_, 1);
v_isSharedCheck_545_ = !lean_is_exclusive(v_state_532_);
if (v_isSharedCheck_545_ == 0)
{
v___x_537_ = v_state_532_;
v_isShared_538_ = v_isSharedCheck_545_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_cache_535_);
lean_inc(v_cnf_534_);
lean_dec(v_state_532_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_545_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v_val_539_; lean_object* v_newCnf_540_; lean_object* v___x_541_; lean_object* v___x_543_; 
v_val_539_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg(v_cache_535_, v_idx_533_);
v_newCnf_540_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg(v_idx_533_);
v___x_541_ = l_Array_append___redArg(v_cnf_534_, v_newCnf_540_);
lean_dec_ref(v_newCnf_540_);
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 1, v_val_539_);
lean_ctor_set(v___x_537_, 0, v___x_541_);
v___x_543_ = v___x_537_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_541_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v_val_539_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse(lean_object* v_00_u03b1_546_, lean_object* v_inst_547_, lean_object* v_inst_548_, lean_object* v_aig_549_, lean_object* v_state_550_, lean_object* v_idx_551_, lean_object* v_h_552_, lean_object* v_htip_553_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___redArg(v_state_550_, v_idx_551_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___boxed(lean_object* v_00_u03b1_555_, lean_object* v_inst_556_, lean_object* v_inst_557_, lean_object* v_aig_558_, lean_object* v_state_559_, lean_object* v_idx_560_, lean_object* v_h_561_, lean_object* v_htip_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse(v_00_u03b1_555_, v_inst_556_, v_inst_557_, v_aig_558_, v_state_559_, v_idx_560_, v_h_561_, v_htip_562_);
lean_dec_ref(v_aig_558_);
lean_dec_ref(v_inst_557_);
lean_dec_ref(v_inst_556_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg(lean_object* v_state_564_, lean_object* v_idx_565_){
_start:
{
lean_object* v_cnf_566_; lean_object* v_cache_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_575_; 
v_cnf_566_ = lean_ctor_get(v_state_564_, 0);
v_cache_567_ = lean_ctor_get(v_state_564_, 1);
v_isSharedCheck_575_ = !lean_is_exclusive(v_state_564_);
if (v_isSharedCheck_575_ == 0)
{
v___x_569_ = v_state_564_;
v_isShared_570_ = v_isSharedCheck_575_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_cache_567_);
lean_inc(v_cnf_566_);
lean_dec(v_state_564_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_575_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v_val_571_; lean_object* v___x_573_; 
v_val_571_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg(v_cache_567_, v_idx_565_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 1, v_val_571_);
v___x_573_ = v___x_569_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_cnf_566_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v_val_571_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg___boxed(lean_object* v_state_576_, lean_object* v_idx_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg(v_state_576_, v_idx_577_);
lean_dec(v_idx_577_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom(lean_object* v_00_u03b1_579_, lean_object* v_inst_580_, lean_object* v_inst_581_, lean_object* v_aig_582_, lean_object* v_a_583_, lean_object* v_state_584_, lean_object* v_idx_585_, lean_object* v_h_586_, lean_object* v_htip_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg(v_state_584_, v_idx_585_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___boxed(lean_object* v_00_u03b1_589_, lean_object* v_inst_590_, lean_object* v_inst_591_, lean_object* v_aig_592_, lean_object* v_a_593_, lean_object* v_state_594_, lean_object* v_idx_595_, lean_object* v_h_596_, lean_object* v_htip_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom(v_00_u03b1_589_, v_inst_590_, v_inst_591_, v_aig_592_, v_a_593_, v_state_594_, v_idx_595_, v_h_596_, v_htip_597_);
lean_dec(v_idx_595_);
lean_dec(v_a_593_);
lean_dec_ref(v_aig_592_);
lean_dec_ref(v_inst_591_);
lean_dec_ref(v_inst_590_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg(lean_object* v_lhs_599_, lean_object* v_rhs_600_, lean_object* v_state_601_, lean_object* v_idx_602_){
_start:
{
lean_object* v_cnf_603_; lean_object* v_cache_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_632_; 
v_cnf_603_ = lean_ctor_get(v_state_601_, 0);
v_cache_604_ = lean_ctor_get(v_state_601_, 1);
v_isSharedCheck_632_ = !lean_is_exclusive(v_state_601_);
if (v_isSharedCheck_632_ == 0)
{
v___x_606_ = v_state_601_;
v_isShared_607_ = v_isSharedCheck_632_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_cache_604_);
lean_inc(v_cnf_603_);
lean_dec(v_state_601_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_632_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; uint8_t v___y_612_; uint8_t v___y_613_; uint8_t v___y_621_; lean_object* v___x_627_; lean_object* v___x_628_; uint8_t v___x_629_; 
v___x_608_ = lean_unsigned_to_nat(1u);
v___x_609_ = lean_nat_shiftr(v_lhs_599_, v___x_608_);
v___x_610_ = lean_nat_shiftr(v_rhs_600_, v___x_608_);
v___x_627_ = lean_nat_land(v___x_608_, v_lhs_599_);
v___x_628_ = lean_unsigned_to_nat(0u);
v___x_629_ = lean_nat_dec_eq(v___x_627_, v___x_628_);
lean_dec(v___x_627_);
if (v___x_629_ == 0)
{
uint8_t v___x_630_; 
v___x_630_ = 1;
v___y_621_ = v___x_630_;
goto v___jp_620_;
}
else
{
uint8_t v___x_631_; 
v___x_631_ = 0;
v___y_621_ = v___x_631_;
goto v___jp_620_;
}
v___jp_611_:
{
lean_object* v_val_614_; lean_object* v_newCnf_615_; lean_object* v___x_616_; lean_object* v___x_618_; 
v_val_614_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg(v_lhs_599_, v_rhs_600_, v_cache_604_, v_idx_602_);
v_newCnf_615_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg(v_idx_602_, v___x_609_, v___x_610_, v___y_612_, v___y_613_);
v___x_616_ = l_Array_append___redArg(v_cnf_603_, v_newCnf_615_);
lean_dec_ref(v_newCnf_615_);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 1, v_val_614_);
lean_ctor_set(v___x_606_, 0, v___x_616_);
v___x_618_ = v___x_606_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_616_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v_val_614_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
v___jp_620_:
{
lean_object* v___x_622_; lean_object* v___x_623_; uint8_t v___x_624_; 
v___x_622_ = lean_nat_land(v___x_608_, v_rhs_600_);
v___x_623_ = lean_unsigned_to_nat(0u);
v___x_624_ = lean_nat_dec_eq(v___x_622_, v___x_623_);
lean_dec(v___x_622_);
if (v___x_624_ == 0)
{
uint8_t v___x_625_; 
v___x_625_ = 1;
v___y_612_ = v___y_621_;
v___y_613_ = v___x_625_;
goto v___jp_611_;
}
else
{
uint8_t v___x_626_; 
v___x_626_ = 0;
v___y_612_ = v___y_621_;
v___y_613_ = v___x_626_;
goto v___jp_611_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg___boxed(lean_object* v_lhs_633_, lean_object* v_rhs_634_, lean_object* v_state_635_, lean_object* v_idx_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg(v_lhs_633_, v_rhs_634_, v_state_635_, v_idx_636_);
lean_dec(v_rhs_634_);
lean_dec(v_lhs_633_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate(lean_object* v_00_u03b1_638_, lean_object* v_inst_639_, lean_object* v_inst_640_, lean_object* v_aig_641_, lean_object* v_lhs_642_, lean_object* v_rhs_643_, lean_object* v_state_644_, lean_object* v_hlb_645_, lean_object* v_hrb_646_, lean_object* v_idx_647_, lean_object* v_h_648_, lean_object* v_htip_649_, lean_object* v_hl_650_, lean_object* v_hr_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg(v_lhs_642_, v_rhs_643_, v_state_644_, v_idx_647_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___boxed(lean_object* v_00_u03b1_653_, lean_object* v_inst_654_, lean_object* v_inst_655_, lean_object* v_aig_656_, lean_object* v_lhs_657_, lean_object* v_rhs_658_, lean_object* v_state_659_, lean_object* v_hlb_660_, lean_object* v_hrb_661_, lean_object* v_idx_662_, lean_object* v_h_663_, lean_object* v_htip_664_, lean_object* v_hl_665_, lean_object* v_hr_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate(v_00_u03b1_653_, v_inst_654_, v_inst_655_, v_aig_656_, v_lhs_657_, v_rhs_658_, v_state_659_, v_hlb_660_, v_hrb_661_, v_idx_662_, v_h_663_, v_htip_664_, v_hl_665_, v_hr_666_);
lean_dec(v_rhs_658_);
lean_dec(v_lhs_657_);
lean_dec_ref(v_aig_656_);
lean_dec_ref(v_inst_655_);
lean_dec_ref(v_inst_654_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___redArg(lean_object* v_state_668_, lean_object* v_cond_669_, lean_object* v_ifTrue_670_, lean_object* v_ifFalse_671_, lean_object* v_idx_672_){
_start:
{
lean_object* v_cnf_673_; lean_object* v_cache_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_712_; 
v_cnf_673_ = lean_ctor_get(v_state_668_, 0);
v_cache_674_ = lean_ctor_get(v_state_668_, 1);
v_isSharedCheck_712_ = !lean_is_exclusive(v_state_668_);
if (v_isSharedCheck_712_ == 0)
{
v___x_676_ = v_state_668_;
v_isShared_677_ = v_isSharedCheck_712_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_cache_674_);
lean_inc(v_cnf_673_);
lean_dec(v_state_668_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_712_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; uint8_t v___y_683_; uint8_t v___y_684_; uint8_t v___y_685_; uint8_t v___y_693_; uint8_t v___y_694_; uint8_t v___y_701_; lean_object* v___x_707_; lean_object* v___x_708_; uint8_t v___x_709_; 
v___x_678_ = lean_unsigned_to_nat(1u);
v___x_679_ = lean_nat_shiftr(v_cond_669_, v___x_678_);
v___x_680_ = lean_nat_shiftr(v_ifTrue_670_, v___x_678_);
v___x_681_ = lean_nat_shiftr(v_ifFalse_671_, v___x_678_);
v___x_707_ = lean_nat_land(v___x_678_, v_cond_669_);
v___x_708_ = lean_unsigned_to_nat(0u);
v___x_709_ = lean_nat_dec_eq(v___x_707_, v___x_708_);
lean_dec(v___x_707_);
if (v___x_709_ == 0)
{
uint8_t v___x_710_; 
v___x_710_ = 1;
v___y_701_ = v___x_710_;
goto v___jp_700_;
}
else
{
uint8_t v___x_711_; 
v___x_711_ = 0;
v___y_701_ = v___x_711_;
goto v___jp_700_;
}
v___jp_682_:
{
lean_object* v_val_686_; lean_object* v_newCnf_687_; lean_object* v___x_688_; lean_object* v___x_690_; 
v_val_686_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___redArg(v_cache_674_, v_cond_669_, v_ifTrue_670_, v_ifFalse_671_, v_idx_672_);
v_newCnf_687_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF___redArg(v_idx_672_, v___x_679_, v___x_680_, v___x_681_, v___y_683_, v___y_684_, v___y_685_);
v___x_688_ = l_Array_append___redArg(v_cnf_673_, v_newCnf_687_);
lean_dec_ref(v_newCnf_687_);
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 1, v_val_686_);
lean_ctor_set(v___x_676_, 0, v___x_688_);
v___x_690_ = v___x_676_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_688_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v_val_686_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
v___jp_692_:
{
lean_object* v___x_695_; lean_object* v___x_696_; uint8_t v___x_697_; 
v___x_695_ = lean_nat_land(v___x_678_, v_ifFalse_671_);
v___x_696_ = lean_unsigned_to_nat(0u);
v___x_697_ = lean_nat_dec_eq(v___x_695_, v___x_696_);
lean_dec(v___x_695_);
if (v___x_697_ == 0)
{
uint8_t v___x_698_; 
v___x_698_ = 1;
v___y_683_ = v___y_693_;
v___y_684_ = v___y_694_;
v___y_685_ = v___x_698_;
goto v___jp_682_;
}
else
{
uint8_t v___x_699_; 
v___x_699_ = 0;
v___y_683_ = v___y_693_;
v___y_684_ = v___y_694_;
v___y_685_ = v___x_699_;
goto v___jp_682_;
}
}
v___jp_700_:
{
lean_object* v___x_702_; lean_object* v___x_703_; uint8_t v___x_704_; 
v___x_702_ = lean_nat_land(v___x_678_, v_ifTrue_670_);
v___x_703_ = lean_unsigned_to_nat(0u);
v___x_704_ = lean_nat_dec_eq(v___x_702_, v___x_703_);
lean_dec(v___x_702_);
if (v___x_704_ == 0)
{
uint8_t v___x_705_; 
v___x_705_ = 1;
v___y_693_ = v___y_701_;
v___y_694_ = v___x_705_;
goto v___jp_692_;
}
else
{
uint8_t v___x_706_; 
v___x_706_ = 0;
v___y_693_ = v___y_701_;
v___y_694_ = v___x_706_;
goto v___jp_692_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___redArg___boxed(lean_object* v_state_713_, lean_object* v_cond_714_, lean_object* v_ifTrue_715_, lean_object* v_ifFalse_716_, lean_object* v_idx_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___redArg(v_state_713_, v_cond_714_, v_ifTrue_715_, v_ifFalse_716_, v_idx_717_);
lean_dec(v_ifFalse_716_);
lean_dec(v_ifTrue_715_);
lean_dec(v_cond_714_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte(lean_object* v_00_u03b1_719_, lean_object* v_inst_720_, lean_object* v_inst_721_, lean_object* v_aig_722_, lean_object* v_state_723_, lean_object* v_cond_724_, lean_object* v_ifTrue_725_, lean_object* v_ifFalse_726_, lean_object* v_idx_727_, lean_object* v_hcb_728_, lean_object* v_htb_729_, lean_object* v_hfb_730_, lean_object* v_h_731_, lean_object* v_hltc_732_, lean_object* v_hltt_733_, lean_object* v_hltf_734_, lean_object* v_hc_735_, lean_object* v_ht_736_, lean_object* v_hf_737_, lean_object* v_hdenote_738_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___redArg(v_state_723_, v_cond_724_, v_ifTrue_725_, v_ifFalse_726_, v_idx_727_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___boxed(lean_object** _args){
lean_object* v_00_u03b1_740_ = _args[0];
lean_object* v_inst_741_ = _args[1];
lean_object* v_inst_742_ = _args[2];
lean_object* v_aig_743_ = _args[3];
lean_object* v_state_744_ = _args[4];
lean_object* v_cond_745_ = _args[5];
lean_object* v_ifTrue_746_ = _args[6];
lean_object* v_ifFalse_747_ = _args[7];
lean_object* v_idx_748_ = _args[8];
lean_object* v_hcb_749_ = _args[9];
lean_object* v_htb_750_ = _args[10];
lean_object* v_hfb_751_ = _args[11];
lean_object* v_h_752_ = _args[12];
lean_object* v_hltc_753_ = _args[13];
lean_object* v_hltt_754_ = _args[14];
lean_object* v_hltf_755_ = _args[15];
lean_object* v_hc_756_ = _args[16];
lean_object* v_ht_757_ = _args[17];
lean_object* v_hf_758_ = _args[18];
lean_object* v_hdenote_759_ = _args[19];
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte(v_00_u03b1_740_, v_inst_741_, v_inst_742_, v_aig_743_, v_state_744_, v_cond_745_, v_ifTrue_746_, v_ifFalse_747_, v_idx_748_, v_hcb_749_, v_htb_750_, v_hfb_751_, v_h_752_, v_hltc_753_, v_hltt_754_, v_hltf_755_, v_hc_756_, v_ht_757_, v_hf_758_, v_hdenote_759_);
lean_dec(v_ifFalse_747_);
lean_dec(v_ifTrue_746_);
lean_dec(v_cond_745_);
lean_dec_ref(v_aig_743_);
lean_dec_ref(v_inst_742_);
lean_dec_ref(v_inst_741_);
return v_res_760_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg(lean_object* v_assign_761_, lean_object* v_state_762_){
_start:
{
lean_object* v_cnf_763_; uint8_t v___x_764_; 
v_cnf_763_ = lean_ctor_get(v_state_762_, 0);
v___x_764_ = l_Std_Sat_CNF_eval___redArg(v_assign_761_, v_cnf_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg___boxed(lean_object* v_assign_765_, lean_object* v_state_766_){
_start:
{
uint8_t v_res_767_; lean_object* v_r_768_; 
v_res_767_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg(v_assign_765_, v_state_766_);
lean_dec_ref(v_state_766_);
v_r_768_ = lean_box(v_res_767_);
return v_r_768_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval(lean_object* v_00_u03b1_769_, lean_object* v_inst_770_, lean_object* v_inst_771_, lean_object* v_aig_772_, lean_object* v_assign_773_, lean_object* v_state_774_){
_start:
{
uint8_t v___x_775_; 
v___x_775_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg(v_assign_773_, v_state_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___boxed(lean_object* v_00_u03b1_776_, lean_object* v_inst_777_, lean_object* v_inst_778_, lean_object* v_aig_779_, lean_object* v_assign_780_, lean_object* v_state_781_){
_start:
{
uint8_t v_res_782_; lean_object* v_r_783_; 
v_res_782_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval(v_00_u03b1_776_, v_inst_777_, v_inst_778_, v_aig_779_, v_assign_780_, v_state_781_);
lean_dec_ref(v_state_781_);
lean_dec_ref(v_aig_779_);
lean_dec_ref(v_inst_778_);
lean_dec_ref(v_inst_777_);
v_r_783_ = lean_box(v_res_782_);
return v_r_783_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg(lean_object* v_l0_784_, lean_object* v_l1_785_, lean_object* v_r0_786_, lean_object* v_r1_787_){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; uint8_t v___x_790_; 
v___x_788_ = lean_unsigned_to_nat(1u);
v___x_789_ = lean_nat_lxor(v_r0_786_, v___x_788_);
v___x_790_ = lean_nat_dec_eq(v_l0_784_, v___x_789_);
if (v___x_790_ == 0)
{
lean_object* v___x_791_; uint8_t v___x_792_; 
v___x_791_ = lean_nat_lxor(v_r1_787_, v___x_788_);
v___x_792_ = lean_nat_dec_eq(v_l0_784_, v___x_791_);
if (v___x_792_ == 0)
{
uint8_t v___x_793_; 
v___x_793_ = lean_nat_dec_eq(v_l1_785_, v___x_789_);
if (v___x_793_ == 0)
{
uint8_t v___x_794_; 
v___x_794_ = lean_nat_dec_eq(v_l1_785_, v___x_791_);
lean_dec(v___x_791_);
if (v___x_794_ == 0)
{
lean_object* v___x_795_; 
lean_dec(v___x_789_);
lean_dec(v_l1_785_);
lean_dec(v_l0_784_);
v___x_795_ = lean_box(0);
return v___x_795_;
}
else
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_796_ = lean_nat_lxor(v_l0_784_, v___x_788_);
lean_dec(v_l0_784_);
v___x_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
lean_ctor_set(v___x_797_, 1, v___x_789_);
v___x_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_798_, 0, v_l1_785_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
v___x_799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
return v___x_799_;
}
}
else
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
lean_dec(v___x_789_);
v___x_800_ = lean_nat_lxor(v_l0_784_, v___x_788_);
lean_dec(v_l0_784_);
v___x_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
lean_ctor_set(v___x_801_, 1, v___x_791_);
v___x_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_802_, 0, v_l1_785_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
v___x_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
return v___x_803_;
}
}
else
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
lean_dec(v___x_791_);
v___x_804_ = lean_nat_lxor(v_l1_785_, v___x_788_);
lean_dec(v_l1_785_);
v___x_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
lean_ctor_set(v___x_805_, 1, v___x_789_);
v___x_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_806_, 0, v_l0_784_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
v___x_807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
return v___x_807_;
}
}
else
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
lean_dec(v___x_789_);
v___x_808_ = lean_nat_lxor(v_l1_785_, v___x_788_);
lean_dec(v_l1_785_);
v___x_809_ = lean_nat_lxor(v_r1_787_, v___x_788_);
v___x_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_810_, 0, v___x_808_);
lean_ctor_set(v___x_810_, 1, v___x_809_);
v___x_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_811_, 0, v_l0_784_);
lean_ctor_set(v___x_811_, 1, v___x_810_);
v___x_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
return v___x_812_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg___boxed(lean_object* v_l0_813_, lean_object* v_l1_814_, lean_object* v_r0_815_, lean_object* v_r1_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg(v_l0_813_, v_l1_814_, v_r0_815_, v_r1_816_);
lean_dec(v_r1_816_);
lean_dec(v_r0_815_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go(lean_object* v_l_818_, lean_object* v_r_819_, lean_object* v_l0_820_, lean_object* v_l1_821_, lean_object* v_r0_822_, lean_object* v_r1_823_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg(v_l0_820_, v_l1_821_, v_r0_822_, v_r1_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___boxed(lean_object* v_l_825_, lean_object* v_r_826_, lean_object* v_l0_827_, lean_object* v_l1_828_, lean_object* v_r0_829_, lean_object* v_r1_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go(v_l_825_, v_r_826_, v_l0_827_, v_l1_828_, v_r0_829_, v_r1_830_);
lean_dec(v_r1_830_);
lean_dec(v_r0_829_);
lean_dec(v_r_826_);
lean_dec(v_l_825_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___redArg(lean_object* v_aig_832_, lean_object* v_root_833_){
_start:
{
lean_object* v_decls_834_; lean_object* v___x_835_; 
v_decls_834_ = lean_ctor_get(v_aig_832_, 0);
v___x_835_ = lean_array_fget_borrowed(v_decls_834_, v_root_833_);
if (lean_obj_tag(v___x_835_) == 2)
{
lean_object* v_l_836_; lean_object* v_r_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; uint8_t v___x_841_; 
v_l_836_ = lean_ctor_get(v___x_835_, 0);
v_r_837_ = lean_ctor_get(v___x_835_, 1);
v___x_838_ = lean_unsigned_to_nat(1u);
v___x_839_ = lean_nat_land(v___x_838_, v_l_836_);
v___x_840_ = lean_unsigned_to_nat(0u);
v___x_841_ = lean_nat_dec_eq(v___x_839_, v___x_840_);
lean_dec(v___x_839_);
if (v___x_841_ == 0)
{
lean_object* v___x_842_; uint8_t v___x_843_; 
v___x_842_ = lean_nat_land(v___x_838_, v_r_837_);
v___x_843_ = lean_nat_dec_eq(v___x_842_, v___x_840_);
lean_dec(v___x_842_);
if (v___x_843_ == 0)
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = lean_nat_shiftr(v_l_836_, v___x_838_);
v___x_845_ = lean_array_fget_borrowed(v_decls_834_, v___x_844_);
lean_dec(v___x_844_);
if (lean_obj_tag(v___x_845_) == 2)
{
lean_object* v_l_846_; lean_object* v_r_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v_l_846_ = lean_ctor_get(v___x_845_, 0);
v_r_847_ = lean_ctor_get(v___x_845_, 1);
v___x_848_ = lean_nat_shiftr(v_r_837_, v___x_838_);
v___x_849_ = lean_array_fget_borrowed(v_decls_834_, v___x_848_);
lean_dec(v___x_848_);
if (lean_obj_tag(v___x_849_) == 2)
{
lean_object* v_l_850_; lean_object* v_r_851_; lean_object* v___x_852_; 
v_l_850_ = lean_ctor_get(v___x_849_, 0);
v_r_851_ = lean_ctor_get(v___x_849_, 1);
lean_inc(v_r_847_);
lean_inc(v_l_846_);
v___x_852_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg(v_l_846_, v_r_847_, v_l_850_, v_r_851_);
return v___x_852_;
}
else
{
lean_object* v___x_853_; 
v___x_853_ = lean_box(0);
return v___x_853_;
}
}
else
{
lean_object* v___x_854_; 
v___x_854_ = lean_box(0);
return v___x_854_;
}
}
else
{
lean_object* v___x_855_; 
v___x_855_ = lean_box(0);
return v___x_855_;
}
}
else
{
lean_object* v___x_856_; 
v___x_856_ = lean_box(0);
return v___x_856_;
}
}
else
{
lean_object* v___x_857_; 
v___x_857_ = lean_box(0);
return v___x_857_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___redArg___boxed(lean_object* v_aig_858_, lean_object* v_root_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___redArg(v_aig_858_, v_root_859_);
lean_dec(v_root_859_);
lean_dec_ref(v_aig_858_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte(lean_object* v_00_u03b1_861_, lean_object* v_inst_862_, lean_object* v_inst_863_, lean_object* v_aig_864_, lean_object* v_root_865_, lean_object* v_h_866_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___redArg(v_aig_864_, v_root_865_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___boxed(lean_object* v_00_u03b1_868_, lean_object* v_inst_869_, lean_object* v_inst_870_, lean_object* v_aig_871_, lean_object* v_root_872_, lean_object* v_h_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte(v_00_u03b1_868_, v_inst_869_, v_inst_870_, v_aig_871_, v_root_872_, v_h_873_);
lean_dec(v_root_872_);
lean_dec_ref(v_aig_871_);
lean_dec_ref(v_inst_870_);
lean_dec_ref(v_inst_869_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_match__4_splitter___redArg(lean_object* v_x_875_, lean_object* v_h__1_876_, lean_object* v_h__2_877_){
_start:
{
if (lean_obj_tag(v_x_875_) == 2)
{
lean_object* v_l_878_; lean_object* v_r_879_; lean_object* v___x_880_; 
lean_dec(v_h__2_877_);
v_l_878_ = lean_ctor_get(v_x_875_, 0);
lean_inc(v_l_878_);
v_r_879_ = lean_ctor_get(v_x_875_, 1);
lean_inc(v_r_879_);
lean_dec_ref_known(v_x_875_, 2);
v___x_880_ = lean_apply_3(v_h__1_876_, v_l_878_, v_r_879_, lean_box(0));
return v___x_880_;
}
else
{
lean_object* v___x_881_; 
lean_dec(v_h__1_876_);
v___x_881_ = lean_apply_3(v_h__2_877_, v_x_875_, lean_box(0), lean_box(0));
return v___x_881_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_match__4_splitter(lean_object* v_00_u03b1_882_, lean_object* v_motive_883_, lean_object* v_x_884_, lean_object* v_h__1_885_, lean_object* v_h__2_886_){
_start:
{
if (lean_obj_tag(v_x_884_) == 2)
{
lean_object* v_l_887_; lean_object* v_r_888_; lean_object* v___x_889_; 
lean_dec(v_h__2_886_);
v_l_887_ = lean_ctor_get(v_x_884_, 0);
lean_inc(v_l_887_);
v_r_888_ = lean_ctor_get(v_x_884_, 1);
lean_inc(v_r_888_);
lean_dec_ref_known(v_x_884_, 2);
v___x_889_ = lean_apply_3(v_h__1_885_, v_l_887_, v_r_888_, lean_box(0));
return v___x_889_;
}
else
{
lean_object* v___x_890_; 
lean_dec(v_h__1_885_);
v___x_890_ = lean_apply_3(v_h__2_886_, v_x_884_, lean_box(0), lean_box(0));
return v___x_890_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_match__1_splitter___redArg(lean_object* v_x_891_, lean_object* v_x_892_, lean_object* v_h__1_893_, lean_object* v_h__2_894_){
_start:
{
if (lean_obj_tag(v_x_891_) == 2)
{
if (lean_obj_tag(v_x_892_) == 2)
{
lean_object* v_l_895_; lean_object* v_r_896_; lean_object* v_l_897_; lean_object* v_r_898_; lean_object* v___x_899_; 
lean_dec(v_h__2_894_);
v_l_895_ = lean_ctor_get(v_x_891_, 0);
lean_inc(v_l_895_);
v_r_896_ = lean_ctor_get(v_x_891_, 1);
lean_inc(v_r_896_);
lean_dec_ref_known(v_x_891_, 2);
v_l_897_ = lean_ctor_get(v_x_892_, 0);
lean_inc(v_l_897_);
v_r_898_ = lean_ctor_get(v_x_892_, 1);
lean_inc(v_r_898_);
lean_dec_ref_known(v_x_892_, 2);
v___x_899_ = lean_apply_6(v_h__1_893_, v_l_895_, v_r_896_, v_l_897_, v_r_898_, lean_box(0), lean_box(0));
return v___x_899_;
}
else
{
lean_object* v___x_900_; 
lean_dec(v_h__1_893_);
v___x_900_ = lean_apply_5(v_h__2_894_, v_x_891_, v_x_892_, lean_box(0), lean_box(0), lean_box(0));
return v___x_900_;
}
}
else
{
lean_object* v___x_901_; 
lean_dec(v_h__1_893_);
v___x_901_ = lean_apply_5(v_h__2_894_, v_x_891_, v_x_892_, lean_box(0), lean_box(0), lean_box(0));
return v___x_901_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_match__1_splitter(lean_object* v_00_u03b1_902_, lean_object* v_motive_903_, lean_object* v_x_904_, lean_object* v_x_905_, lean_object* v_h__1_906_, lean_object* v_h__2_907_){
_start:
{
if (lean_obj_tag(v_x_904_) == 2)
{
if (lean_obj_tag(v_x_905_) == 2)
{
lean_object* v_l_908_; lean_object* v_r_909_; lean_object* v_l_910_; lean_object* v_r_911_; lean_object* v___x_912_; 
lean_dec(v_h__2_907_);
v_l_908_ = lean_ctor_get(v_x_904_, 0);
lean_inc(v_l_908_);
v_r_909_ = lean_ctor_get(v_x_904_, 1);
lean_inc(v_r_909_);
lean_dec_ref_known(v_x_904_, 2);
v_l_910_ = lean_ctor_get(v_x_905_, 0);
lean_inc(v_l_910_);
v_r_911_ = lean_ctor_get(v_x_905_, 1);
lean_inc(v_r_911_);
lean_dec_ref_known(v_x_905_, 2);
v___x_912_ = lean_apply_6(v_h__1_906_, v_l_908_, v_r_909_, v_l_910_, v_r_911_, lean_box(0), lean_box(0));
return v___x_912_;
}
else
{
lean_object* v___x_913_; 
lean_dec(v_h__1_906_);
v___x_913_ = lean_apply_5(v_h__2_907_, v_x_904_, v_x_905_, lean_box(0), lean_box(0), lean_box(0));
return v___x_913_;
}
}
else
{
lean_object* v___x_914_; 
lean_dec(v_h__1_906_);
v___x_914_ = lean_apply_5(v_h__2_907_, v_x_904_, v_x_905_, lean_box(0), lean_box(0), lean_box(0));
return v___x_914_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(lean_object* v_aig_915_, lean_object* v_upper_916_, lean_object* v_state_917_){
_start:
{
lean_object* v_cache_918_; lean_object* v___x_919_; uint8_t v___x_920_; 
v_cache_918_ = lean_ctor_get(v_state_917_, 1);
v___x_919_ = lean_array_fget_borrowed(v_cache_918_, v_upper_916_);
v___x_920_ = lean_unbox(v___x_919_);
if (v___x_920_ == 0)
{
lean_object* v_decls_921_; lean_object* v_decl_922_; 
v_decls_921_ = lean_ctor_get(v_aig_915_, 0);
v_decl_922_ = lean_array_fget_borrowed(v_decls_921_, v_upper_916_);
switch(lean_obj_tag(v_decl_922_))
{
case 0:
{
lean_object* v___x_923_; 
v___x_923_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___redArg(v_state_917_, v_upper_916_);
return v___x_923_;
}
case 1:
{
lean_object* v___x_924_; 
v___x_924_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg(v_state_917_, v_upper_916_);
lean_dec(v_upper_916_);
return v___x_924_;
}
default: 
{
lean_object* v_l_925_; lean_object* v_r_926_; lean_object* v___x_927_; 
v_l_925_ = lean_ctor_get(v_decl_922_, 0);
v_r_926_ = lean_ctor_get(v_decl_922_, 1);
v___x_927_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___redArg(v_aig_915_, v_upper_916_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v_val_930_; lean_object* v___x_931_; lean_object* v_val_932_; lean_object* v_val_933_; 
v___x_928_ = lean_unsigned_to_nat(1u);
v___x_929_ = lean_nat_shiftr(v_l_925_, v___x_928_);
v_val_930_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(v_aig_915_, v___x_929_, v_state_917_);
v___x_931_ = lean_nat_shiftr(v_r_926_, v___x_928_);
v_val_932_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(v_aig_915_, v___x_931_, v_val_930_);
v_val_933_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg(v_l_925_, v_r_926_, v_val_932_, v_upper_916_);
return v_val_933_;
}
else
{
lean_object* v_val_934_; lean_object* v_snd_935_; lean_object* v_fst_936_; lean_object* v_fst_937_; lean_object* v_snd_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v_val_941_; lean_object* v___x_942_; lean_object* v_val_943_; lean_object* v___x_944_; lean_object* v_val_945_; lean_object* v_val_946_; 
v_val_934_ = lean_ctor_get(v___x_927_, 0);
lean_inc(v_val_934_);
lean_dec_ref_known(v___x_927_, 1);
v_snd_935_ = lean_ctor_get(v_val_934_, 1);
lean_inc(v_snd_935_);
v_fst_936_ = lean_ctor_get(v_val_934_, 0);
lean_inc(v_fst_936_);
lean_dec(v_val_934_);
v_fst_937_ = lean_ctor_get(v_snd_935_, 0);
lean_inc(v_fst_937_);
v_snd_938_ = lean_ctor_get(v_snd_935_, 1);
lean_inc(v_snd_938_);
lean_dec(v_snd_935_);
v___x_939_ = lean_unsigned_to_nat(1u);
v___x_940_ = lean_nat_shiftr(v_fst_936_, v___x_939_);
v_val_941_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(v_aig_915_, v___x_940_, v_state_917_);
v___x_942_ = lean_nat_shiftr(v_fst_937_, v___x_939_);
v_val_943_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(v_aig_915_, v___x_942_, v_val_941_);
v___x_944_ = lean_nat_shiftr(v_snd_938_, v___x_939_);
v_val_945_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(v_aig_915_, v___x_944_, v_val_943_);
v_val_946_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___redArg(v_val_945_, v_fst_936_, v_fst_937_, v_snd_938_, v_upper_916_);
lean_dec(v_snd_938_);
lean_dec(v_fst_937_);
lean_dec(v_fst_936_);
return v_val_946_;
}
}
}
}
else
{
lean_dec(v_upper_916_);
return v_state_917_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg___boxed(lean_object* v_aig_947_, lean_object* v_upper_948_, lean_object* v_state_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(v_aig_947_, v_upper_948_, v_state_949_);
lean_dec_ref(v_aig_947_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go(lean_object* v_00_u03b1_951_, lean_object* v_inst_952_, lean_object* v_inst_953_, lean_object* v_aig_954_, lean_object* v_upper_955_, lean_object* v_h_956_, lean_object* v_state_957_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(v_aig_954_, v_upper_955_, v_state_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___boxed(lean_object* v_00_u03b1_959_, lean_object* v_inst_960_, lean_object* v_inst_961_, lean_object* v_aig_962_, lean_object* v_upper_963_, lean_object* v_h_964_, lean_object* v_state_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go(v_00_u03b1_959_, v_inst_960_, v_inst_961_, v_aig_962_, v_upper_963_, v_h_964_, v_state_965_);
lean_dec_ref(v_aig_962_);
lean_dec_ref(v_inst_961_);
lean_dec_ref(v_inst_960_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go_match__103_splitter___redArg(lean_object* v_decl_967_, lean_object* v_h__1_968_, lean_object* v_h__2_969_, lean_object* v_h__3_970_){
_start:
{
switch(lean_obj_tag(v_decl_967_))
{
case 0:
{
lean_object* v___x_971_; 
lean_dec(v_h__3_970_);
lean_dec(v_h__2_969_);
v___x_971_ = lean_apply_1(v_h__1_968_, lean_box(0));
return v___x_971_;
}
case 1:
{
lean_object* v_idx_972_; lean_object* v___x_973_; 
lean_dec(v_h__3_970_);
lean_dec(v_h__1_968_);
v_idx_972_ = lean_ctor_get(v_decl_967_, 0);
lean_inc(v_idx_972_);
lean_dec_ref_known(v_decl_967_, 1);
v___x_973_ = lean_apply_2(v_h__2_969_, v_idx_972_, lean_box(0));
return v___x_973_;
}
default: 
{
lean_object* v_l_974_; lean_object* v_r_975_; lean_object* v___x_976_; 
lean_dec(v_h__2_969_);
lean_dec(v_h__1_968_);
v_l_974_ = lean_ctor_get(v_decl_967_, 0);
lean_inc(v_l_974_);
v_r_975_ = lean_ctor_get(v_decl_967_, 1);
lean_inc(v_r_975_);
lean_dec_ref_known(v_decl_967_, 2);
v___x_976_ = lean_apply_3(v_h__3_970_, v_l_974_, v_r_975_, lean_box(0));
return v___x_976_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go_match__103_splitter(lean_object* v_00_u03b1_977_, lean_object* v_motive_978_, lean_object* v_decl_979_, lean_object* v_h__1_980_, lean_object* v_h__2_981_, lean_object* v_h__3_982_){
_start:
{
switch(lean_obj_tag(v_decl_979_))
{
case 0:
{
lean_object* v___x_983_; 
lean_dec(v_h__3_982_);
lean_dec(v_h__2_981_);
v___x_983_ = lean_apply_1(v_h__1_980_, lean_box(0));
return v___x_983_;
}
case 1:
{
lean_object* v_idx_984_; lean_object* v___x_985_; 
lean_dec(v_h__3_982_);
lean_dec(v_h__1_980_);
v_idx_984_ = lean_ctor_get(v_decl_979_, 0);
lean_inc(v_idx_984_);
lean_dec_ref_known(v_decl_979_, 1);
v___x_985_ = lean_apply_2(v_h__2_981_, v_idx_984_, lean_box(0));
return v___x_985_;
}
default: 
{
lean_object* v_l_986_; lean_object* v_r_987_; lean_object* v___x_988_; 
lean_dec(v_h__2_981_);
lean_dec(v_h__1_980_);
v_l_986_ = lean_ctor_get(v_decl_979_, 0);
lean_inc(v_l_986_);
v_r_987_ = lean_ctor_get(v_decl_979_, 1);
lean_inc(v_r_987_);
lean_dec_ref_known(v_decl_979_, 2);
v___x_988_ = lean_apply_3(v_h__3_982_, v_l_986_, v_r_987_, lean_box(0));
return v___x_988_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go_match__81_splitter___redArg(lean_object* v_x_989_, lean_object* v_h__1_990_, lean_object* v_h__2_991_){
_start:
{
if (lean_obj_tag(v_x_989_) == 0)
{
lean_object* v___x_992_; 
lean_dec(v_h__1_990_);
v___x_992_ = lean_apply_1(v_h__2_991_, lean_box(0));
return v___x_992_;
}
else
{
lean_object* v_val_993_; lean_object* v_snd_994_; lean_object* v_fst_995_; lean_object* v_fst_996_; lean_object* v_snd_997_; lean_object* v___x_998_; 
lean_dec(v_h__2_991_);
v_val_993_ = lean_ctor_get(v_x_989_, 0);
lean_inc(v_val_993_);
lean_dec_ref_known(v_x_989_, 1);
v_snd_994_ = lean_ctor_get(v_val_993_, 1);
lean_inc(v_snd_994_);
v_fst_995_ = lean_ctor_get(v_val_993_, 0);
lean_inc(v_fst_995_);
lean_dec(v_val_993_);
v_fst_996_ = lean_ctor_get(v_snd_994_, 0);
lean_inc(v_fst_996_);
v_snd_997_ = lean_ctor_get(v_snd_994_, 1);
lean_inc(v_snd_997_);
lean_dec(v_snd_994_);
v___x_998_ = lean_apply_4(v_h__1_990_, v_fst_995_, v_fst_996_, v_snd_997_, lean_box(0));
return v___x_998_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go_match__81_splitter(lean_object* v_motive_999_, lean_object* v_x_1000_, lean_object* v_h__1_1001_, lean_object* v_h__2_1002_){
_start:
{
if (lean_obj_tag(v_x_1000_) == 0)
{
lean_object* v___x_1003_; 
lean_dec(v_h__1_1001_);
v___x_1003_ = lean_apply_1(v_h__2_1002_, lean_box(0));
return v___x_1003_;
}
else
{
lean_object* v_val_1004_; lean_object* v_snd_1005_; lean_object* v_fst_1006_; lean_object* v_fst_1007_; lean_object* v_snd_1008_; lean_object* v___x_1009_; 
lean_dec(v_h__2_1002_);
v_val_1004_ = lean_ctor_get(v_x_1000_, 0);
lean_inc(v_val_1004_);
lean_dec_ref_known(v_x_1000_, 1);
v_snd_1005_ = lean_ctor_get(v_val_1004_, 1);
lean_inc(v_snd_1005_);
v_fst_1006_ = lean_ctor_get(v_val_1004_, 0);
lean_inc(v_fst_1006_);
lean_dec(v_val_1004_);
v_fst_1007_ = lean_ctor_get(v_snd_1005_, 0);
lean_inc(v_fst_1007_);
v_snd_1008_ = lean_ctor_get(v_snd_1005_, 1);
lean_inc(v_snd_1008_);
lean_dec(v_snd_1005_);
v___x_1009_ = lean_apply_4(v_h__1_1001_, v_fst_1006_, v_fst_1007_, v_snd_1008_, lean_box(0));
return v___x_1009_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__52_splitter___redArg(lean_object* v_x_1010_, lean_object* v_h__1_1011_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = lean_apply_2(v_h__1_1011_, v_x_1010_, lean_box(0));
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__52_splitter(lean_object* v_00_u03b1_1013_, lean_object* v_inst_1014_, lean_object* v_inst_1015_, lean_object* v_aig_1016_, lean_object* v_upper_1017_, lean_object* v_h_1018_, lean_object* v_state_1019_, lean_object* v_cond_1020_, lean_object* v_ifTrue_1021_, lean_object* v_ifFalse_1022_, lean_object* v_hltc_1023_, lean_object* v_motive_1024_, lean_object* v_x_1025_, lean_object* v_h__1_1026_){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = lean_apply_2(v_h__1_1026_, v_x_1025_, lean_box(0));
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__52_splitter___boxed(lean_object* v_00_u03b1_1028_, lean_object* v_inst_1029_, lean_object* v_inst_1030_, lean_object* v_aig_1031_, lean_object* v_upper_1032_, lean_object* v_h_1033_, lean_object* v_state_1034_, lean_object* v_cond_1035_, lean_object* v_ifTrue_1036_, lean_object* v_ifFalse_1037_, lean_object* v_hltc_1038_, lean_object* v_motive_1039_, lean_object* v_x_1040_, lean_object* v_h__1_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__52_splitter(v_00_u03b1_1028_, v_inst_1029_, v_inst_1030_, v_aig_1031_, v_upper_1032_, v_h_1033_, v_state_1034_, v_cond_1035_, v_ifTrue_1036_, v_ifFalse_1037_, v_hltc_1038_, v_motive_1039_, v_x_1040_, v_h__1_1041_);
lean_dec(v_ifFalse_1037_);
lean_dec(v_ifTrue_1036_);
lean_dec(v_cond_1035_);
lean_dec_ref(v_state_1034_);
lean_dec(v_upper_1032_);
lean_dec_ref(v_aig_1031_);
lean_dec_ref(v_inst_1030_);
lean_dec_ref(v_inst_1029_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__50_splitter___redArg(lean_object* v_x_1043_, lean_object* v_h__1_1044_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = lean_apply_2(v_h__1_1044_, v_x_1043_, lean_box(0));
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__50_splitter(lean_object* v_00_u03b1_1046_, lean_object* v_inst_1047_, lean_object* v_inst_1048_, lean_object* v_aig_1049_, lean_object* v_upper_1050_, lean_object* v_h_1051_, lean_object* v_cond_1052_, lean_object* v_ifTrue_1053_, lean_object* v_ifFalse_1054_, lean_object* v_hltt_1055_, lean_object* v_cstate_1056_, lean_object* v_motive_1057_, lean_object* v_x_1058_, lean_object* v_h__1_1059_){
_start:
{
lean_object* v___x_1060_; 
v___x_1060_ = lean_apply_2(v_h__1_1059_, v_x_1058_, lean_box(0));
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__50_splitter___boxed(lean_object* v_00_u03b1_1061_, lean_object* v_inst_1062_, lean_object* v_inst_1063_, lean_object* v_aig_1064_, lean_object* v_upper_1065_, lean_object* v_h_1066_, lean_object* v_cond_1067_, lean_object* v_ifTrue_1068_, lean_object* v_ifFalse_1069_, lean_object* v_hltt_1070_, lean_object* v_cstate_1071_, lean_object* v_motive_1072_, lean_object* v_x_1073_, lean_object* v_h__1_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__50_splitter(v_00_u03b1_1061_, v_inst_1062_, v_inst_1063_, v_aig_1064_, v_upper_1065_, v_h_1066_, v_cond_1067_, v_ifTrue_1068_, v_ifFalse_1069_, v_hltt_1070_, v_cstate_1071_, v_motive_1072_, v_x_1073_, v_h__1_1074_);
lean_dec_ref(v_cstate_1071_);
lean_dec(v_ifFalse_1069_);
lean_dec(v_ifTrue_1068_);
lean_dec(v_cond_1067_);
lean_dec(v_upper_1065_);
lean_dec_ref(v_aig_1064_);
lean_dec_ref(v_inst_1063_);
lean_dec_ref(v_inst_1062_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__48_splitter___redArg(lean_object* v_x_1076_, lean_object* v_h__1_1077_){
_start:
{
lean_object* v___x_1078_; 
v___x_1078_ = lean_apply_2(v_h__1_1077_, v_x_1076_, lean_box(0));
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__48_splitter(lean_object* v_00_u03b1_1079_, lean_object* v_inst_1080_, lean_object* v_inst_1081_, lean_object* v_aig_1082_, lean_object* v_upper_1083_, lean_object* v_h_1084_, lean_object* v_cond_1085_, lean_object* v_ifTrue_1086_, lean_object* v_ifFalse_1087_, lean_object* v_hltf_1088_, lean_object* v_tstate_1089_, lean_object* v_motive_1090_, lean_object* v_x_1091_, lean_object* v_h__1_1092_){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = lean_apply_2(v_h__1_1092_, v_x_1091_, lean_box(0));
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__48_splitter___boxed(lean_object* v_00_u03b1_1094_, lean_object* v_inst_1095_, lean_object* v_inst_1096_, lean_object* v_aig_1097_, lean_object* v_upper_1098_, lean_object* v_h_1099_, lean_object* v_cond_1100_, lean_object* v_ifTrue_1101_, lean_object* v_ifFalse_1102_, lean_object* v_hltf_1103_, lean_object* v_tstate_1104_, lean_object* v_motive_1105_, lean_object* v_x_1106_, lean_object* v_h__1_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__48_splitter(v_00_u03b1_1094_, v_inst_1095_, v_inst_1096_, v_aig_1097_, v_upper_1098_, v_h_1099_, v_cond_1100_, v_ifTrue_1101_, v_ifFalse_1102_, v_hltf_1103_, v_tstate_1104_, v_motive_1105_, v_x_1106_, v_h__1_1107_);
lean_dec_ref(v_tstate_1104_);
lean_dec(v_ifFalse_1102_);
lean_dec(v_ifTrue_1101_);
lean_dec(v_cond_1100_);
lean_dec(v_upper_1098_);
lean_dec_ref(v_aig_1097_);
lean_dec_ref(v_inst_1096_);
lean_dec_ref(v_inst_1095_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__45_splitter___redArg(lean_object* v_x_1109_, lean_object* v_h__1_1110_){
_start:
{
lean_object* v___x_1111_; 
v___x_1111_ = lean_apply_2(v_h__1_1110_, v_x_1109_, lean_box(0));
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__45_splitter(lean_object* v_00_u03b1_1112_, lean_object* v_inst_1113_, lean_object* v_inst_1114_, lean_object* v_aig_1115_, lean_object* v_upper_1116_, lean_object* v_h_1117_, lean_object* v_fstate_1118_, lean_object* v_motive_1119_, lean_object* v_x_1120_, lean_object* v_h__1_1121_){
_start:
{
lean_object* v___x_1122_; 
v___x_1122_ = lean_apply_2(v_h__1_1121_, v_x_1120_, lean_box(0));
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__45_splitter___boxed(lean_object* v_00_u03b1_1123_, lean_object* v_inst_1124_, lean_object* v_inst_1125_, lean_object* v_aig_1126_, lean_object* v_upper_1127_, lean_object* v_h_1128_, lean_object* v_fstate_1129_, lean_object* v_motive_1130_, lean_object* v_x_1131_, lean_object* v_h__1_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__45_splitter(v_00_u03b1_1123_, v_inst_1124_, v_inst_1125_, v_aig_1126_, v_upper_1127_, v_h_1128_, v_fstate_1129_, v_motive_1130_, v_x_1131_, v_h__1_1132_);
lean_dec_ref(v_fstate_1129_);
lean_dec(v_upper_1127_);
lean_dec_ref(v_aig_1126_);
lean_dec_ref(v_inst_1125_);
lean_dec_ref(v_inst_1124_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__56_splitter___redArg(lean_object* v_x_1134_, lean_object* v_h__1_1135_){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = lean_apply_2(v_h__1_1135_, v_x_1134_, lean_box(0));
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__56_splitter(lean_object* v_00_u03b1_1137_, lean_object* v_inst_1138_, lean_object* v_inst_1139_, lean_object* v_aig_1140_, lean_object* v_upper_1141_, lean_object* v_h_1142_, lean_object* v_state_1143_, lean_object* v_lhs_1144_, lean_object* v_rhs_1145_, lean_object* v_this_1146_, lean_object* v_motive_1147_, lean_object* v_x_1148_, lean_object* v_h__1_1149_){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = lean_apply_2(v_h__1_1149_, v_x_1148_, lean_box(0));
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__56_splitter___boxed(lean_object* v_00_u03b1_1151_, lean_object* v_inst_1152_, lean_object* v_inst_1153_, lean_object* v_aig_1154_, lean_object* v_upper_1155_, lean_object* v_h_1156_, lean_object* v_state_1157_, lean_object* v_lhs_1158_, lean_object* v_rhs_1159_, lean_object* v_this_1160_, lean_object* v_motive_1161_, lean_object* v_x_1162_, lean_object* v_h__1_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__56_splitter(v_00_u03b1_1151_, v_inst_1152_, v_inst_1153_, v_aig_1154_, v_upper_1155_, v_h_1156_, v_state_1157_, v_lhs_1158_, v_rhs_1159_, v_this_1160_, v_motive_1161_, v_x_1162_, v_h__1_1163_);
lean_dec(v_rhs_1159_);
lean_dec(v_lhs_1158_);
lean_dec_ref(v_state_1157_);
lean_dec(v_upper_1155_);
lean_dec_ref(v_aig_1154_);
lean_dec_ref(v_inst_1153_);
lean_dec_ref(v_inst_1152_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__54_splitter___redArg(lean_object* v_x_1165_, lean_object* v_h__1_1166_){
_start:
{
lean_object* v___x_1167_; 
v___x_1167_ = lean_apply_2(v_h__1_1166_, v_x_1165_, lean_box(0));
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__54_splitter(lean_object* v_00_u03b1_1168_, lean_object* v_inst_1169_, lean_object* v_inst_1170_, lean_object* v_aig_1171_, lean_object* v_upper_1172_, lean_object* v_h_1173_, lean_object* v_lhs_1174_, lean_object* v_rhs_1175_, lean_object* v_this_1176_, lean_object* v_lstate_1177_, lean_object* v_motive_1178_, lean_object* v_x_1179_, lean_object* v_h__1_1180_){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = lean_apply_2(v_h__1_1180_, v_x_1179_, lean_box(0));
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__54_splitter___boxed(lean_object* v_00_u03b1_1182_, lean_object* v_inst_1183_, lean_object* v_inst_1184_, lean_object* v_aig_1185_, lean_object* v_upper_1186_, lean_object* v_h_1187_, lean_object* v_lhs_1188_, lean_object* v_rhs_1189_, lean_object* v_this_1190_, lean_object* v_lstate_1191_, lean_object* v_motive_1192_, lean_object* v_x_1193_, lean_object* v_h__1_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__54_splitter(v_00_u03b1_1182_, v_inst_1183_, v_inst_1184_, v_aig_1185_, v_upper_1186_, v_h_1187_, v_lhs_1188_, v_rhs_1189_, v_this_1190_, v_lstate_1191_, v_motive_1192_, v_x_1193_, v_h__1_1194_);
lean_dec_ref(v_lstate_1191_);
lean_dec(v_rhs_1189_);
lean_dec(v_lhs_1188_);
lean_dec(v_upper_1186_);
lean_dec_ref(v_aig_1185_);
lean_dec_ref(v_inst_1184_);
lean_dec_ref(v_inst_1183_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__3_spec__5___redArg(lean_object* v_cache_1196_, lean_object* v_idx_1197_){
_start:
{
uint8_t v___x_1198_; lean_object* v___x_1199_; lean_object* v_out_1200_; 
v___x_1198_ = 1;
v___x_1199_ = lean_box(v___x_1198_);
v_out_1200_ = lean_array_fset(v_cache_1196_, v_idx_1197_, v___x_1199_);
return v_out_1200_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_cache_1201_, lean_object* v_idx_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__3_spec__5___redArg(v_cache_1201_, v_idx_1202_);
lean_dec(v_idx_1202_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__3___redArg(lean_object* v_inst_1204_, lean_object* v_inst_1205_, lean_object* v_aig_1206_, lean_object* v_a_1207_, lean_object* v_state_1208_, lean_object* v_idx_1209_){
_start:
{
lean_object* v_cnf_1210_; lean_object* v_cache_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1219_; 
v_cnf_1210_ = lean_ctor_get(v_state_1208_, 0);
v_cache_1211_ = lean_ctor_get(v_state_1208_, 1);
v_isSharedCheck_1219_ = !lean_is_exclusive(v_state_1208_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1213_ = v_state_1208_;
v_isShared_1214_ = v_isSharedCheck_1219_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_cache_1211_);
lean_inc(v_cnf_1210_);
lean_dec(v_state_1208_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1219_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v_val_1215_; lean_object* v___x_1217_; 
v_val_1215_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__3_spec__5___redArg(v_cache_1211_, v_idx_1209_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 1, v_val_1215_);
v___x_1217_ = v___x_1213_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_cnf_1210_);
lean_ctor_set(v_reuseFailAlloc_1218_, 1, v_val_1215_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__3___redArg___boxed(lean_object* v_inst_1220_, lean_object* v_inst_1221_, lean_object* v_aig_1222_, lean_object* v_a_1223_, lean_object* v_state_1224_, lean_object* v_idx_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__3___redArg(v_inst_1220_, v_inst_1221_, v_aig_1222_, v_a_1223_, v_state_1224_, v_idx_1225_);
lean_dec(v_idx_1225_);
lean_dec(v_a_1223_);
lean_dec_ref(v_aig_1222_);
lean_dec_ref(v_inst_1221_);
lean_dec_ref(v_inst_1220_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__4___redArg(lean_object* v_aig_1227_, lean_object* v_root_1228_){
_start:
{
lean_object* v_decls_1229_; lean_object* v___x_1230_; 
v_decls_1229_ = lean_ctor_get(v_aig_1227_, 0);
v___x_1230_ = lean_array_fget_borrowed(v_decls_1229_, v_root_1228_);
if (lean_obj_tag(v___x_1230_) == 2)
{
lean_object* v_l_1231_; lean_object* v_r_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; uint8_t v___x_1236_; 
v_l_1231_ = lean_ctor_get(v___x_1230_, 0);
v_r_1232_ = lean_ctor_get(v___x_1230_, 1);
v___x_1233_ = lean_unsigned_to_nat(1u);
v___x_1234_ = lean_nat_land(v___x_1233_, v_l_1231_);
v___x_1235_ = lean_unsigned_to_nat(0u);
v___x_1236_ = lean_nat_dec_eq(v___x_1234_, v___x_1235_);
lean_dec(v___x_1234_);
if (v___x_1236_ == 0)
{
lean_object* v___x_1237_; uint8_t v___x_1238_; 
v___x_1237_ = lean_nat_land(v___x_1233_, v_r_1232_);
v___x_1238_ = lean_nat_dec_eq(v___x_1237_, v___x_1235_);
lean_dec(v___x_1237_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1239_ = lean_nat_shiftr(v_l_1231_, v___x_1233_);
v___x_1240_ = lean_array_fget_borrowed(v_decls_1229_, v___x_1239_);
lean_dec(v___x_1239_);
if (lean_obj_tag(v___x_1240_) == 2)
{
lean_object* v_l_1241_; lean_object* v_r_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v_l_1241_ = lean_ctor_get(v___x_1240_, 0);
v_r_1242_ = lean_ctor_get(v___x_1240_, 1);
v___x_1243_ = lean_nat_shiftr(v_r_1232_, v___x_1233_);
v___x_1244_ = lean_array_fget_borrowed(v_decls_1229_, v___x_1243_);
lean_dec(v___x_1243_);
if (lean_obj_tag(v___x_1244_) == 2)
{
lean_object* v_l_1245_; lean_object* v_r_1246_; lean_object* v___x_1247_; 
v_l_1245_ = lean_ctor_get(v___x_1244_, 0);
v_r_1246_ = lean_ctor_get(v___x_1244_, 1);
lean_inc(v_r_1242_);
lean_inc(v_l_1241_);
v___x_1247_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg(v_l_1241_, v_r_1242_, v_l_1245_, v_r_1246_);
return v___x_1247_;
}
else
{
lean_object* v___x_1248_; 
v___x_1248_ = lean_box(0);
return v___x_1248_;
}
}
else
{
lean_object* v___x_1249_; 
v___x_1249_ = lean_box(0);
return v___x_1249_;
}
}
else
{
lean_object* v___x_1250_; 
v___x_1250_ = lean_box(0);
return v___x_1250_;
}
}
else
{
lean_object* v___x_1251_; 
v___x_1251_ = lean_box(0);
return v___x_1251_;
}
}
else
{
lean_object* v___x_1252_; 
v___x_1252_ = lean_box(0);
return v___x_1252_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__4___redArg___boxed(lean_object* v_aig_1253_, lean_object* v_root_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__4___redArg(v_aig_1253_, v_root_1254_);
lean_dec(v_root_1254_);
lean_dec_ref(v_aig_1253_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__6_spec__10___redArg(lean_object* v_cache_1256_, lean_object* v_cond_1257_, lean_object* v_ifTrue_1258_, lean_object* v_ifFalse_1259_, lean_object* v_idx_1260_){
_start:
{
uint8_t v___x_1261_; lean_object* v___x_1262_; lean_object* v_out_1263_; 
v___x_1261_ = 1;
v___x_1262_ = lean_box(v___x_1261_);
v_out_1263_ = lean_array_fset(v_cache_1256_, v_idx_1260_, v___x_1262_);
return v_out_1263_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__6_spec__10___redArg___boxed(lean_object* v_cache_1264_, lean_object* v_cond_1265_, lean_object* v_ifTrue_1266_, lean_object* v_ifFalse_1267_, lean_object* v_idx_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__6_spec__10___redArg(v_cache_1264_, v_cond_1265_, v_ifTrue_1266_, v_ifFalse_1267_, v_idx_1268_);
lean_dec(v_idx_1268_);
lean_dec(v_ifFalse_1267_);
lean_dec(v_ifTrue_1266_);
lean_dec(v_cond_1265_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__6___redArg(lean_object* v_inst_1270_, lean_object* v_inst_1271_, lean_object* v_aig_1272_, lean_object* v_state_1273_, lean_object* v_cond_1274_, lean_object* v_ifTrue_1275_, lean_object* v_ifFalse_1276_, lean_object* v_idx_1277_){
_start:
{
lean_object* v_cnf_1278_; lean_object* v_cache_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1317_; 
v_cnf_1278_ = lean_ctor_get(v_state_1273_, 0);
v_cache_1279_ = lean_ctor_get(v_state_1273_, 1);
v_isSharedCheck_1317_ = !lean_is_exclusive(v_state_1273_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1281_ = v_state_1273_;
v_isShared_1282_ = v_isSharedCheck_1317_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_cache_1279_);
lean_inc(v_cnf_1278_);
lean_dec(v_state_1273_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1317_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; uint8_t v___y_1288_; uint8_t v___y_1289_; uint8_t v___y_1290_; uint8_t v___y_1298_; uint8_t v___y_1299_; uint8_t v___y_1306_; lean_object* v___x_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; 
v___x_1283_ = lean_unsigned_to_nat(1u);
v___x_1284_ = lean_nat_shiftr(v_cond_1274_, v___x_1283_);
v___x_1285_ = lean_nat_shiftr(v_ifTrue_1275_, v___x_1283_);
v___x_1286_ = lean_nat_shiftr(v_ifFalse_1276_, v___x_1283_);
v___x_1312_ = lean_nat_land(v___x_1283_, v_cond_1274_);
v___x_1313_ = lean_unsigned_to_nat(0u);
v___x_1314_ = lean_nat_dec_eq(v___x_1312_, v___x_1313_);
lean_dec(v___x_1312_);
if (v___x_1314_ == 0)
{
uint8_t v___x_1315_; 
v___x_1315_ = 1;
v___y_1306_ = v___x_1315_;
goto v___jp_1305_;
}
else
{
uint8_t v___x_1316_; 
v___x_1316_ = 0;
v___y_1306_ = v___x_1316_;
goto v___jp_1305_;
}
v___jp_1287_:
{
lean_object* v_val_1291_; lean_object* v_newCnf_1292_; lean_object* v___x_1293_; lean_object* v___x_1295_; 
v_val_1291_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__6_spec__10___redArg(v_cache_1279_, v_cond_1274_, v_ifTrue_1275_, v_ifFalse_1276_, v_idx_1277_);
v_newCnf_1292_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF___redArg(v_idx_1277_, v___x_1284_, v___x_1285_, v___x_1286_, v___y_1289_, v___y_1288_, v___y_1290_);
v___x_1293_ = l_Array_append___redArg(v_cnf_1278_, v_newCnf_1292_);
lean_dec_ref(v_newCnf_1292_);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 1, v_val_1291_);
lean_ctor_set(v___x_1281_, 0, v___x_1293_);
v___x_1295_ = v___x_1281_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1293_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v_val_1291_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
v___jp_1297_:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; uint8_t v___x_1302_; 
v___x_1300_ = lean_nat_land(v___x_1283_, v_ifFalse_1276_);
v___x_1301_ = lean_unsigned_to_nat(0u);
v___x_1302_ = lean_nat_dec_eq(v___x_1300_, v___x_1301_);
lean_dec(v___x_1300_);
if (v___x_1302_ == 0)
{
uint8_t v___x_1303_; 
v___x_1303_ = 1;
v___y_1288_ = v___y_1299_;
v___y_1289_ = v___y_1298_;
v___y_1290_ = v___x_1303_;
goto v___jp_1287_;
}
else
{
uint8_t v___x_1304_; 
v___x_1304_ = 0;
v___y_1288_ = v___y_1299_;
v___y_1289_ = v___y_1298_;
v___y_1290_ = v___x_1304_;
goto v___jp_1287_;
}
}
v___jp_1305_:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; uint8_t v___x_1309_; 
v___x_1307_ = lean_nat_land(v___x_1283_, v_ifTrue_1275_);
v___x_1308_ = lean_unsigned_to_nat(0u);
v___x_1309_ = lean_nat_dec_eq(v___x_1307_, v___x_1308_);
lean_dec(v___x_1307_);
if (v___x_1309_ == 0)
{
uint8_t v___x_1310_; 
v___x_1310_ = 1;
v___y_1298_ = v___y_1306_;
v___y_1299_ = v___x_1310_;
goto v___jp_1297_;
}
else
{
uint8_t v___x_1311_; 
v___x_1311_ = 0;
v___y_1298_ = v___y_1306_;
v___y_1299_ = v___x_1311_;
goto v___jp_1297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__6___redArg___boxed(lean_object* v_inst_1318_, lean_object* v_inst_1319_, lean_object* v_aig_1320_, lean_object* v_state_1321_, lean_object* v_cond_1322_, lean_object* v_ifTrue_1323_, lean_object* v_ifFalse_1324_, lean_object* v_idx_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__6___redArg(v_inst_1318_, v_inst_1319_, v_aig_1320_, v_state_1321_, v_cond_1322_, v_ifTrue_1323_, v_ifFalse_1324_, v_idx_1325_);
lean_dec(v_ifFalse_1324_);
lean_dec(v_ifTrue_1323_);
lean_dec(v_cond_1322_);
lean_dec_ref(v_aig_1320_);
lean_dec_ref(v_inst_1319_);
lean_dec_ref(v_inst_1318_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__5_spec__8___redArg(lean_object* v_lhs_1327_, lean_object* v_rhs_1328_, lean_object* v_cache_1329_, lean_object* v_idx_1330_){
_start:
{
uint8_t v___x_1331_; lean_object* v___x_1332_; lean_object* v_out_1333_; 
v___x_1331_ = 1;
v___x_1332_ = lean_box(v___x_1331_);
v_out_1333_ = lean_array_fset(v_cache_1329_, v_idx_1330_, v___x_1332_);
return v_out_1333_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__5_spec__8___redArg___boxed(lean_object* v_lhs_1334_, lean_object* v_rhs_1335_, lean_object* v_cache_1336_, lean_object* v_idx_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__5_spec__8___redArg(v_lhs_1334_, v_rhs_1335_, v_cache_1336_, v_idx_1337_);
lean_dec(v_idx_1337_);
lean_dec(v_rhs_1335_);
lean_dec(v_lhs_1334_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__5___redArg(lean_object* v_inst_1339_, lean_object* v_inst_1340_, lean_object* v_aig_1341_, lean_object* v_lhs_1342_, lean_object* v_rhs_1343_, lean_object* v_state_1344_, lean_object* v_idx_1345_){
_start:
{
lean_object* v_cnf_1346_; lean_object* v_cache_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1375_; 
v_cnf_1346_ = lean_ctor_get(v_state_1344_, 0);
v_cache_1347_ = lean_ctor_get(v_state_1344_, 1);
v_isSharedCheck_1375_ = !lean_is_exclusive(v_state_1344_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1349_ = v_state_1344_;
v_isShared_1350_ = v_isSharedCheck_1375_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_cache_1347_);
lean_inc(v_cnf_1346_);
lean_dec(v_state_1344_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1375_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; uint8_t v___y_1355_; uint8_t v___y_1356_; uint8_t v___y_1364_; lean_object* v___x_1370_; lean_object* v___x_1371_; uint8_t v___x_1372_; 
v___x_1351_ = lean_unsigned_to_nat(1u);
v___x_1352_ = lean_nat_shiftr(v_lhs_1342_, v___x_1351_);
v___x_1353_ = lean_nat_shiftr(v_rhs_1343_, v___x_1351_);
v___x_1370_ = lean_nat_land(v___x_1351_, v_lhs_1342_);
v___x_1371_ = lean_unsigned_to_nat(0u);
v___x_1372_ = lean_nat_dec_eq(v___x_1370_, v___x_1371_);
lean_dec(v___x_1370_);
if (v___x_1372_ == 0)
{
uint8_t v___x_1373_; 
v___x_1373_ = 1;
v___y_1364_ = v___x_1373_;
goto v___jp_1363_;
}
else
{
uint8_t v___x_1374_; 
v___x_1374_ = 0;
v___y_1364_ = v___x_1374_;
goto v___jp_1363_;
}
v___jp_1354_:
{
lean_object* v_val_1357_; lean_object* v_newCnf_1358_; lean_object* v___x_1359_; lean_object* v___x_1361_; 
v_val_1357_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__5_spec__8___redArg(v_lhs_1342_, v_rhs_1343_, v_cache_1347_, v_idx_1345_);
v_newCnf_1358_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg(v_idx_1345_, v___x_1352_, v___x_1353_, v___y_1355_, v___y_1356_);
v___x_1359_ = l_Array_append___redArg(v_cnf_1346_, v_newCnf_1358_);
lean_dec_ref(v_newCnf_1358_);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 1, v_val_1357_);
lean_ctor_set(v___x_1349_, 0, v___x_1359_);
v___x_1361_ = v___x_1349_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___x_1359_);
lean_ctor_set(v_reuseFailAlloc_1362_, 1, v_val_1357_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
v___jp_1363_:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; uint8_t v___x_1367_; 
v___x_1365_ = lean_nat_land(v___x_1351_, v_rhs_1343_);
v___x_1366_ = lean_unsigned_to_nat(0u);
v___x_1367_ = lean_nat_dec_eq(v___x_1365_, v___x_1366_);
lean_dec(v___x_1365_);
if (v___x_1367_ == 0)
{
uint8_t v___x_1368_; 
v___x_1368_ = 1;
v___y_1355_ = v___y_1364_;
v___y_1356_ = v___x_1368_;
goto v___jp_1354_;
}
else
{
uint8_t v___x_1369_; 
v___x_1369_ = 0;
v___y_1355_ = v___y_1364_;
v___y_1356_ = v___x_1369_;
goto v___jp_1354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__5___redArg___boxed(lean_object* v_inst_1376_, lean_object* v_inst_1377_, lean_object* v_aig_1378_, lean_object* v_lhs_1379_, lean_object* v_rhs_1380_, lean_object* v_state_1381_, lean_object* v_idx_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__5___redArg(v_inst_1376_, v_inst_1377_, v_aig_1378_, v_lhs_1379_, v_rhs_1380_, v_state_1381_, v_idx_1382_);
lean_dec(v_rhs_1380_);
lean_dec(v_lhs_1379_);
lean_dec_ref(v_aig_1378_);
lean_dec_ref(v_inst_1377_);
lean_dec_ref(v_inst_1376_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__2_spec__3___redArg(lean_object* v_cache_1384_, lean_object* v_idx_1385_){
_start:
{
uint8_t v___x_1386_; lean_object* v___x_1387_; lean_object* v_out_1388_; 
v___x_1386_ = 1;
v___x_1387_ = lean_box(v___x_1386_);
v_out_1388_ = lean_array_fset(v_cache_1384_, v_idx_1385_, v___x_1387_);
return v_out_1388_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_cache_1389_, lean_object* v_idx_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__2_spec__3___redArg(v_cache_1389_, v_idx_1390_);
lean_dec(v_idx_1390_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__2___redArg(lean_object* v_inst_1392_, lean_object* v_inst_1393_, lean_object* v_aig_1394_, lean_object* v_state_1395_, lean_object* v_idx_1396_){
_start:
{
lean_object* v_cnf_1397_; lean_object* v_cache_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1408_; 
v_cnf_1397_ = lean_ctor_get(v_state_1395_, 0);
v_cache_1398_ = lean_ctor_get(v_state_1395_, 1);
v_isSharedCheck_1408_ = !lean_is_exclusive(v_state_1395_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1400_ = v_state_1395_;
v_isShared_1401_ = v_isSharedCheck_1408_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_cache_1398_);
lean_inc(v_cnf_1397_);
lean_dec(v_state_1395_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1408_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v_val_1402_; lean_object* v_newCnf_1403_; lean_object* v___x_1404_; lean_object* v___x_1406_; 
v_val_1402_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__2_spec__3___redArg(v_cache_1398_, v_idx_1396_);
v_newCnf_1403_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg(v_idx_1396_);
v___x_1404_ = l_Array_append___redArg(v_cnf_1397_, v_newCnf_1403_);
lean_dec_ref(v_newCnf_1403_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 1, v_val_1402_);
lean_ctor_set(v___x_1400_, 0, v___x_1404_);
v___x_1406_ = v___x_1400_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v___x_1404_);
lean_ctor_set(v_reuseFailAlloc_1407_, 1, v_val_1402_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__2___redArg___boxed(lean_object* v_inst_1409_, lean_object* v_inst_1410_, lean_object* v_aig_1411_, lean_object* v_state_1412_, lean_object* v_idx_1413_){
_start:
{
lean_object* v_res_1414_; 
v_res_1414_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__2___redArg(v_inst_1409_, v_inst_1410_, v_aig_1411_, v_state_1412_, v_idx_1413_);
lean_dec_ref(v_aig_1411_);
lean_dec_ref(v_inst_1410_);
lean_dec_ref(v_inst_1409_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1___redArg(lean_object* v_inst_1415_, lean_object* v_inst_1416_, lean_object* v_aig_1417_, lean_object* v_upper_1418_, lean_object* v_state_1419_){
_start:
{
lean_object* v_cache_1420_; lean_object* v___x_1421_; uint8_t v___x_1422_; 
v_cache_1420_ = lean_ctor_get(v_state_1419_, 1);
v___x_1421_ = lean_array_fget_borrowed(v_cache_1420_, v_upper_1418_);
v___x_1422_ = lean_unbox(v___x_1421_);
if (v___x_1422_ == 0)
{
lean_object* v_decls_1423_; lean_object* v_decl_1424_; 
v_decls_1423_ = lean_ctor_get(v_aig_1417_, 0);
v_decl_1424_ = lean_array_fget_borrowed(v_decls_1423_, v_upper_1418_);
switch(lean_obj_tag(v_decl_1424_))
{
case 0:
{
lean_object* v___x_1425_; 
v___x_1425_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__2___redArg(v_inst_1415_, v_inst_1416_, v_aig_1417_, v_state_1419_, v_upper_1418_);
return v___x_1425_;
}
case 1:
{
lean_object* v_idx_1426_; lean_object* v___x_1427_; 
v_idx_1426_ = lean_ctor_get(v_decl_1424_, 0);
v___x_1427_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__3___redArg(v_inst_1415_, v_inst_1416_, v_aig_1417_, v_idx_1426_, v_state_1419_, v_upper_1418_);
lean_dec(v_upper_1418_);
return v___x_1427_;
}
default: 
{
lean_object* v_l_1428_; lean_object* v_r_1429_; lean_object* v___x_1430_; 
v_l_1428_ = lean_ctor_get(v_decl_1424_, 0);
v_r_1429_ = lean_ctor_get(v_decl_1424_, 1);
v___x_1430_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__4___redArg(v_aig_1417_, v_upper_1418_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v_val_1433_; lean_object* v___x_1434_; lean_object* v_val_1435_; lean_object* v___x_1436_; 
v___x_1431_ = lean_unsigned_to_nat(1u);
v___x_1432_ = lean_nat_shiftr(v_l_1428_, v___x_1431_);
v_val_1433_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1___redArg(v_inst_1415_, v_inst_1416_, v_aig_1417_, v___x_1432_, v_state_1419_);
v___x_1434_ = lean_nat_shiftr(v_r_1429_, v___x_1431_);
v_val_1435_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1___redArg(v_inst_1415_, v_inst_1416_, v_aig_1417_, v___x_1434_, v_val_1433_);
v___x_1436_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__5___redArg(v_inst_1415_, v_inst_1416_, v_aig_1417_, v_l_1428_, v_r_1429_, v_val_1435_, v_upper_1418_);
return v___x_1436_;
}
else
{
lean_object* v_val_1437_; lean_object* v_snd_1438_; lean_object* v_fst_1439_; lean_object* v_fst_1440_; lean_object* v_snd_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v_val_1444_; lean_object* v___x_1445_; lean_object* v_val_1446_; lean_object* v___x_1447_; lean_object* v_val_1448_; lean_object* v___x_1449_; 
v_val_1437_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_val_1437_);
lean_dec_ref_known(v___x_1430_, 1);
v_snd_1438_ = lean_ctor_get(v_val_1437_, 1);
lean_inc(v_snd_1438_);
v_fst_1439_ = lean_ctor_get(v_val_1437_, 0);
lean_inc(v_fst_1439_);
lean_dec(v_val_1437_);
v_fst_1440_ = lean_ctor_get(v_snd_1438_, 0);
lean_inc(v_fst_1440_);
v_snd_1441_ = lean_ctor_get(v_snd_1438_, 1);
lean_inc(v_snd_1441_);
lean_dec(v_snd_1438_);
v___x_1442_ = lean_unsigned_to_nat(1u);
v___x_1443_ = lean_nat_shiftr(v_fst_1439_, v___x_1442_);
v_val_1444_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1___redArg(v_inst_1415_, v_inst_1416_, v_aig_1417_, v___x_1443_, v_state_1419_);
v___x_1445_ = lean_nat_shiftr(v_fst_1440_, v___x_1442_);
v_val_1446_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1___redArg(v_inst_1415_, v_inst_1416_, v_aig_1417_, v___x_1445_, v_val_1444_);
v___x_1447_ = lean_nat_shiftr(v_snd_1441_, v___x_1442_);
v_val_1448_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1___redArg(v_inst_1415_, v_inst_1416_, v_aig_1417_, v___x_1447_, v_val_1446_);
v___x_1449_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__6___redArg(v_inst_1415_, v_inst_1416_, v_aig_1417_, v_val_1448_, v_fst_1439_, v_fst_1440_, v_snd_1441_, v_upper_1418_);
lean_dec(v_snd_1441_);
lean_dec(v_fst_1440_);
lean_dec(v_fst_1439_);
return v___x_1449_;
}
}
}
}
else
{
lean_dec(v_upper_1418_);
return v_state_1419_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1___redArg___boxed(lean_object* v_inst_1450_, lean_object* v_inst_1451_, lean_object* v_aig_1452_, lean_object* v_upper_1453_, lean_object* v_state_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1___redArg(v_inst_1450_, v_inst_1451_, v_aig_1452_, v_upper_1453_, v_state_1454_);
lean_dec_ref(v_aig_1452_);
lean_dec_ref(v_inst_1451_);
lean_dec_ref(v_inst_1450_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty___at___00Std_Sat_AIG_toCNF_spec__0_spec__0___redArg(lean_object* v_aig_1456_){
_start:
{
lean_object* v_decls_1457_; lean_object* v___x_1458_; uint8_t v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v_decls_1457_ = lean_ctor_get(v_aig_1456_, 0);
v___x_1458_ = lean_array_get_size(v_decls_1457_);
v___x_1459_ = 0;
v___x_1460_ = lean_box(v___x_1459_);
v___x_1461_ = lean_mk_array(v___x_1458_, v___x_1460_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty___at___00Std_Sat_AIG_toCNF_spec__0_spec__0___redArg___boxed(lean_object* v_aig_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty___at___00Std_Sat_AIG_toCNF_spec__0_spec__0___redArg(v_aig_1462_);
lean_dec_ref(v_aig_1462_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty___at___00Std_Sat_AIG_toCNF_spec__0___redArg(lean_object* v_inst_1464_, lean_object* v_inst_1465_, lean_object* v_aig_1466_){
_start:
{
lean_object* v_decls_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1479_; 
v_decls_1467_ = lean_ctor_get(v_aig_1466_, 0);
v___x_1468_ = lean_array_get_size(v_decls_1467_);
v___x_1469_ = lean_unsigned_to_nat(2u);
v___x_1470_ = lean_nat_mul(v___x_1468_, v___x_1469_);
v___x_1471_ = lean_mk_empty_array_with_capacity(v___x_1470_);
lean_dec(v___x_1470_);
v___x_1472_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty___at___00Std_Sat_AIG_toCNF_spec__0_spec__0___redArg(v_aig_1466_);
v_isSharedCheck_1479_ = !lean_is_exclusive(v_aig_1466_);
if (v_isSharedCheck_1479_ == 0)
{
lean_object* v_unused_1480_; lean_object* v_unused_1481_; 
v_unused_1480_ = lean_ctor_get(v_aig_1466_, 1);
lean_dec(v_unused_1480_);
v_unused_1481_ = lean_ctor_get(v_aig_1466_, 0);
lean_dec(v_unused_1481_);
v___x_1474_ = v_aig_1466_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_dec(v_aig_1466_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1477_; 
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 1, v___x_1472_);
lean_ctor_set(v___x_1474_, 0, v___x_1471_);
v___x_1477_ = v___x_1474_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1471_);
lean_ctor_set(v_reuseFailAlloc_1478_, 1, v___x_1472_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty___at___00Std_Sat_AIG_toCNF_spec__0___redArg___boxed(lean_object* v_inst_1482_, lean_object* v_inst_1483_, lean_object* v_aig_1484_){
_start:
{
lean_object* v_res_1485_; 
v_res_1485_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty___at___00Std_Sat_AIG_toCNF_spec__0___redArg(v_inst_1482_, v_inst_1483_, v_aig_1484_);
lean_dec_ref(v_inst_1483_);
lean_dec_ref(v_inst_1482_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF___redArg(lean_object* v_inst_1488_, lean_object* v_inst_1489_, lean_object* v_entry_1490_){
_start:
{
lean_object* v_ref_1491_; lean_object* v_aig_1492_; lean_object* v_gate_1493_; uint8_t v_invert_1494_; lean_object* v___x_1495_; lean_object* v_val_1496_; lean_object* v_cnf_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1515_; 
v_ref_1491_ = lean_ctor_get(v_entry_1490_, 1);
lean_inc_ref(v_ref_1491_);
v_aig_1492_ = lean_ctor_get(v_entry_1490_, 0);
lean_inc_ref_n(v_aig_1492_, 2);
lean_dec_ref(v_entry_1490_);
v_gate_1493_ = lean_ctor_get(v_ref_1491_, 0);
lean_inc_n(v_gate_1493_, 2);
v_invert_1494_ = lean_ctor_get_uint8(v_ref_1491_, sizeof(void*)*1);
lean_dec_ref(v_ref_1491_);
v___x_1495_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty___at___00Std_Sat_AIG_toCNF_spec__0___redArg(v_inst_1488_, v_inst_1489_, v_aig_1492_);
v_val_1496_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1___redArg(v_inst_1488_, v_inst_1489_, v_aig_1492_, v_gate_1493_, v___x_1495_);
lean_dec_ref(v_aig_1492_);
v_cnf_1497_ = lean_ctor_get(v_val_1496_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v_val_1496_);
if (v_isSharedCheck_1515_ == 0)
{
lean_object* v_unused_1516_; 
v_unused_1516_ = lean_ctor_get(v_val_1496_, 1);
lean_dec(v_unused_1516_);
v___x_1499_ = v_val_1496_;
v_isShared_1500_ = v_isSharedCheck_1515_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_cnf_1497_);
lean_dec(v_val_1496_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1515_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___y_1504_; uint8_t v___y_1505_; 
v___x_1501_ = ((lean_object*)(l_Std_Sat_AIG_toCNF___redArg___closed__0));
v___x_1502_ = l_ByteArray_empty;
if (v_invert_1494_ == 0)
{
lean_object* v___x_1511_; uint8_t v___x_1512_; 
v___x_1511_ = lean_array_push(v___x_1501_, v_gate_1493_);
v___x_1512_ = 1;
v___y_1504_ = v___x_1511_;
v___y_1505_ = v___x_1512_;
goto v___jp_1503_;
}
else
{
lean_object* v___x_1513_; uint8_t v___x_1514_; 
v___x_1513_ = lean_array_push(v___x_1501_, v_gate_1493_);
v___x_1514_ = 0;
v___y_1504_ = v___x_1513_;
v___y_1505_ = v___x_1514_;
goto v___jp_1503_;
}
v___jp_1503_:
{
lean_object* v___x_1506_; lean_object* v___x_1508_; 
v___x_1506_ = lean_byte_array_push(v___x_1502_, v___y_1505_);
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 1, v___x_1506_);
lean_ctor_set(v___x_1499_, 0, v___y_1504_);
v___x_1508_ = v___x_1499_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___y_1504_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v___x_1506_);
v___x_1508_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
lean_object* v___x_1509_; 
v___x_1509_ = lean_array_push(v_cnf_1497_, v___x_1508_);
return v___x_1509_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF___redArg___boxed(lean_object* v_inst_1517_, lean_object* v_inst_1518_, lean_object* v_entry_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l_Std_Sat_AIG_toCNF___redArg(v_inst_1517_, v_inst_1518_, v_entry_1519_);
lean_dec_ref(v_inst_1518_);
lean_dec_ref(v_inst_1517_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF(lean_object* v_00_u03b1_1521_, lean_object* v_inst_1522_, lean_object* v_inst_1523_, lean_object* v_entry_1524_){
_start:
{
lean_object* v___x_1525_; 
v___x_1525_ = l_Std_Sat_AIG_toCNF___redArg(v_inst_1522_, v_inst_1523_, v_entry_1524_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF___boxed(lean_object* v_00_u03b1_1526_, lean_object* v_inst_1527_, lean_object* v_inst_1528_, lean_object* v_entry_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_Std_Sat_AIG_toCNF(v_00_u03b1_1526_, v_inst_1527_, v_inst_1528_, v_entry_1529_);
lean_dec_ref(v_inst_1528_);
lean_dec_ref(v_inst_1527_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty___at___00Std_Sat_AIG_toCNF_spec__0_spec__0(lean_object* v_00_u03b1_1531_, lean_object* v_inst_1532_, lean_object* v_inst_1533_, lean_object* v_aig_1534_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty___at___00Std_Sat_AIG_toCNF_spec__0_spec__0___redArg(v_aig_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty___at___00Std_Sat_AIG_toCNF_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1536_, lean_object* v_inst_1537_, lean_object* v_inst_1538_, lean_object* v_aig_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty___at___00Std_Sat_AIG_toCNF_spec__0_spec__0(v_00_u03b1_1536_, v_inst_1537_, v_inst_1538_, v_aig_1539_);
lean_dec_ref(v_aig_1539_);
lean_dec_ref(v_inst_1538_);
lean_dec_ref(v_inst_1537_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty___at___00Std_Sat_AIG_toCNF_spec__0(lean_object* v_00_u03b1_1541_, lean_object* v_inst_1542_, lean_object* v_inst_1543_, lean_object* v_aig_1544_){
_start:
{
lean_object* v___x_1545_; 
v___x_1545_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty___at___00Std_Sat_AIG_toCNF_spec__0___redArg(v_inst_1542_, v_inst_1543_, v_aig_1544_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty___at___00Std_Sat_AIG_toCNF_spec__0___boxed(lean_object* v_00_u03b1_1546_, lean_object* v_inst_1547_, lean_object* v_inst_1548_, lean_object* v_aig_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty___at___00Std_Sat_AIG_toCNF_spec__0(v_00_u03b1_1546_, v_inst_1547_, v_inst_1548_, v_aig_1549_);
lean_dec_ref(v_inst_1548_);
lean_dec_ref(v_inst_1547_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__4(lean_object* v_00_u03b1_1551_, lean_object* v_inst_1552_, lean_object* v_inst_1553_, lean_object* v_aig_1554_, lean_object* v_root_1555_, lean_object* v_h_1556_){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__4___redArg(v_aig_1554_, v_root_1555_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1558_, lean_object* v_inst_1559_, lean_object* v_inst_1560_, lean_object* v_aig_1561_, lean_object* v_root_1562_, lean_object* v_h_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__4(v_00_u03b1_1558_, v_inst_1559_, v_inst_1560_, v_aig_1561_, v_root_1562_, v_h_1563_);
lean_dec(v_root_1562_);
lean_dec_ref(v_aig_1561_);
lean_dec_ref(v_inst_1560_);
lean_dec_ref(v_inst_1559_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1(lean_object* v_00_u03b1_1565_, lean_object* v_inst_1566_, lean_object* v_inst_1567_, lean_object* v_aig_1568_, lean_object* v_upper_1569_, lean_object* v_h_1570_, lean_object* v_state_1571_){
_start:
{
lean_object* v___x_1572_; 
v___x_1572_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1___redArg(v_inst_1566_, v_inst_1567_, v_aig_1568_, v_upper_1569_, v_state_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1___boxed(lean_object* v_00_u03b1_1573_, lean_object* v_inst_1574_, lean_object* v_inst_1575_, lean_object* v_aig_1576_, lean_object* v_upper_1577_, lean_object* v_h_1578_, lean_object* v_state_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1(v_00_u03b1_1573_, v_inst_1574_, v_inst_1575_, v_aig_1576_, v_upper_1577_, v_h_1578_, v_state_1579_);
lean_dec_ref(v_aig_1576_);
lean_dec_ref(v_inst_1575_);
lean_dec_ref(v_inst_1574_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_1581_, lean_object* v_inst_1582_, lean_object* v_inst_1583_, lean_object* v_aig_1584_, lean_object* v_cnf_1585_, lean_object* v_cache_1586_, lean_object* v_idx_1587_, lean_object* v_h_1588_, lean_object* v_htip_1589_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__2_spec__3___redArg(v_cache_1586_, v_idx_1587_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1591_, lean_object* v_inst_1592_, lean_object* v_inst_1593_, lean_object* v_aig_1594_, lean_object* v_cnf_1595_, lean_object* v_cache_1596_, lean_object* v_idx_1597_, lean_object* v_h_1598_, lean_object* v_htip_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__2_spec__3(v_00_u03b1_1591_, v_inst_1592_, v_inst_1593_, v_aig_1594_, v_cnf_1595_, v_cache_1596_, v_idx_1597_, v_h_1598_, v_htip_1599_);
lean_dec(v_idx_1597_);
lean_dec_ref(v_cnf_1595_);
lean_dec_ref(v_aig_1594_);
lean_dec_ref(v_inst_1593_);
lean_dec_ref(v_inst_1592_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__2(lean_object* v_00_u03b1_1601_, lean_object* v_inst_1602_, lean_object* v_inst_1603_, lean_object* v_aig_1604_, lean_object* v_state_1605_, lean_object* v_idx_1606_, lean_object* v_h_1607_, lean_object* v_htip_1608_){
_start:
{
lean_object* v___x_1609_; 
v___x_1609_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__2___redArg(v_inst_1602_, v_inst_1603_, v_aig_1604_, v_state_1605_, v_idx_1606_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1610_, lean_object* v_inst_1611_, lean_object* v_inst_1612_, lean_object* v_aig_1613_, lean_object* v_state_1614_, lean_object* v_idx_1615_, lean_object* v_h_1616_, lean_object* v_htip_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__2(v_00_u03b1_1610_, v_inst_1611_, v_inst_1612_, v_aig_1613_, v_state_1614_, v_idx_1615_, v_h_1616_, v_htip_1617_);
lean_dec_ref(v_aig_1613_);
lean_dec_ref(v_inst_1612_);
lean_dec_ref(v_inst_1611_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_1619_, lean_object* v_inst_1620_, lean_object* v_inst_1621_, lean_object* v_aig_1622_, lean_object* v_cnf_1623_, lean_object* v_a_1624_, lean_object* v_cache_1625_, lean_object* v_idx_1626_, lean_object* v_h_1627_, lean_object* v_htip_1628_){
_start:
{
lean_object* v___x_1629_; 
v___x_1629_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__3_spec__5___redArg(v_cache_1625_, v_idx_1626_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1630_, lean_object* v_inst_1631_, lean_object* v_inst_1632_, lean_object* v_aig_1633_, lean_object* v_cnf_1634_, lean_object* v_a_1635_, lean_object* v_cache_1636_, lean_object* v_idx_1637_, lean_object* v_h_1638_, lean_object* v_htip_1639_){
_start:
{
lean_object* v_res_1640_; 
v_res_1640_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__3_spec__5(v_00_u03b1_1630_, v_inst_1631_, v_inst_1632_, v_aig_1633_, v_cnf_1634_, v_a_1635_, v_cache_1636_, v_idx_1637_, v_h_1638_, v_htip_1639_);
lean_dec(v_idx_1637_);
lean_dec(v_a_1635_);
lean_dec_ref(v_cnf_1634_);
lean_dec_ref(v_aig_1633_);
lean_dec_ref(v_inst_1632_);
lean_dec_ref(v_inst_1631_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__3(lean_object* v_00_u03b1_1641_, lean_object* v_inst_1642_, lean_object* v_inst_1643_, lean_object* v_aig_1644_, lean_object* v_a_1645_, lean_object* v_state_1646_, lean_object* v_idx_1647_, lean_object* v_h_1648_, lean_object* v_htip_1649_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__3___redArg(v_inst_1642_, v_inst_1643_, v_aig_1644_, v_a_1645_, v_state_1646_, v_idx_1647_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__3___boxed(lean_object* v_00_u03b1_1651_, lean_object* v_inst_1652_, lean_object* v_inst_1653_, lean_object* v_aig_1654_, lean_object* v_a_1655_, lean_object* v_state_1656_, lean_object* v_idx_1657_, lean_object* v_h_1658_, lean_object* v_htip_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__3(v_00_u03b1_1651_, v_inst_1652_, v_inst_1653_, v_aig_1654_, v_a_1655_, v_state_1656_, v_idx_1657_, v_h_1658_, v_htip_1659_);
lean_dec(v_idx_1657_);
lean_dec(v_a_1655_);
lean_dec_ref(v_aig_1654_);
lean_dec_ref(v_inst_1653_);
lean_dec_ref(v_inst_1652_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__5_spec__8(lean_object* v_00_u03b1_1661_, lean_object* v_inst_1662_, lean_object* v_inst_1663_, lean_object* v_aig_1664_, lean_object* v_cnf_1665_, lean_object* v_lhs_1666_, lean_object* v_rhs_1667_, lean_object* v_cache_1668_, lean_object* v_hlb_1669_, lean_object* v_hrb_1670_, lean_object* v_idx_1671_, lean_object* v_h_1672_, lean_object* v_htip_1673_, lean_object* v_hl_1674_, lean_object* v_hr_1675_){
_start:
{
lean_object* v___x_1676_; 
v___x_1676_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__5_spec__8___redArg(v_lhs_1666_, v_rhs_1667_, v_cache_1668_, v_idx_1671_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1677_, lean_object* v_inst_1678_, lean_object* v_inst_1679_, lean_object* v_aig_1680_, lean_object* v_cnf_1681_, lean_object* v_lhs_1682_, lean_object* v_rhs_1683_, lean_object* v_cache_1684_, lean_object* v_hlb_1685_, lean_object* v_hrb_1686_, lean_object* v_idx_1687_, lean_object* v_h_1688_, lean_object* v_htip_1689_, lean_object* v_hl_1690_, lean_object* v_hr_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__5_spec__8(v_00_u03b1_1677_, v_inst_1678_, v_inst_1679_, v_aig_1680_, v_cnf_1681_, v_lhs_1682_, v_rhs_1683_, v_cache_1684_, v_hlb_1685_, v_hrb_1686_, v_idx_1687_, v_h_1688_, v_htip_1689_, v_hl_1690_, v_hr_1691_);
lean_dec(v_idx_1687_);
lean_dec(v_rhs_1683_);
lean_dec(v_lhs_1682_);
lean_dec_ref(v_cnf_1681_);
lean_dec_ref(v_aig_1680_);
lean_dec_ref(v_inst_1679_);
lean_dec_ref(v_inst_1678_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__5(lean_object* v_00_u03b1_1693_, lean_object* v_inst_1694_, lean_object* v_inst_1695_, lean_object* v_aig_1696_, lean_object* v_lhs_1697_, lean_object* v_rhs_1698_, lean_object* v_state_1699_, lean_object* v_hlb_1700_, lean_object* v_hrb_1701_, lean_object* v_idx_1702_, lean_object* v_h_1703_, lean_object* v_htip_1704_, lean_object* v_hl_1705_, lean_object* v_hr_1706_){
_start:
{
lean_object* v___x_1707_; 
v___x_1707_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__5___redArg(v_inst_1694_, v_inst_1695_, v_aig_1696_, v_lhs_1697_, v_rhs_1698_, v_state_1699_, v_idx_1702_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__5___boxed(lean_object* v_00_u03b1_1708_, lean_object* v_inst_1709_, lean_object* v_inst_1710_, lean_object* v_aig_1711_, lean_object* v_lhs_1712_, lean_object* v_rhs_1713_, lean_object* v_state_1714_, lean_object* v_hlb_1715_, lean_object* v_hrb_1716_, lean_object* v_idx_1717_, lean_object* v_h_1718_, lean_object* v_htip_1719_, lean_object* v_hl_1720_, lean_object* v_hr_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__5(v_00_u03b1_1708_, v_inst_1709_, v_inst_1710_, v_aig_1711_, v_lhs_1712_, v_rhs_1713_, v_state_1714_, v_hlb_1715_, v_hrb_1716_, v_idx_1717_, v_h_1718_, v_htip_1719_, v_hl_1720_, v_hr_1721_);
lean_dec(v_rhs_1713_);
lean_dec(v_lhs_1712_);
lean_dec_ref(v_aig_1711_);
lean_dec_ref(v_inst_1710_);
lean_dec_ref(v_inst_1709_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__6_spec__10(lean_object* v_00_u03b1_1723_, lean_object* v_inst_1724_, lean_object* v_inst_1725_, lean_object* v_aig_1726_, lean_object* v_cnf_1727_, lean_object* v_cache_1728_, lean_object* v_cond_1729_, lean_object* v_ifTrue_1730_, lean_object* v_ifFalse_1731_, lean_object* v_idx_1732_, lean_object* v_hcb_1733_, lean_object* v_htb_1734_, lean_object* v_hfb_1735_, lean_object* v_h_1736_, lean_object* v_hltc_1737_, lean_object* v_hltt_1738_, lean_object* v_hltf_1739_, lean_object* v_hc_1740_, lean_object* v_ht_1741_, lean_object* v_hf_1742_, lean_object* v_hdenote_1743_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__6_spec__10___redArg(v_cache_1728_, v_cond_1729_, v_ifTrue_1730_, v_ifFalse_1731_, v_idx_1732_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__6_spec__10___boxed(lean_object** _args){
lean_object* v_00_u03b1_1745_ = _args[0];
lean_object* v_inst_1746_ = _args[1];
lean_object* v_inst_1747_ = _args[2];
lean_object* v_aig_1748_ = _args[3];
lean_object* v_cnf_1749_ = _args[4];
lean_object* v_cache_1750_ = _args[5];
lean_object* v_cond_1751_ = _args[6];
lean_object* v_ifTrue_1752_ = _args[7];
lean_object* v_ifFalse_1753_ = _args[8];
lean_object* v_idx_1754_ = _args[9];
lean_object* v_hcb_1755_ = _args[10];
lean_object* v_htb_1756_ = _args[11];
lean_object* v_hfb_1757_ = _args[12];
lean_object* v_h_1758_ = _args[13];
lean_object* v_hltc_1759_ = _args[14];
lean_object* v_hltt_1760_ = _args[15];
lean_object* v_hltf_1761_ = _args[16];
lean_object* v_hc_1762_ = _args[17];
lean_object* v_ht_1763_ = _args[18];
lean_object* v_hf_1764_ = _args[19];
lean_object* v_hdenote_1765_ = _args[20];
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__6_spec__10(v_00_u03b1_1745_, v_inst_1746_, v_inst_1747_, v_aig_1748_, v_cnf_1749_, v_cache_1750_, v_cond_1751_, v_ifTrue_1752_, v_ifFalse_1753_, v_idx_1754_, v_hcb_1755_, v_htb_1756_, v_hfb_1757_, v_h_1758_, v_hltc_1759_, v_hltt_1760_, v_hltf_1761_, v_hc_1762_, v_ht_1763_, v_hf_1764_, v_hdenote_1765_);
lean_dec(v_idx_1754_);
lean_dec(v_ifFalse_1753_);
lean_dec(v_ifTrue_1752_);
lean_dec(v_cond_1751_);
lean_dec_ref(v_cnf_1749_);
lean_dec_ref(v_aig_1748_);
lean_dec_ref(v_inst_1747_);
lean_dec_ref(v_inst_1746_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__6(lean_object* v_00_u03b1_1767_, lean_object* v_inst_1768_, lean_object* v_inst_1769_, lean_object* v_aig_1770_, lean_object* v_state_1771_, lean_object* v_cond_1772_, lean_object* v_ifTrue_1773_, lean_object* v_ifFalse_1774_, lean_object* v_idx_1775_, lean_object* v_hcb_1776_, lean_object* v_htb_1777_, lean_object* v_hfb_1778_, lean_object* v_h_1779_, lean_object* v_hltc_1780_, lean_object* v_hltt_1781_, lean_object* v_hltf_1782_, lean_object* v_hc_1783_, lean_object* v_ht_1784_, lean_object* v_hf_1785_, lean_object* v_hdenote_1786_){
_start:
{
lean_object* v___x_1787_; 
v___x_1787_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__6___redArg(v_inst_1768_, v_inst_1769_, v_aig_1770_, v_state_1771_, v_cond_1772_, v_ifTrue_1773_, v_ifFalse_1774_, v_idx_1775_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__6___boxed(lean_object** _args){
lean_object* v_00_u03b1_1788_ = _args[0];
lean_object* v_inst_1789_ = _args[1];
lean_object* v_inst_1790_ = _args[2];
lean_object* v_aig_1791_ = _args[3];
lean_object* v_state_1792_ = _args[4];
lean_object* v_cond_1793_ = _args[5];
lean_object* v_ifTrue_1794_ = _args[6];
lean_object* v_ifFalse_1795_ = _args[7];
lean_object* v_idx_1796_ = _args[8];
lean_object* v_hcb_1797_ = _args[9];
lean_object* v_htb_1798_ = _args[10];
lean_object* v_hfb_1799_ = _args[11];
lean_object* v_h_1800_ = _args[12];
lean_object* v_hltc_1801_ = _args[13];
lean_object* v_hltt_1802_ = _args[14];
lean_object* v_hltf_1803_ = _args[15];
lean_object* v_hc_1804_ = _args[16];
lean_object* v_ht_1805_ = _args[17];
lean_object* v_hf_1806_ = _args[18];
lean_object* v_hdenote_1807_ = _args[19];
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___at___00Std_Sat_AIG_toCNF_spec__1_spec__6(v_00_u03b1_1788_, v_inst_1789_, v_inst_1790_, v_aig_1791_, v_state_1792_, v_cond_1793_, v_ifTrue_1794_, v_ifFalse_1795_, v_idx_1796_, v_hcb_1797_, v_htb_1798_, v_hfb_1799_, v_h_1800_, v_hltc_1801_, v_hltt_1802_, v_hltf_1803_, v_hc_1804_, v_ht_1805_, v_hf_1806_, v_hdenote_1807_);
lean_dec(v_ifFalse_1795_);
lean_dec(v_ifTrue_1794_);
lean_dec(v_cond_1793_);
lean_dec_ref(v_aig_1791_);
lean_dec_ref(v_inst_1790_);
lean_dec_ref(v_inst_1789_);
return v_res_1808_;
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
