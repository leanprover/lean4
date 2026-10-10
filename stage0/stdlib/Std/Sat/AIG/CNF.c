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
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
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
static const lean_array_object l_Std_Sat_AIG_toCNF_State_empty___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Sat_AIG_toCNF_State_empty___redArg___closed__0 = (const lean_object*)&l_Std_Sat_AIG_toCNF_State_empty___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_cast___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_cast___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_cast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_cast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go_match__103_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go_match__103_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go_match__81_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go_match__81_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__52_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__52_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__52_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__50_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__50_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__50_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__48_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__48_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__48_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__45_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__45_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__45_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__56_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__56_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__56_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__54_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__54_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__54_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4_spec__8___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4___boxed(lean_object**);
static const lean_array_object l_Std_Sat_AIG_toCNF___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Sat_AIG_toCNF___redArg___closed__0 = (const lean_object*)&l_Std_Sat_AIG_toCNF___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg(lean_object* v_output_18_, lean_object* v_lhs_19_, lean_object* v_rhs_20_, uint8_t v_linv_21_, uint8_t v_rinv_22_){
_start:
{
lean_object* v___y_24_; lean_object* v___y_25_; lean_object* v___y_26_; uint8_t v___y_27_; lean_object* v___x_31_; lean_object* v___x_32_; uint8_t v___x_33_; lean_object* v___y_35_; lean_object* v___y_36_; lean_object* v___y_37_; uint8_t v___y_38_; uint8_t v___y_39_; lean_object* v___x_42_; lean_object* v___y_44_; lean_object* v___y_45_; lean_object* v___y_46_; uint8_t v___y_47_; lean_object* v___y_54_; uint8_t v___y_55_; 
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
lean_inc_ref(v___y_37_);
v___x_40_ = lean_byte_array_push(v___y_37_, v___y_39_);
v___x_41_ = lean_array_push(v___y_36_, v_rhs_20_);
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
v___y_27_ = v___y_38_;
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
v___x_50_ = lean_array_push(v___y_46_, v___x_49_);
v___x_51_ = 1;
v___x_52_ = lean_obj_once(&l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg___closed__0, &l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg___closed__0_once, _init_l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg___closed__0);
if (v_linv_21_ == 0)
{
v___y_35_ = v___x_50_;
v___y_36_ = v___y_44_;
v___y_37_ = v___x_52_;
v___y_38_ = v___x_51_;
v___y_39_ = v___x_33_;
goto v___jp_34_;
}
else
{
v___y_35_ = v___x_50_;
v___y_36_ = v___y_44_;
v___y_37_ = v___x_52_;
v___y_38_ = v___x_51_;
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
v___y_44_ = v___y_54_;
v___y_45_ = v___x_59_;
v___y_46_ = v___x_58_;
v___y_47_ = v___x_60_;
goto v___jp_43_;
}
else
{
lean_object* v___x_61_; 
lean_inc(v_rhs_20_);
v___x_61_ = lean_array_push(v___x_32_, v_rhs_20_);
v___y_44_ = v___y_54_;
v___y_45_ = v___x_61_;
v___y_46_ = v___x_58_;
v___y_47_ = v___x_33_;
goto v___jp_43_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_output_18_ = stack[0].m_obj;
lean_object* v_lhs_19_ = stack[1].m_obj;
lean_object* v_rhs_20_ = stack[2].m_obj;
uint8_t v_linv_21_ = stack[3].m_num;
uint8_t v_rinv_22_ = stack[4].m_num;
lean_object* v_res_65_;
v_res_65_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg(v_output_18_, v_lhs_19_, v_rhs_20_, v_linv_21_, v_rinv_22_);
stack->m_obj
 = v_res_65_;
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg___boxed(lean_object* v_output_66_, lean_object* v_lhs_67_, lean_object* v_rhs_68_, lean_object* v_linv_69_, lean_object* v_rinv_70_){
_start:
{
uint8_t v_linv_boxed_71_; uint8_t v_rinv_boxed_72_; lean_object* v_res_73_; 
v_linv_boxed_71_ = lean_unbox(v_linv_69_);
v_rinv_boxed_72_ = lean_unbox(v_rinv_70_);
v_res_73_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg(v_output_66_, v_lhs_67_, v_rhs_68_, v_linv_boxed_71_, v_rinv_boxed_72_);
return v_res_73_;
}
}
lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF(lean_object* v_00_u03b1_74_, lean_object* v_output_75_, lean_object* v_lhs_76_, lean_object* v_rhs_77_, uint8_t v_linv_78_, uint8_t v_rinv_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg(v_output_75_, v_lhs_76_, v_rhs_77_, v_linv_78_, v_rinv_79_);
return v___x_80_;
}
}
LEAN_EXPORT void l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF_0interp(lean_interpreter_value* stack)
{
lean_object* v_output_75_ = stack[1].m_obj;
lean_object* v_lhs_76_ = stack[2].m_obj;
lean_object* v_rhs_77_ = stack[3].m_obj;
uint8_t v_linv_78_ = stack[4].m_num;
uint8_t v_rinv_79_ = stack[5].m_num;
lean_object* v_res_81_;
v_res_81_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF(lean_box(0), v_output_75_, v_lhs_76_, v_rhs_77_, v_linv_78_, v_rinv_79_);
stack->m_obj
 = v_res_81_;
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___boxed(lean_object* v_00_u03b1_82_, lean_object* v_output_83_, lean_object* v_lhs_84_, lean_object* v_rhs_85_, lean_object* v_linv_86_, lean_object* v_rinv_87_){
_start:
{
uint8_t v_linv_boxed_88_; uint8_t v_rinv_boxed_89_; lean_object* v_res_90_; 
v_linv_boxed_88_ = lean_unbox(v_linv_86_);
v_rinv_boxed_89_ = lean_unbox(v_rinv_87_);
v_res_90_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF(v_00_u03b1_82_, v_output_83_, v_lhs_84_, v_rhs_85_, v_linv_boxed_88_, v_rinv_boxed_89_);
return v_res_90_;
}
}
lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF___redArg(lean_object* v_output_91_, lean_object* v_cond_92_, lean_object* v_ifTrue_93_, lean_object* v_ifFalse_94_, uint8_t v_cinv_95_, uint8_t v_tinv_96_, uint8_t v_finv_97_){
_start:
{
uint8_t v___y_99_; lean_object* v___y_100_; lean_object* v___y_101_; lean_object* v___y_102_; uint8_t v___y_103_; uint8_t v___y_109_; lean_object* v___y_110_; lean_object* v___y_111_; uint8_t v___y_112_; lean_object* v___y_113_; uint8_t v___y_114_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___y_124_; uint8_t v___y_125_; uint8_t v___y_126_; uint8_t v___y_127_; uint8_t v___y_131_; lean_object* v___y_132_; lean_object* v___y_133_; lean_object* v___y_134_; uint8_t v___y_135_; lean_object* v___y_142_; lean_object* v___y_143_; uint8_t v___y_144_; uint8_t v___y_153_; 
v___x_120_ = ((lean_object*)(l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__0));
v___x_121_ = l_ByteArray_empty;
v___x_122_ = lean_array_push(v___x_120_, v_cond_92_);
if (v_cinv_95_ == 0)
{
uint8_t v___x_158_; 
v___x_158_ = 0;
v___y_153_ = v___x_158_;
goto v___jp_152_;
}
else
{
uint8_t v___x_159_; 
v___x_159_ = 1;
v___y_153_ = v___x_159_;
goto v___jp_152_;
}
v___jp_98_:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_104_ = lean_byte_array_push(v___y_100_, v___y_103_);
v___x_105_ = lean_byte_array_push(v___x_104_, v___y_99_);
v___x_106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_106_, 0, v___y_101_);
lean_ctor_set(v___x_106_, 1, v___x_105_);
v___x_107_ = lean_array_push(v___y_102_, v___x_106_);
return v___x_107_;
}
v___jp_108_:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
lean_inc_ref(v___y_111_);
v___x_115_ = lean_byte_array_push(v___y_111_, v___y_114_);
v___x_116_ = lean_array_push(v___y_113_, v_output_91_);
v___x_117_ = lean_byte_array_push(v___x_115_, v___y_112_);
lean_inc_ref(v___x_116_);
v___x_118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_118_, 0, v___x_116_);
lean_ctor_set(v___x_118_, 1, v___x_117_);
v___x_119_ = lean_array_push(v___y_110_, v___x_118_);
if (v_finv_97_ == 0)
{
v___y_99_ = v___y_109_;
v___y_100_ = v___y_111_;
v___y_101_ = v___x_116_;
v___y_102_ = v___x_119_;
v___y_103_ = v___y_112_;
goto v___jp_98_;
}
else
{
v___y_99_ = v___y_109_;
v___y_100_ = v___y_111_;
v___y_101_ = v___x_116_;
v___y_102_ = v___x_119_;
v___y_103_ = v___y_109_;
goto v___jp_98_;
}
}
v___jp_123_:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = lean_byte_array_push(v___x_121_, v___y_127_);
v___x_129_ = lean_array_push(v___x_122_, v_ifFalse_94_);
if (v_finv_97_ == 0)
{
v___y_109_ = v___y_125_;
v___y_110_ = v___y_124_;
v___y_111_ = v___x_128_;
v___y_112_ = v___y_126_;
v___y_113_ = v___x_129_;
v___y_114_ = v___y_125_;
goto v___jp_108_;
}
else
{
v___y_109_ = v___y_125_;
v___y_110_ = v___y_124_;
v___y_111_ = v___x_128_;
v___y_112_ = v___y_126_;
v___y_113_ = v___x_129_;
v___y_114_ = v___y_126_;
goto v___jp_108_;
}
}
v___jp_130_:
{
lean_object* v___x_136_; uint8_t v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_136_ = lean_byte_array_push(v___y_133_, v___y_135_);
v___x_137_ = 0;
v___x_138_ = lean_byte_array_push(v___x_136_, v___x_137_);
v___x_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_139_, 0, v___y_134_);
lean_ctor_set(v___x_139_, 1, v___x_138_);
v___x_140_ = lean_array_push(v___y_132_, v___x_139_);
if (v_cinv_95_ == 0)
{
v___y_124_ = v___x_140_;
v___y_125_ = v___x_137_;
v___y_126_ = v___y_131_;
v___y_127_ = v___y_131_;
goto v___jp_123_;
}
else
{
v___y_124_ = v___x_140_;
v___y_125_ = v___x_137_;
v___y_126_ = v___y_131_;
v___y_127_ = v___x_137_;
goto v___jp_123_;
}
}
v___jp_141_:
{
lean_object* v___x_145_; lean_object* v___x_146_; uint8_t v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
lean_inc_ref(v___y_143_);
v___x_145_ = lean_byte_array_push(v___y_143_, v___y_144_);
lean_inc(v_output_91_);
v___x_146_ = lean_array_push(v___y_142_, v_output_91_);
v___x_147_ = 1;
v___x_148_ = lean_byte_array_push(v___x_145_, v___x_147_);
lean_inc_ref(v___x_146_);
v___x_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_146_);
lean_ctor_set(v___x_149_, 1, v___x_148_);
v___x_150_ = lean_array_push(v___x_120_, v___x_149_);
if (v_tinv_96_ == 0)
{
v___y_131_ = v___x_147_;
v___y_132_ = v___x_150_;
v___y_133_ = v___y_143_;
v___y_134_ = v___x_146_;
v___y_135_ = v___x_147_;
goto v___jp_130_;
}
else
{
uint8_t v___x_151_; 
v___x_151_ = 0;
v___y_131_ = v___x_147_;
v___y_132_ = v___x_150_;
v___y_133_ = v___y_143_;
v___y_134_ = v___x_146_;
v___y_135_ = v___x_151_;
goto v___jp_130_;
}
}
v___jp_152_:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = lean_byte_array_push(v___x_121_, v___y_153_);
lean_inc_ref(v___x_122_);
v___x_155_ = lean_array_push(v___x_122_, v_ifTrue_93_);
if (v_tinv_96_ == 0)
{
uint8_t v___x_156_; 
v___x_156_ = 0;
v___y_142_ = v___x_155_;
v___y_143_ = v___x_154_;
v___y_144_ = v___x_156_;
goto v___jp_141_;
}
else
{
uint8_t v___x_157_; 
v___x_157_ = 1;
v___y_142_ = v___x_155_;
v___y_143_ = v___x_154_;
v___y_144_ = v___x_157_;
goto v___jp_141_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_output_91_ = stack[0].m_obj;
lean_object* v_cond_92_ = stack[1].m_obj;
lean_object* v_ifTrue_93_ = stack[2].m_obj;
lean_object* v_ifFalse_94_ = stack[3].m_obj;
uint8_t v_cinv_95_ = stack[4].m_num;
uint8_t v_tinv_96_ = stack[5].m_num;
uint8_t v_finv_97_ = stack[6].m_num;
lean_object* v_res_160_;
v_res_160_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF___redArg(v_output_91_, v_cond_92_, v_ifTrue_93_, v_ifFalse_94_, v_cinv_95_, v_tinv_96_, v_finv_97_);
stack->m_obj
 = v_res_160_;
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF___redArg___boxed(lean_object* v_output_161_, lean_object* v_cond_162_, lean_object* v_ifTrue_163_, lean_object* v_ifFalse_164_, lean_object* v_cinv_165_, lean_object* v_tinv_166_, lean_object* v_finv_167_){
_start:
{
uint8_t v_cinv_boxed_168_; uint8_t v_tinv_boxed_169_; uint8_t v_finv_boxed_170_; lean_object* v_res_171_; 
v_cinv_boxed_168_ = lean_unbox(v_cinv_165_);
v_tinv_boxed_169_ = lean_unbox(v_tinv_166_);
v_finv_boxed_170_ = lean_unbox(v_finv_167_);
v_res_171_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF___redArg(v_output_161_, v_cond_162_, v_ifTrue_163_, v_ifFalse_164_, v_cinv_boxed_168_, v_tinv_boxed_169_, v_finv_boxed_170_);
return v_res_171_;
}
}
lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF(lean_object* v_00_u03b1_172_, lean_object* v_output_173_, lean_object* v_cond_174_, lean_object* v_ifTrue_175_, lean_object* v_ifFalse_176_, uint8_t v_cinv_177_, uint8_t v_tinv_178_, uint8_t v_finv_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF___redArg(v_output_173_, v_cond_174_, v_ifTrue_175_, v_ifFalse_176_, v_cinv_177_, v_tinv_178_, v_finv_179_);
return v___x_180_;
}
}
LEAN_EXPORT void l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF_0interp(lean_interpreter_value* stack)
{
lean_object* v_output_173_ = stack[1].m_obj;
lean_object* v_cond_174_ = stack[2].m_obj;
lean_object* v_ifTrue_175_ = stack[3].m_obj;
lean_object* v_ifFalse_176_ = stack[4].m_obj;
uint8_t v_cinv_177_ = stack[5].m_num;
uint8_t v_tinv_178_ = stack[6].m_num;
uint8_t v_finv_179_ = stack[7].m_num;
lean_object* v_res_181_;
v_res_181_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF(lean_box(0), v_output_173_, v_cond_174_, v_ifTrue_175_, v_ifFalse_176_, v_cinv_177_, v_tinv_178_, v_finv_179_);
stack->m_obj
 = v_res_181_;
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF___boxed(lean_object* v_00_u03b1_182_, lean_object* v_output_183_, lean_object* v_cond_184_, lean_object* v_ifTrue_185_, lean_object* v_ifFalse_186_, lean_object* v_cinv_187_, lean_object* v_tinv_188_, lean_object* v_finv_189_){
_start:
{
uint8_t v_cinv_boxed_190_; uint8_t v_tinv_boxed_191_; uint8_t v_finv_boxed_192_; lean_object* v_res_193_; 
v_cinv_boxed_190_ = lean_unbox(v_cinv_187_);
v_tinv_boxed_191_ = lean_unbox(v_tinv_188_);
v_finv_boxed_192_ = lean_unbox(v_finv_189_);
v_res_193_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF(v_00_u03b1_182_, v_output_183_, v_cond_184_, v_ifTrue_185_, v_ifFalse_186_, v_cinv_boxed_190_, v_tinv_boxed_191_, v_finv_boxed_192_);
return v_res_193_;
}
}
uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign___redArg___lam__0(lean_object* v_inst_194_, lean_object* v_a_195_, lean_object* v_b_196_){
_start:
{
uint8_t v___x_197_; 
v___x_197_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v_inst_194_, v_a_195_, v_b_196_);
return v___x_197_;
}
}
LEAN_EXPORT void l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_194_ = stack[0].m_obj;
lean_object* v_a_195_ = stack[1].m_obj;
lean_object* v_b_196_ = stack[2].m_obj;
uint8_t v_res_198_;
v_res_198_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign___redArg___lam__0(v_inst_194_, v_a_195_, v_b_196_);
stack->m_num = v_res_198_;
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign___redArg___lam__0___boxed(lean_object* v_inst_199_, lean_object* v_a_200_, lean_object* v_b_201_){
_start:
{
uint8_t v_res_202_; lean_object* v_r_203_; 
v_res_202_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign___redArg___lam__0(v_inst_199_, v_a_200_, v_b_201_);
v_r_203_ = lean_box(v_res_202_);
return v_r_203_;
}
}
uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign___redArg(lean_object* v_inst_204_, lean_object* v_inst_205_, lean_object* v_aig_206_, lean_object* v_assign_207_, lean_object* v_a_208_){
_start:
{
lean_object* v_cache_209_; lean_object* v___f_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___f_213_; lean_object* v___x_214_; 
v_cache_209_ = lean_ctor_get(v_aig_206_, 1);
v___f_210_ = lean_alloc_closure((void*)(l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_210_, 0, v_inst_205_);
v___x_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_211_, 0, v_a_208_);
v___x_212_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_212_, 0, lean_box(0));
lean_closure_set(v___x_212_, 1, v_inst_204_);
v___f_213_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_213_, 0, v___f_210_);
v___x_214_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_213_, v___x_212_, v_cache_209_, v___x_211_);
if (lean_obj_tag(v___x_214_) == 0)
{
uint8_t v___x_215_; 
lean_dec_ref(v_assign_207_);
v___x_215_ = 0;
return v___x_215_;
}
else
{
lean_object* v_val_216_; lean_object* v___x_217_; uint8_t v___x_218_; 
v_val_216_ = lean_ctor_get(v___x_214_, 0);
lean_inc(v_val_216_);
lean_dec_ref_known(v___x_214_, 1);
v___x_217_ = lean_apply_1(v_assign_207_, v_val_216_);
v___x_218_ = lean_unbox(v___x_217_);
return v___x_218_;
}
}
}
LEAN_EXPORT void l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_204_ = stack[0].m_obj;
lean_object* v_inst_205_ = stack[1].m_obj;
lean_object* v_aig_206_ = stack[2].m_obj;
lean_object* v_assign_207_ = stack[3].m_obj;
lean_object* v_a_208_ = stack[4].m_obj;
uint8_t v_res_219_;
v_res_219_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign___redArg(v_inst_204_, v_inst_205_, v_aig_206_, v_assign_207_, v_a_208_);
stack->m_num = v_res_219_;
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign___redArg___boxed(lean_object* v_inst_220_, lean_object* v_inst_221_, lean_object* v_aig_222_, lean_object* v_assign_223_, lean_object* v_a_224_){
_start:
{
uint8_t v_res_225_; lean_object* v_r_226_; 
v_res_225_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign___redArg(v_inst_220_, v_inst_221_, v_aig_222_, v_assign_223_, v_a_224_);
lean_dec_ref(v_aig_222_);
v_r_226_ = lean_box(v_res_225_);
return v_r_226_;
}
}
uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign(lean_object* v_00_u03b1_227_, lean_object* v_inst_228_, lean_object* v_inst_229_, lean_object* v_aig_230_, lean_object* v_assign_231_, lean_object* v_a_232_){
_start:
{
uint8_t v___x_233_; 
v___x_233_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign___redArg(v_inst_228_, v_inst_229_, v_aig_230_, v_assign_231_, v_a_232_);
return v___x_233_;
}
}
LEAN_EXPORT void l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_228_ = stack[1].m_obj;
lean_object* v_inst_229_ = stack[2].m_obj;
lean_object* v_aig_230_ = stack[3].m_obj;
lean_object* v_assign_231_ = stack[4].m_obj;
lean_object* v_a_232_ = stack[5].m_obj;
uint8_t v_res_234_;
v_res_234_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign(lean_box(0), v_inst_228_, v_inst_229_, v_aig_230_, v_assign_231_, v_a_232_);
stack->m_num = v_res_234_;
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign___boxed(lean_object* v_00_u03b1_235_, lean_object* v_inst_236_, lean_object* v_inst_237_, lean_object* v_aig_238_, lean_object* v_assign_239_, lean_object* v_a_240_){
_start:
{
uint8_t v_res_241_; lean_object* v_r_242_; 
v_res_241_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign(v_00_u03b1_235_, v_inst_236_, v_inst_237_, v_aig_238_, v_assign_239_, v_a_240_);
lean_dec_ref(v_aig_238_);
v_r_242_ = lean_box(v_res_241_);
return v_r_242_;
}
}
uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___redArg(lean_object* v_aig_243_, lean_object* v_assign1_244_, lean_object* v_idx_245_){
_start:
{
lean_object* v_decls_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v_decls_246_ = lean_ctor_get(v_aig_243_, 0);
v___x_247_ = lean_array_get_size(v_decls_246_);
v___x_248_ = lean_nat_dec_lt(v_idx_245_, v___x_247_);
if (v___x_248_ == 0)
{
lean_dec(v_idx_245_);
lean_dec_ref(v_assign1_244_);
lean_dec_ref(v_aig_243_);
return v___x_248_;
}
else
{
uint8_t v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_249_ = 0;
v___x_250_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_250_, 0, v_idx_245_);
lean_ctor_set_uint8(v___x_250_, sizeof(void*)*1, v___x_249_);
v___x_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_251_, 0, v_aig_243_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
v___x_252_ = l_Std_Sat_AIG_denote___redArg(v_assign1_244_, v___x_251_);
lean_dec_ref_known(v___x_251_, 2);
return v___x_252_;
}
}
}
LEAN_EXPORT void l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_aig_243_ = stack[0].m_obj;
lean_object* v_assign1_244_ = stack[1].m_obj;
lean_object* v_idx_245_ = stack[2].m_obj;
uint8_t v_res_253_;
v_res_253_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___redArg(v_aig_243_, v_assign1_244_, v_idx_245_);
stack->m_num = v_res_253_;
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___redArg___boxed(lean_object* v_aig_254_, lean_object* v_assign1_255_, lean_object* v_idx_256_){
_start:
{
uint8_t v_res_257_; lean_object* v_r_258_; 
v_res_257_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___redArg(v_aig_254_, v_assign1_255_, v_idx_256_);
v_r_258_ = lean_box(v_res_257_);
return v_r_258_;
}
}
uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment(lean_object* v_00_u03b1_259_, lean_object* v_inst_260_, lean_object* v_inst_261_, lean_object* v_aig_262_, lean_object* v_assign1_263_, lean_object* v_idx_264_){
_start:
{
uint8_t v___x_265_; 
v___x_265_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___redArg(v_aig_262_, v_assign1_263_, v_idx_264_);
return v___x_265_;
}
}
LEAN_EXPORT void l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_260_ = stack[1].m_obj;
lean_object* v_inst_261_ = stack[2].m_obj;
lean_object* v_aig_262_ = stack[3].m_obj;
lean_object* v_assign1_263_ = stack[4].m_obj;
lean_object* v_idx_264_ = stack[5].m_obj;
uint8_t v_res_266_;
v_res_266_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment(lean_box(0), v_inst_260_, v_inst_261_, v_aig_262_, v_assign1_263_, v_idx_264_);
stack->m_num = v_res_266_;
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___boxed(lean_object* v_00_u03b1_267_, lean_object* v_inst_268_, lean_object* v_inst_269_, lean_object* v_aig_270_, lean_object* v_assign1_271_, lean_object* v_idx_272_){
_start:
{
uint8_t v_res_273_; lean_object* v_r_274_; 
v_res_273_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment(v_00_u03b1_267_, v_inst_268_, v_inst_269_, v_aig_270_, v_assign1_271_, v_idx_272_);
lean_dec_ref(v_inst_269_);
lean_dec_ref(v_inst_268_);
v_r_274_ = lean_box(v_res_273_);
return v_r_274_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___redArg(lean_object* v_aig_275_){
_start:
{
lean_object* v_decls_276_; lean_object* v___x_277_; uint8_t v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v_decls_276_ = lean_ctor_get(v_aig_275_, 0);
v___x_277_ = lean_array_get_size(v_decls_276_);
v___x_278_ = 0;
v___x_279_ = lean_box(v___x_278_);
v___x_280_ = lean_mk_array(v___x_277_, v___x_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___redArg___boxed(lean_object* v_aig_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___redArg(v_aig_281_);
lean_dec_ref(v_aig_281_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init(lean_object* v_00_u03b1_283_, lean_object* v_inst_284_, lean_object* v_inst_285_, lean_object* v_aig_286_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___redArg(v_aig_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___boxed(lean_object* v_00_u03b1_288_, lean_object* v_inst_289_, lean_object* v_inst_290_, lean_object* v_aig_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init(v_00_u03b1_288_, v_inst_289_, v_inst_290_, v_aig_291_);
lean_dec_ref(v_aig_291_);
lean_dec_ref(v_inst_290_);
lean_dec_ref(v_inst_289_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_cast___redArg(lean_object* v_aig2_293_, lean_object* v_cache_294_){
_start:
{
lean_object* v_decls_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; uint8_t v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v_decls_295_ = lean_ctor_get(v_aig2_293_, 0);
v___x_296_ = lean_array_get_size(v_decls_295_);
v___x_297_ = lean_array_get_size(v_cache_294_);
v___x_298_ = lean_nat_sub(v___x_296_, v___x_297_);
v___x_299_ = 0;
v___x_300_ = lean_box(v___x_299_);
v___x_301_ = lean_mk_array(v___x_298_, v___x_300_);
v___x_302_ = l_Array_append___redArg(v_cache_294_, v___x_301_);
lean_dec_ref(v___x_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_cast___redArg___boxed(lean_object* v_aig2_303_, lean_object* v_cache_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_cast___redArg(v_aig2_303_, v_cache_304_);
lean_dec_ref(v_aig2_303_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_cast(lean_object* v_00_u03b1_306_, lean_object* v_inst_307_, lean_object* v_inst_308_, lean_object* v_cnf_309_, lean_object* v_aig1_310_, lean_object* v_aig2_311_, lean_object* v_cache_312_, lean_object* v_hprefix_313_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_cast___redArg(v_aig2_311_, v_cache_312_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_cast___boxed(lean_object* v_00_u03b1_315_, lean_object* v_inst_316_, lean_object* v_inst_317_, lean_object* v_cnf_318_, lean_object* v_aig1_319_, lean_object* v_aig2_320_, lean_object* v_cache_321_, lean_object* v_hprefix_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_cast(v_00_u03b1_315_, v_inst_316_, v_inst_317_, v_cnf_318_, v_aig1_319_, v_aig2_320_, v_cache_321_, v_hprefix_322_);
lean_dec_ref(v_aig2_320_);
lean_dec_ref(v_aig1_319_);
lean_dec_ref(v_cnf_318_);
lean_dec_ref(v_inst_317_);
lean_dec_ref(v_inst_316_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg(lean_object* v_cache_324_, lean_object* v_idx_325_){
_start:
{
uint8_t v___x_326_; lean_object* v___x_327_; lean_object* v_out_328_; 
v___x_326_ = 1;
v___x_327_ = lean_box(v___x_326_);
v_out_328_ = lean_array_fset(v_cache_324_, v_idx_325_, v___x_327_);
return v_out_328_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg___boxed(lean_object* v_cache_329_, lean_object* v_idx_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg(v_cache_329_, v_idx_330_);
lean_dec(v_idx_330_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse(lean_object* v_00_u03b1_332_, lean_object* v_inst_333_, lean_object* v_inst_334_, lean_object* v_aig_335_, lean_object* v_cnf_336_, lean_object* v_cache_337_, lean_object* v_idx_338_, lean_object* v_h_339_, lean_object* v_htip_340_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg(v_cache_337_, v_idx_338_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___boxed(lean_object* v_00_u03b1_342_, lean_object* v_inst_343_, lean_object* v_inst_344_, lean_object* v_aig_345_, lean_object* v_cnf_346_, lean_object* v_cache_347_, lean_object* v_idx_348_, lean_object* v_h_349_, lean_object* v_htip_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse(v_00_u03b1_342_, v_inst_343_, v_inst_344_, v_aig_345_, v_cnf_346_, v_cache_347_, v_idx_348_, v_h_349_, v_htip_350_);
lean_dec(v_idx_348_);
lean_dec_ref(v_cnf_346_);
lean_dec_ref(v_aig_345_);
lean_dec_ref(v_inst_344_);
lean_dec_ref(v_inst_343_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg(lean_object* v_cache_352_, lean_object* v_idx_353_){
_start:
{
uint8_t v___x_354_; lean_object* v___x_355_; lean_object* v_out_356_; 
v___x_354_ = 1;
v___x_355_ = lean_box(v___x_354_);
v_out_356_ = lean_array_fset(v_cache_352_, v_idx_353_, v___x_355_);
return v_out_356_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg___boxed(lean_object* v_cache_357_, lean_object* v_idx_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg(v_cache_357_, v_idx_358_);
lean_dec(v_idx_358_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom(lean_object* v_00_u03b1_360_, lean_object* v_inst_361_, lean_object* v_inst_362_, lean_object* v_aig_363_, lean_object* v_cnf_364_, lean_object* v_a_365_, lean_object* v_cache_366_, lean_object* v_idx_367_, lean_object* v_h_368_, lean_object* v_htip_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg(v_cache_366_, v_idx_367_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___boxed(lean_object* v_00_u03b1_371_, lean_object* v_inst_372_, lean_object* v_inst_373_, lean_object* v_aig_374_, lean_object* v_cnf_375_, lean_object* v_a_376_, lean_object* v_cache_377_, lean_object* v_idx_378_, lean_object* v_h_379_, lean_object* v_htip_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom(v_00_u03b1_371_, v_inst_372_, v_inst_373_, v_aig_374_, v_cnf_375_, v_a_376_, v_cache_377_, v_idx_378_, v_h_379_, v_htip_380_);
lean_dec(v_idx_378_);
lean_dec(v_a_376_);
lean_dec_ref(v_cnf_375_);
lean_dec_ref(v_aig_374_);
lean_dec_ref(v_inst_373_);
lean_dec_ref(v_inst_372_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg(lean_object* v_lhs_382_, lean_object* v_rhs_383_, lean_object* v_cache_384_, lean_object* v_idx_385_){
_start:
{
uint8_t v___x_386_; lean_object* v___x_387_; lean_object* v_out_388_; 
v___x_386_ = 1;
v___x_387_ = lean_box(v___x_386_);
v_out_388_ = lean_array_fset(v_cache_384_, v_idx_385_, v___x_387_);
return v_out_388_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg___boxed(lean_object* v_lhs_389_, lean_object* v_rhs_390_, lean_object* v_cache_391_, lean_object* v_idx_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg(v_lhs_389_, v_rhs_390_, v_cache_391_, v_idx_392_);
lean_dec(v_idx_392_);
lean_dec(v_rhs_390_);
lean_dec(v_lhs_389_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate(lean_object* v_00_u03b1_394_, lean_object* v_inst_395_, lean_object* v_inst_396_, lean_object* v_aig_397_, lean_object* v_cnf_398_, lean_object* v_lhs_399_, lean_object* v_rhs_400_, lean_object* v_cache_401_, lean_object* v_hlb_402_, lean_object* v_hrb_403_, lean_object* v_idx_404_, lean_object* v_h_405_, lean_object* v_htip_406_, lean_object* v_hl_407_, lean_object* v_hr_408_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg(v_lhs_399_, v_rhs_400_, v_cache_401_, v_idx_404_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___boxed(lean_object* v_00_u03b1_410_, lean_object* v_inst_411_, lean_object* v_inst_412_, lean_object* v_aig_413_, lean_object* v_cnf_414_, lean_object* v_lhs_415_, lean_object* v_rhs_416_, lean_object* v_cache_417_, lean_object* v_hlb_418_, lean_object* v_hrb_419_, lean_object* v_idx_420_, lean_object* v_h_421_, lean_object* v_htip_422_, lean_object* v_hl_423_, lean_object* v_hr_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate(v_00_u03b1_410_, v_inst_411_, v_inst_412_, v_aig_413_, v_cnf_414_, v_lhs_415_, v_rhs_416_, v_cache_417_, v_hlb_418_, v_hrb_419_, v_idx_420_, v_h_421_, v_htip_422_, v_hl_423_, v_hr_424_);
lean_dec(v_idx_420_);
lean_dec(v_rhs_416_);
lean_dec(v_lhs_415_);
lean_dec_ref(v_cnf_414_);
lean_dec_ref(v_aig_413_);
lean_dec_ref(v_inst_412_);
lean_dec_ref(v_inst_411_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___redArg(lean_object* v_cache_426_, lean_object* v_cond_427_, lean_object* v_ifTrue_428_, lean_object* v_ifFalse_429_, lean_object* v_idx_430_){
_start:
{
uint8_t v___x_431_; lean_object* v___x_432_; lean_object* v_out_433_; 
v___x_431_ = 1;
v___x_432_ = lean_box(v___x_431_);
v_out_433_ = lean_array_fset(v_cache_426_, v_idx_430_, v___x_432_);
return v_out_433_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___redArg___boxed(lean_object* v_cache_434_, lean_object* v_cond_435_, lean_object* v_ifTrue_436_, lean_object* v_ifFalse_437_, lean_object* v_idx_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___redArg(v_cache_434_, v_cond_435_, v_ifTrue_436_, v_ifFalse_437_, v_idx_438_);
lean_dec(v_idx_438_);
lean_dec(v_ifFalse_437_);
lean_dec(v_ifTrue_436_);
lean_dec(v_cond_435_);
return v_res_439_;
}
}
lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte(lean_object* v_00_u03b1_440_, lean_object* v_inst_441_, lean_object* v_inst_442_, lean_object* v_aig_443_, lean_object* v_cnf_444_, lean_object* v_cache_445_, lean_object* v_cond_446_, lean_object* v_ifTrue_447_, lean_object* v_ifFalse_448_, lean_object* v_idx_449_, lean_object* v_hcb_450_, lean_object* v_htb_451_, lean_object* v_hfb_452_, lean_object* v_h_453_, lean_object* v_hltc_454_, lean_object* v_hltt_455_, lean_object* v_hltf_456_, lean_object* v_hc_457_, lean_object* v_ht_458_, lean_object* v_hf_459_, lean_object* v_hdenote_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___redArg(v_cache_445_, v_cond_446_, v_ifTrue_447_, v_ifFalse_448_, v_idx_449_);
return v___x_461_;
}
}
LEAN_EXPORT void l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_441_ = stack[1].m_obj;
lean_object* v_inst_442_ = stack[2].m_obj;
lean_object* v_aig_443_ = stack[3].m_obj;
lean_object* v_cnf_444_ = stack[4].m_obj;
lean_object* v_cache_445_ = stack[5].m_obj;
lean_object* v_cond_446_ = stack[6].m_obj;
lean_object* v_ifTrue_447_ = stack[7].m_obj;
lean_object* v_ifFalse_448_ = stack[8].m_obj;
lean_object* v_idx_449_ = stack[9].m_obj;
lean_object* v_res_462_;
v_res_462_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte(lean_box(0), v_inst_441_, v_inst_442_, v_aig_443_, v_cnf_444_, v_cache_445_, v_cond_446_, v_ifTrue_447_, v_ifFalse_448_, v_idx_449_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
stack->m_obj
 = v_res_462_;
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___boxed(lean_object** _args){
lean_object* v_00_u03b1_463_ = _args[0];
lean_object* v_inst_464_ = _args[1];
lean_object* v_inst_465_ = _args[2];
lean_object* v_aig_466_ = _args[3];
lean_object* v_cnf_467_ = _args[4];
lean_object* v_cache_468_ = _args[5];
lean_object* v_cond_469_ = _args[6];
lean_object* v_ifTrue_470_ = _args[7];
lean_object* v_ifFalse_471_ = _args[8];
lean_object* v_idx_472_ = _args[9];
lean_object* v_hcb_473_ = _args[10];
lean_object* v_htb_474_ = _args[11];
lean_object* v_hfb_475_ = _args[12];
lean_object* v_h_476_ = _args[13];
lean_object* v_hltc_477_ = _args[14];
lean_object* v_hltt_478_ = _args[15];
lean_object* v_hltf_479_ = _args[16];
lean_object* v_hc_480_ = _args[17];
lean_object* v_ht_481_ = _args[18];
lean_object* v_hf_482_ = _args[19];
lean_object* v_hdenote_483_ = _args[20];
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte(v_00_u03b1_463_, v_inst_464_, v_inst_465_, v_aig_466_, v_cnf_467_, v_cache_468_, v_cond_469_, v_ifTrue_470_, v_ifFalse_471_, v_idx_472_, v_hcb_473_, v_htb_474_, v_hfb_475_, v_h_476_, v_hltc_477_, v_hltt_478_, v_hltf_479_, v_hc_480_, v_ht_481_, v_hf_482_, v_hdenote_483_);
lean_dec(v_idx_472_);
lean_dec(v_ifFalse_471_);
lean_dec(v_ifTrue_470_);
lean_dec(v_cond_469_);
lean_dec_ref(v_cnf_467_);
lean_dec_ref(v_aig_466_);
lean_dec_ref(v_inst_465_);
lean_dec_ref(v_inst_464_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty___redArg(lean_object* v_aig_487_){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_488_ = ((lean_object*)(l_Std_Sat_AIG_toCNF_State_empty___redArg___closed__0));
v___x_489_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___redArg(v_aig_487_);
v___x_490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_490_, 0, v___x_488_);
lean_ctor_set(v___x_490_, 1, v___x_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty___redArg___boxed(lean_object* v_aig_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Std_Sat_AIG_toCNF_State_empty___redArg(v_aig_491_);
lean_dec_ref(v_aig_491_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty(lean_object* v_00_u03b1_493_, lean_object* v_inst_494_, lean_object* v_inst_495_, lean_object* v_aig_496_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l_Std_Sat_AIG_toCNF_State_empty___redArg(v_aig_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty___boxed(lean_object* v_00_u03b1_498_, lean_object* v_inst_499_, lean_object* v_inst_500_, lean_object* v_aig_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Std_Sat_AIG_toCNF_State_empty(v_00_u03b1_498_, v_inst_499_, v_inst_500_, v_aig_501_);
lean_dec_ref(v_aig_501_);
lean_dec_ref(v_inst_500_);
lean_dec_ref(v_inst_499_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_cast___redArg(lean_object* v_aig2_503_, lean_object* v_state_504_){
_start:
{
lean_object* v_cnf_505_; lean_object* v_cache_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_514_; 
v_cnf_505_ = lean_ctor_get(v_state_504_, 0);
v_cache_506_ = lean_ctor_get(v_state_504_, 1);
v_isSharedCheck_514_ = !lean_is_exclusive(v_state_504_);
if (v_isSharedCheck_514_ == 0)
{
v___x_508_ = v_state_504_;
v_isShared_509_ = v_isSharedCheck_514_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_cache_506_);
lean_inc(v_cnf_505_);
lean_dec(v_state_504_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_514_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v___x_512_; 
v___x_510_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_cast___redArg(v_aig2_503_, v_cache_506_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 1, v___x_510_);
v___x_512_ = v___x_508_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_cnf_505_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v___x_510_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_cast___redArg___boxed(lean_object* v_aig2_515_, lean_object* v_state_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Std_Sat_AIG_toCNF_State_cast___redArg(v_aig2_515_, v_state_516_);
lean_dec_ref(v_aig2_515_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_cast(lean_object* v_00_u03b1_518_, lean_object* v_inst_519_, lean_object* v_inst_520_, lean_object* v_aig1_521_, lean_object* v_aig2_522_, lean_object* v_state_523_, lean_object* v_hprefix_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Std_Sat_AIG_toCNF_State_cast___redArg(v_aig2_522_, v_state_523_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_cast___boxed(lean_object* v_00_u03b1_526_, lean_object* v_inst_527_, lean_object* v_inst_528_, lean_object* v_aig1_529_, lean_object* v_aig2_530_, lean_object* v_state_531_, lean_object* v_hprefix_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Std_Sat_AIG_toCNF_State_cast(v_00_u03b1_526_, v_inst_527_, v_inst_528_, v_aig1_529_, v_aig2_530_, v_state_531_, v_hprefix_532_);
lean_dec_ref(v_aig2_530_);
lean_dec_ref(v_aig1_529_);
lean_dec_ref(v_inst_528_);
lean_dec_ref(v_inst_527_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___redArg(lean_object* v_state_534_, lean_object* v_idx_535_){
_start:
{
lean_object* v_cnf_536_; lean_object* v_cache_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_547_; 
v_cnf_536_ = lean_ctor_get(v_state_534_, 0);
v_cache_537_ = lean_ctor_get(v_state_534_, 1);
v_isSharedCheck_547_ = !lean_is_exclusive(v_state_534_);
if (v_isSharedCheck_547_ == 0)
{
v___x_539_ = v_state_534_;
v_isShared_540_ = v_isSharedCheck_547_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_cache_537_);
lean_inc(v_cnf_536_);
lean_dec(v_state_534_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_547_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v_val_541_; lean_object* v_newCnf_542_; lean_object* v___x_543_; lean_object* v___x_545_; 
v_val_541_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg(v_cache_537_, v_idx_535_);
v_newCnf_542_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg(v_idx_535_);
v___x_543_ = l_Array_append___redArg(v_cnf_536_, v_newCnf_542_);
lean_dec_ref(v_newCnf_542_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 1, v_val_541_);
lean_ctor_set(v___x_539_, 0, v___x_543_);
v___x_545_ = v___x_539_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_543_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_val_541_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse(lean_object* v_00_u03b1_548_, lean_object* v_inst_549_, lean_object* v_inst_550_, lean_object* v_aig_551_, lean_object* v_state_552_, lean_object* v_idx_553_, lean_object* v_h_554_, lean_object* v_htip_555_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___redArg(v_state_552_, v_idx_553_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___boxed(lean_object* v_00_u03b1_557_, lean_object* v_inst_558_, lean_object* v_inst_559_, lean_object* v_aig_560_, lean_object* v_state_561_, lean_object* v_idx_562_, lean_object* v_h_563_, lean_object* v_htip_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse(v_00_u03b1_557_, v_inst_558_, v_inst_559_, v_aig_560_, v_state_561_, v_idx_562_, v_h_563_, v_htip_564_);
lean_dec_ref(v_aig_560_);
lean_dec_ref(v_inst_559_);
lean_dec_ref(v_inst_558_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg(lean_object* v_state_566_, lean_object* v_idx_567_){
_start:
{
lean_object* v_cnf_568_; lean_object* v_cache_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_577_; 
v_cnf_568_ = lean_ctor_get(v_state_566_, 0);
v_cache_569_ = lean_ctor_get(v_state_566_, 1);
v_isSharedCheck_577_ = !lean_is_exclusive(v_state_566_);
if (v_isSharedCheck_577_ == 0)
{
v___x_571_ = v_state_566_;
v_isShared_572_ = v_isSharedCheck_577_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_cache_569_);
lean_inc(v_cnf_568_);
lean_dec(v_state_566_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_577_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v_val_573_; lean_object* v___x_575_; 
v_val_573_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg(v_cache_569_, v_idx_567_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 1, v_val_573_);
v___x_575_ = v___x_571_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_cnf_568_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v_val_573_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg___boxed(lean_object* v_state_578_, lean_object* v_idx_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg(v_state_578_, v_idx_579_);
lean_dec(v_idx_579_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom(lean_object* v_00_u03b1_581_, lean_object* v_inst_582_, lean_object* v_inst_583_, lean_object* v_aig_584_, lean_object* v_a_585_, lean_object* v_state_586_, lean_object* v_idx_587_, lean_object* v_h_588_, lean_object* v_htip_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg(v_state_586_, v_idx_587_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___boxed(lean_object* v_00_u03b1_591_, lean_object* v_inst_592_, lean_object* v_inst_593_, lean_object* v_aig_594_, lean_object* v_a_595_, lean_object* v_state_596_, lean_object* v_idx_597_, lean_object* v_h_598_, lean_object* v_htip_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom(v_00_u03b1_591_, v_inst_592_, v_inst_593_, v_aig_594_, v_a_595_, v_state_596_, v_idx_597_, v_h_598_, v_htip_599_);
lean_dec(v_idx_597_);
lean_dec(v_a_595_);
lean_dec_ref(v_aig_594_);
lean_dec_ref(v_inst_593_);
lean_dec_ref(v_inst_592_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg(lean_object* v_lhs_601_, lean_object* v_rhs_602_, lean_object* v_state_603_, lean_object* v_idx_604_){
_start:
{
lean_object* v_cnf_605_; lean_object* v_cache_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_634_; 
v_cnf_605_ = lean_ctor_get(v_state_603_, 0);
v_cache_606_ = lean_ctor_get(v_state_603_, 1);
v_isSharedCheck_634_ = !lean_is_exclusive(v_state_603_);
if (v_isSharedCheck_634_ == 0)
{
v___x_608_ = v_state_603_;
v_isShared_609_ = v_isSharedCheck_634_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_cache_606_);
lean_inc(v_cnf_605_);
lean_dec(v_state_603_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_634_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; uint8_t v___y_614_; uint8_t v___y_615_; uint8_t v___y_623_; lean_object* v___x_629_; lean_object* v___x_630_; uint8_t v___x_631_; 
v___x_610_ = lean_unsigned_to_nat(1u);
v___x_611_ = lean_nat_shiftr(v_lhs_601_, v___x_610_);
v___x_612_ = lean_nat_shiftr(v_rhs_602_, v___x_610_);
v___x_629_ = lean_nat_land(v___x_610_, v_lhs_601_);
v___x_630_ = lean_unsigned_to_nat(0u);
v___x_631_ = lean_nat_dec_eq(v___x_629_, v___x_630_);
lean_dec(v___x_629_);
if (v___x_631_ == 0)
{
uint8_t v___x_632_; 
v___x_632_ = 1;
v___y_623_ = v___x_632_;
goto v___jp_622_;
}
else
{
uint8_t v___x_633_; 
v___x_633_ = 0;
v___y_623_ = v___x_633_;
goto v___jp_622_;
}
v___jp_613_:
{
lean_object* v_val_616_; lean_object* v_newCnf_617_; lean_object* v___x_618_; lean_object* v___x_620_; 
v_val_616_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg(v_lhs_601_, v_rhs_602_, v_cache_606_, v_idx_604_);
v_newCnf_617_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg(v_idx_604_, v___x_611_, v___x_612_, v___y_614_, v___y_615_);
v___x_618_ = l_Array_append___redArg(v_cnf_605_, v_newCnf_617_);
lean_dec_ref(v_newCnf_617_);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 1, v_val_616_);
lean_ctor_set(v___x_608_, 0, v___x_618_);
v___x_620_ = v___x_608_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_618_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v_val_616_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
v___jp_622_:
{
lean_object* v___x_624_; lean_object* v___x_625_; uint8_t v___x_626_; 
v___x_624_ = lean_nat_land(v___x_610_, v_rhs_602_);
v___x_625_ = lean_unsigned_to_nat(0u);
v___x_626_ = lean_nat_dec_eq(v___x_624_, v___x_625_);
lean_dec(v___x_624_);
if (v___x_626_ == 0)
{
uint8_t v___x_627_; 
v___x_627_ = 1;
v___y_614_ = v___y_623_;
v___y_615_ = v___x_627_;
goto v___jp_613_;
}
else
{
uint8_t v___x_628_; 
v___x_628_ = 0;
v___y_614_ = v___y_623_;
v___y_615_ = v___x_628_;
goto v___jp_613_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg___boxed(lean_object* v_lhs_635_, lean_object* v_rhs_636_, lean_object* v_state_637_, lean_object* v_idx_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg(v_lhs_635_, v_rhs_636_, v_state_637_, v_idx_638_);
lean_dec(v_rhs_636_);
lean_dec(v_lhs_635_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate(lean_object* v_00_u03b1_640_, lean_object* v_inst_641_, lean_object* v_inst_642_, lean_object* v_aig_643_, lean_object* v_lhs_644_, lean_object* v_rhs_645_, lean_object* v_state_646_, lean_object* v_hlb_647_, lean_object* v_hrb_648_, lean_object* v_idx_649_, lean_object* v_h_650_, lean_object* v_htip_651_, lean_object* v_hl_652_, lean_object* v_hr_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg(v_lhs_644_, v_rhs_645_, v_state_646_, v_idx_649_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___boxed(lean_object* v_00_u03b1_655_, lean_object* v_inst_656_, lean_object* v_inst_657_, lean_object* v_aig_658_, lean_object* v_lhs_659_, lean_object* v_rhs_660_, lean_object* v_state_661_, lean_object* v_hlb_662_, lean_object* v_hrb_663_, lean_object* v_idx_664_, lean_object* v_h_665_, lean_object* v_htip_666_, lean_object* v_hl_667_, lean_object* v_hr_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate(v_00_u03b1_655_, v_inst_656_, v_inst_657_, v_aig_658_, v_lhs_659_, v_rhs_660_, v_state_661_, v_hlb_662_, v_hrb_663_, v_idx_664_, v_h_665_, v_htip_666_, v_hl_667_, v_hr_668_);
lean_dec(v_rhs_660_);
lean_dec(v_lhs_659_);
lean_dec_ref(v_aig_658_);
lean_dec_ref(v_inst_657_);
lean_dec_ref(v_inst_656_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___redArg(lean_object* v_state_670_, lean_object* v_cond_671_, lean_object* v_ifTrue_672_, lean_object* v_ifFalse_673_, lean_object* v_idx_674_){
_start:
{
lean_object* v_cnf_675_; lean_object* v_cache_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_714_; 
v_cnf_675_ = lean_ctor_get(v_state_670_, 0);
v_cache_676_ = lean_ctor_get(v_state_670_, 1);
v_isSharedCheck_714_ = !lean_is_exclusive(v_state_670_);
if (v_isSharedCheck_714_ == 0)
{
v___x_678_ = v_state_670_;
v_isShared_679_ = v_isSharedCheck_714_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_cache_676_);
lean_inc(v_cnf_675_);
lean_dec(v_state_670_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_714_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; uint8_t v___y_685_; uint8_t v___y_686_; uint8_t v___y_687_; uint8_t v___y_695_; uint8_t v___y_696_; uint8_t v___y_703_; lean_object* v___x_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
v___x_680_ = lean_unsigned_to_nat(1u);
v___x_681_ = lean_nat_shiftr(v_cond_671_, v___x_680_);
v___x_682_ = lean_nat_shiftr(v_ifTrue_672_, v___x_680_);
v___x_683_ = lean_nat_shiftr(v_ifFalse_673_, v___x_680_);
v___x_709_ = lean_nat_land(v___x_680_, v_cond_671_);
v___x_710_ = lean_unsigned_to_nat(0u);
v___x_711_ = lean_nat_dec_eq(v___x_709_, v___x_710_);
lean_dec(v___x_709_);
if (v___x_711_ == 0)
{
uint8_t v___x_712_; 
v___x_712_ = 1;
v___y_703_ = v___x_712_;
goto v___jp_702_;
}
else
{
uint8_t v___x_713_; 
v___x_713_ = 0;
v___y_703_ = v___x_713_;
goto v___jp_702_;
}
v___jp_684_:
{
lean_object* v_val_688_; lean_object* v_newCnf_689_; lean_object* v___x_690_; lean_object* v___x_692_; 
v_val_688_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___redArg(v_cache_676_, v_cond_671_, v_ifTrue_672_, v_ifFalse_673_, v_idx_674_);
v_newCnf_689_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF___redArg(v_idx_674_, v___x_681_, v___x_682_, v___x_683_, v___y_685_, v___y_686_, v___y_687_);
v___x_690_ = l_Array_append___redArg(v_cnf_675_, v_newCnf_689_);
lean_dec_ref(v_newCnf_689_);
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 1, v_val_688_);
lean_ctor_set(v___x_678_, 0, v___x_690_);
v___x_692_ = v___x_678_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_690_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v_val_688_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
v___jp_694_:
{
lean_object* v___x_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
v___x_697_ = lean_nat_land(v___x_680_, v_ifFalse_673_);
v___x_698_ = lean_unsigned_to_nat(0u);
v___x_699_ = lean_nat_dec_eq(v___x_697_, v___x_698_);
lean_dec(v___x_697_);
if (v___x_699_ == 0)
{
uint8_t v___x_700_; 
v___x_700_ = 1;
v___y_685_ = v___y_695_;
v___y_686_ = v___y_696_;
v___y_687_ = v___x_700_;
goto v___jp_684_;
}
else
{
uint8_t v___x_701_; 
v___x_701_ = 0;
v___y_685_ = v___y_695_;
v___y_686_ = v___y_696_;
v___y_687_ = v___x_701_;
goto v___jp_684_;
}
}
v___jp_702_:
{
lean_object* v___x_704_; lean_object* v___x_705_; uint8_t v___x_706_; 
v___x_704_ = lean_nat_land(v___x_680_, v_ifTrue_672_);
v___x_705_ = lean_unsigned_to_nat(0u);
v___x_706_ = lean_nat_dec_eq(v___x_704_, v___x_705_);
lean_dec(v___x_704_);
if (v___x_706_ == 0)
{
uint8_t v___x_707_; 
v___x_707_ = 1;
v___y_695_ = v___y_703_;
v___y_696_ = v___x_707_;
goto v___jp_694_;
}
else
{
uint8_t v___x_708_; 
v___x_708_ = 0;
v___y_695_ = v___y_703_;
v___y_696_ = v___x_708_;
goto v___jp_694_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___redArg___boxed(lean_object* v_state_715_, lean_object* v_cond_716_, lean_object* v_ifTrue_717_, lean_object* v_ifFalse_718_, lean_object* v_idx_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___redArg(v_state_715_, v_cond_716_, v_ifTrue_717_, v_ifFalse_718_, v_idx_719_);
lean_dec(v_ifFalse_718_);
lean_dec(v_ifTrue_717_);
lean_dec(v_cond_716_);
return v_res_720_;
}
}
lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte(lean_object* v_00_u03b1_721_, lean_object* v_inst_722_, lean_object* v_inst_723_, lean_object* v_aig_724_, lean_object* v_state_725_, lean_object* v_cond_726_, lean_object* v_ifTrue_727_, lean_object* v_ifFalse_728_, lean_object* v_idx_729_, lean_object* v_hcb_730_, lean_object* v_htb_731_, lean_object* v_hfb_732_, lean_object* v_h_733_, lean_object* v_hltc_734_, lean_object* v_hltt_735_, lean_object* v_hltf_736_, lean_object* v_hc_737_, lean_object* v_ht_738_, lean_object* v_hf_739_, lean_object* v_hdenote_740_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___redArg(v_state_725_, v_cond_726_, v_ifTrue_727_, v_ifFalse_728_, v_idx_729_);
return v___x_741_;
}
}
LEAN_EXPORT void l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_722_ = stack[1].m_obj;
lean_object* v_inst_723_ = stack[2].m_obj;
lean_object* v_aig_724_ = stack[3].m_obj;
lean_object* v_state_725_ = stack[4].m_obj;
lean_object* v_cond_726_ = stack[5].m_obj;
lean_object* v_ifTrue_727_ = stack[6].m_obj;
lean_object* v_ifFalse_728_ = stack[7].m_obj;
lean_object* v_idx_729_ = stack[8].m_obj;
lean_object* v_res_742_;
v_res_742_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte(lean_box(0), v_inst_722_, v_inst_723_, v_aig_724_, v_state_725_, v_cond_726_, v_ifTrue_727_, v_ifFalse_728_, v_idx_729_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
stack->m_obj
 = v_res_742_;
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___boxed(lean_object** _args){
lean_object* v_00_u03b1_743_ = _args[0];
lean_object* v_inst_744_ = _args[1];
lean_object* v_inst_745_ = _args[2];
lean_object* v_aig_746_ = _args[3];
lean_object* v_state_747_ = _args[4];
lean_object* v_cond_748_ = _args[5];
lean_object* v_ifTrue_749_ = _args[6];
lean_object* v_ifFalse_750_ = _args[7];
lean_object* v_idx_751_ = _args[8];
lean_object* v_hcb_752_ = _args[9];
lean_object* v_htb_753_ = _args[10];
lean_object* v_hfb_754_ = _args[11];
lean_object* v_h_755_ = _args[12];
lean_object* v_hltc_756_ = _args[13];
lean_object* v_hltt_757_ = _args[14];
lean_object* v_hltf_758_ = _args[15];
lean_object* v_hc_759_ = _args[16];
lean_object* v_ht_760_ = _args[17];
lean_object* v_hf_761_ = _args[18];
lean_object* v_hdenote_762_ = _args[19];
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte(v_00_u03b1_743_, v_inst_744_, v_inst_745_, v_aig_746_, v_state_747_, v_cond_748_, v_ifTrue_749_, v_ifFalse_750_, v_idx_751_, v_hcb_752_, v_htb_753_, v_hfb_754_, v_h_755_, v_hltc_756_, v_hltt_757_, v_hltf_758_, v_hc_759_, v_ht_760_, v_hf_761_, v_hdenote_762_);
lean_dec(v_ifFalse_750_);
lean_dec(v_ifTrue_749_);
lean_dec(v_cond_748_);
lean_dec_ref(v_aig_746_);
lean_dec_ref(v_inst_745_);
lean_dec_ref(v_inst_744_);
return v_res_763_;
}
}
uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg(lean_object* v_assign_764_, lean_object* v_state_765_){
_start:
{
lean_object* v_cnf_766_; uint8_t v___x_767_; 
v_cnf_766_ = lean_ctor_get(v_state_765_, 0);
v___x_767_ = l_Std_Sat_CNF_eval___redArg(v_assign_764_, v_cnf_766_);
return v___x_767_;
}
}
LEAN_EXPORT void l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_assign_764_ = stack[0].m_obj;
lean_object* v_state_765_ = stack[1].m_obj;
uint8_t v_res_768_;
v_res_768_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg(v_assign_764_, v_state_765_);
stack->m_num = v_res_768_;
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg___boxed(lean_object* v_assign_769_, lean_object* v_state_770_){
_start:
{
uint8_t v_res_771_; lean_object* v_r_772_; 
v_res_771_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg(v_assign_769_, v_state_770_);
lean_dec_ref(v_state_770_);
v_r_772_ = lean_box(v_res_771_);
return v_r_772_;
}
}
uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval(lean_object* v_00_u03b1_773_, lean_object* v_inst_774_, lean_object* v_inst_775_, lean_object* v_aig_776_, lean_object* v_assign_777_, lean_object* v_state_778_){
_start:
{
uint8_t v___x_779_; 
v___x_779_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg(v_assign_777_, v_state_778_);
return v___x_779_;
}
}
LEAN_EXPORT void l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_774_ = stack[1].m_obj;
lean_object* v_inst_775_ = stack[2].m_obj;
lean_object* v_aig_776_ = stack[3].m_obj;
lean_object* v_assign_777_ = stack[4].m_obj;
lean_object* v_state_778_ = stack[5].m_obj;
uint8_t v_res_780_;
v_res_780_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval(lean_box(0), v_inst_774_, v_inst_775_, v_aig_776_, v_assign_777_, v_state_778_);
stack->m_num = v_res_780_;
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___boxed(lean_object* v_00_u03b1_781_, lean_object* v_inst_782_, lean_object* v_inst_783_, lean_object* v_aig_784_, lean_object* v_assign_785_, lean_object* v_state_786_){
_start:
{
uint8_t v_res_787_; lean_object* v_r_788_; 
v_res_787_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval(v_00_u03b1_781_, v_inst_782_, v_inst_783_, v_aig_784_, v_assign_785_, v_state_786_);
lean_dec_ref(v_state_786_);
lean_dec_ref(v_aig_784_);
lean_dec_ref(v_inst_783_);
lean_dec_ref(v_inst_782_);
v_r_788_ = lean_box(v_res_787_);
return v_r_788_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg(lean_object* v_l0_789_, lean_object* v_l1_790_, lean_object* v_r0_791_, lean_object* v_r1_792_){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_793_ = lean_unsigned_to_nat(1u);
v___x_794_ = lean_nat_lxor(v_r0_791_, v___x_793_);
v___x_795_ = lean_nat_dec_eq(v_l0_789_, v___x_794_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; uint8_t v___x_797_; 
v___x_796_ = lean_nat_lxor(v_r1_792_, v___x_793_);
v___x_797_ = lean_nat_dec_eq(v_l0_789_, v___x_796_);
if (v___x_797_ == 0)
{
uint8_t v___x_798_; 
v___x_798_ = lean_nat_dec_eq(v_l1_790_, v___x_794_);
if (v___x_798_ == 0)
{
uint8_t v___x_799_; 
v___x_799_ = lean_nat_dec_eq(v_l1_790_, v___x_796_);
lean_dec(v___x_796_);
if (v___x_799_ == 0)
{
lean_object* v___x_800_; 
lean_dec(v___x_794_);
lean_dec(v_l1_790_);
lean_dec(v_l0_789_);
v___x_800_ = lean_box(0);
return v___x_800_;
}
else
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_801_ = lean_nat_lxor(v_l0_789_, v___x_793_);
lean_dec(v_l0_789_);
v___x_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
lean_ctor_set(v___x_802_, 1, v___x_794_);
v___x_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_803_, 0, v_l1_790_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
v___x_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
return v___x_804_;
}
}
else
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
lean_dec(v___x_794_);
v___x_805_ = lean_nat_lxor(v_l0_789_, v___x_793_);
lean_dec(v_l0_789_);
v___x_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
lean_ctor_set(v___x_806_, 1, v___x_796_);
v___x_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_807_, 0, v_l1_790_);
lean_ctor_set(v___x_807_, 1, v___x_806_);
v___x_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
return v___x_808_;
}
}
else
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
lean_dec(v___x_796_);
v___x_809_ = lean_nat_lxor(v_l1_790_, v___x_793_);
lean_dec(v_l1_790_);
v___x_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
lean_ctor_set(v___x_810_, 1, v___x_794_);
v___x_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_811_, 0, v_l0_789_);
lean_ctor_set(v___x_811_, 1, v___x_810_);
v___x_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
return v___x_812_;
}
}
else
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
lean_dec(v___x_794_);
v___x_813_ = lean_nat_lxor(v_l1_790_, v___x_793_);
lean_dec(v_l1_790_);
v___x_814_ = lean_nat_lxor(v_r1_792_, v___x_793_);
v___x_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_813_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
v___x_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_816_, 0, v_l0_789_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
return v___x_817_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg___boxed(lean_object* v_l0_818_, lean_object* v_l1_819_, lean_object* v_r0_820_, lean_object* v_r1_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg(v_l0_818_, v_l1_819_, v_r0_820_, v_r1_821_);
lean_dec(v_r1_821_);
lean_dec(v_r0_820_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go(lean_object* v_l_823_, lean_object* v_r_824_, lean_object* v_l0_825_, lean_object* v_l1_826_, lean_object* v_r0_827_, lean_object* v_r1_828_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg(v_l0_825_, v_l1_826_, v_r0_827_, v_r1_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___boxed(lean_object* v_l_830_, lean_object* v_r_831_, lean_object* v_l0_832_, lean_object* v_l1_833_, lean_object* v_r0_834_, lean_object* v_r1_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go(v_l_830_, v_r_831_, v_l0_832_, v_l1_833_, v_r0_834_, v_r1_835_);
lean_dec(v_r1_835_);
lean_dec(v_r0_834_);
lean_dec(v_r_831_);
lean_dec(v_l_830_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___redArg(lean_object* v_aig_837_, lean_object* v_root_838_){
_start:
{
lean_object* v_decls_839_; lean_object* v___x_840_; 
v_decls_839_ = lean_ctor_get(v_aig_837_, 0);
v___x_840_ = lean_array_fget_borrowed(v_decls_839_, v_root_838_);
if (lean_obj_tag(v___x_840_) == 2)
{
lean_object* v_l_841_; lean_object* v_r_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; uint8_t v___x_846_; 
v_l_841_ = lean_ctor_get(v___x_840_, 0);
v_r_842_ = lean_ctor_get(v___x_840_, 1);
v___x_843_ = lean_unsigned_to_nat(1u);
v___x_844_ = lean_nat_land(v___x_843_, v_l_841_);
v___x_845_ = lean_unsigned_to_nat(0u);
v___x_846_ = lean_nat_dec_eq(v___x_844_, v___x_845_);
lean_dec(v___x_844_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; uint8_t v___x_848_; 
v___x_847_ = lean_nat_land(v___x_843_, v_r_842_);
v___x_848_ = lean_nat_dec_eq(v___x_847_, v___x_845_);
lean_dec(v___x_847_);
if (v___x_848_ == 0)
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = lean_nat_shiftr(v_l_841_, v___x_843_);
v___x_850_ = lean_array_fget_borrowed(v_decls_839_, v___x_849_);
lean_dec(v___x_849_);
if (lean_obj_tag(v___x_850_) == 2)
{
lean_object* v_l_851_; lean_object* v_r_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v_l_851_ = lean_ctor_get(v___x_850_, 0);
v_r_852_ = lean_ctor_get(v___x_850_, 1);
v___x_853_ = lean_nat_shiftr(v_r_842_, v___x_843_);
v___x_854_ = lean_array_fget_borrowed(v_decls_839_, v___x_853_);
lean_dec(v___x_853_);
if (lean_obj_tag(v___x_854_) == 2)
{
lean_object* v_l_855_; lean_object* v_r_856_; lean_object* v___x_857_; 
v_l_855_ = lean_ctor_get(v___x_854_, 0);
v_r_856_ = lean_ctor_get(v___x_854_, 1);
lean_inc(v_r_852_);
lean_inc(v_l_851_);
v___x_857_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg(v_l_851_, v_r_852_, v_l_855_, v_r_856_);
return v___x_857_;
}
else
{
lean_object* v___x_858_; 
v___x_858_ = lean_box(0);
return v___x_858_;
}
}
else
{
lean_object* v___x_859_; 
v___x_859_ = lean_box(0);
return v___x_859_;
}
}
else
{
lean_object* v___x_860_; 
v___x_860_ = lean_box(0);
return v___x_860_;
}
}
else
{
lean_object* v___x_861_; 
v___x_861_ = lean_box(0);
return v___x_861_;
}
}
else
{
lean_object* v___x_862_; 
v___x_862_ = lean_box(0);
return v___x_862_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___redArg___boxed(lean_object* v_aig_863_, lean_object* v_root_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___redArg(v_aig_863_, v_root_864_);
lean_dec(v_root_864_);
lean_dec_ref(v_aig_863_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte(lean_object* v_00_u03b1_866_, lean_object* v_inst_867_, lean_object* v_inst_868_, lean_object* v_aig_869_, lean_object* v_root_870_, lean_object* v_h_871_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___redArg(v_aig_869_, v_root_870_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___boxed(lean_object* v_00_u03b1_873_, lean_object* v_inst_874_, lean_object* v_inst_875_, lean_object* v_aig_876_, lean_object* v_root_877_, lean_object* v_h_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte(v_00_u03b1_873_, v_inst_874_, v_inst_875_, v_aig_876_, v_root_877_, v_h_878_);
lean_dec(v_root_877_);
lean_dec_ref(v_aig_876_);
lean_dec_ref(v_inst_875_);
lean_dec_ref(v_inst_874_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_match__4_splitter___redArg(lean_object* v_x_880_, lean_object* v_h__1_881_, lean_object* v_h__2_882_){
_start:
{
if (lean_obj_tag(v_x_880_) == 2)
{
lean_object* v_l_883_; lean_object* v_r_884_; lean_object* v___x_885_; 
lean_dec(v_h__2_882_);
v_l_883_ = lean_ctor_get(v_x_880_, 0);
lean_inc(v_l_883_);
v_r_884_ = lean_ctor_get(v_x_880_, 1);
lean_inc(v_r_884_);
lean_dec_ref_known(v_x_880_, 2);
v___x_885_ = lean_apply_3(v_h__1_881_, v_l_883_, v_r_884_, lean_box(0));
return v___x_885_;
}
else
{
lean_object* v___x_886_; 
lean_dec(v_h__1_881_);
v___x_886_ = lean_apply_3(v_h__2_882_, v_x_880_, lean_box(0), lean_box(0));
return v___x_886_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_match__4_splitter(lean_object* v_00_u03b1_887_, lean_object* v_motive_888_, lean_object* v_x_889_, lean_object* v_h__1_890_, lean_object* v_h__2_891_){
_start:
{
if (lean_obj_tag(v_x_889_) == 2)
{
lean_object* v_l_892_; lean_object* v_r_893_; lean_object* v___x_894_; 
lean_dec(v_h__2_891_);
v_l_892_ = lean_ctor_get(v_x_889_, 0);
lean_inc(v_l_892_);
v_r_893_ = lean_ctor_get(v_x_889_, 1);
lean_inc(v_r_893_);
lean_dec_ref_known(v_x_889_, 2);
v___x_894_ = lean_apply_3(v_h__1_890_, v_l_892_, v_r_893_, lean_box(0));
return v___x_894_;
}
else
{
lean_object* v___x_895_; 
lean_dec(v_h__1_890_);
v___x_895_ = lean_apply_3(v_h__2_891_, v_x_889_, lean_box(0), lean_box(0));
return v___x_895_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_match__1_splitter___redArg(lean_object* v_x_896_, lean_object* v_x_897_, lean_object* v_h__1_898_, lean_object* v_h__2_899_){
_start:
{
if (lean_obj_tag(v_x_896_) == 2)
{
if (lean_obj_tag(v_x_897_) == 2)
{
lean_object* v_l_900_; lean_object* v_r_901_; lean_object* v_l_902_; lean_object* v_r_903_; lean_object* v___x_904_; 
lean_dec(v_h__2_899_);
v_l_900_ = lean_ctor_get(v_x_896_, 0);
lean_inc(v_l_900_);
v_r_901_ = lean_ctor_get(v_x_896_, 1);
lean_inc(v_r_901_);
lean_dec_ref_known(v_x_896_, 2);
v_l_902_ = lean_ctor_get(v_x_897_, 0);
lean_inc(v_l_902_);
v_r_903_ = lean_ctor_get(v_x_897_, 1);
lean_inc(v_r_903_);
lean_dec_ref_known(v_x_897_, 2);
v___x_904_ = lean_apply_6(v_h__1_898_, v_l_900_, v_r_901_, v_l_902_, v_r_903_, lean_box(0), lean_box(0));
return v___x_904_;
}
else
{
lean_object* v___x_905_; 
lean_dec(v_h__1_898_);
v___x_905_ = lean_apply_5(v_h__2_899_, v_x_896_, v_x_897_, lean_box(0), lean_box(0), lean_box(0));
return v___x_905_;
}
}
else
{
lean_object* v___x_906_; 
lean_dec(v_h__1_898_);
v___x_906_ = lean_apply_5(v_h__2_899_, v_x_896_, v_x_897_, lean_box(0), lean_box(0), lean_box(0));
return v___x_906_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_match__1_splitter(lean_object* v_00_u03b1_907_, lean_object* v_motive_908_, lean_object* v_x_909_, lean_object* v_x_910_, lean_object* v_h__1_911_, lean_object* v_h__2_912_){
_start:
{
if (lean_obj_tag(v_x_909_) == 2)
{
if (lean_obj_tag(v_x_910_) == 2)
{
lean_object* v_l_913_; lean_object* v_r_914_; lean_object* v_l_915_; lean_object* v_r_916_; lean_object* v___x_917_; 
lean_dec(v_h__2_912_);
v_l_913_ = lean_ctor_get(v_x_909_, 0);
lean_inc(v_l_913_);
v_r_914_ = lean_ctor_get(v_x_909_, 1);
lean_inc(v_r_914_);
lean_dec_ref_known(v_x_909_, 2);
v_l_915_ = lean_ctor_get(v_x_910_, 0);
lean_inc(v_l_915_);
v_r_916_ = lean_ctor_get(v_x_910_, 1);
lean_inc(v_r_916_);
lean_dec_ref_known(v_x_910_, 2);
v___x_917_ = lean_apply_6(v_h__1_911_, v_l_913_, v_r_914_, v_l_915_, v_r_916_, lean_box(0), lean_box(0));
return v___x_917_;
}
else
{
lean_object* v___x_918_; 
lean_dec(v_h__1_911_);
v___x_918_ = lean_apply_5(v_h__2_912_, v_x_909_, v_x_910_, lean_box(0), lean_box(0), lean_box(0));
return v___x_918_;
}
}
else
{
lean_object* v___x_919_; 
lean_dec(v_h__1_911_);
v___x_919_ = lean_apply_5(v_h__2_912_, v_x_909_, v_x_910_, lean_box(0), lean_box(0), lean_box(0));
return v___x_919_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___redArg(lean_object* v_aig_920_, lean_object* v_upper_921_, lean_object* v_state_922_){
_start:
{
lean_object* v_cache_923_; lean_object* v___x_924_; uint8_t v___x_925_; 
v_cache_923_ = lean_ctor_get(v_state_922_, 1);
v___x_924_ = lean_array_fget_borrowed(v_cache_923_, v_upper_921_);
v___x_925_ = lean_unbox(v___x_924_);
if (v___x_925_ == 0)
{
lean_object* v_decls_926_; lean_object* v_decl_927_; 
v_decls_926_ = lean_ctor_get(v_aig_920_, 0);
v_decl_927_ = lean_array_fget_borrowed(v_decls_926_, v_upper_921_);
switch(lean_obj_tag(v_decl_927_))
{
case 0:
{
lean_object* v___x_928_; 
v___x_928_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___redArg(v_state_922_, v_upper_921_);
return v___x_928_;
}
case 1:
{
lean_object* v___x_929_; 
v___x_929_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg(v_state_922_, v_upper_921_);
lean_dec(v_upper_921_);
return v___x_929_;
}
default: 
{
lean_object* v_l_930_; lean_object* v_r_931_; lean_object* v___x_932_; 
v_l_930_ = lean_ctor_get(v_decl_927_, 0);
v_r_931_ = lean_ctor_get(v_decl_927_, 1);
v___x_932_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___redArg(v_aig_920_, v_upper_921_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v_val_935_; lean_object* v___x_936_; lean_object* v_val_937_; lean_object* v_val_938_; 
v___x_933_ = lean_unsigned_to_nat(1u);
v___x_934_ = lean_nat_shiftr(v_l_930_, v___x_933_);
v_val_935_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___redArg(v_aig_920_, v___x_934_, v_state_922_);
v___x_936_ = lean_nat_shiftr(v_r_931_, v___x_933_);
v_val_937_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___redArg(v_aig_920_, v___x_936_, v_val_935_);
v_val_938_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg(v_l_930_, v_r_931_, v_val_937_, v_upper_921_);
return v_val_938_;
}
else
{
lean_object* v_val_939_; lean_object* v_snd_940_; lean_object* v_fst_941_; lean_object* v_fst_942_; lean_object* v_snd_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v_val_946_; lean_object* v___x_947_; lean_object* v_val_948_; lean_object* v___x_949_; lean_object* v_val_950_; lean_object* v_val_951_; 
v_val_939_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_val_939_);
lean_dec_ref_known(v___x_932_, 1);
v_snd_940_ = lean_ctor_get(v_val_939_, 1);
lean_inc(v_snd_940_);
v_fst_941_ = lean_ctor_get(v_val_939_, 0);
lean_inc(v_fst_941_);
lean_dec(v_val_939_);
v_fst_942_ = lean_ctor_get(v_snd_940_, 0);
lean_inc(v_fst_942_);
v_snd_943_ = lean_ctor_get(v_snd_940_, 1);
lean_inc(v_snd_943_);
lean_dec(v_snd_940_);
v___x_944_ = lean_unsigned_to_nat(1u);
v___x_945_ = lean_nat_shiftr(v_fst_941_, v___x_944_);
v_val_946_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___redArg(v_aig_920_, v___x_945_, v_state_922_);
v___x_947_ = lean_nat_shiftr(v_fst_942_, v___x_944_);
v_val_948_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___redArg(v_aig_920_, v___x_947_, v_val_946_);
v___x_949_ = lean_nat_shiftr(v_snd_943_, v___x_944_);
v_val_950_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___redArg(v_aig_920_, v___x_949_, v_val_948_);
v_val_951_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___redArg(v_val_950_, v_fst_941_, v_fst_942_, v_snd_943_, v_upper_921_);
lean_dec(v_snd_943_);
lean_dec(v_fst_942_);
lean_dec(v_fst_941_);
return v_val_951_;
}
}
}
}
else
{
lean_dec(v_upper_921_);
return v_state_922_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___redArg___boxed(lean_object* v_aig_952_, lean_object* v_upper_953_, lean_object* v_state_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___redArg(v_aig_952_, v_upper_953_, v_state_954_);
lean_dec_ref(v_aig_952_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go(lean_object* v_00_u03b1_956_, lean_object* v_inst_957_, lean_object* v_inst_958_, lean_object* v_aig_959_, lean_object* v_upper_960_, lean_object* v_h_961_, lean_object* v_state_962_){
_start:
{
lean_object* v___x_963_; 
v___x_963_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___redArg(v_aig_959_, v_upper_960_, v_state_962_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___boxed(lean_object* v_00_u03b1_964_, lean_object* v_inst_965_, lean_object* v_inst_966_, lean_object* v_aig_967_, lean_object* v_upper_968_, lean_object* v_h_969_, lean_object* v_state_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go(v_00_u03b1_964_, v_inst_965_, v_inst_966_, v_aig_967_, v_upper_968_, v_h_969_, v_state_970_);
lean_dec_ref(v_aig_967_);
lean_dec_ref(v_inst_966_);
lean_dec_ref(v_inst_965_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go_match__103_splitter___redArg(lean_object* v_decl_972_, lean_object* v_h__1_973_, lean_object* v_h__2_974_, lean_object* v_h__3_975_){
_start:
{
switch(lean_obj_tag(v_decl_972_))
{
case 0:
{
lean_object* v___x_976_; 
lean_dec(v_h__3_975_);
lean_dec(v_h__2_974_);
v___x_976_ = lean_apply_1(v_h__1_973_, lean_box(0));
return v___x_976_;
}
case 1:
{
lean_object* v_idx_977_; lean_object* v___x_978_; 
lean_dec(v_h__3_975_);
lean_dec(v_h__1_973_);
v_idx_977_ = lean_ctor_get(v_decl_972_, 0);
lean_inc(v_idx_977_);
lean_dec_ref_known(v_decl_972_, 1);
v___x_978_ = lean_apply_2(v_h__2_974_, v_idx_977_, lean_box(0));
return v___x_978_;
}
default: 
{
lean_object* v_l_979_; lean_object* v_r_980_; lean_object* v___x_981_; 
lean_dec(v_h__2_974_);
lean_dec(v_h__1_973_);
v_l_979_ = lean_ctor_get(v_decl_972_, 0);
lean_inc(v_l_979_);
v_r_980_ = lean_ctor_get(v_decl_972_, 1);
lean_inc(v_r_980_);
lean_dec_ref_known(v_decl_972_, 2);
v___x_981_ = lean_apply_3(v_h__3_975_, v_l_979_, v_r_980_, lean_box(0));
return v___x_981_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go_match__103_splitter(lean_object* v_00_u03b1_982_, lean_object* v_motive_983_, lean_object* v_decl_984_, lean_object* v_h__1_985_, lean_object* v_h__2_986_, lean_object* v_h__3_987_){
_start:
{
switch(lean_obj_tag(v_decl_984_))
{
case 0:
{
lean_object* v___x_988_; 
lean_dec(v_h__3_987_);
lean_dec(v_h__2_986_);
v___x_988_ = lean_apply_1(v_h__1_985_, lean_box(0));
return v___x_988_;
}
case 1:
{
lean_object* v_idx_989_; lean_object* v___x_990_; 
lean_dec(v_h__3_987_);
lean_dec(v_h__1_985_);
v_idx_989_ = lean_ctor_get(v_decl_984_, 0);
lean_inc(v_idx_989_);
lean_dec_ref_known(v_decl_984_, 1);
v___x_990_ = lean_apply_2(v_h__2_986_, v_idx_989_, lean_box(0));
return v___x_990_;
}
default: 
{
lean_object* v_l_991_; lean_object* v_r_992_; lean_object* v___x_993_; 
lean_dec(v_h__2_986_);
lean_dec(v_h__1_985_);
v_l_991_ = lean_ctor_get(v_decl_984_, 0);
lean_inc(v_l_991_);
v_r_992_ = lean_ctor_get(v_decl_984_, 1);
lean_inc(v_r_992_);
lean_dec_ref_known(v_decl_984_, 2);
v___x_993_ = lean_apply_3(v_h__3_987_, v_l_991_, v_r_992_, lean_box(0));
return v___x_993_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go_match__81_splitter___redArg(lean_object* v_x_994_, lean_object* v_h__1_995_, lean_object* v_h__2_996_){
_start:
{
if (lean_obj_tag(v_x_994_) == 0)
{
lean_object* v___x_997_; 
lean_dec(v_h__1_995_);
v___x_997_ = lean_apply_1(v_h__2_996_, lean_box(0));
return v___x_997_;
}
else
{
lean_object* v_val_998_; lean_object* v_snd_999_; lean_object* v_fst_1000_; lean_object* v_fst_1001_; lean_object* v_snd_1002_; lean_object* v___x_1003_; 
lean_dec(v_h__2_996_);
v_val_998_ = lean_ctor_get(v_x_994_, 0);
lean_inc(v_val_998_);
lean_dec_ref_known(v_x_994_, 1);
v_snd_999_ = lean_ctor_get(v_val_998_, 1);
lean_inc(v_snd_999_);
v_fst_1000_ = lean_ctor_get(v_val_998_, 0);
lean_inc(v_fst_1000_);
lean_dec(v_val_998_);
v_fst_1001_ = lean_ctor_get(v_snd_999_, 0);
lean_inc(v_fst_1001_);
v_snd_1002_ = lean_ctor_get(v_snd_999_, 1);
lean_inc(v_snd_1002_);
lean_dec(v_snd_999_);
v___x_1003_ = lean_apply_4(v_h__1_995_, v_fst_1000_, v_fst_1001_, v_snd_1002_, lean_box(0));
return v___x_1003_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go_match__81_splitter(lean_object* v_motive_1004_, lean_object* v_x_1005_, lean_object* v_h__1_1006_, lean_object* v_h__2_1007_){
_start:
{
if (lean_obj_tag(v_x_1005_) == 0)
{
lean_object* v___x_1008_; 
lean_dec(v_h__1_1006_);
v___x_1008_ = lean_apply_1(v_h__2_1007_, lean_box(0));
return v___x_1008_;
}
else
{
lean_object* v_val_1009_; lean_object* v_snd_1010_; lean_object* v_fst_1011_; lean_object* v_fst_1012_; lean_object* v_snd_1013_; lean_object* v___x_1014_; 
lean_dec(v_h__2_1007_);
v_val_1009_ = lean_ctor_get(v_x_1005_, 0);
lean_inc(v_val_1009_);
lean_dec_ref_known(v_x_1005_, 1);
v_snd_1010_ = lean_ctor_get(v_val_1009_, 1);
lean_inc(v_snd_1010_);
v_fst_1011_ = lean_ctor_get(v_val_1009_, 0);
lean_inc(v_fst_1011_);
lean_dec(v_val_1009_);
v_fst_1012_ = lean_ctor_get(v_snd_1010_, 0);
lean_inc(v_fst_1012_);
v_snd_1013_ = lean_ctor_get(v_snd_1010_, 1);
lean_inc(v_snd_1013_);
lean_dec(v_snd_1010_);
v___x_1014_ = lean_apply_4(v_h__1_1006_, v_fst_1011_, v_fst_1012_, v_snd_1013_, lean_box(0));
return v___x_1014_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__52_splitter___redArg(lean_object* v_x_1015_, lean_object* v_h__1_1016_){
_start:
{
lean_object* v___x_1017_; 
v___x_1017_ = lean_apply_2(v_h__1_1016_, v_x_1015_, lean_box(0));
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__52_splitter(lean_object* v_00_u03b1_1018_, lean_object* v_inst_1019_, lean_object* v_inst_1020_, lean_object* v_aig_1021_, lean_object* v_upper_1022_, lean_object* v_h_1023_, lean_object* v_state_1024_, lean_object* v_cond_1025_, lean_object* v_ifTrue_1026_, lean_object* v_ifFalse_1027_, lean_object* v_hltc_1028_, lean_object* v_motive_1029_, lean_object* v_x_1030_, lean_object* v_h__1_1031_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = lean_apply_2(v_h__1_1031_, v_x_1030_, lean_box(0));
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__52_splitter___boxed(lean_object* v_00_u03b1_1033_, lean_object* v_inst_1034_, lean_object* v_inst_1035_, lean_object* v_aig_1036_, lean_object* v_upper_1037_, lean_object* v_h_1038_, lean_object* v_state_1039_, lean_object* v_cond_1040_, lean_object* v_ifTrue_1041_, lean_object* v_ifFalse_1042_, lean_object* v_hltc_1043_, lean_object* v_motive_1044_, lean_object* v_x_1045_, lean_object* v_h__1_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__52_splitter(v_00_u03b1_1033_, v_inst_1034_, v_inst_1035_, v_aig_1036_, v_upper_1037_, v_h_1038_, v_state_1039_, v_cond_1040_, v_ifTrue_1041_, v_ifFalse_1042_, v_hltc_1043_, v_motive_1044_, v_x_1045_, v_h__1_1046_);
lean_dec(v_ifFalse_1042_);
lean_dec(v_ifTrue_1041_);
lean_dec(v_cond_1040_);
lean_dec_ref(v_state_1039_);
lean_dec(v_upper_1037_);
lean_dec_ref(v_aig_1036_);
lean_dec_ref(v_inst_1035_);
lean_dec_ref(v_inst_1034_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__50_splitter___redArg(lean_object* v_x_1048_, lean_object* v_h__1_1049_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = lean_apply_2(v_h__1_1049_, v_x_1048_, lean_box(0));
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__50_splitter(lean_object* v_00_u03b1_1051_, lean_object* v_inst_1052_, lean_object* v_inst_1053_, lean_object* v_aig_1054_, lean_object* v_upper_1055_, lean_object* v_h_1056_, lean_object* v_cond_1057_, lean_object* v_ifTrue_1058_, lean_object* v_ifFalse_1059_, lean_object* v_hltt_1060_, lean_object* v_cstate_1061_, lean_object* v_motive_1062_, lean_object* v_x_1063_, lean_object* v_h__1_1064_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = lean_apply_2(v_h__1_1064_, v_x_1063_, lean_box(0));
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__50_splitter___boxed(lean_object* v_00_u03b1_1066_, lean_object* v_inst_1067_, lean_object* v_inst_1068_, lean_object* v_aig_1069_, lean_object* v_upper_1070_, lean_object* v_h_1071_, lean_object* v_cond_1072_, lean_object* v_ifTrue_1073_, lean_object* v_ifFalse_1074_, lean_object* v_hltt_1075_, lean_object* v_cstate_1076_, lean_object* v_motive_1077_, lean_object* v_x_1078_, lean_object* v_h__1_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__50_splitter(v_00_u03b1_1066_, v_inst_1067_, v_inst_1068_, v_aig_1069_, v_upper_1070_, v_h_1071_, v_cond_1072_, v_ifTrue_1073_, v_ifFalse_1074_, v_hltt_1075_, v_cstate_1076_, v_motive_1077_, v_x_1078_, v_h__1_1079_);
lean_dec_ref(v_cstate_1076_);
lean_dec(v_ifFalse_1074_);
lean_dec(v_ifTrue_1073_);
lean_dec(v_cond_1072_);
lean_dec(v_upper_1070_);
lean_dec_ref(v_aig_1069_);
lean_dec_ref(v_inst_1068_);
lean_dec_ref(v_inst_1067_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__48_splitter___redArg(lean_object* v_x_1081_, lean_object* v_h__1_1082_){
_start:
{
lean_object* v___x_1083_; 
v___x_1083_ = lean_apply_2(v_h__1_1082_, v_x_1081_, lean_box(0));
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__48_splitter(lean_object* v_00_u03b1_1084_, lean_object* v_inst_1085_, lean_object* v_inst_1086_, lean_object* v_aig_1087_, lean_object* v_upper_1088_, lean_object* v_h_1089_, lean_object* v_cond_1090_, lean_object* v_ifTrue_1091_, lean_object* v_ifFalse_1092_, lean_object* v_hltf_1093_, lean_object* v_tstate_1094_, lean_object* v_motive_1095_, lean_object* v_x_1096_, lean_object* v_h__1_1097_){
_start:
{
lean_object* v___x_1098_; 
v___x_1098_ = lean_apply_2(v_h__1_1097_, v_x_1096_, lean_box(0));
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__48_splitter___boxed(lean_object* v_00_u03b1_1099_, lean_object* v_inst_1100_, lean_object* v_inst_1101_, lean_object* v_aig_1102_, lean_object* v_upper_1103_, lean_object* v_h_1104_, lean_object* v_cond_1105_, lean_object* v_ifTrue_1106_, lean_object* v_ifFalse_1107_, lean_object* v_hltf_1108_, lean_object* v_tstate_1109_, lean_object* v_motive_1110_, lean_object* v_x_1111_, lean_object* v_h__1_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__48_splitter(v_00_u03b1_1099_, v_inst_1100_, v_inst_1101_, v_aig_1102_, v_upper_1103_, v_h_1104_, v_cond_1105_, v_ifTrue_1106_, v_ifFalse_1107_, v_hltf_1108_, v_tstate_1109_, v_motive_1110_, v_x_1111_, v_h__1_1112_);
lean_dec_ref(v_tstate_1109_);
lean_dec(v_ifFalse_1107_);
lean_dec(v_ifTrue_1106_);
lean_dec(v_cond_1105_);
lean_dec(v_upper_1103_);
lean_dec_ref(v_aig_1102_);
lean_dec_ref(v_inst_1101_);
lean_dec_ref(v_inst_1100_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__45_splitter___redArg(lean_object* v_x_1114_, lean_object* v_h__1_1115_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = lean_apply_2(v_h__1_1115_, v_x_1114_, lean_box(0));
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__45_splitter(lean_object* v_00_u03b1_1117_, lean_object* v_inst_1118_, lean_object* v_inst_1119_, lean_object* v_aig_1120_, lean_object* v_upper_1121_, lean_object* v_h_1122_, lean_object* v_fstate_1123_, lean_object* v_motive_1124_, lean_object* v_x_1125_, lean_object* v_h__1_1126_){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = lean_apply_2(v_h__1_1126_, v_x_1125_, lean_box(0));
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__45_splitter___boxed(lean_object* v_00_u03b1_1128_, lean_object* v_inst_1129_, lean_object* v_inst_1130_, lean_object* v_aig_1131_, lean_object* v_upper_1132_, lean_object* v_h_1133_, lean_object* v_fstate_1134_, lean_object* v_motive_1135_, lean_object* v_x_1136_, lean_object* v_h__1_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__45_splitter(v_00_u03b1_1128_, v_inst_1129_, v_inst_1130_, v_aig_1131_, v_upper_1132_, v_h_1133_, v_fstate_1134_, v_motive_1135_, v_x_1136_, v_h__1_1137_);
lean_dec_ref(v_fstate_1134_);
lean_dec(v_upper_1132_);
lean_dec_ref(v_aig_1131_);
lean_dec_ref(v_inst_1130_);
lean_dec_ref(v_inst_1129_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__56_splitter___redArg(lean_object* v_x_1139_, lean_object* v_h__1_1140_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = lean_apply_2(v_h__1_1140_, v_x_1139_, lean_box(0));
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__56_splitter(lean_object* v_00_u03b1_1142_, lean_object* v_inst_1143_, lean_object* v_inst_1144_, lean_object* v_aig_1145_, lean_object* v_upper_1146_, lean_object* v_h_1147_, lean_object* v_state_1148_, lean_object* v_lhs_1149_, lean_object* v_rhs_1150_, lean_object* v_this_1151_, lean_object* v_motive_1152_, lean_object* v_x_1153_, lean_object* v_h__1_1154_){
_start:
{
lean_object* v___x_1155_; 
v___x_1155_ = lean_apply_2(v_h__1_1154_, v_x_1153_, lean_box(0));
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__56_splitter___boxed(lean_object* v_00_u03b1_1156_, lean_object* v_inst_1157_, lean_object* v_inst_1158_, lean_object* v_aig_1159_, lean_object* v_upper_1160_, lean_object* v_h_1161_, lean_object* v_state_1162_, lean_object* v_lhs_1163_, lean_object* v_rhs_1164_, lean_object* v_this_1165_, lean_object* v_motive_1166_, lean_object* v_x_1167_, lean_object* v_h__1_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__56_splitter(v_00_u03b1_1156_, v_inst_1157_, v_inst_1158_, v_aig_1159_, v_upper_1160_, v_h_1161_, v_state_1162_, v_lhs_1163_, v_rhs_1164_, v_this_1165_, v_motive_1166_, v_x_1167_, v_h__1_1168_);
lean_dec(v_rhs_1164_);
lean_dec(v_lhs_1163_);
lean_dec_ref(v_state_1162_);
lean_dec(v_upper_1160_);
lean_dec_ref(v_aig_1159_);
lean_dec_ref(v_inst_1158_);
lean_dec_ref(v_inst_1157_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__54_splitter___redArg(lean_object* v_x_1170_, lean_object* v_h__1_1171_){
_start:
{
lean_object* v___x_1172_; 
v___x_1172_ = lean_apply_2(v_h__1_1171_, v_x_1170_, lean_box(0));
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__54_splitter(lean_object* v_00_u03b1_1173_, lean_object* v_inst_1174_, lean_object* v_inst_1175_, lean_object* v_aig_1176_, lean_object* v_upper_1177_, lean_object* v_h_1178_, lean_object* v_lhs_1179_, lean_object* v_rhs_1180_, lean_object* v_this_1181_, lean_object* v_lstate_1182_, lean_object* v_motive_1183_, lean_object* v_x_1184_, lean_object* v_h__1_1185_){
_start:
{
lean_object* v___x_1186_; 
v___x_1186_ = lean_apply_2(v_h__1_1185_, v_x_1184_, lean_box(0));
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__54_splitter___boxed(lean_object* v_00_u03b1_1187_, lean_object* v_inst_1188_, lean_object* v_inst_1189_, lean_object* v_aig_1190_, lean_object* v_upper_1191_, lean_object* v_h_1192_, lean_object* v_lhs_1193_, lean_object* v_rhs_1194_, lean_object* v_this_1195_, lean_object* v_lstate_1196_, lean_object* v_motive_1197_, lean_object* v_x_1198_, lean_object* v_h__1_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__54_splitter(v_00_u03b1_1187_, v_inst_1188_, v_inst_1189_, v_aig_1190_, v_upper_1191_, v_h_1192_, v_lhs_1193_, v_rhs_1194_, v_this_1195_, v_lstate_1196_, v_motive_1197_, v_x_1198_, v_h__1_1199_);
lean_dec_ref(v_lstate_1196_);
lean_dec(v_rhs_1194_);
lean_dec(v_lhs_1193_);
lean_dec(v_upper_1191_);
lean_dec_ref(v_aig_1190_);
lean_dec_ref(v_inst_1189_);
lean_dec_ref(v_inst_1188_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__0_spec__1___redArg(lean_object* v_cache_1201_, lean_object* v_idx_1202_){
_start:
{
uint8_t v___x_1203_; lean_object* v___x_1204_; lean_object* v_out_1205_; 
v___x_1203_ = 1;
v___x_1204_ = lean_box(v___x_1203_);
v_out_1205_ = lean_array_fset(v_cache_1201_, v_idx_1202_, v___x_1204_);
return v_out_1205_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_cache_1206_, lean_object* v_idx_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__0_spec__1___redArg(v_cache_1206_, v_idx_1207_);
lean_dec(v_idx_1207_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__0___redArg(lean_object* v_inst_1209_, lean_object* v_inst_1210_, lean_object* v_aig_1211_, lean_object* v_state_1212_, lean_object* v_idx_1213_){
_start:
{
lean_object* v_cnf_1214_; lean_object* v_cache_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1225_; 
v_cnf_1214_ = lean_ctor_get(v_state_1212_, 0);
v_cache_1215_ = lean_ctor_get(v_state_1212_, 1);
v_isSharedCheck_1225_ = !lean_is_exclusive(v_state_1212_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1217_ = v_state_1212_;
v_isShared_1218_ = v_isSharedCheck_1225_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_cache_1215_);
lean_inc(v_cnf_1214_);
lean_dec(v_state_1212_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1225_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v_val_1219_; lean_object* v_newCnf_1220_; lean_object* v___x_1221_; lean_object* v___x_1223_; 
v_val_1219_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__0_spec__1___redArg(v_cache_1215_, v_idx_1213_);
v_newCnf_1220_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg(v_idx_1213_);
v___x_1221_ = l_Array_append___redArg(v_cnf_1214_, v_newCnf_1220_);
lean_dec_ref(v_newCnf_1220_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 1, v_val_1219_);
lean_ctor_set(v___x_1217_, 0, v___x_1221_);
v___x_1223_ = v___x_1217_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v___x_1221_);
lean_ctor_set(v_reuseFailAlloc_1224_, 1, v_val_1219_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__0___redArg___boxed(lean_object* v_inst_1226_, lean_object* v_inst_1227_, lean_object* v_aig_1228_, lean_object* v_state_1229_, lean_object* v_idx_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__0___redArg(v_inst_1226_, v_inst_1227_, v_aig_1228_, v_state_1229_, v_idx_1230_);
lean_dec_ref(v_aig_1228_);
lean_dec_ref(v_inst_1227_);
lean_dec_ref(v_inst_1226_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__2___redArg(lean_object* v_aig_1232_, lean_object* v_root_1233_){
_start:
{
lean_object* v_decls_1234_; lean_object* v___x_1235_; 
v_decls_1234_ = lean_ctor_get(v_aig_1232_, 0);
v___x_1235_ = lean_array_fget_borrowed(v_decls_1234_, v_root_1233_);
if (lean_obj_tag(v___x_1235_) == 2)
{
lean_object* v_l_1236_; lean_object* v_r_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; uint8_t v___x_1241_; 
v_l_1236_ = lean_ctor_get(v___x_1235_, 0);
v_r_1237_ = lean_ctor_get(v___x_1235_, 1);
v___x_1238_ = lean_unsigned_to_nat(1u);
v___x_1239_ = lean_nat_land(v___x_1238_, v_l_1236_);
v___x_1240_ = lean_unsigned_to_nat(0u);
v___x_1241_ = lean_nat_dec_eq(v___x_1239_, v___x_1240_);
lean_dec(v___x_1239_);
if (v___x_1241_ == 0)
{
lean_object* v___x_1242_; uint8_t v___x_1243_; 
v___x_1242_ = lean_nat_land(v___x_1238_, v_r_1237_);
v___x_1243_ = lean_nat_dec_eq(v___x_1242_, v___x_1240_);
lean_dec(v___x_1242_);
if (v___x_1243_ == 0)
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = lean_nat_shiftr(v_l_1236_, v___x_1238_);
v___x_1245_ = lean_array_fget_borrowed(v_decls_1234_, v___x_1244_);
lean_dec(v___x_1244_);
if (lean_obj_tag(v___x_1245_) == 2)
{
lean_object* v_l_1246_; lean_object* v_r_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v_l_1246_ = lean_ctor_get(v___x_1245_, 0);
v_r_1247_ = lean_ctor_get(v___x_1245_, 1);
v___x_1248_ = lean_nat_shiftr(v_r_1237_, v___x_1238_);
v___x_1249_ = lean_array_fget_borrowed(v_decls_1234_, v___x_1248_);
lean_dec(v___x_1248_);
if (lean_obj_tag(v___x_1249_) == 2)
{
lean_object* v_l_1250_; lean_object* v_r_1251_; lean_object* v___x_1252_; 
v_l_1250_ = lean_ctor_get(v___x_1249_, 0);
v_r_1251_ = lean_ctor_get(v___x_1249_, 1);
lean_inc(v_r_1247_);
lean_inc(v_l_1246_);
v___x_1252_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg(v_l_1246_, v_r_1247_, v_l_1250_, v_r_1251_);
return v___x_1252_;
}
else
{
lean_object* v___x_1253_; 
v___x_1253_ = lean_box(0);
return v___x_1253_;
}
}
else
{
lean_object* v___x_1254_; 
v___x_1254_ = lean_box(0);
return v___x_1254_;
}
}
else
{
lean_object* v___x_1255_; 
v___x_1255_ = lean_box(0);
return v___x_1255_;
}
}
else
{
lean_object* v___x_1256_; 
v___x_1256_ = lean_box(0);
return v___x_1256_;
}
}
else
{
lean_object* v___x_1257_; 
v___x_1257_ = lean_box(0);
return v___x_1257_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__2___redArg___boxed(lean_object* v_aig_1258_, lean_object* v_root_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__2___redArg(v_aig_1258_, v_root_1259_);
lean_dec(v_root_1259_);
lean_dec_ref(v_aig_1258_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4_spec__8___redArg(lean_object* v_cache_1261_, lean_object* v_cond_1262_, lean_object* v_ifTrue_1263_, lean_object* v_ifFalse_1264_, lean_object* v_idx_1265_){
_start:
{
uint8_t v___x_1266_; lean_object* v___x_1267_; lean_object* v_out_1268_; 
v___x_1266_ = 1;
v___x_1267_ = lean_box(v___x_1266_);
v_out_1268_ = lean_array_fset(v_cache_1261_, v_idx_1265_, v___x_1267_);
return v_out_1268_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4_spec__8___redArg___boxed(lean_object* v_cache_1269_, lean_object* v_cond_1270_, lean_object* v_ifTrue_1271_, lean_object* v_ifFalse_1272_, lean_object* v_idx_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4_spec__8___redArg(v_cache_1269_, v_cond_1270_, v_ifTrue_1271_, v_ifFalse_1272_, v_idx_1273_);
lean_dec(v_idx_1273_);
lean_dec(v_ifFalse_1272_);
lean_dec(v_ifTrue_1271_);
lean_dec(v_cond_1270_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4___redArg(lean_object* v_inst_1275_, lean_object* v_inst_1276_, lean_object* v_aig_1277_, lean_object* v_state_1278_, lean_object* v_cond_1279_, lean_object* v_ifTrue_1280_, lean_object* v_ifFalse_1281_, lean_object* v_idx_1282_){
_start:
{
lean_object* v_cnf_1283_; lean_object* v_cache_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1322_; 
v_cnf_1283_ = lean_ctor_get(v_state_1278_, 0);
v_cache_1284_ = lean_ctor_get(v_state_1278_, 1);
v_isSharedCheck_1322_ = !lean_is_exclusive(v_state_1278_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1286_ = v_state_1278_;
v_isShared_1287_ = v_isSharedCheck_1322_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_cache_1284_);
lean_inc(v_cnf_1283_);
lean_dec(v_state_1278_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1322_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; uint8_t v___y_1293_; uint8_t v___y_1294_; uint8_t v___y_1295_; uint8_t v___y_1303_; uint8_t v___y_1304_; uint8_t v___y_1311_; lean_object* v___x_1317_; lean_object* v___x_1318_; uint8_t v___x_1319_; 
v___x_1288_ = lean_unsigned_to_nat(1u);
v___x_1289_ = lean_nat_shiftr(v_cond_1279_, v___x_1288_);
v___x_1290_ = lean_nat_shiftr(v_ifTrue_1280_, v___x_1288_);
v___x_1291_ = lean_nat_shiftr(v_ifFalse_1281_, v___x_1288_);
v___x_1317_ = lean_nat_land(v___x_1288_, v_cond_1279_);
v___x_1318_ = lean_unsigned_to_nat(0u);
v___x_1319_ = lean_nat_dec_eq(v___x_1317_, v___x_1318_);
lean_dec(v___x_1317_);
if (v___x_1319_ == 0)
{
uint8_t v___x_1320_; 
v___x_1320_ = 1;
v___y_1311_ = v___x_1320_;
goto v___jp_1310_;
}
else
{
uint8_t v___x_1321_; 
v___x_1321_ = 0;
v___y_1311_ = v___x_1321_;
goto v___jp_1310_;
}
v___jp_1292_:
{
lean_object* v_val_1296_; lean_object* v_newCnf_1297_; lean_object* v___x_1298_; lean_object* v___x_1300_; 
v_val_1296_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4_spec__8___redArg(v_cache_1284_, v_cond_1279_, v_ifTrue_1280_, v_ifFalse_1281_, v_idx_1282_);
v_newCnf_1297_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF___redArg(v_idx_1282_, v___x_1289_, v___x_1290_, v___x_1291_, v___y_1293_, v___y_1294_, v___y_1295_);
v___x_1298_ = l_Array_append___redArg(v_cnf_1283_, v_newCnf_1297_);
lean_dec_ref(v_newCnf_1297_);
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 1, v_val_1296_);
lean_ctor_set(v___x_1286_, 0, v___x_1298_);
v___x_1300_ = v___x_1286_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v___x_1298_);
lean_ctor_set(v_reuseFailAlloc_1301_, 1, v_val_1296_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
v___jp_1302_:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; uint8_t v___x_1307_; 
v___x_1305_ = lean_nat_land(v___x_1288_, v_ifFalse_1281_);
v___x_1306_ = lean_unsigned_to_nat(0u);
v___x_1307_ = lean_nat_dec_eq(v___x_1305_, v___x_1306_);
lean_dec(v___x_1305_);
if (v___x_1307_ == 0)
{
uint8_t v___x_1308_; 
v___x_1308_ = 1;
v___y_1293_ = v___y_1303_;
v___y_1294_ = v___y_1304_;
v___y_1295_ = v___x_1308_;
goto v___jp_1292_;
}
else
{
uint8_t v___x_1309_; 
v___x_1309_ = 0;
v___y_1293_ = v___y_1303_;
v___y_1294_ = v___y_1304_;
v___y_1295_ = v___x_1309_;
goto v___jp_1292_;
}
}
v___jp_1310_:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; 
v___x_1312_ = lean_nat_land(v___x_1288_, v_ifTrue_1280_);
v___x_1313_ = lean_unsigned_to_nat(0u);
v___x_1314_ = lean_nat_dec_eq(v___x_1312_, v___x_1313_);
lean_dec(v___x_1312_);
if (v___x_1314_ == 0)
{
uint8_t v___x_1315_; 
v___x_1315_ = 1;
v___y_1303_ = v___y_1311_;
v___y_1304_ = v___x_1315_;
goto v___jp_1302_;
}
else
{
uint8_t v___x_1316_; 
v___x_1316_ = 0;
v___y_1303_ = v___y_1311_;
v___y_1304_ = v___x_1316_;
goto v___jp_1302_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4___redArg___boxed(lean_object* v_inst_1323_, lean_object* v_inst_1324_, lean_object* v_aig_1325_, lean_object* v_state_1326_, lean_object* v_cond_1327_, lean_object* v_ifTrue_1328_, lean_object* v_ifFalse_1329_, lean_object* v_idx_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4___redArg(v_inst_1323_, v_inst_1324_, v_aig_1325_, v_state_1326_, v_cond_1327_, v_ifTrue_1328_, v_ifFalse_1329_, v_idx_1330_);
lean_dec(v_ifFalse_1329_);
lean_dec(v_ifTrue_1328_);
lean_dec(v_cond_1327_);
lean_dec_ref(v_aig_1325_);
lean_dec_ref(v_inst_1324_);
lean_dec_ref(v_inst_1323_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__3_spec__6___redArg(lean_object* v_lhs_1332_, lean_object* v_rhs_1333_, lean_object* v_cache_1334_, lean_object* v_idx_1335_){
_start:
{
uint8_t v___x_1336_; lean_object* v___x_1337_; lean_object* v_out_1338_; 
v___x_1336_ = 1;
v___x_1337_ = lean_box(v___x_1336_);
v_out_1338_ = lean_array_fset(v_cache_1334_, v_idx_1335_, v___x_1337_);
return v_out_1338_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__3_spec__6___redArg___boxed(lean_object* v_lhs_1339_, lean_object* v_rhs_1340_, lean_object* v_cache_1341_, lean_object* v_idx_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__3_spec__6___redArg(v_lhs_1339_, v_rhs_1340_, v_cache_1341_, v_idx_1342_);
lean_dec(v_idx_1342_);
lean_dec(v_rhs_1340_);
lean_dec(v_lhs_1339_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__3___redArg(lean_object* v_inst_1344_, lean_object* v_inst_1345_, lean_object* v_aig_1346_, lean_object* v_lhs_1347_, lean_object* v_rhs_1348_, lean_object* v_state_1349_, lean_object* v_idx_1350_){
_start:
{
lean_object* v_cnf_1351_; lean_object* v_cache_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1380_; 
v_cnf_1351_ = lean_ctor_get(v_state_1349_, 0);
v_cache_1352_ = lean_ctor_get(v_state_1349_, 1);
v_isSharedCheck_1380_ = !lean_is_exclusive(v_state_1349_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1354_ = v_state_1349_;
v_isShared_1355_ = v_isSharedCheck_1380_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_cache_1352_);
lean_inc(v_cnf_1351_);
lean_dec(v_state_1349_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1380_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; uint8_t v___y_1360_; uint8_t v___y_1361_; uint8_t v___y_1369_; lean_object* v___x_1375_; lean_object* v___x_1376_; uint8_t v___x_1377_; 
v___x_1356_ = lean_unsigned_to_nat(1u);
v___x_1357_ = lean_nat_shiftr(v_lhs_1347_, v___x_1356_);
v___x_1358_ = lean_nat_shiftr(v_rhs_1348_, v___x_1356_);
v___x_1375_ = lean_nat_land(v___x_1356_, v_lhs_1347_);
v___x_1376_ = lean_unsigned_to_nat(0u);
v___x_1377_ = lean_nat_dec_eq(v___x_1375_, v___x_1376_);
lean_dec(v___x_1375_);
if (v___x_1377_ == 0)
{
uint8_t v___x_1378_; 
v___x_1378_ = 1;
v___y_1369_ = v___x_1378_;
goto v___jp_1368_;
}
else
{
uint8_t v___x_1379_; 
v___x_1379_ = 0;
v___y_1369_ = v___x_1379_;
goto v___jp_1368_;
}
v___jp_1359_:
{
lean_object* v_val_1362_; lean_object* v_newCnf_1363_; lean_object* v___x_1364_; lean_object* v___x_1366_; 
v_val_1362_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__3_spec__6___redArg(v_lhs_1347_, v_rhs_1348_, v_cache_1352_, v_idx_1350_);
v_newCnf_1363_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg(v_idx_1350_, v___x_1357_, v___x_1358_, v___y_1360_, v___y_1361_);
v___x_1364_ = l_Array_append___redArg(v_cnf_1351_, v_newCnf_1363_);
lean_dec_ref(v_newCnf_1363_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 1, v_val_1362_);
lean_ctor_set(v___x_1354_, 0, v___x_1364_);
v___x_1366_ = v___x_1354_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1364_);
lean_ctor_set(v_reuseFailAlloc_1367_, 1, v_val_1362_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
v___jp_1368_:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; uint8_t v___x_1372_; 
v___x_1370_ = lean_nat_land(v___x_1356_, v_rhs_1348_);
v___x_1371_ = lean_unsigned_to_nat(0u);
v___x_1372_ = lean_nat_dec_eq(v___x_1370_, v___x_1371_);
lean_dec(v___x_1370_);
if (v___x_1372_ == 0)
{
uint8_t v___x_1373_; 
v___x_1373_ = 1;
v___y_1360_ = v___y_1369_;
v___y_1361_ = v___x_1373_;
goto v___jp_1359_;
}
else
{
uint8_t v___x_1374_; 
v___x_1374_ = 0;
v___y_1360_ = v___y_1369_;
v___y_1361_ = v___x_1374_;
goto v___jp_1359_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__3___redArg___boxed(lean_object* v_inst_1381_, lean_object* v_inst_1382_, lean_object* v_aig_1383_, lean_object* v_lhs_1384_, lean_object* v_rhs_1385_, lean_object* v_state_1386_, lean_object* v_idx_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__3___redArg(v_inst_1381_, v_inst_1382_, v_aig_1383_, v_lhs_1384_, v_rhs_1385_, v_state_1386_, v_idx_1387_);
lean_dec(v_rhs_1385_);
lean_dec(v_lhs_1384_);
lean_dec_ref(v_aig_1383_);
lean_dec_ref(v_inst_1382_);
lean_dec_ref(v_inst_1381_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__1_spec__3___redArg(lean_object* v_cache_1389_, lean_object* v_idx_1390_){
_start:
{
uint8_t v___x_1391_; lean_object* v___x_1392_; lean_object* v_out_1393_; 
v___x_1391_ = 1;
v___x_1392_ = lean_box(v___x_1391_);
v_out_1393_ = lean_array_fset(v_cache_1389_, v_idx_1390_, v___x_1392_);
return v_out_1393_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_cache_1394_, lean_object* v_idx_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__1_spec__3___redArg(v_cache_1394_, v_idx_1395_);
lean_dec(v_idx_1395_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__1___redArg(lean_object* v_inst_1397_, lean_object* v_inst_1398_, lean_object* v_aig_1399_, lean_object* v_a_1400_, lean_object* v_state_1401_, lean_object* v_idx_1402_){
_start:
{
lean_object* v_cnf_1403_; lean_object* v_cache_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1412_; 
v_cnf_1403_ = lean_ctor_get(v_state_1401_, 0);
v_cache_1404_ = lean_ctor_get(v_state_1401_, 1);
v_isSharedCheck_1412_ = !lean_is_exclusive(v_state_1401_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1406_ = v_state_1401_;
v_isShared_1407_ = v_isSharedCheck_1412_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_cache_1404_);
lean_inc(v_cnf_1403_);
lean_dec(v_state_1401_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1412_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v_val_1408_; lean_object* v___x_1410_; 
v_val_1408_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__1_spec__3___redArg(v_cache_1404_, v_idx_1402_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 1, v_val_1408_);
v___x_1410_ = v___x_1406_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_cnf_1403_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v_val_1408_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__1___redArg___boxed(lean_object* v_inst_1413_, lean_object* v_inst_1414_, lean_object* v_aig_1415_, lean_object* v_a_1416_, lean_object* v_state_1417_, lean_object* v_idx_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__1___redArg(v_inst_1413_, v_inst_1414_, v_aig_1415_, v_a_1416_, v_state_1417_, v_idx_1418_);
lean_dec(v_idx_1418_);
lean_dec(v_a_1416_);
lean_dec_ref(v_aig_1415_);
lean_dec_ref(v_inst_1414_);
lean_dec_ref(v_inst_1413_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0___redArg(lean_object* v_inst_1420_, lean_object* v_inst_1421_, lean_object* v_aig_1422_, lean_object* v_upper_1423_, lean_object* v_state_1424_){
_start:
{
lean_object* v_cache_1425_; lean_object* v___x_1426_; uint8_t v___x_1427_; 
v_cache_1425_ = lean_ctor_get(v_state_1424_, 1);
v___x_1426_ = lean_array_fget_borrowed(v_cache_1425_, v_upper_1423_);
v___x_1427_ = lean_unbox(v___x_1426_);
if (v___x_1427_ == 0)
{
lean_object* v_decls_1428_; lean_object* v_decl_1429_; 
v_decls_1428_ = lean_ctor_get(v_aig_1422_, 0);
v_decl_1429_ = lean_array_fget_borrowed(v_decls_1428_, v_upper_1423_);
switch(lean_obj_tag(v_decl_1429_))
{
case 0:
{
lean_object* v___x_1430_; 
v___x_1430_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__0___redArg(v_inst_1420_, v_inst_1421_, v_aig_1422_, v_state_1424_, v_upper_1423_);
return v___x_1430_;
}
case 1:
{
lean_object* v_idx_1431_; lean_object* v___x_1432_; 
v_idx_1431_ = lean_ctor_get(v_decl_1429_, 0);
v___x_1432_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__1___redArg(v_inst_1420_, v_inst_1421_, v_aig_1422_, v_idx_1431_, v_state_1424_, v_upper_1423_);
lean_dec(v_upper_1423_);
return v___x_1432_;
}
default: 
{
lean_object* v_l_1433_; lean_object* v_r_1434_; lean_object* v___x_1435_; 
v_l_1433_ = lean_ctor_get(v_decl_1429_, 0);
v_r_1434_ = lean_ctor_get(v_decl_1429_, 1);
v___x_1435_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__2___redArg(v_aig_1422_, v_upper_1423_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v_val_1438_; lean_object* v___x_1439_; lean_object* v_val_1440_; lean_object* v___x_1441_; 
v___x_1436_ = lean_unsigned_to_nat(1u);
v___x_1437_ = lean_nat_shiftr(v_l_1433_, v___x_1436_);
v_val_1438_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0___redArg(v_inst_1420_, v_inst_1421_, v_aig_1422_, v___x_1437_, v_state_1424_);
v___x_1439_ = lean_nat_shiftr(v_r_1434_, v___x_1436_);
v_val_1440_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0___redArg(v_inst_1420_, v_inst_1421_, v_aig_1422_, v___x_1439_, v_val_1438_);
v___x_1441_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__3___redArg(v_inst_1420_, v_inst_1421_, v_aig_1422_, v_l_1433_, v_r_1434_, v_val_1440_, v_upper_1423_);
return v___x_1441_;
}
else
{
lean_object* v_val_1442_; lean_object* v_snd_1443_; lean_object* v_fst_1444_; lean_object* v_fst_1445_; lean_object* v_snd_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v_val_1449_; lean_object* v___x_1450_; lean_object* v_val_1451_; lean_object* v___x_1452_; lean_object* v_val_1453_; lean_object* v___x_1454_; 
v_val_1442_ = lean_ctor_get(v___x_1435_, 0);
lean_inc(v_val_1442_);
lean_dec_ref_known(v___x_1435_, 1);
v_snd_1443_ = lean_ctor_get(v_val_1442_, 1);
lean_inc(v_snd_1443_);
v_fst_1444_ = lean_ctor_get(v_val_1442_, 0);
lean_inc(v_fst_1444_);
lean_dec(v_val_1442_);
v_fst_1445_ = lean_ctor_get(v_snd_1443_, 0);
lean_inc(v_fst_1445_);
v_snd_1446_ = lean_ctor_get(v_snd_1443_, 1);
lean_inc(v_snd_1446_);
lean_dec(v_snd_1443_);
v___x_1447_ = lean_unsigned_to_nat(1u);
v___x_1448_ = lean_nat_shiftr(v_fst_1444_, v___x_1447_);
v_val_1449_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0___redArg(v_inst_1420_, v_inst_1421_, v_aig_1422_, v___x_1448_, v_state_1424_);
v___x_1450_ = lean_nat_shiftr(v_fst_1445_, v___x_1447_);
v_val_1451_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0___redArg(v_inst_1420_, v_inst_1421_, v_aig_1422_, v___x_1450_, v_val_1449_);
v___x_1452_ = lean_nat_shiftr(v_snd_1446_, v___x_1447_);
v_val_1453_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0___redArg(v_inst_1420_, v_inst_1421_, v_aig_1422_, v___x_1452_, v_val_1451_);
v___x_1454_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4___redArg(v_inst_1420_, v_inst_1421_, v_aig_1422_, v_val_1453_, v_fst_1444_, v_fst_1445_, v_snd_1446_, v_upper_1423_);
lean_dec(v_snd_1446_);
lean_dec(v_fst_1445_);
lean_dec(v_fst_1444_);
return v___x_1454_;
}
}
}
}
else
{
lean_dec(v_upper_1423_);
return v_state_1424_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0___redArg___boxed(lean_object* v_inst_1455_, lean_object* v_inst_1456_, lean_object* v_aig_1457_, lean_object* v_upper_1458_, lean_object* v_state_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0___redArg(v_inst_1455_, v_inst_1456_, v_aig_1457_, v_upper_1458_, v_state_1459_);
lean_dec_ref(v_aig_1457_);
lean_dec_ref(v_inst_1456_);
lean_dec_ref(v_inst_1455_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_x27___redArg(lean_object* v_inst_1461_, lean_object* v_inst_1462_, lean_object* v_entry_1463_, lean_object* v_state_1464_){
_start:
{
lean_object* v_ref_1465_; lean_object* v_aig_1466_; lean_object* v_gate_1467_; lean_object* v___x_1468_; 
v_ref_1465_ = lean_ctor_get(v_entry_1463_, 1);
lean_inc_ref(v_ref_1465_);
v_aig_1466_ = lean_ctor_get(v_entry_1463_, 0);
lean_inc_ref(v_aig_1466_);
lean_dec_ref(v_entry_1463_);
v_gate_1467_ = lean_ctor_get(v_ref_1465_, 0);
lean_inc(v_gate_1467_);
lean_dec_ref(v_ref_1465_);
v___x_1468_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0___redArg(v_inst_1461_, v_inst_1462_, v_aig_1466_, v_gate_1467_, v_state_1464_);
lean_dec_ref(v_aig_1466_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_x27___redArg___boxed(lean_object* v_inst_1469_, lean_object* v_inst_1470_, lean_object* v_entry_1471_, lean_object* v_state_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l_Std_Sat_AIG_toCNF_x27___redArg(v_inst_1469_, v_inst_1470_, v_entry_1471_, v_state_1472_);
lean_dec_ref(v_inst_1470_);
lean_dec_ref(v_inst_1469_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_x27(lean_object* v_00_u03b1_1474_, lean_object* v_inst_1475_, lean_object* v_inst_1476_, lean_object* v_entry_1477_, lean_object* v_state_1478_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = l_Std_Sat_AIG_toCNF_x27___redArg(v_inst_1475_, v_inst_1476_, v_entry_1477_, v_state_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_x27___boxed(lean_object* v_00_u03b1_1480_, lean_object* v_inst_1481_, lean_object* v_inst_1482_, lean_object* v_entry_1483_, lean_object* v_state_1484_){
_start:
{
lean_object* v_res_1485_; 
v_res_1485_ = l_Std_Sat_AIG_toCNF_x27(v_00_u03b1_1480_, v_inst_1481_, v_inst_1482_, v_entry_1483_, v_state_1484_);
lean_dec_ref(v_inst_1482_);
lean_dec_ref(v_inst_1481_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__2(lean_object* v_00_u03b1_1486_, lean_object* v_inst_1487_, lean_object* v_inst_1488_, lean_object* v_aig_1489_, lean_object* v_root_1490_, lean_object* v_h_1491_){
_start:
{
lean_object* v___x_1492_; 
v___x_1492_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__2___redArg(v_aig_1489_, v_root_1490_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1493_, lean_object* v_inst_1494_, lean_object* v_inst_1495_, lean_object* v_aig_1496_, lean_object* v_root_1497_, lean_object* v_h_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__2(v_00_u03b1_1493_, v_inst_1494_, v_inst_1495_, v_aig_1496_, v_root_1497_, v_h_1498_);
lean_dec(v_root_1497_);
lean_dec_ref(v_aig_1496_);
lean_dec_ref(v_inst_1495_);
lean_dec_ref(v_inst_1494_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0(lean_object* v_00_u03b1_1500_, lean_object* v_inst_1501_, lean_object* v_inst_1502_, lean_object* v_aig_1503_, lean_object* v_upper_1504_, lean_object* v_h_1505_, lean_object* v_state_1506_){
_start:
{
lean_object* v___x_1507_; 
v___x_1507_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0___redArg(v_inst_1501_, v_inst_1502_, v_aig_1503_, v_upper_1504_, v_state_1506_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0___boxed(lean_object* v_00_u03b1_1508_, lean_object* v_inst_1509_, lean_object* v_inst_1510_, lean_object* v_aig_1511_, lean_object* v_upper_1512_, lean_object* v_h_1513_, lean_object* v_state_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0(v_00_u03b1_1508_, v_inst_1509_, v_inst_1510_, v_aig_1511_, v_upper_1512_, v_h_1513_, v_state_1514_);
lean_dec_ref(v_aig_1511_);
lean_dec_ref(v_inst_1510_);
lean_dec_ref(v_inst_1509_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1516_, lean_object* v_inst_1517_, lean_object* v_inst_1518_, lean_object* v_aig_1519_, lean_object* v_cnf_1520_, lean_object* v_cache_1521_, lean_object* v_idx_1522_, lean_object* v_h_1523_, lean_object* v_htip_1524_){
_start:
{
lean_object* v___x_1525_; 
v___x_1525_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__0_spec__1___redArg(v_cache_1521_, v_idx_1522_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1526_, lean_object* v_inst_1527_, lean_object* v_inst_1528_, lean_object* v_aig_1529_, lean_object* v_cnf_1530_, lean_object* v_cache_1531_, lean_object* v_idx_1532_, lean_object* v_h_1533_, lean_object* v_htip_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__0_spec__1(v_00_u03b1_1526_, v_inst_1527_, v_inst_1528_, v_aig_1529_, v_cnf_1530_, v_cache_1531_, v_idx_1532_, v_h_1533_, v_htip_1534_);
lean_dec(v_idx_1532_);
lean_dec_ref(v_cnf_1530_);
lean_dec_ref(v_aig_1529_);
lean_dec_ref(v_inst_1528_);
lean_dec_ref(v_inst_1527_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__0(lean_object* v_00_u03b1_1536_, lean_object* v_inst_1537_, lean_object* v_inst_1538_, lean_object* v_aig_1539_, lean_object* v_state_1540_, lean_object* v_idx_1541_, lean_object* v_h_1542_, lean_object* v_htip_1543_){
_start:
{
lean_object* v___x_1544_; 
v___x_1544_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__0___redArg(v_inst_1537_, v_inst_1538_, v_aig_1539_, v_state_1540_, v_idx_1541_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1545_, lean_object* v_inst_1546_, lean_object* v_inst_1547_, lean_object* v_aig_1548_, lean_object* v_state_1549_, lean_object* v_idx_1550_, lean_object* v_h_1551_, lean_object* v_htip_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__0(v_00_u03b1_1545_, v_inst_1546_, v_inst_1547_, v_aig_1548_, v_state_1549_, v_idx_1550_, v_h_1551_, v_htip_1552_);
lean_dec_ref(v_aig_1548_);
lean_dec_ref(v_inst_1547_);
lean_dec_ref(v_inst_1546_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_1554_, lean_object* v_inst_1555_, lean_object* v_inst_1556_, lean_object* v_aig_1557_, lean_object* v_cnf_1558_, lean_object* v_a_1559_, lean_object* v_cache_1560_, lean_object* v_idx_1561_, lean_object* v_h_1562_, lean_object* v_htip_1563_){
_start:
{
lean_object* v___x_1564_; 
v___x_1564_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__1_spec__3___redArg(v_cache_1560_, v_idx_1561_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_1565_, lean_object* v_inst_1566_, lean_object* v_inst_1567_, lean_object* v_aig_1568_, lean_object* v_cnf_1569_, lean_object* v_a_1570_, lean_object* v_cache_1571_, lean_object* v_idx_1572_, lean_object* v_h_1573_, lean_object* v_htip_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__1_spec__3(v_00_u03b1_1565_, v_inst_1566_, v_inst_1567_, v_aig_1568_, v_cnf_1569_, v_a_1570_, v_cache_1571_, v_idx_1572_, v_h_1573_, v_htip_1574_);
lean_dec(v_idx_1572_);
lean_dec(v_a_1570_);
lean_dec_ref(v_cnf_1569_);
lean_dec_ref(v_aig_1568_);
lean_dec_ref(v_inst_1567_);
lean_dec_ref(v_inst_1566_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__1(lean_object* v_00_u03b1_1576_, lean_object* v_inst_1577_, lean_object* v_inst_1578_, lean_object* v_aig_1579_, lean_object* v_a_1580_, lean_object* v_state_1581_, lean_object* v_idx_1582_, lean_object* v_h_1583_, lean_object* v_htip_1584_){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__1___redArg(v_inst_1577_, v_inst_1578_, v_aig_1579_, v_a_1580_, v_state_1581_, v_idx_1582_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1586_, lean_object* v_inst_1587_, lean_object* v_inst_1588_, lean_object* v_aig_1589_, lean_object* v_a_1590_, lean_object* v_state_1591_, lean_object* v_idx_1592_, lean_object* v_h_1593_, lean_object* v_htip_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__1(v_00_u03b1_1586_, v_inst_1587_, v_inst_1588_, v_aig_1589_, v_a_1590_, v_state_1591_, v_idx_1592_, v_h_1593_, v_htip_1594_);
lean_dec(v_idx_1592_);
lean_dec(v_a_1590_);
lean_dec_ref(v_aig_1589_);
lean_dec_ref(v_inst_1588_);
lean_dec_ref(v_inst_1587_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__3_spec__6(lean_object* v_00_u03b1_1596_, lean_object* v_inst_1597_, lean_object* v_inst_1598_, lean_object* v_aig_1599_, lean_object* v_cnf_1600_, lean_object* v_lhs_1601_, lean_object* v_rhs_1602_, lean_object* v_cache_1603_, lean_object* v_hlb_1604_, lean_object* v_hrb_1605_, lean_object* v_idx_1606_, lean_object* v_h_1607_, lean_object* v_htip_1608_, lean_object* v_hl_1609_, lean_object* v_hr_1610_){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__3_spec__6___redArg(v_lhs_1601_, v_rhs_1602_, v_cache_1603_, v_idx_1606_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__3_spec__6___boxed(lean_object* v_00_u03b1_1612_, lean_object* v_inst_1613_, lean_object* v_inst_1614_, lean_object* v_aig_1615_, lean_object* v_cnf_1616_, lean_object* v_lhs_1617_, lean_object* v_rhs_1618_, lean_object* v_cache_1619_, lean_object* v_hlb_1620_, lean_object* v_hrb_1621_, lean_object* v_idx_1622_, lean_object* v_h_1623_, lean_object* v_htip_1624_, lean_object* v_hl_1625_, lean_object* v_hr_1626_){
_start:
{
lean_object* v_res_1627_; 
v_res_1627_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__3_spec__6(v_00_u03b1_1612_, v_inst_1613_, v_inst_1614_, v_aig_1615_, v_cnf_1616_, v_lhs_1617_, v_rhs_1618_, v_cache_1619_, v_hlb_1620_, v_hrb_1621_, v_idx_1622_, v_h_1623_, v_htip_1624_, v_hl_1625_, v_hr_1626_);
lean_dec(v_idx_1622_);
lean_dec(v_rhs_1618_);
lean_dec(v_lhs_1617_);
lean_dec_ref(v_cnf_1616_);
lean_dec_ref(v_aig_1615_);
lean_dec_ref(v_inst_1614_);
lean_dec_ref(v_inst_1613_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__3(lean_object* v_00_u03b1_1628_, lean_object* v_inst_1629_, lean_object* v_inst_1630_, lean_object* v_aig_1631_, lean_object* v_lhs_1632_, lean_object* v_rhs_1633_, lean_object* v_state_1634_, lean_object* v_hlb_1635_, lean_object* v_hrb_1636_, lean_object* v_idx_1637_, lean_object* v_h_1638_, lean_object* v_htip_1639_, lean_object* v_hl_1640_, lean_object* v_hr_1641_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__3___redArg(v_inst_1629_, v_inst_1630_, v_aig_1631_, v_lhs_1632_, v_rhs_1633_, v_state_1634_, v_idx_1637_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__3___boxed(lean_object* v_00_u03b1_1643_, lean_object* v_inst_1644_, lean_object* v_inst_1645_, lean_object* v_aig_1646_, lean_object* v_lhs_1647_, lean_object* v_rhs_1648_, lean_object* v_state_1649_, lean_object* v_hlb_1650_, lean_object* v_hrb_1651_, lean_object* v_idx_1652_, lean_object* v_h_1653_, lean_object* v_htip_1654_, lean_object* v_hl_1655_, lean_object* v_hr_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__3(v_00_u03b1_1643_, v_inst_1644_, v_inst_1645_, v_aig_1646_, v_lhs_1647_, v_rhs_1648_, v_state_1649_, v_hlb_1650_, v_hrb_1651_, v_idx_1652_, v_h_1653_, v_htip_1654_, v_hl_1655_, v_hr_1656_);
lean_dec(v_rhs_1648_);
lean_dec(v_lhs_1647_);
lean_dec_ref(v_aig_1646_);
lean_dec_ref(v_inst_1645_);
lean_dec_ref(v_inst_1644_);
return v_res_1657_;
}
}
lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4_spec__8(lean_object* v_00_u03b1_1658_, lean_object* v_inst_1659_, lean_object* v_inst_1660_, lean_object* v_aig_1661_, lean_object* v_cnf_1662_, lean_object* v_cache_1663_, lean_object* v_cond_1664_, lean_object* v_ifTrue_1665_, lean_object* v_ifFalse_1666_, lean_object* v_idx_1667_, lean_object* v_hcb_1668_, lean_object* v_htb_1669_, lean_object* v_hfb_1670_, lean_object* v_h_1671_, lean_object* v_hltc_1672_, lean_object* v_hltt_1673_, lean_object* v_hltf_1674_, lean_object* v_hc_1675_, lean_object* v_ht_1676_, lean_object* v_hf_1677_, lean_object* v_hdenote_1678_){
_start:
{
lean_object* v___x_1679_; 
v___x_1679_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4_spec__8___redArg(v_cache_1663_, v_cond_1664_, v_ifTrue_1665_, v_ifFalse_1666_, v_idx_1667_);
return v___x_1679_;
}
}
LEAN_EXPORT void l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1659_ = stack[1].m_obj;
lean_object* v_inst_1660_ = stack[2].m_obj;
lean_object* v_aig_1661_ = stack[3].m_obj;
lean_object* v_cnf_1662_ = stack[4].m_obj;
lean_object* v_cache_1663_ = stack[5].m_obj;
lean_object* v_cond_1664_ = stack[6].m_obj;
lean_object* v_ifTrue_1665_ = stack[7].m_obj;
lean_object* v_ifFalse_1666_ = stack[8].m_obj;
lean_object* v_idx_1667_ = stack[9].m_obj;
lean_object* v_res_1680_;
v_res_1680_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4_spec__8(lean_box(0), v_inst_1659_, v_inst_1660_, v_aig_1661_, v_cnf_1662_, v_cache_1663_, v_cond_1664_, v_ifTrue_1665_, v_ifFalse_1666_, v_idx_1667_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
stack->m_obj
 = v_res_1680_;
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4_spec__8___boxed(lean_object** _args){
lean_object* v_00_u03b1_1681_ = _args[0];
lean_object* v_inst_1682_ = _args[1];
lean_object* v_inst_1683_ = _args[2];
lean_object* v_aig_1684_ = _args[3];
lean_object* v_cnf_1685_ = _args[4];
lean_object* v_cache_1686_ = _args[5];
lean_object* v_cond_1687_ = _args[6];
lean_object* v_ifTrue_1688_ = _args[7];
lean_object* v_ifFalse_1689_ = _args[8];
lean_object* v_idx_1690_ = _args[9];
lean_object* v_hcb_1691_ = _args[10];
lean_object* v_htb_1692_ = _args[11];
lean_object* v_hfb_1693_ = _args[12];
lean_object* v_h_1694_ = _args[13];
lean_object* v_hltc_1695_ = _args[14];
lean_object* v_hltt_1696_ = _args[15];
lean_object* v_hltf_1697_ = _args[16];
lean_object* v_hc_1698_ = _args[17];
lean_object* v_ht_1699_ = _args[18];
lean_object* v_hf_1700_ = _args[19];
lean_object* v_hdenote_1701_ = _args[20];
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4_spec__8(v_00_u03b1_1681_, v_inst_1682_, v_inst_1683_, v_aig_1684_, v_cnf_1685_, v_cache_1686_, v_cond_1687_, v_ifTrue_1688_, v_ifFalse_1689_, v_idx_1690_, v_hcb_1691_, v_htb_1692_, v_hfb_1693_, v_h_1694_, v_hltc_1695_, v_hltt_1696_, v_hltf_1697_, v_hc_1698_, v_ht_1699_, v_hf_1700_, v_hdenote_1701_);
lean_dec(v_idx_1690_);
lean_dec(v_ifFalse_1689_);
lean_dec(v_ifTrue_1688_);
lean_dec(v_cond_1687_);
lean_dec_ref(v_cnf_1685_);
lean_dec_ref(v_aig_1684_);
lean_dec_ref(v_inst_1683_);
lean_dec_ref(v_inst_1682_);
return v_res_1702_;
}
}
lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4(lean_object* v_00_u03b1_1703_, lean_object* v_inst_1704_, lean_object* v_inst_1705_, lean_object* v_aig_1706_, lean_object* v_state_1707_, lean_object* v_cond_1708_, lean_object* v_ifTrue_1709_, lean_object* v_ifFalse_1710_, lean_object* v_idx_1711_, lean_object* v_hcb_1712_, lean_object* v_htb_1713_, lean_object* v_hfb_1714_, lean_object* v_h_1715_, lean_object* v_hltc_1716_, lean_object* v_hltt_1717_, lean_object* v_hltf_1718_, lean_object* v_hc_1719_, lean_object* v_ht_1720_, lean_object* v_hf_1721_, lean_object* v_hdenote_1722_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4___redArg(v_inst_1704_, v_inst_1705_, v_aig_1706_, v_state_1707_, v_cond_1708_, v_ifTrue_1709_, v_ifFalse_1710_, v_idx_1711_);
return v___x_1723_;
}
}
LEAN_EXPORT void l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1704_ = stack[1].m_obj;
lean_object* v_inst_1705_ = stack[2].m_obj;
lean_object* v_aig_1706_ = stack[3].m_obj;
lean_object* v_state_1707_ = stack[4].m_obj;
lean_object* v_cond_1708_ = stack[5].m_obj;
lean_object* v_ifTrue_1709_ = stack[6].m_obj;
lean_object* v_ifFalse_1710_ = stack[7].m_obj;
lean_object* v_idx_1711_ = stack[8].m_obj;
lean_object* v_res_1724_;
v_res_1724_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4(lean_box(0), v_inst_1704_, v_inst_1705_, v_aig_1706_, v_state_1707_, v_cond_1708_, v_ifTrue_1709_, v_ifFalse_1710_, v_idx_1711_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
stack->m_obj
 = v_res_1724_;
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4___boxed(lean_object** _args){
lean_object* v_00_u03b1_1725_ = _args[0];
lean_object* v_inst_1726_ = _args[1];
lean_object* v_inst_1727_ = _args[2];
lean_object* v_aig_1728_ = _args[3];
lean_object* v_state_1729_ = _args[4];
lean_object* v_cond_1730_ = _args[5];
lean_object* v_ifTrue_1731_ = _args[6];
lean_object* v_ifFalse_1732_ = _args[7];
lean_object* v_idx_1733_ = _args[8];
lean_object* v_hcb_1734_ = _args[9];
lean_object* v_htb_1735_ = _args[10];
lean_object* v_hfb_1736_ = _args[11];
lean_object* v_h_1737_ = _args[12];
lean_object* v_hltc_1738_ = _args[13];
lean_object* v_hltt_1739_ = _args[14];
lean_object* v_hltf_1740_ = _args[15];
lean_object* v_hc_1741_ = _args[16];
lean_object* v_ht_1742_ = _args[17];
lean_object* v_hf_1743_ = _args[18];
lean_object* v_hdenote_1744_ = _args[19];
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4(v_00_u03b1_1725_, v_inst_1726_, v_inst_1727_, v_aig_1728_, v_state_1729_, v_cond_1730_, v_ifTrue_1731_, v_ifFalse_1732_, v_idx_1733_, v_hcb_1734_, v_htb_1735_, v_hfb_1736_, v_h_1737_, v_hltc_1738_, v_hltt_1739_, v_hltf_1740_, v_hc_1741_, v_ht_1742_, v_hf_1743_, v_hdenote_1744_);
lean_dec(v_ifFalse_1732_);
lean_dec(v_ifTrue_1731_);
lean_dec(v_cond_1730_);
lean_dec_ref(v_aig_1728_);
lean_dec_ref(v_inst_1727_);
lean_dec_ref(v_inst_1726_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF___redArg(lean_object* v_inst_1748_, lean_object* v_inst_1749_, lean_object* v_entry_1750_){
_start:
{
lean_object* v_aig_1751_; lean_object* v_ref_1752_; lean_object* v___x_1753_; lean_object* v_state_1754_; lean_object* v_cnf_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1775_; 
v_aig_1751_ = lean_ctor_get(v_entry_1750_, 0);
v_ref_1752_ = lean_ctor_get(v_entry_1750_, 1);
lean_inc_ref(v_ref_1752_);
v___x_1753_ = l_Std_Sat_AIG_toCNF_State_empty___redArg(v_aig_1751_);
v_state_1754_ = l_Std_Sat_AIG_toCNF_x27___redArg(v_inst_1748_, v_inst_1749_, v_entry_1750_, v___x_1753_);
v_cnf_1755_ = lean_ctor_get(v_state_1754_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v_state_1754_);
if (v_isSharedCheck_1775_ == 0)
{
lean_object* v_unused_1776_; 
v_unused_1776_ = lean_ctor_get(v_state_1754_, 1);
lean_dec(v_unused_1776_);
v___x_1757_ = v_state_1754_;
v_isShared_1758_ = v_isSharedCheck_1775_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_cnf_1755_);
lean_dec(v_state_1754_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1775_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v_gate_1759_; uint8_t v_invert_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___y_1764_; uint8_t v___y_1765_; 
v_gate_1759_ = lean_ctor_get(v_ref_1752_, 0);
lean_inc(v_gate_1759_);
v_invert_1760_ = lean_ctor_get_uint8(v_ref_1752_, sizeof(void*)*1);
lean_dec_ref(v_ref_1752_);
v___x_1761_ = ((lean_object*)(l_Std_Sat_AIG_toCNF___redArg___closed__0));
v___x_1762_ = l_ByteArray_empty;
if (v_invert_1760_ == 0)
{
lean_object* v___x_1771_; uint8_t v___x_1772_; 
v___x_1771_ = lean_array_push(v___x_1761_, v_gate_1759_);
v___x_1772_ = 1;
v___y_1764_ = v___x_1771_;
v___y_1765_ = v___x_1772_;
goto v___jp_1763_;
}
else
{
lean_object* v___x_1773_; uint8_t v___x_1774_; 
v___x_1773_ = lean_array_push(v___x_1761_, v_gate_1759_);
v___x_1774_ = 0;
v___y_1764_ = v___x_1773_;
v___y_1765_ = v___x_1774_;
goto v___jp_1763_;
}
v___jp_1763_:
{
lean_object* v___x_1766_; lean_object* v___x_1768_; 
v___x_1766_ = lean_byte_array_push(v___x_1762_, v___y_1765_);
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 1, v___x_1766_);
lean_ctor_set(v___x_1757_, 0, v___y_1764_);
v___x_1768_ = v___x_1757_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v___y_1764_);
lean_ctor_set(v_reuseFailAlloc_1770_, 1, v___x_1766_);
v___x_1768_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
lean_object* v___x_1769_; 
v___x_1769_ = lean_array_push(v_cnf_1755_, v___x_1768_);
return v___x_1769_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF___redArg___boxed(lean_object* v_inst_1777_, lean_object* v_inst_1778_, lean_object* v_entry_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_Std_Sat_AIG_toCNF___redArg(v_inst_1777_, v_inst_1778_, v_entry_1779_);
lean_dec_ref(v_inst_1778_);
lean_dec_ref(v_inst_1777_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF(lean_object* v_00_u03b1_1781_, lean_object* v_inst_1782_, lean_object* v_inst_1783_, lean_object* v_entry_1784_){
_start:
{
lean_object* v_aig_1785_; lean_object* v_ref_1786_; lean_object* v___x_1787_; lean_object* v_state_1788_; lean_object* v_cnf_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1809_; 
v_aig_1785_ = lean_ctor_get(v_entry_1784_, 0);
v_ref_1786_ = lean_ctor_get(v_entry_1784_, 1);
lean_inc_ref(v_ref_1786_);
v___x_1787_ = l_Std_Sat_AIG_toCNF_State_empty___redArg(v_aig_1785_);
v_state_1788_ = l_Std_Sat_AIG_toCNF_x27___redArg(v_inst_1782_, v_inst_1783_, v_entry_1784_, v___x_1787_);
v_cnf_1789_ = lean_ctor_get(v_state_1788_, 0);
v_isSharedCheck_1809_ = !lean_is_exclusive(v_state_1788_);
if (v_isSharedCheck_1809_ == 0)
{
lean_object* v_unused_1810_; 
v_unused_1810_ = lean_ctor_get(v_state_1788_, 1);
lean_dec(v_unused_1810_);
v___x_1791_ = v_state_1788_;
v_isShared_1792_ = v_isSharedCheck_1809_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_cnf_1789_);
lean_dec(v_state_1788_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1809_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v_gate_1793_; uint8_t v_invert_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___y_1798_; uint8_t v___y_1799_; 
v_gate_1793_ = lean_ctor_get(v_ref_1786_, 0);
lean_inc(v_gate_1793_);
v_invert_1794_ = lean_ctor_get_uint8(v_ref_1786_, sizeof(void*)*1);
lean_dec_ref(v_ref_1786_);
v___x_1795_ = ((lean_object*)(l_Std_Sat_AIG_toCNF___redArg___closed__0));
v___x_1796_ = l_ByteArray_empty;
if (v_invert_1794_ == 0)
{
lean_object* v___x_1805_; uint8_t v___x_1806_; 
v___x_1805_ = lean_array_push(v___x_1795_, v_gate_1793_);
v___x_1806_ = 1;
v___y_1798_ = v___x_1805_;
v___y_1799_ = v___x_1806_;
goto v___jp_1797_;
}
else
{
lean_object* v___x_1807_; uint8_t v___x_1808_; 
v___x_1807_ = lean_array_push(v___x_1795_, v_gate_1793_);
v___x_1808_ = 0;
v___y_1798_ = v___x_1807_;
v___y_1799_ = v___x_1808_;
goto v___jp_1797_;
}
v___jp_1797_:
{
lean_object* v___x_1800_; lean_object* v___x_1802_; 
v___x_1800_ = lean_byte_array_push(v___x_1796_, v___y_1799_);
if (v_isShared_1792_ == 0)
{
lean_ctor_set(v___x_1791_, 1, v___x_1800_);
lean_ctor_set(v___x_1791_, 0, v___y_1798_);
v___x_1802_ = v___x_1791_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v___y_1798_);
lean_ctor_set(v_reuseFailAlloc_1804_, 1, v___x_1800_);
v___x_1802_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
lean_object* v___x_1803_; 
v___x_1803_ = lean_array_push(v_cnf_1789_, v___x_1802_);
return v___x_1803_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF___boxed(lean_object* v_00_u03b1_1811_, lean_object* v_inst_1812_, lean_object* v_inst_1813_, lean_object* v_entry_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l_Std_Sat_AIG_toCNF(v_00_u03b1_1811_, v_inst_1812_, v_inst_1813_, v_entry_1814_);
lean_dec_ref(v_inst_1813_);
lean_dec_ref(v_inst_1812_);
return v_res_1815_;
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
