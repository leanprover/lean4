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
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg(lean_object* v_output_18_, lean_object* v_lhs_19_, lean_object* v_rhs_20_, uint8_t v_linv_21_, uint8_t v_rinv_22_){
_start:
{
lean_object* v___y_24_; lean_object* v___y_25_; lean_object* v___y_26_; uint8_t v___y_27_; lean_object* v___x_31_; lean_object* v___x_32_; uint8_t v___x_33_; uint8_t v___y_35_; lean_object* v___y_36_; lean_object* v___y_37_; lean_object* v___y_38_; uint8_t v___y_39_; lean_object* v___x_42_; lean_object* v___y_44_; lean_object* v___y_45_; lean_object* v___y_46_; uint8_t v___y_47_; lean_object* v___y_54_; uint8_t v___y_55_; 
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
v___x_28_ = lean_byte_array_push(v___y_24_, v___y_27_);
v___x_29_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_29_, 0, v___y_26_);
lean_ctor_set(v___x_29_, 1, v___x_28_);
v___x_30_ = lean_array_push(v___y_25_, v___x_29_);
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
v___y_24_ = v___x_40_;
v___y_25_ = v___y_37_;
v___y_26_ = v___x_41_;
v___y_27_ = v___x_33_;
goto v___jp_23_;
}
else
{
v___y_24_ = v___x_40_;
v___y_25_ = v___y_37_;
v___y_26_ = v___x_41_;
v___y_27_ = v___y_35_;
goto v___jp_23_;
}
}
v___jp_43_:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; uint8_t v___x_51_; lean_object* v___x_52_; 
v___x_48_ = lean_byte_array_push(v___x_42_, v___y_47_);
v___x_49_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_49_, 0, v___y_46_);
lean_ctor_set(v___x_49_, 1, v___x_48_);
v___x_50_ = lean_array_push(v___y_44_, v___x_49_);
v___x_51_ = 1;
v___x_52_ = lean_obj_once(&l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg___closed__0, &l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg___closed__0_once, _init_l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg___closed__0);
if (v_linv_21_ == 0)
{
v___y_35_ = v___x_51_;
v___y_36_ = v___x_52_;
v___y_37_ = v___x_50_;
v___y_38_ = v___y_45_;
v___y_39_ = v___x_33_;
goto v___jp_34_;
}
else
{
v___y_35_ = v___x_51_;
v___y_36_ = v___x_52_;
v___y_37_ = v___x_50_;
v___y_38_ = v___y_45_;
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
v___y_45_ = v___y_54_;
v___y_46_ = v___x_59_;
v___y_47_ = v___x_60_;
goto v___jp_43_;
}
else
{
lean_object* v___x_61_; 
lean_inc(v_rhs_20_);
v___x_61_ = lean_array_push(v___x_32_, v_rhs_20_);
v___y_44_ = v___x_58_;
v___y_45_ = v___y_54_;
v___y_46_ = v___x_61_;
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
uint8_t v___y_97_; lean_object* v___y_98_; lean_object* v___y_99_; lean_object* v___y_100_; uint8_t v___y_101_; uint8_t v___y_107_; lean_object* v___y_108_; uint8_t v___y_109_; lean_object* v___y_110_; lean_object* v___y_111_; uint8_t v___y_112_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; uint8_t v___y_122_; uint8_t v___y_123_; lean_object* v___y_124_; uint8_t v___y_125_; lean_object* v___y_129_; uint8_t v___y_130_; lean_object* v___y_131_; lean_object* v___y_132_; uint8_t v___y_133_; lean_object* v___y_140_; lean_object* v___y_141_; uint8_t v___y_142_; uint8_t v___y_151_; 
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
v___x_102_ = lean_byte_array_push(v___y_99_, v___y_101_);
v___x_103_ = lean_byte_array_push(v___x_102_, v___y_97_);
v___x_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_104_, 0, v___y_100_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
v___x_105_ = lean_array_push(v___y_98_, v___x_104_);
return v___x_105_;
}
v___jp_106_:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
lean_inc_ref(v___y_108_);
v___x_113_ = lean_byte_array_push(v___y_108_, v___y_112_);
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
v___y_98_ = v___x_117_;
v___y_99_ = v___y_108_;
v___y_100_ = v___x_114_;
v___y_101_ = v___y_109_;
goto v___jp_96_;
}
else
{
v___y_97_ = v___y_107_;
v___y_98_ = v___x_117_;
v___y_99_ = v___y_108_;
v___y_100_ = v___x_114_;
v___y_101_ = v___y_107_;
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
v___y_107_ = v___y_122_;
v___y_108_ = v___x_126_;
v___y_109_ = v___y_123_;
v___y_110_ = v___y_124_;
v___y_111_ = v___x_127_;
v___y_112_ = v___y_122_;
goto v___jp_106_;
}
else
{
v___y_107_ = v___y_122_;
v___y_108_ = v___x_126_;
v___y_109_ = v___y_123_;
v___y_110_ = v___y_124_;
v___y_111_ = v___x_127_;
v___y_112_ = v___y_123_;
goto v___jp_106_;
}
}
v___jp_128_:
{
lean_object* v___x_134_; uint8_t v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_134_ = lean_byte_array_push(v___y_129_, v___y_133_);
v___x_135_ = 0;
v___x_136_ = lean_byte_array_push(v___x_134_, v___x_135_);
v___x_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_137_, 0, v___y_131_);
lean_ctor_set(v___x_137_, 1, v___x_136_);
v___x_138_ = lean_array_push(v___y_132_, v___x_137_);
if (v_cinv_93_ == 0)
{
v___y_122_ = v___x_135_;
v___y_123_ = v___y_130_;
v___y_124_ = v___x_138_;
v___y_125_ = v___y_130_;
goto v___jp_121_;
}
else
{
v___y_122_ = v___x_135_;
v___y_123_ = v___y_130_;
v___y_124_ = v___x_138_;
v___y_125_ = v___x_135_;
goto v___jp_121_;
}
}
v___jp_139_:
{
lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
lean_inc_ref(v___y_140_);
v___x_143_ = lean_byte_array_push(v___y_140_, v___y_142_);
lean_inc(v_output_89_);
v___x_144_ = lean_array_push(v___y_141_, v_output_89_);
v___x_145_ = 1;
v___x_146_ = lean_byte_array_push(v___x_143_, v___x_145_);
lean_inc_ref(v___x_144_);
v___x_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_144_);
lean_ctor_set(v___x_147_, 1, v___x_146_);
v___x_148_ = lean_array_push(v___x_118_, v___x_147_);
if (v_tinv_94_ == 0)
{
v___y_129_ = v___y_140_;
v___y_130_ = v___x_145_;
v___y_131_ = v___x_144_;
v___y_132_ = v___x_148_;
v___y_133_ = v___x_145_;
goto v___jp_128_;
}
else
{
uint8_t v___x_149_; 
v___x_149_ = 0;
v___y_129_ = v___y_140_;
v___y_130_ = v___x_145_;
v___y_131_ = v___x_144_;
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
v___y_140_ = v___x_152_;
v___y_141_ = v___x_153_;
v___y_142_ = v___x_154_;
goto v___jp_139_;
}
else
{
uint8_t v___x_155_; 
v___x_155_ = 1;
v___y_140_ = v___x_152_;
v___y_141_ = v___x_153_;
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty___redArg(lean_object* v_aig_477_){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_478_ = ((lean_object*)(l_Std_Sat_AIG_toCNF_State_empty___redArg___closed__0));
v___x_479_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___redArg(v_aig_477_);
v___x_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_480_, 0, v___x_478_);
lean_ctor_set(v___x_480_, 1, v___x_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty___redArg___boxed(lean_object* v_aig_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Std_Sat_AIG_toCNF_State_empty___redArg(v_aig_481_);
lean_dec_ref(v_aig_481_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty(lean_object* v_00_u03b1_483_, lean_object* v_inst_484_, lean_object* v_inst_485_, lean_object* v_aig_486_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l_Std_Sat_AIG_toCNF_State_empty___redArg(v_aig_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty___boxed(lean_object* v_00_u03b1_488_, lean_object* v_inst_489_, lean_object* v_inst_490_, lean_object* v_aig_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Std_Sat_AIG_toCNF_State_empty(v_00_u03b1_488_, v_inst_489_, v_inst_490_, v_aig_491_);
lean_dec_ref(v_aig_491_);
lean_dec_ref(v_inst_490_);
lean_dec_ref(v_inst_489_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_cast___redArg(lean_object* v_aig2_493_, lean_object* v_state_494_){
_start:
{
lean_object* v_cnf_495_; lean_object* v_cache_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_504_; 
v_cnf_495_ = lean_ctor_get(v_state_494_, 0);
v_cache_496_ = lean_ctor_get(v_state_494_, 1);
v_isSharedCheck_504_ = !lean_is_exclusive(v_state_494_);
if (v_isSharedCheck_504_ == 0)
{
v___x_498_ = v_state_494_;
v_isShared_499_ = v_isSharedCheck_504_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_cache_496_);
lean_inc(v_cnf_495_);
lean_dec(v_state_494_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_504_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_500_; lean_object* v___x_502_; 
v___x_500_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_cast___redArg(v_aig2_493_, v_cache_496_);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 1, v___x_500_);
v___x_502_ = v___x_498_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_cnf_495_);
lean_ctor_set(v_reuseFailAlloc_503_, 1, v___x_500_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_cast___redArg___boxed(lean_object* v_aig2_505_, lean_object* v_state_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Std_Sat_AIG_toCNF_State_cast___redArg(v_aig2_505_, v_state_506_);
lean_dec_ref(v_aig2_505_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_cast(lean_object* v_00_u03b1_508_, lean_object* v_inst_509_, lean_object* v_inst_510_, lean_object* v_aig1_511_, lean_object* v_aig2_512_, lean_object* v_state_513_, lean_object* v_hprefix_514_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = l_Std_Sat_AIG_toCNF_State_cast___redArg(v_aig2_512_, v_state_513_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_cast___boxed(lean_object* v_00_u03b1_516_, lean_object* v_inst_517_, lean_object* v_inst_518_, lean_object* v_aig1_519_, lean_object* v_aig2_520_, lean_object* v_state_521_, lean_object* v_hprefix_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Std_Sat_AIG_toCNF_State_cast(v_00_u03b1_516_, v_inst_517_, v_inst_518_, v_aig1_519_, v_aig2_520_, v_state_521_, v_hprefix_522_);
lean_dec_ref(v_aig2_520_);
lean_dec_ref(v_aig1_519_);
lean_dec_ref(v_inst_518_);
lean_dec_ref(v_inst_517_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___redArg(lean_object* v_state_524_, lean_object* v_idx_525_){
_start:
{
lean_object* v_cnf_526_; lean_object* v_cache_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_537_; 
v_cnf_526_ = lean_ctor_get(v_state_524_, 0);
v_cache_527_ = lean_ctor_get(v_state_524_, 1);
v_isSharedCheck_537_ = !lean_is_exclusive(v_state_524_);
if (v_isSharedCheck_537_ == 0)
{
v___x_529_ = v_state_524_;
v_isShared_530_ = v_isSharedCheck_537_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_cache_527_);
lean_inc(v_cnf_526_);
lean_dec(v_state_524_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_537_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v_val_531_; lean_object* v_newCnf_532_; lean_object* v___x_533_; lean_object* v___x_535_; 
v_val_531_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg(v_cache_527_, v_idx_525_);
v_newCnf_532_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg(v_idx_525_);
v___x_533_ = l_Array_append___redArg(v_cnf_526_, v_newCnf_532_);
lean_dec_ref(v_newCnf_532_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 1, v_val_531_);
lean_ctor_set(v___x_529_, 0, v___x_533_);
v___x_535_ = v___x_529_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_533_);
lean_ctor_set(v_reuseFailAlloc_536_, 1, v_val_531_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse(lean_object* v_00_u03b1_538_, lean_object* v_inst_539_, lean_object* v_inst_540_, lean_object* v_aig_541_, lean_object* v_state_542_, lean_object* v_idx_543_, lean_object* v_h_544_, lean_object* v_htip_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___redArg(v_state_542_, v_idx_543_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___boxed(lean_object* v_00_u03b1_547_, lean_object* v_inst_548_, lean_object* v_inst_549_, lean_object* v_aig_550_, lean_object* v_state_551_, lean_object* v_idx_552_, lean_object* v_h_553_, lean_object* v_htip_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse(v_00_u03b1_547_, v_inst_548_, v_inst_549_, v_aig_550_, v_state_551_, v_idx_552_, v_h_553_, v_htip_554_);
lean_dec_ref(v_aig_550_);
lean_dec_ref(v_inst_549_);
lean_dec_ref(v_inst_548_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg(lean_object* v_state_556_, lean_object* v_idx_557_){
_start:
{
lean_object* v_cnf_558_; lean_object* v_cache_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_567_; 
v_cnf_558_ = lean_ctor_get(v_state_556_, 0);
v_cache_559_ = lean_ctor_get(v_state_556_, 1);
v_isSharedCheck_567_ = !lean_is_exclusive(v_state_556_);
if (v_isSharedCheck_567_ == 0)
{
v___x_561_ = v_state_556_;
v_isShared_562_ = v_isSharedCheck_567_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_cache_559_);
lean_inc(v_cnf_558_);
lean_dec(v_state_556_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_567_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v_val_563_; lean_object* v___x_565_; 
v_val_563_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg(v_cache_559_, v_idx_557_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 1, v_val_563_);
v___x_565_ = v___x_561_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_cnf_558_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_val_563_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg___boxed(lean_object* v_state_568_, lean_object* v_idx_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg(v_state_568_, v_idx_569_);
lean_dec(v_idx_569_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom(lean_object* v_00_u03b1_571_, lean_object* v_inst_572_, lean_object* v_inst_573_, lean_object* v_aig_574_, lean_object* v_a_575_, lean_object* v_state_576_, lean_object* v_idx_577_, lean_object* v_h_578_, lean_object* v_htip_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg(v_state_576_, v_idx_577_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___boxed(lean_object* v_00_u03b1_581_, lean_object* v_inst_582_, lean_object* v_inst_583_, lean_object* v_aig_584_, lean_object* v_a_585_, lean_object* v_state_586_, lean_object* v_idx_587_, lean_object* v_h_588_, lean_object* v_htip_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom(v_00_u03b1_581_, v_inst_582_, v_inst_583_, v_aig_584_, v_a_585_, v_state_586_, v_idx_587_, v_h_588_, v_htip_589_);
lean_dec(v_idx_587_);
lean_dec(v_a_585_);
lean_dec_ref(v_aig_584_);
lean_dec_ref(v_inst_583_);
lean_dec_ref(v_inst_582_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg(lean_object* v_lhs_591_, lean_object* v_rhs_592_, lean_object* v_state_593_, lean_object* v_idx_594_){
_start:
{
lean_object* v_cnf_595_; lean_object* v_cache_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_624_; 
v_cnf_595_ = lean_ctor_get(v_state_593_, 0);
v_cache_596_ = lean_ctor_get(v_state_593_, 1);
v_isSharedCheck_624_ = !lean_is_exclusive(v_state_593_);
if (v_isSharedCheck_624_ == 0)
{
v___x_598_ = v_state_593_;
v_isShared_599_ = v_isSharedCheck_624_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_cache_596_);
lean_inc(v_cnf_595_);
lean_dec(v_state_593_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_624_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; uint8_t v___y_604_; uint8_t v___y_605_; uint8_t v___y_613_; lean_object* v___x_619_; lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_600_ = lean_unsigned_to_nat(1u);
v___x_601_ = lean_nat_shiftr(v_lhs_591_, v___x_600_);
v___x_602_ = lean_nat_shiftr(v_rhs_592_, v___x_600_);
v___x_619_ = lean_nat_land(v___x_600_, v_lhs_591_);
v___x_620_ = lean_unsigned_to_nat(0u);
v___x_621_ = lean_nat_dec_eq(v___x_619_, v___x_620_);
lean_dec(v___x_619_);
if (v___x_621_ == 0)
{
uint8_t v___x_622_; 
v___x_622_ = 1;
v___y_613_ = v___x_622_;
goto v___jp_612_;
}
else
{
uint8_t v___x_623_; 
v___x_623_ = 0;
v___y_613_ = v___x_623_;
goto v___jp_612_;
}
v___jp_603_:
{
lean_object* v_val_606_; lean_object* v_newCnf_607_; lean_object* v___x_608_; lean_object* v___x_610_; 
v_val_606_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg(v_lhs_591_, v_rhs_592_, v_cache_596_, v_idx_594_);
v_newCnf_607_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg(v_idx_594_, v___x_601_, v___x_602_, v___y_604_, v___y_605_);
v___x_608_ = l_Array_append___redArg(v_cnf_595_, v_newCnf_607_);
lean_dec_ref(v_newCnf_607_);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 1, v_val_606_);
lean_ctor_set(v___x_598_, 0, v___x_608_);
v___x_610_ = v___x_598_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_608_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v_val_606_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
v___jp_612_:
{
lean_object* v___x_614_; lean_object* v___x_615_; uint8_t v___x_616_; 
v___x_614_ = lean_nat_land(v___x_600_, v_rhs_592_);
v___x_615_ = lean_unsigned_to_nat(0u);
v___x_616_ = lean_nat_dec_eq(v___x_614_, v___x_615_);
lean_dec(v___x_614_);
if (v___x_616_ == 0)
{
uint8_t v___x_617_; 
v___x_617_ = 1;
v___y_604_ = v___y_613_;
v___y_605_ = v___x_617_;
goto v___jp_603_;
}
else
{
uint8_t v___x_618_; 
v___x_618_ = 0;
v___y_604_ = v___y_613_;
v___y_605_ = v___x_618_;
goto v___jp_603_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg___boxed(lean_object* v_lhs_625_, lean_object* v_rhs_626_, lean_object* v_state_627_, lean_object* v_idx_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg(v_lhs_625_, v_rhs_626_, v_state_627_, v_idx_628_);
lean_dec(v_rhs_626_);
lean_dec(v_lhs_625_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate(lean_object* v_00_u03b1_630_, lean_object* v_inst_631_, lean_object* v_inst_632_, lean_object* v_aig_633_, lean_object* v_lhs_634_, lean_object* v_rhs_635_, lean_object* v_state_636_, lean_object* v_hlb_637_, lean_object* v_hrb_638_, lean_object* v_idx_639_, lean_object* v_h_640_, lean_object* v_htip_641_, lean_object* v_hl_642_, lean_object* v_hr_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg(v_lhs_634_, v_rhs_635_, v_state_636_, v_idx_639_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___boxed(lean_object* v_00_u03b1_645_, lean_object* v_inst_646_, lean_object* v_inst_647_, lean_object* v_aig_648_, lean_object* v_lhs_649_, lean_object* v_rhs_650_, lean_object* v_state_651_, lean_object* v_hlb_652_, lean_object* v_hrb_653_, lean_object* v_idx_654_, lean_object* v_h_655_, lean_object* v_htip_656_, lean_object* v_hl_657_, lean_object* v_hr_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate(v_00_u03b1_645_, v_inst_646_, v_inst_647_, v_aig_648_, v_lhs_649_, v_rhs_650_, v_state_651_, v_hlb_652_, v_hrb_653_, v_idx_654_, v_h_655_, v_htip_656_, v_hl_657_, v_hr_658_);
lean_dec(v_rhs_650_);
lean_dec(v_lhs_649_);
lean_dec_ref(v_aig_648_);
lean_dec_ref(v_inst_647_);
lean_dec_ref(v_inst_646_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___redArg(lean_object* v_state_660_, lean_object* v_cond_661_, lean_object* v_ifTrue_662_, lean_object* v_ifFalse_663_, lean_object* v_idx_664_){
_start:
{
lean_object* v_cnf_665_; lean_object* v_cache_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_704_; 
v_cnf_665_ = lean_ctor_get(v_state_660_, 0);
v_cache_666_ = lean_ctor_get(v_state_660_, 1);
v_isSharedCheck_704_ = !lean_is_exclusive(v_state_660_);
if (v_isSharedCheck_704_ == 0)
{
v___x_668_ = v_state_660_;
v_isShared_669_ = v_isSharedCheck_704_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_cache_666_);
lean_inc(v_cnf_665_);
lean_dec(v_state_660_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_704_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; uint8_t v___y_675_; uint8_t v___y_676_; uint8_t v___y_677_; uint8_t v___y_685_; uint8_t v___y_686_; uint8_t v___y_693_; lean_object* v___x_699_; lean_object* v___x_700_; uint8_t v___x_701_; 
v___x_670_ = lean_unsigned_to_nat(1u);
v___x_671_ = lean_nat_shiftr(v_cond_661_, v___x_670_);
v___x_672_ = lean_nat_shiftr(v_ifTrue_662_, v___x_670_);
v___x_673_ = lean_nat_shiftr(v_ifFalse_663_, v___x_670_);
v___x_699_ = lean_nat_land(v___x_670_, v_cond_661_);
v___x_700_ = lean_unsigned_to_nat(0u);
v___x_701_ = lean_nat_dec_eq(v___x_699_, v___x_700_);
lean_dec(v___x_699_);
if (v___x_701_ == 0)
{
uint8_t v___x_702_; 
v___x_702_ = 1;
v___y_693_ = v___x_702_;
goto v___jp_692_;
}
else
{
uint8_t v___x_703_; 
v___x_703_ = 0;
v___y_693_ = v___x_703_;
goto v___jp_692_;
}
v___jp_674_:
{
lean_object* v_val_678_; lean_object* v_newCnf_679_; lean_object* v___x_680_; lean_object* v___x_682_; 
v_val_678_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___redArg(v_cache_666_, v_cond_661_, v_ifTrue_662_, v_ifFalse_663_, v_idx_664_);
v_newCnf_679_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF___redArg(v_idx_664_, v___x_671_, v___x_672_, v___x_673_, v___y_676_, v___y_675_, v___y_677_);
v___x_680_ = l_Array_append___redArg(v_cnf_665_, v_newCnf_679_);
lean_dec_ref(v_newCnf_679_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 1, v_val_678_);
lean_ctor_set(v___x_668_, 0, v___x_680_);
v___x_682_ = v___x_668_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_680_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v_val_678_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
v___jp_684_:
{
lean_object* v___x_687_; lean_object* v___x_688_; uint8_t v___x_689_; 
v___x_687_ = lean_nat_land(v___x_670_, v_ifFalse_663_);
v___x_688_ = lean_unsigned_to_nat(0u);
v___x_689_ = lean_nat_dec_eq(v___x_687_, v___x_688_);
lean_dec(v___x_687_);
if (v___x_689_ == 0)
{
uint8_t v___x_690_; 
v___x_690_ = 1;
v___y_675_ = v___y_686_;
v___y_676_ = v___y_685_;
v___y_677_ = v___x_690_;
goto v___jp_674_;
}
else
{
uint8_t v___x_691_; 
v___x_691_ = 0;
v___y_675_ = v___y_686_;
v___y_676_ = v___y_685_;
v___y_677_ = v___x_691_;
goto v___jp_674_;
}
}
v___jp_692_:
{
lean_object* v___x_694_; lean_object* v___x_695_; uint8_t v___x_696_; 
v___x_694_ = lean_nat_land(v___x_670_, v_ifTrue_662_);
v___x_695_ = lean_unsigned_to_nat(0u);
v___x_696_ = lean_nat_dec_eq(v___x_694_, v___x_695_);
lean_dec(v___x_694_);
if (v___x_696_ == 0)
{
uint8_t v___x_697_; 
v___x_697_ = 1;
v___y_685_ = v___y_693_;
v___y_686_ = v___x_697_;
goto v___jp_684_;
}
else
{
uint8_t v___x_698_; 
v___x_698_ = 0;
v___y_685_ = v___y_693_;
v___y_686_ = v___x_698_;
goto v___jp_684_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___redArg___boxed(lean_object* v_state_705_, lean_object* v_cond_706_, lean_object* v_ifTrue_707_, lean_object* v_ifFalse_708_, lean_object* v_idx_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___redArg(v_state_705_, v_cond_706_, v_ifTrue_707_, v_ifFalse_708_, v_idx_709_);
lean_dec(v_ifFalse_708_);
lean_dec(v_ifTrue_707_);
lean_dec(v_cond_706_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte(lean_object* v_00_u03b1_711_, lean_object* v_inst_712_, lean_object* v_inst_713_, lean_object* v_aig_714_, lean_object* v_state_715_, lean_object* v_cond_716_, lean_object* v_ifTrue_717_, lean_object* v_ifFalse_718_, lean_object* v_idx_719_, lean_object* v_hcb_720_, lean_object* v_htb_721_, lean_object* v_hfb_722_, lean_object* v_h_723_, lean_object* v_hltc_724_, lean_object* v_hltt_725_, lean_object* v_hltf_726_, lean_object* v_hc_727_, lean_object* v_ht_728_, lean_object* v_hf_729_, lean_object* v_hdenote_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___redArg(v_state_715_, v_cond_716_, v_ifTrue_717_, v_ifFalse_718_, v_idx_719_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___boxed(lean_object** _args){
lean_object* v_00_u03b1_732_ = _args[0];
lean_object* v_inst_733_ = _args[1];
lean_object* v_inst_734_ = _args[2];
lean_object* v_aig_735_ = _args[3];
lean_object* v_state_736_ = _args[4];
lean_object* v_cond_737_ = _args[5];
lean_object* v_ifTrue_738_ = _args[6];
lean_object* v_ifFalse_739_ = _args[7];
lean_object* v_idx_740_ = _args[8];
lean_object* v_hcb_741_ = _args[9];
lean_object* v_htb_742_ = _args[10];
lean_object* v_hfb_743_ = _args[11];
lean_object* v_h_744_ = _args[12];
lean_object* v_hltc_745_ = _args[13];
lean_object* v_hltt_746_ = _args[14];
lean_object* v_hltf_747_ = _args[15];
lean_object* v_hc_748_ = _args[16];
lean_object* v_ht_749_ = _args[17];
lean_object* v_hf_750_ = _args[18];
lean_object* v_hdenote_751_ = _args[19];
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte(v_00_u03b1_732_, v_inst_733_, v_inst_734_, v_aig_735_, v_state_736_, v_cond_737_, v_ifTrue_738_, v_ifFalse_739_, v_idx_740_, v_hcb_741_, v_htb_742_, v_hfb_743_, v_h_744_, v_hltc_745_, v_hltt_746_, v_hltf_747_, v_hc_748_, v_ht_749_, v_hf_750_, v_hdenote_751_);
lean_dec(v_ifFalse_739_);
lean_dec(v_ifTrue_738_);
lean_dec(v_cond_737_);
lean_dec_ref(v_aig_735_);
lean_dec_ref(v_inst_734_);
lean_dec_ref(v_inst_733_);
return v_res_752_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg(lean_object* v_assign_753_, lean_object* v_state_754_){
_start:
{
lean_object* v_cnf_755_; uint8_t v___x_756_; 
v_cnf_755_ = lean_ctor_get(v_state_754_, 0);
v___x_756_ = l_Std_Sat_CNF_eval___redArg(v_assign_753_, v_cnf_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg___boxed(lean_object* v_assign_757_, lean_object* v_state_758_){
_start:
{
uint8_t v_res_759_; lean_object* v_r_760_; 
v_res_759_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg(v_assign_757_, v_state_758_);
lean_dec_ref(v_state_758_);
v_r_760_ = lean_box(v_res_759_);
return v_r_760_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval(lean_object* v_00_u03b1_761_, lean_object* v_inst_762_, lean_object* v_inst_763_, lean_object* v_aig_764_, lean_object* v_assign_765_, lean_object* v_state_766_){
_start:
{
uint8_t v___x_767_; 
v___x_767_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg(v_assign_765_, v_state_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___boxed(lean_object* v_00_u03b1_768_, lean_object* v_inst_769_, lean_object* v_inst_770_, lean_object* v_aig_771_, lean_object* v_assign_772_, lean_object* v_state_773_){
_start:
{
uint8_t v_res_774_; lean_object* v_r_775_; 
v_res_774_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval(v_00_u03b1_768_, v_inst_769_, v_inst_770_, v_aig_771_, v_assign_772_, v_state_773_);
lean_dec_ref(v_state_773_);
lean_dec_ref(v_aig_771_);
lean_dec_ref(v_inst_770_);
lean_dec_ref(v_inst_769_);
v_r_775_ = lean_box(v_res_774_);
return v_r_775_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg(lean_object* v_l0_776_, lean_object* v_l1_777_, lean_object* v_r0_778_, lean_object* v_r1_779_){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; uint8_t v___x_782_; 
v___x_780_ = lean_unsigned_to_nat(1u);
v___x_781_ = lean_nat_lxor(v_r0_778_, v___x_780_);
v___x_782_ = lean_nat_dec_eq(v_l0_776_, v___x_781_);
if (v___x_782_ == 0)
{
lean_object* v___x_783_; uint8_t v___x_784_; 
v___x_783_ = lean_nat_lxor(v_r1_779_, v___x_780_);
v___x_784_ = lean_nat_dec_eq(v_l0_776_, v___x_783_);
if (v___x_784_ == 0)
{
uint8_t v___x_785_; 
v___x_785_ = lean_nat_dec_eq(v_l1_777_, v___x_781_);
if (v___x_785_ == 0)
{
uint8_t v___x_786_; 
v___x_786_ = lean_nat_dec_eq(v_l1_777_, v___x_783_);
lean_dec(v___x_783_);
if (v___x_786_ == 0)
{
lean_object* v___x_787_; 
lean_dec(v___x_781_);
lean_dec(v_l1_777_);
lean_dec(v_l0_776_);
v___x_787_ = lean_box(0);
return v___x_787_;
}
else
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_788_ = lean_nat_lxor(v_l0_776_, v___x_780_);
lean_dec(v_l0_776_);
v___x_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_788_);
lean_ctor_set(v___x_789_, 1, v___x_781_);
v___x_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_790_, 0, v_l1_777_);
lean_ctor_set(v___x_790_, 1, v___x_789_);
v___x_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
return v___x_791_;
}
}
else
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
lean_dec(v___x_781_);
v___x_792_ = lean_nat_lxor(v_l0_776_, v___x_780_);
lean_dec(v_l0_776_);
v___x_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
lean_ctor_set(v___x_793_, 1, v___x_783_);
v___x_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_794_, 0, v_l1_777_);
lean_ctor_set(v___x_794_, 1, v___x_793_);
v___x_795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_795_, 0, v___x_794_);
return v___x_795_;
}
}
else
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
lean_dec(v___x_783_);
v___x_796_ = lean_nat_lxor(v_l1_777_, v___x_780_);
lean_dec(v_l1_777_);
v___x_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
lean_ctor_set(v___x_797_, 1, v___x_781_);
v___x_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_798_, 0, v_l0_776_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
v___x_799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
return v___x_799_;
}
}
else
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
lean_dec(v___x_781_);
v___x_800_ = lean_nat_lxor(v_l1_777_, v___x_780_);
lean_dec(v_l1_777_);
v___x_801_ = lean_nat_lxor(v_r1_779_, v___x_780_);
v___x_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_802_, 0, v___x_800_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
v___x_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_803_, 0, v_l0_776_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
v___x_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
return v___x_804_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg___boxed(lean_object* v_l0_805_, lean_object* v_l1_806_, lean_object* v_r0_807_, lean_object* v_r1_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg(v_l0_805_, v_l1_806_, v_r0_807_, v_r1_808_);
lean_dec(v_r1_808_);
lean_dec(v_r0_807_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go(lean_object* v_l_810_, lean_object* v_r_811_, lean_object* v_l0_812_, lean_object* v_l1_813_, lean_object* v_r0_814_, lean_object* v_r1_815_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg(v_l0_812_, v_l1_813_, v_r0_814_, v_r1_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___boxed(lean_object* v_l_817_, lean_object* v_r_818_, lean_object* v_l0_819_, lean_object* v_l1_820_, lean_object* v_r0_821_, lean_object* v_r1_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go(v_l_817_, v_r_818_, v_l0_819_, v_l1_820_, v_r0_821_, v_r1_822_);
lean_dec(v_r1_822_);
lean_dec(v_r0_821_);
lean_dec(v_r_818_);
lean_dec(v_l_817_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___redArg(lean_object* v_aig_824_, lean_object* v_root_825_){
_start:
{
lean_object* v_decls_826_; lean_object* v___x_827_; 
v_decls_826_ = lean_ctor_get(v_aig_824_, 0);
v___x_827_ = lean_array_fget_borrowed(v_decls_826_, v_root_825_);
if (lean_obj_tag(v___x_827_) == 2)
{
lean_object* v_l_828_; lean_object* v_r_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; uint8_t v___x_833_; 
v_l_828_ = lean_ctor_get(v___x_827_, 0);
v_r_829_ = lean_ctor_get(v___x_827_, 1);
v___x_830_ = lean_unsigned_to_nat(1u);
v___x_831_ = lean_nat_land(v___x_830_, v_l_828_);
v___x_832_ = lean_unsigned_to_nat(0u);
v___x_833_ = lean_nat_dec_eq(v___x_831_, v___x_832_);
lean_dec(v___x_831_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; uint8_t v___x_835_; 
v___x_834_ = lean_nat_land(v___x_830_, v_r_829_);
v___x_835_ = lean_nat_dec_eq(v___x_834_, v___x_832_);
lean_dec(v___x_834_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = lean_nat_shiftr(v_l_828_, v___x_830_);
v___x_837_ = lean_array_fget_borrowed(v_decls_826_, v___x_836_);
lean_dec(v___x_836_);
if (lean_obj_tag(v___x_837_) == 2)
{
lean_object* v_l_838_; lean_object* v_r_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v_l_838_ = lean_ctor_get(v___x_837_, 0);
v_r_839_ = lean_ctor_get(v___x_837_, 1);
v___x_840_ = lean_nat_shiftr(v_r_829_, v___x_830_);
v___x_841_ = lean_array_fget_borrowed(v_decls_826_, v___x_840_);
lean_dec(v___x_840_);
if (lean_obj_tag(v___x_841_) == 2)
{
lean_object* v_l_842_; lean_object* v_r_843_; lean_object* v___x_844_; 
v_l_842_ = lean_ctor_get(v___x_841_, 0);
v_r_843_ = lean_ctor_get(v___x_841_, 1);
lean_inc(v_r_839_);
lean_inc(v_l_838_);
v___x_844_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg(v_l_838_, v_r_839_, v_l_842_, v_r_843_);
return v___x_844_;
}
else
{
lean_object* v___x_845_; 
v___x_845_ = lean_box(0);
return v___x_845_;
}
}
else
{
lean_object* v___x_846_; 
v___x_846_ = lean_box(0);
return v___x_846_;
}
}
else
{
lean_object* v___x_847_; 
v___x_847_ = lean_box(0);
return v___x_847_;
}
}
else
{
lean_object* v___x_848_; 
v___x_848_ = lean_box(0);
return v___x_848_;
}
}
else
{
lean_object* v___x_849_; 
v___x_849_ = lean_box(0);
return v___x_849_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___redArg___boxed(lean_object* v_aig_850_, lean_object* v_root_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___redArg(v_aig_850_, v_root_851_);
lean_dec(v_root_851_);
lean_dec_ref(v_aig_850_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte(lean_object* v_00_u03b1_853_, lean_object* v_inst_854_, lean_object* v_inst_855_, lean_object* v_aig_856_, lean_object* v_root_857_, lean_object* v_h_858_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___redArg(v_aig_856_, v_root_857_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___boxed(lean_object* v_00_u03b1_860_, lean_object* v_inst_861_, lean_object* v_inst_862_, lean_object* v_aig_863_, lean_object* v_root_864_, lean_object* v_h_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte(v_00_u03b1_860_, v_inst_861_, v_inst_862_, v_aig_863_, v_root_864_, v_h_865_);
lean_dec(v_root_864_);
lean_dec_ref(v_aig_863_);
lean_dec_ref(v_inst_862_);
lean_dec_ref(v_inst_861_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_match__4_splitter___redArg(lean_object* v_x_867_, lean_object* v_h__1_868_, lean_object* v_h__2_869_){
_start:
{
if (lean_obj_tag(v_x_867_) == 2)
{
lean_object* v_l_870_; lean_object* v_r_871_; lean_object* v___x_872_; 
lean_dec(v_h__2_869_);
v_l_870_ = lean_ctor_get(v_x_867_, 0);
lean_inc(v_l_870_);
v_r_871_ = lean_ctor_get(v_x_867_, 1);
lean_inc(v_r_871_);
lean_dec_ref_known(v_x_867_, 2);
v___x_872_ = lean_apply_3(v_h__1_868_, v_l_870_, v_r_871_, lean_box(0));
return v___x_872_;
}
else
{
lean_object* v___x_873_; 
lean_dec(v_h__1_868_);
v___x_873_ = lean_apply_3(v_h__2_869_, v_x_867_, lean_box(0), lean_box(0));
return v___x_873_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_match__4_splitter(lean_object* v_00_u03b1_874_, lean_object* v_motive_875_, lean_object* v_x_876_, lean_object* v_h__1_877_, lean_object* v_h__2_878_){
_start:
{
if (lean_obj_tag(v_x_876_) == 2)
{
lean_object* v_l_879_; lean_object* v_r_880_; lean_object* v___x_881_; 
lean_dec(v_h__2_878_);
v_l_879_ = lean_ctor_get(v_x_876_, 0);
lean_inc(v_l_879_);
v_r_880_ = lean_ctor_get(v_x_876_, 1);
lean_inc(v_r_880_);
lean_dec_ref_known(v_x_876_, 2);
v___x_881_ = lean_apply_3(v_h__1_877_, v_l_879_, v_r_880_, lean_box(0));
return v___x_881_;
}
else
{
lean_object* v___x_882_; 
lean_dec(v_h__1_877_);
v___x_882_ = lean_apply_3(v_h__2_878_, v_x_876_, lean_box(0), lean_box(0));
return v___x_882_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_match__1_splitter___redArg(lean_object* v_x_883_, lean_object* v_x_884_, lean_object* v_h__1_885_, lean_object* v_h__2_886_){
_start:
{
if (lean_obj_tag(v_x_883_) == 2)
{
if (lean_obj_tag(v_x_884_) == 2)
{
lean_object* v_l_887_; lean_object* v_r_888_; lean_object* v_l_889_; lean_object* v_r_890_; lean_object* v___x_891_; 
lean_dec(v_h__2_886_);
v_l_887_ = lean_ctor_get(v_x_883_, 0);
lean_inc(v_l_887_);
v_r_888_ = lean_ctor_get(v_x_883_, 1);
lean_inc(v_r_888_);
lean_dec_ref_known(v_x_883_, 2);
v_l_889_ = lean_ctor_get(v_x_884_, 0);
lean_inc(v_l_889_);
v_r_890_ = lean_ctor_get(v_x_884_, 1);
lean_inc(v_r_890_);
lean_dec_ref_known(v_x_884_, 2);
v___x_891_ = lean_apply_6(v_h__1_885_, v_l_887_, v_r_888_, v_l_889_, v_r_890_, lean_box(0), lean_box(0));
return v___x_891_;
}
else
{
lean_object* v___x_892_; 
lean_dec(v_h__1_885_);
v___x_892_ = lean_apply_5(v_h__2_886_, v_x_883_, v_x_884_, lean_box(0), lean_box(0), lean_box(0));
return v___x_892_;
}
}
else
{
lean_object* v___x_893_; 
lean_dec(v_h__1_885_);
v___x_893_ = lean_apply_5(v_h__2_886_, v_x_883_, v_x_884_, lean_box(0), lean_box(0), lean_box(0));
return v___x_893_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_match__1_splitter(lean_object* v_00_u03b1_894_, lean_object* v_motive_895_, lean_object* v_x_896_, lean_object* v_x_897_, lean_object* v_h__1_898_, lean_object* v_h__2_899_){
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
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___redArg(lean_object* v_aig_907_, lean_object* v_upper_908_, lean_object* v_state_909_){
_start:
{
lean_object* v_cache_910_; lean_object* v___x_911_; uint8_t v___x_912_; 
v_cache_910_ = lean_ctor_get(v_state_909_, 1);
v___x_911_ = lean_array_fget_borrowed(v_cache_910_, v_upper_908_);
v___x_912_ = lean_unbox(v___x_911_);
if (v___x_912_ == 0)
{
lean_object* v_decls_913_; lean_object* v_decl_914_; 
v_decls_913_ = lean_ctor_get(v_aig_907_, 0);
v_decl_914_ = lean_array_fget_borrowed(v_decls_913_, v_upper_908_);
switch(lean_obj_tag(v_decl_914_))
{
case 0:
{
lean_object* v___x_915_; 
v___x_915_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___redArg(v_state_909_, v_upper_908_);
return v___x_915_;
}
case 1:
{
lean_object* v___x_916_; 
v___x_916_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg(v_state_909_, v_upper_908_);
lean_dec(v_upper_908_);
return v___x_916_;
}
default: 
{
lean_object* v_l_917_; lean_object* v_r_918_; lean_object* v___x_919_; 
v_l_917_ = lean_ctor_get(v_decl_914_, 0);
v_r_918_ = lean_ctor_get(v_decl_914_, 1);
v___x_919_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___redArg(v_aig_907_, v_upper_908_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v_val_922_; lean_object* v___x_923_; lean_object* v_val_924_; lean_object* v_val_925_; 
v___x_920_ = lean_unsigned_to_nat(1u);
v___x_921_ = lean_nat_shiftr(v_l_917_, v___x_920_);
v_val_922_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___redArg(v_aig_907_, v___x_921_, v_state_909_);
v___x_923_ = lean_nat_shiftr(v_r_918_, v___x_920_);
v_val_924_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___redArg(v_aig_907_, v___x_923_, v_val_922_);
v_val_925_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg(v_l_917_, v_r_918_, v_val_924_, v_upper_908_);
return v_val_925_;
}
else
{
lean_object* v_val_926_; lean_object* v_snd_927_; lean_object* v_fst_928_; lean_object* v_fst_929_; lean_object* v_snd_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v_val_933_; lean_object* v___x_934_; lean_object* v_val_935_; lean_object* v___x_936_; lean_object* v_val_937_; lean_object* v_val_938_; 
v_val_926_ = lean_ctor_get(v___x_919_, 0);
lean_inc(v_val_926_);
lean_dec_ref_known(v___x_919_, 1);
v_snd_927_ = lean_ctor_get(v_val_926_, 1);
lean_inc(v_snd_927_);
v_fst_928_ = lean_ctor_get(v_val_926_, 0);
lean_inc(v_fst_928_);
lean_dec(v_val_926_);
v_fst_929_ = lean_ctor_get(v_snd_927_, 0);
lean_inc(v_fst_929_);
v_snd_930_ = lean_ctor_get(v_snd_927_, 1);
lean_inc(v_snd_930_);
lean_dec(v_snd_927_);
v___x_931_ = lean_unsigned_to_nat(1u);
v___x_932_ = lean_nat_shiftr(v_fst_928_, v___x_931_);
v_val_933_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___redArg(v_aig_907_, v___x_932_, v_state_909_);
v___x_934_ = lean_nat_shiftr(v_fst_929_, v___x_931_);
v_val_935_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___redArg(v_aig_907_, v___x_934_, v_val_933_);
v___x_936_ = lean_nat_shiftr(v_snd_930_, v___x_931_);
v_val_937_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___redArg(v_aig_907_, v___x_936_, v_val_935_);
v_val_938_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___redArg(v_val_937_, v_fst_928_, v_fst_929_, v_snd_930_, v_upper_908_);
lean_dec(v_snd_930_);
lean_dec(v_fst_929_);
lean_dec(v_fst_928_);
return v_val_938_;
}
}
}
}
else
{
lean_dec(v_upper_908_);
return v_state_909_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___redArg___boxed(lean_object* v_aig_939_, lean_object* v_upper_940_, lean_object* v_state_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___redArg(v_aig_939_, v_upper_940_, v_state_941_);
lean_dec_ref(v_aig_939_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go(lean_object* v_00_u03b1_943_, lean_object* v_inst_944_, lean_object* v_inst_945_, lean_object* v_aig_946_, lean_object* v_upper_947_, lean_object* v_h_948_, lean_object* v_state_949_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___redArg(v_aig_946_, v_upper_947_, v_state_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___boxed(lean_object* v_00_u03b1_951_, lean_object* v_inst_952_, lean_object* v_inst_953_, lean_object* v_aig_954_, lean_object* v_upper_955_, lean_object* v_h_956_, lean_object* v_state_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go(v_00_u03b1_951_, v_inst_952_, v_inst_953_, v_aig_954_, v_upper_955_, v_h_956_, v_state_957_);
lean_dec_ref(v_aig_954_);
lean_dec_ref(v_inst_953_);
lean_dec_ref(v_inst_952_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go_match__103_splitter___redArg(lean_object* v_decl_959_, lean_object* v_h__1_960_, lean_object* v_h__2_961_, lean_object* v_h__3_962_){
_start:
{
switch(lean_obj_tag(v_decl_959_))
{
case 0:
{
lean_object* v___x_963_; 
lean_dec(v_h__3_962_);
lean_dec(v_h__2_961_);
v___x_963_ = lean_apply_1(v_h__1_960_, lean_box(0));
return v___x_963_;
}
case 1:
{
lean_object* v_idx_964_; lean_object* v___x_965_; 
lean_dec(v_h__3_962_);
lean_dec(v_h__1_960_);
v_idx_964_ = lean_ctor_get(v_decl_959_, 0);
lean_inc(v_idx_964_);
lean_dec_ref_known(v_decl_959_, 1);
v___x_965_ = lean_apply_2(v_h__2_961_, v_idx_964_, lean_box(0));
return v___x_965_;
}
default: 
{
lean_object* v_l_966_; lean_object* v_r_967_; lean_object* v___x_968_; 
lean_dec(v_h__2_961_);
lean_dec(v_h__1_960_);
v_l_966_ = lean_ctor_get(v_decl_959_, 0);
lean_inc(v_l_966_);
v_r_967_ = lean_ctor_get(v_decl_959_, 1);
lean_inc(v_r_967_);
lean_dec_ref_known(v_decl_959_, 2);
v___x_968_ = lean_apply_3(v_h__3_962_, v_l_966_, v_r_967_, lean_box(0));
return v___x_968_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go_match__103_splitter(lean_object* v_00_u03b1_969_, lean_object* v_motive_970_, lean_object* v_decl_971_, lean_object* v_h__1_972_, lean_object* v_h__2_973_, lean_object* v_h__3_974_){
_start:
{
switch(lean_obj_tag(v_decl_971_))
{
case 0:
{
lean_object* v___x_975_; 
lean_dec(v_h__3_974_);
lean_dec(v_h__2_973_);
v___x_975_ = lean_apply_1(v_h__1_972_, lean_box(0));
return v___x_975_;
}
case 1:
{
lean_object* v_idx_976_; lean_object* v___x_977_; 
lean_dec(v_h__3_974_);
lean_dec(v_h__1_972_);
v_idx_976_ = lean_ctor_get(v_decl_971_, 0);
lean_inc(v_idx_976_);
lean_dec_ref_known(v_decl_971_, 1);
v___x_977_ = lean_apply_2(v_h__2_973_, v_idx_976_, lean_box(0));
return v___x_977_;
}
default: 
{
lean_object* v_l_978_; lean_object* v_r_979_; lean_object* v___x_980_; 
lean_dec(v_h__2_973_);
lean_dec(v_h__1_972_);
v_l_978_ = lean_ctor_get(v_decl_971_, 0);
lean_inc(v_l_978_);
v_r_979_ = lean_ctor_get(v_decl_971_, 1);
lean_inc(v_r_979_);
lean_dec_ref_known(v_decl_971_, 2);
v___x_980_ = lean_apply_3(v_h__3_974_, v_l_978_, v_r_979_, lean_box(0));
return v___x_980_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go_match__81_splitter___redArg(lean_object* v_x_981_, lean_object* v_h__1_982_, lean_object* v_h__2_983_){
_start:
{
if (lean_obj_tag(v_x_981_) == 0)
{
lean_object* v___x_984_; 
lean_dec(v_h__1_982_);
v___x_984_ = lean_apply_1(v_h__2_983_, lean_box(0));
return v___x_984_;
}
else
{
lean_object* v_val_985_; lean_object* v_snd_986_; lean_object* v_fst_987_; lean_object* v_fst_988_; lean_object* v_snd_989_; lean_object* v___x_990_; 
lean_dec(v_h__2_983_);
v_val_985_ = lean_ctor_get(v_x_981_, 0);
lean_inc(v_val_985_);
lean_dec_ref_known(v_x_981_, 1);
v_snd_986_ = lean_ctor_get(v_val_985_, 1);
lean_inc(v_snd_986_);
v_fst_987_ = lean_ctor_get(v_val_985_, 0);
lean_inc(v_fst_987_);
lean_dec(v_val_985_);
v_fst_988_ = lean_ctor_get(v_snd_986_, 0);
lean_inc(v_fst_988_);
v_snd_989_ = lean_ctor_get(v_snd_986_, 1);
lean_inc(v_snd_989_);
lean_dec(v_snd_986_);
v___x_990_ = lean_apply_4(v_h__1_982_, v_fst_987_, v_fst_988_, v_snd_989_, lean_box(0));
return v___x_990_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go_match__81_splitter(lean_object* v_motive_991_, lean_object* v_x_992_, lean_object* v_h__1_993_, lean_object* v_h__2_994_){
_start:
{
if (lean_obj_tag(v_x_992_) == 0)
{
lean_object* v___x_995_; 
lean_dec(v_h__1_993_);
v___x_995_ = lean_apply_1(v_h__2_994_, lean_box(0));
return v___x_995_;
}
else
{
lean_object* v_val_996_; lean_object* v_snd_997_; lean_object* v_fst_998_; lean_object* v_fst_999_; lean_object* v_snd_1000_; lean_object* v___x_1001_; 
lean_dec(v_h__2_994_);
v_val_996_ = lean_ctor_get(v_x_992_, 0);
lean_inc(v_val_996_);
lean_dec_ref_known(v_x_992_, 1);
v_snd_997_ = lean_ctor_get(v_val_996_, 1);
lean_inc(v_snd_997_);
v_fst_998_ = lean_ctor_get(v_val_996_, 0);
lean_inc(v_fst_998_);
lean_dec(v_val_996_);
v_fst_999_ = lean_ctor_get(v_snd_997_, 0);
lean_inc(v_fst_999_);
v_snd_1000_ = lean_ctor_get(v_snd_997_, 1);
lean_inc(v_snd_1000_);
lean_dec(v_snd_997_);
v___x_1001_ = lean_apply_4(v_h__1_993_, v_fst_998_, v_fst_999_, v_snd_1000_, lean_box(0));
return v___x_1001_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__52_splitter___redArg(lean_object* v_x_1002_, lean_object* v_h__1_1003_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = lean_apply_2(v_h__1_1003_, v_x_1002_, lean_box(0));
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__52_splitter(lean_object* v_00_u03b1_1005_, lean_object* v_inst_1006_, lean_object* v_inst_1007_, lean_object* v_aig_1008_, lean_object* v_upper_1009_, lean_object* v_h_1010_, lean_object* v_state_1011_, lean_object* v_cond_1012_, lean_object* v_ifTrue_1013_, lean_object* v_ifFalse_1014_, lean_object* v_hltc_1015_, lean_object* v_motive_1016_, lean_object* v_x_1017_, lean_object* v_h__1_1018_){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = lean_apply_2(v_h__1_1018_, v_x_1017_, lean_box(0));
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__52_splitter___boxed(lean_object* v_00_u03b1_1020_, lean_object* v_inst_1021_, lean_object* v_inst_1022_, lean_object* v_aig_1023_, lean_object* v_upper_1024_, lean_object* v_h_1025_, lean_object* v_state_1026_, lean_object* v_cond_1027_, lean_object* v_ifTrue_1028_, lean_object* v_ifFalse_1029_, lean_object* v_hltc_1030_, lean_object* v_motive_1031_, lean_object* v_x_1032_, lean_object* v_h__1_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__52_splitter(v_00_u03b1_1020_, v_inst_1021_, v_inst_1022_, v_aig_1023_, v_upper_1024_, v_h_1025_, v_state_1026_, v_cond_1027_, v_ifTrue_1028_, v_ifFalse_1029_, v_hltc_1030_, v_motive_1031_, v_x_1032_, v_h__1_1033_);
lean_dec(v_ifFalse_1029_);
lean_dec(v_ifTrue_1028_);
lean_dec(v_cond_1027_);
lean_dec_ref(v_state_1026_);
lean_dec(v_upper_1024_);
lean_dec_ref(v_aig_1023_);
lean_dec_ref(v_inst_1022_);
lean_dec_ref(v_inst_1021_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__50_splitter___redArg(lean_object* v_x_1035_, lean_object* v_h__1_1036_){
_start:
{
lean_object* v___x_1037_; 
v___x_1037_ = lean_apply_2(v_h__1_1036_, v_x_1035_, lean_box(0));
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__50_splitter(lean_object* v_00_u03b1_1038_, lean_object* v_inst_1039_, lean_object* v_inst_1040_, lean_object* v_aig_1041_, lean_object* v_upper_1042_, lean_object* v_h_1043_, lean_object* v_cond_1044_, lean_object* v_ifTrue_1045_, lean_object* v_ifFalse_1046_, lean_object* v_hltt_1047_, lean_object* v_cstate_1048_, lean_object* v_motive_1049_, lean_object* v_x_1050_, lean_object* v_h__1_1051_){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = lean_apply_2(v_h__1_1051_, v_x_1050_, lean_box(0));
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__50_splitter___boxed(lean_object* v_00_u03b1_1053_, lean_object* v_inst_1054_, lean_object* v_inst_1055_, lean_object* v_aig_1056_, lean_object* v_upper_1057_, lean_object* v_h_1058_, lean_object* v_cond_1059_, lean_object* v_ifTrue_1060_, lean_object* v_ifFalse_1061_, lean_object* v_hltt_1062_, lean_object* v_cstate_1063_, lean_object* v_motive_1064_, lean_object* v_x_1065_, lean_object* v_h__1_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__50_splitter(v_00_u03b1_1053_, v_inst_1054_, v_inst_1055_, v_aig_1056_, v_upper_1057_, v_h_1058_, v_cond_1059_, v_ifTrue_1060_, v_ifFalse_1061_, v_hltt_1062_, v_cstate_1063_, v_motive_1064_, v_x_1065_, v_h__1_1066_);
lean_dec_ref(v_cstate_1063_);
lean_dec(v_ifFalse_1061_);
lean_dec(v_ifTrue_1060_);
lean_dec(v_cond_1059_);
lean_dec(v_upper_1057_);
lean_dec_ref(v_aig_1056_);
lean_dec_ref(v_inst_1055_);
lean_dec_ref(v_inst_1054_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__48_splitter___redArg(lean_object* v_x_1068_, lean_object* v_h__1_1069_){
_start:
{
lean_object* v___x_1070_; 
v___x_1070_ = lean_apply_2(v_h__1_1069_, v_x_1068_, lean_box(0));
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__48_splitter(lean_object* v_00_u03b1_1071_, lean_object* v_inst_1072_, lean_object* v_inst_1073_, lean_object* v_aig_1074_, lean_object* v_upper_1075_, lean_object* v_h_1076_, lean_object* v_cond_1077_, lean_object* v_ifTrue_1078_, lean_object* v_ifFalse_1079_, lean_object* v_hltf_1080_, lean_object* v_tstate_1081_, lean_object* v_motive_1082_, lean_object* v_x_1083_, lean_object* v_h__1_1084_){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = lean_apply_2(v_h__1_1084_, v_x_1083_, lean_box(0));
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__48_splitter___boxed(lean_object* v_00_u03b1_1086_, lean_object* v_inst_1087_, lean_object* v_inst_1088_, lean_object* v_aig_1089_, lean_object* v_upper_1090_, lean_object* v_h_1091_, lean_object* v_cond_1092_, lean_object* v_ifTrue_1093_, lean_object* v_ifFalse_1094_, lean_object* v_hltf_1095_, lean_object* v_tstate_1096_, lean_object* v_motive_1097_, lean_object* v_x_1098_, lean_object* v_h__1_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__48_splitter(v_00_u03b1_1086_, v_inst_1087_, v_inst_1088_, v_aig_1089_, v_upper_1090_, v_h_1091_, v_cond_1092_, v_ifTrue_1093_, v_ifFalse_1094_, v_hltf_1095_, v_tstate_1096_, v_motive_1097_, v_x_1098_, v_h__1_1099_);
lean_dec_ref(v_tstate_1096_);
lean_dec(v_ifFalse_1094_);
lean_dec(v_ifTrue_1093_);
lean_dec(v_cond_1092_);
lean_dec(v_upper_1090_);
lean_dec_ref(v_aig_1089_);
lean_dec_ref(v_inst_1088_);
lean_dec_ref(v_inst_1087_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__45_splitter___redArg(lean_object* v_x_1101_, lean_object* v_h__1_1102_){
_start:
{
lean_object* v___x_1103_; 
v___x_1103_ = lean_apply_2(v_h__1_1102_, v_x_1101_, lean_box(0));
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__45_splitter(lean_object* v_00_u03b1_1104_, lean_object* v_inst_1105_, lean_object* v_inst_1106_, lean_object* v_aig_1107_, lean_object* v_upper_1108_, lean_object* v_h_1109_, lean_object* v_fstate_1110_, lean_object* v_motive_1111_, lean_object* v_x_1112_, lean_object* v_h__1_1113_){
_start:
{
lean_object* v___x_1114_; 
v___x_1114_ = lean_apply_2(v_h__1_1113_, v_x_1112_, lean_box(0));
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__45_splitter___boxed(lean_object* v_00_u03b1_1115_, lean_object* v_inst_1116_, lean_object* v_inst_1117_, lean_object* v_aig_1118_, lean_object* v_upper_1119_, lean_object* v_h_1120_, lean_object* v_fstate_1121_, lean_object* v_motive_1122_, lean_object* v_x_1123_, lean_object* v_h__1_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__45_splitter(v_00_u03b1_1115_, v_inst_1116_, v_inst_1117_, v_aig_1118_, v_upper_1119_, v_h_1120_, v_fstate_1121_, v_motive_1122_, v_x_1123_, v_h__1_1124_);
lean_dec_ref(v_fstate_1121_);
lean_dec(v_upper_1119_);
lean_dec_ref(v_aig_1118_);
lean_dec_ref(v_inst_1117_);
lean_dec_ref(v_inst_1116_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__56_splitter___redArg(lean_object* v_x_1126_, lean_object* v_h__1_1127_){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = lean_apply_2(v_h__1_1127_, v_x_1126_, lean_box(0));
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__56_splitter(lean_object* v_00_u03b1_1129_, lean_object* v_inst_1130_, lean_object* v_inst_1131_, lean_object* v_aig_1132_, lean_object* v_upper_1133_, lean_object* v_h_1134_, lean_object* v_state_1135_, lean_object* v_lhs_1136_, lean_object* v_rhs_1137_, lean_object* v_this_1138_, lean_object* v_motive_1139_, lean_object* v_x_1140_, lean_object* v_h__1_1141_){
_start:
{
lean_object* v___x_1142_; 
v___x_1142_ = lean_apply_2(v_h__1_1141_, v_x_1140_, lean_box(0));
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__56_splitter___boxed(lean_object* v_00_u03b1_1143_, lean_object* v_inst_1144_, lean_object* v_inst_1145_, lean_object* v_aig_1146_, lean_object* v_upper_1147_, lean_object* v_h_1148_, lean_object* v_state_1149_, lean_object* v_lhs_1150_, lean_object* v_rhs_1151_, lean_object* v_this_1152_, lean_object* v_motive_1153_, lean_object* v_x_1154_, lean_object* v_h__1_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__56_splitter(v_00_u03b1_1143_, v_inst_1144_, v_inst_1145_, v_aig_1146_, v_upper_1147_, v_h_1148_, v_state_1149_, v_lhs_1150_, v_rhs_1151_, v_this_1152_, v_motive_1153_, v_x_1154_, v_h__1_1155_);
lean_dec(v_rhs_1151_);
lean_dec(v_lhs_1150_);
lean_dec_ref(v_state_1149_);
lean_dec(v_upper_1147_);
lean_dec_ref(v_aig_1146_);
lean_dec_ref(v_inst_1145_);
lean_dec_ref(v_inst_1144_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__54_splitter___redArg(lean_object* v_x_1157_, lean_object* v_h__1_1158_){
_start:
{
lean_object* v___x_1159_; 
v___x_1159_ = lean_apply_2(v_h__1_1158_, v_x_1157_, lean_box(0));
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__54_splitter(lean_object* v_00_u03b1_1160_, lean_object* v_inst_1161_, lean_object* v_inst_1162_, lean_object* v_aig_1163_, lean_object* v_upper_1164_, lean_object* v_h_1165_, lean_object* v_lhs_1166_, lean_object* v_rhs_1167_, lean_object* v_this_1168_, lean_object* v_lstate_1169_, lean_object* v_motive_1170_, lean_object* v_x_1171_, lean_object* v_h__1_1172_){
_start:
{
lean_object* v___x_1173_; 
v___x_1173_ = lean_apply_2(v_h__1_1172_, v_x_1171_, lean_box(0));
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__54_splitter___boxed(lean_object* v_00_u03b1_1174_, lean_object* v_inst_1175_, lean_object* v_inst_1176_, lean_object* v_aig_1177_, lean_object* v_upper_1178_, lean_object* v_h_1179_, lean_object* v_lhs_1180_, lean_object* v_rhs_1181_, lean_object* v_this_1182_, lean_object* v_lstate_1183_, lean_object* v_motive_1184_, lean_object* v_x_1185_, lean_object* v_h__1_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_match__54_splitter(v_00_u03b1_1174_, v_inst_1175_, v_inst_1176_, v_aig_1177_, v_upper_1178_, v_h_1179_, v_lhs_1180_, v_rhs_1181_, v_this_1182_, v_lstate_1183_, v_motive_1184_, v_x_1185_, v_h__1_1186_);
lean_dec_ref(v_lstate_1183_);
lean_dec(v_rhs_1181_);
lean_dec(v_lhs_1180_);
lean_dec(v_upper_1178_);
lean_dec_ref(v_aig_1177_);
lean_dec_ref(v_inst_1176_);
lean_dec_ref(v_inst_1175_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__0_spec__1___redArg(lean_object* v_cache_1188_, lean_object* v_idx_1189_){
_start:
{
uint8_t v___x_1190_; lean_object* v___x_1191_; lean_object* v_out_1192_; 
v___x_1190_ = 1;
v___x_1191_ = lean_box(v___x_1190_);
v_out_1192_ = lean_array_fset(v_cache_1188_, v_idx_1189_, v___x_1191_);
return v_out_1192_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_cache_1193_, lean_object* v_idx_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__0_spec__1___redArg(v_cache_1193_, v_idx_1194_);
lean_dec(v_idx_1194_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__0___redArg(lean_object* v_inst_1196_, lean_object* v_inst_1197_, lean_object* v_aig_1198_, lean_object* v_state_1199_, lean_object* v_idx_1200_){
_start:
{
lean_object* v_cnf_1201_; lean_object* v_cache_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1212_; 
v_cnf_1201_ = lean_ctor_get(v_state_1199_, 0);
v_cache_1202_ = lean_ctor_get(v_state_1199_, 1);
v_isSharedCheck_1212_ = !lean_is_exclusive(v_state_1199_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1204_ = v_state_1199_;
v_isShared_1205_ = v_isSharedCheck_1212_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_cache_1202_);
lean_inc(v_cnf_1201_);
lean_dec(v_state_1199_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1212_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v_val_1206_; lean_object* v_newCnf_1207_; lean_object* v___x_1208_; lean_object* v___x_1210_; 
v_val_1206_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__0_spec__1___redArg(v_cache_1202_, v_idx_1200_);
v_newCnf_1207_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg(v_idx_1200_);
v___x_1208_ = l_Array_append___redArg(v_cnf_1201_, v_newCnf_1207_);
lean_dec_ref(v_newCnf_1207_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 1, v_val_1206_);
lean_ctor_set(v___x_1204_, 0, v___x_1208_);
v___x_1210_ = v___x_1204_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1208_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v_val_1206_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__0___redArg___boxed(lean_object* v_inst_1213_, lean_object* v_inst_1214_, lean_object* v_aig_1215_, lean_object* v_state_1216_, lean_object* v_idx_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__0___redArg(v_inst_1213_, v_inst_1214_, v_aig_1215_, v_state_1216_, v_idx_1217_);
lean_dec_ref(v_aig_1215_);
lean_dec_ref(v_inst_1214_);
lean_dec_ref(v_inst_1213_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__2___redArg(lean_object* v_aig_1219_, lean_object* v_root_1220_){
_start:
{
lean_object* v_decls_1221_; lean_object* v___x_1222_; 
v_decls_1221_ = lean_ctor_get(v_aig_1219_, 0);
v___x_1222_ = lean_array_fget_borrowed(v_decls_1221_, v_root_1220_);
if (lean_obj_tag(v___x_1222_) == 2)
{
lean_object* v_l_1223_; lean_object* v_r_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; uint8_t v___x_1228_; 
v_l_1223_ = lean_ctor_get(v___x_1222_, 0);
v_r_1224_ = lean_ctor_get(v___x_1222_, 1);
v___x_1225_ = lean_unsigned_to_nat(1u);
v___x_1226_ = lean_nat_land(v___x_1225_, v_l_1223_);
v___x_1227_ = lean_unsigned_to_nat(0u);
v___x_1228_ = lean_nat_dec_eq(v___x_1226_, v___x_1227_);
lean_dec(v___x_1226_);
if (v___x_1228_ == 0)
{
lean_object* v___x_1229_; uint8_t v___x_1230_; 
v___x_1229_ = lean_nat_land(v___x_1225_, v_r_1224_);
v___x_1230_ = lean_nat_dec_eq(v___x_1229_, v___x_1227_);
lean_dec(v___x_1229_);
if (v___x_1230_ == 0)
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1231_ = lean_nat_shiftr(v_l_1223_, v___x_1225_);
v___x_1232_ = lean_array_fget_borrowed(v_decls_1221_, v___x_1231_);
lean_dec(v___x_1231_);
if (lean_obj_tag(v___x_1232_) == 2)
{
lean_object* v_l_1233_; lean_object* v_r_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v_l_1233_ = lean_ctor_get(v___x_1232_, 0);
v_r_1234_ = lean_ctor_get(v___x_1232_, 1);
v___x_1235_ = lean_nat_shiftr(v_r_1224_, v___x_1225_);
v___x_1236_ = lean_array_fget_borrowed(v_decls_1221_, v___x_1235_);
lean_dec(v___x_1235_);
if (lean_obj_tag(v___x_1236_) == 2)
{
lean_object* v_l_1237_; lean_object* v_r_1238_; lean_object* v___x_1239_; 
v_l_1237_ = lean_ctor_get(v___x_1236_, 0);
v_r_1238_ = lean_ctor_get(v___x_1236_, 1);
lean_inc(v_r_1234_);
lean_inc(v_l_1233_);
v___x_1239_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte_go___redArg(v_l_1233_, v_r_1234_, v_l_1237_, v_r_1238_);
return v___x_1239_;
}
else
{
lean_object* v___x_1240_; 
v___x_1240_ = lean_box(0);
return v___x_1240_;
}
}
else
{
lean_object* v___x_1241_; 
v___x_1241_ = lean_box(0);
return v___x_1241_;
}
}
else
{
lean_object* v___x_1242_; 
v___x_1242_ = lean_box(0);
return v___x_1242_;
}
}
else
{
lean_object* v___x_1243_; 
v___x_1243_ = lean_box(0);
return v___x_1243_;
}
}
else
{
lean_object* v___x_1244_; 
v___x_1244_ = lean_box(0);
return v___x_1244_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__2___redArg___boxed(lean_object* v_aig_1245_, lean_object* v_root_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__2___redArg(v_aig_1245_, v_root_1246_);
lean_dec(v_root_1246_);
lean_dec_ref(v_aig_1245_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4_spec__8___redArg(lean_object* v_cache_1248_, lean_object* v_cond_1249_, lean_object* v_ifTrue_1250_, lean_object* v_ifFalse_1251_, lean_object* v_idx_1252_){
_start:
{
uint8_t v___x_1253_; lean_object* v___x_1254_; lean_object* v_out_1255_; 
v___x_1253_ = 1;
v___x_1254_ = lean_box(v___x_1253_);
v_out_1255_ = lean_array_fset(v_cache_1248_, v_idx_1252_, v___x_1254_);
return v_out_1255_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4_spec__8___redArg___boxed(lean_object* v_cache_1256_, lean_object* v_cond_1257_, lean_object* v_ifTrue_1258_, lean_object* v_ifFalse_1259_, lean_object* v_idx_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4_spec__8___redArg(v_cache_1256_, v_cond_1257_, v_ifTrue_1258_, v_ifFalse_1259_, v_idx_1260_);
lean_dec(v_idx_1260_);
lean_dec(v_ifFalse_1259_);
lean_dec(v_ifTrue_1258_);
lean_dec(v_cond_1257_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4___redArg(lean_object* v_inst_1262_, lean_object* v_inst_1263_, lean_object* v_aig_1264_, lean_object* v_state_1265_, lean_object* v_cond_1266_, lean_object* v_ifTrue_1267_, lean_object* v_ifFalse_1268_, lean_object* v_idx_1269_){
_start:
{
lean_object* v_cnf_1270_; lean_object* v_cache_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1309_; 
v_cnf_1270_ = lean_ctor_get(v_state_1265_, 0);
v_cache_1271_ = lean_ctor_get(v_state_1265_, 1);
v_isSharedCheck_1309_ = !lean_is_exclusive(v_state_1265_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1273_ = v_state_1265_;
v_isShared_1274_ = v_isSharedCheck_1309_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_cache_1271_);
lean_inc(v_cnf_1270_);
lean_dec(v_state_1265_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1309_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; uint8_t v___y_1280_; uint8_t v___y_1281_; uint8_t v___y_1282_; uint8_t v___y_1290_; uint8_t v___y_1291_; uint8_t v___y_1298_; lean_object* v___x_1304_; lean_object* v___x_1305_; uint8_t v___x_1306_; 
v___x_1275_ = lean_unsigned_to_nat(1u);
v___x_1276_ = lean_nat_shiftr(v_cond_1266_, v___x_1275_);
v___x_1277_ = lean_nat_shiftr(v_ifTrue_1267_, v___x_1275_);
v___x_1278_ = lean_nat_shiftr(v_ifFalse_1268_, v___x_1275_);
v___x_1304_ = lean_nat_land(v___x_1275_, v_cond_1266_);
v___x_1305_ = lean_unsigned_to_nat(0u);
v___x_1306_ = lean_nat_dec_eq(v___x_1304_, v___x_1305_);
lean_dec(v___x_1304_);
if (v___x_1306_ == 0)
{
uint8_t v___x_1307_; 
v___x_1307_ = 1;
v___y_1298_ = v___x_1307_;
goto v___jp_1297_;
}
else
{
uint8_t v___x_1308_; 
v___x_1308_ = 0;
v___y_1298_ = v___x_1308_;
goto v___jp_1297_;
}
v___jp_1279_:
{
lean_object* v_val_1283_; lean_object* v_newCnf_1284_; lean_object* v___x_1285_; lean_object* v___x_1287_; 
v_val_1283_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4_spec__8___redArg(v_cache_1271_, v_cond_1266_, v_ifTrue_1267_, v_ifFalse_1268_, v_idx_1269_);
v_newCnf_1284_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_iteToCNF___redArg(v_idx_1269_, v___x_1276_, v___x_1277_, v___x_1278_, v___y_1281_, v___y_1280_, v___y_1282_);
v___x_1285_ = l_Array_append___redArg(v_cnf_1270_, v_newCnf_1284_);
lean_dec_ref(v_newCnf_1284_);
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 1, v_val_1283_);
lean_ctor_set(v___x_1273_, 0, v___x_1285_);
v___x_1287_ = v___x_1273_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v___x_1285_);
lean_ctor_set(v_reuseFailAlloc_1288_, 1, v_val_1283_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
v___jp_1289_:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; uint8_t v___x_1294_; 
v___x_1292_ = lean_nat_land(v___x_1275_, v_ifFalse_1268_);
v___x_1293_ = lean_unsigned_to_nat(0u);
v___x_1294_ = lean_nat_dec_eq(v___x_1292_, v___x_1293_);
lean_dec(v___x_1292_);
if (v___x_1294_ == 0)
{
uint8_t v___x_1295_; 
v___x_1295_ = 1;
v___y_1280_ = v___y_1291_;
v___y_1281_ = v___y_1290_;
v___y_1282_ = v___x_1295_;
goto v___jp_1279_;
}
else
{
uint8_t v___x_1296_; 
v___x_1296_ = 0;
v___y_1280_ = v___y_1291_;
v___y_1281_ = v___y_1290_;
v___y_1282_ = v___x_1296_;
goto v___jp_1279_;
}
}
v___jp_1297_:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; uint8_t v___x_1301_; 
v___x_1299_ = lean_nat_land(v___x_1275_, v_ifTrue_1267_);
v___x_1300_ = lean_unsigned_to_nat(0u);
v___x_1301_ = lean_nat_dec_eq(v___x_1299_, v___x_1300_);
lean_dec(v___x_1299_);
if (v___x_1301_ == 0)
{
uint8_t v___x_1302_; 
v___x_1302_ = 1;
v___y_1290_ = v___y_1298_;
v___y_1291_ = v___x_1302_;
goto v___jp_1289_;
}
else
{
uint8_t v___x_1303_; 
v___x_1303_ = 0;
v___y_1290_ = v___y_1298_;
v___y_1291_ = v___x_1303_;
goto v___jp_1289_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4___redArg___boxed(lean_object* v_inst_1310_, lean_object* v_inst_1311_, lean_object* v_aig_1312_, lean_object* v_state_1313_, lean_object* v_cond_1314_, lean_object* v_ifTrue_1315_, lean_object* v_ifFalse_1316_, lean_object* v_idx_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4___redArg(v_inst_1310_, v_inst_1311_, v_aig_1312_, v_state_1313_, v_cond_1314_, v_ifTrue_1315_, v_ifFalse_1316_, v_idx_1317_);
lean_dec(v_ifFalse_1316_);
lean_dec(v_ifTrue_1315_);
lean_dec(v_cond_1314_);
lean_dec_ref(v_aig_1312_);
lean_dec_ref(v_inst_1311_);
lean_dec_ref(v_inst_1310_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__3_spec__6___redArg(lean_object* v_lhs_1319_, lean_object* v_rhs_1320_, lean_object* v_cache_1321_, lean_object* v_idx_1322_){
_start:
{
uint8_t v___x_1323_; lean_object* v___x_1324_; lean_object* v_out_1325_; 
v___x_1323_ = 1;
v___x_1324_ = lean_box(v___x_1323_);
v_out_1325_ = lean_array_fset(v_cache_1321_, v_idx_1322_, v___x_1324_);
return v_out_1325_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__3_spec__6___redArg___boxed(lean_object* v_lhs_1326_, lean_object* v_rhs_1327_, lean_object* v_cache_1328_, lean_object* v_idx_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__3_spec__6___redArg(v_lhs_1326_, v_rhs_1327_, v_cache_1328_, v_idx_1329_);
lean_dec(v_idx_1329_);
lean_dec(v_rhs_1327_);
lean_dec(v_lhs_1326_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__3___redArg(lean_object* v_inst_1331_, lean_object* v_inst_1332_, lean_object* v_aig_1333_, lean_object* v_lhs_1334_, lean_object* v_rhs_1335_, lean_object* v_state_1336_, lean_object* v_idx_1337_){
_start:
{
lean_object* v_cnf_1338_; lean_object* v_cache_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1367_; 
v_cnf_1338_ = lean_ctor_get(v_state_1336_, 0);
v_cache_1339_ = lean_ctor_get(v_state_1336_, 1);
v_isSharedCheck_1367_ = !lean_is_exclusive(v_state_1336_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1341_ = v_state_1336_;
v_isShared_1342_ = v_isSharedCheck_1367_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_cache_1339_);
lean_inc(v_cnf_1338_);
lean_dec(v_state_1336_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1367_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; uint8_t v___y_1347_; uint8_t v___y_1348_; uint8_t v___y_1356_; lean_object* v___x_1362_; lean_object* v___x_1363_; uint8_t v___x_1364_; 
v___x_1343_ = lean_unsigned_to_nat(1u);
v___x_1344_ = lean_nat_shiftr(v_lhs_1334_, v___x_1343_);
v___x_1345_ = lean_nat_shiftr(v_rhs_1335_, v___x_1343_);
v___x_1362_ = lean_nat_land(v___x_1343_, v_lhs_1334_);
v___x_1363_ = lean_unsigned_to_nat(0u);
v___x_1364_ = lean_nat_dec_eq(v___x_1362_, v___x_1363_);
lean_dec(v___x_1362_);
if (v___x_1364_ == 0)
{
uint8_t v___x_1365_; 
v___x_1365_ = 1;
v___y_1356_ = v___x_1365_;
goto v___jp_1355_;
}
else
{
uint8_t v___x_1366_; 
v___x_1366_ = 0;
v___y_1356_ = v___x_1366_;
goto v___jp_1355_;
}
v___jp_1346_:
{
lean_object* v_val_1349_; lean_object* v_newCnf_1350_; lean_object* v___x_1351_; lean_object* v___x_1353_; 
v_val_1349_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__3_spec__6___redArg(v_lhs_1334_, v_rhs_1335_, v_cache_1339_, v_idx_1337_);
v_newCnf_1350_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg(v_idx_1337_, v___x_1344_, v___x_1345_, v___y_1347_, v___y_1348_);
v___x_1351_ = l_Array_append___redArg(v_cnf_1338_, v_newCnf_1350_);
lean_dec_ref(v_newCnf_1350_);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 1, v_val_1349_);
lean_ctor_set(v___x_1341_, 0, v___x_1351_);
v___x_1353_ = v___x_1341_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1351_);
lean_ctor_set(v_reuseFailAlloc_1354_, 1, v_val_1349_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
v___jp_1355_:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; uint8_t v___x_1359_; 
v___x_1357_ = lean_nat_land(v___x_1343_, v_rhs_1335_);
v___x_1358_ = lean_unsigned_to_nat(0u);
v___x_1359_ = lean_nat_dec_eq(v___x_1357_, v___x_1358_);
lean_dec(v___x_1357_);
if (v___x_1359_ == 0)
{
uint8_t v___x_1360_; 
v___x_1360_ = 1;
v___y_1347_ = v___y_1356_;
v___y_1348_ = v___x_1360_;
goto v___jp_1346_;
}
else
{
uint8_t v___x_1361_; 
v___x_1361_ = 0;
v___y_1347_ = v___y_1356_;
v___y_1348_ = v___x_1361_;
goto v___jp_1346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__3___redArg___boxed(lean_object* v_inst_1368_, lean_object* v_inst_1369_, lean_object* v_aig_1370_, lean_object* v_lhs_1371_, lean_object* v_rhs_1372_, lean_object* v_state_1373_, lean_object* v_idx_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__3___redArg(v_inst_1368_, v_inst_1369_, v_aig_1370_, v_lhs_1371_, v_rhs_1372_, v_state_1373_, v_idx_1374_);
lean_dec(v_rhs_1372_);
lean_dec(v_lhs_1371_);
lean_dec_ref(v_aig_1370_);
lean_dec_ref(v_inst_1369_);
lean_dec_ref(v_inst_1368_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__1_spec__3___redArg(lean_object* v_cache_1376_, lean_object* v_idx_1377_){
_start:
{
uint8_t v___x_1378_; lean_object* v___x_1379_; lean_object* v_out_1380_; 
v___x_1378_ = 1;
v___x_1379_ = lean_box(v___x_1378_);
v_out_1380_ = lean_array_fset(v_cache_1376_, v_idx_1377_, v___x_1379_);
return v_out_1380_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_cache_1381_, lean_object* v_idx_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__1_spec__3___redArg(v_cache_1381_, v_idx_1382_);
lean_dec(v_idx_1382_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__1___redArg(lean_object* v_inst_1384_, lean_object* v_inst_1385_, lean_object* v_aig_1386_, lean_object* v_a_1387_, lean_object* v_state_1388_, lean_object* v_idx_1389_){
_start:
{
lean_object* v_cnf_1390_; lean_object* v_cache_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1399_; 
v_cnf_1390_ = lean_ctor_get(v_state_1388_, 0);
v_cache_1391_ = lean_ctor_get(v_state_1388_, 1);
v_isSharedCheck_1399_ = !lean_is_exclusive(v_state_1388_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1393_ = v_state_1388_;
v_isShared_1394_ = v_isSharedCheck_1399_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_cache_1391_);
lean_inc(v_cnf_1390_);
lean_dec(v_state_1388_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1399_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v_val_1395_; lean_object* v___x_1397_; 
v_val_1395_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__1_spec__3___redArg(v_cache_1391_, v_idx_1389_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 1, v_val_1395_);
v___x_1397_ = v___x_1393_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_cnf_1390_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v_val_1395_);
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
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__1___redArg___boxed(lean_object* v_inst_1400_, lean_object* v_inst_1401_, lean_object* v_aig_1402_, lean_object* v_a_1403_, lean_object* v_state_1404_, lean_object* v_idx_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__1___redArg(v_inst_1400_, v_inst_1401_, v_aig_1402_, v_a_1403_, v_state_1404_, v_idx_1405_);
lean_dec(v_idx_1405_);
lean_dec(v_a_1403_);
lean_dec_ref(v_aig_1402_);
lean_dec_ref(v_inst_1401_);
lean_dec_ref(v_inst_1400_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0___redArg(lean_object* v_inst_1407_, lean_object* v_inst_1408_, lean_object* v_aig_1409_, lean_object* v_upper_1410_, lean_object* v_state_1411_){
_start:
{
lean_object* v_cache_1412_; lean_object* v___x_1413_; uint8_t v___x_1414_; 
v_cache_1412_ = lean_ctor_get(v_state_1411_, 1);
v___x_1413_ = lean_array_fget_borrowed(v_cache_1412_, v_upper_1410_);
v___x_1414_ = lean_unbox(v___x_1413_);
if (v___x_1414_ == 0)
{
lean_object* v_decls_1415_; lean_object* v_decl_1416_; 
v_decls_1415_ = lean_ctor_get(v_aig_1409_, 0);
v_decl_1416_ = lean_array_fget_borrowed(v_decls_1415_, v_upper_1410_);
switch(lean_obj_tag(v_decl_1416_))
{
case 0:
{
lean_object* v___x_1417_; 
v___x_1417_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__0___redArg(v_inst_1407_, v_inst_1408_, v_aig_1409_, v_state_1411_, v_upper_1410_);
return v___x_1417_;
}
case 1:
{
lean_object* v_idx_1418_; lean_object* v___x_1419_; 
v_idx_1418_ = lean_ctor_get(v_decl_1416_, 0);
v___x_1419_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__1___redArg(v_inst_1407_, v_inst_1408_, v_aig_1409_, v_idx_1418_, v_state_1411_, v_upper_1410_);
lean_dec(v_upper_1410_);
return v___x_1419_;
}
default: 
{
lean_object* v_l_1420_; lean_object* v_r_1421_; lean_object* v___x_1422_; 
v_l_1420_ = lean_ctor_get(v_decl_1416_, 0);
v_r_1421_ = lean_ctor_get(v_decl_1416_, 1);
v___x_1422_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__2___redArg(v_aig_1409_, v_upper_1410_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v_val_1425_; lean_object* v___x_1426_; lean_object* v_val_1427_; lean_object* v___x_1428_; 
v___x_1423_ = lean_unsigned_to_nat(1u);
v___x_1424_ = lean_nat_shiftr(v_l_1420_, v___x_1423_);
v_val_1425_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0___redArg(v_inst_1407_, v_inst_1408_, v_aig_1409_, v___x_1424_, v_state_1411_);
v___x_1426_ = lean_nat_shiftr(v_r_1421_, v___x_1423_);
v_val_1427_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0___redArg(v_inst_1407_, v_inst_1408_, v_aig_1409_, v___x_1426_, v_val_1425_);
v___x_1428_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__3___redArg(v_inst_1407_, v_inst_1408_, v_aig_1409_, v_l_1420_, v_r_1421_, v_val_1427_, v_upper_1410_);
return v___x_1428_;
}
else
{
lean_object* v_val_1429_; lean_object* v_snd_1430_; lean_object* v_fst_1431_; lean_object* v_fst_1432_; lean_object* v_snd_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v_val_1436_; lean_object* v___x_1437_; lean_object* v_val_1438_; lean_object* v___x_1439_; lean_object* v_val_1440_; lean_object* v___x_1441_; 
v_val_1429_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_val_1429_);
lean_dec_ref_known(v___x_1422_, 1);
v_snd_1430_ = lean_ctor_get(v_val_1429_, 1);
lean_inc(v_snd_1430_);
v_fst_1431_ = lean_ctor_get(v_val_1429_, 0);
lean_inc(v_fst_1431_);
lean_dec(v_val_1429_);
v_fst_1432_ = lean_ctor_get(v_snd_1430_, 0);
lean_inc(v_fst_1432_);
v_snd_1433_ = lean_ctor_get(v_snd_1430_, 1);
lean_inc(v_snd_1433_);
lean_dec(v_snd_1430_);
v___x_1434_ = lean_unsigned_to_nat(1u);
v___x_1435_ = lean_nat_shiftr(v_fst_1431_, v___x_1434_);
v_val_1436_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0___redArg(v_inst_1407_, v_inst_1408_, v_aig_1409_, v___x_1435_, v_state_1411_);
v___x_1437_ = lean_nat_shiftr(v_fst_1432_, v___x_1434_);
v_val_1438_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0___redArg(v_inst_1407_, v_inst_1408_, v_aig_1409_, v___x_1437_, v_val_1436_);
v___x_1439_ = lean_nat_shiftr(v_snd_1433_, v___x_1434_);
v_val_1440_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0___redArg(v_inst_1407_, v_inst_1408_, v_aig_1409_, v___x_1439_, v_val_1438_);
v___x_1441_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4___redArg(v_inst_1407_, v_inst_1408_, v_aig_1409_, v_val_1440_, v_fst_1431_, v_fst_1432_, v_snd_1433_, v_upper_1410_);
lean_dec(v_snd_1433_);
lean_dec(v_fst_1432_);
lean_dec(v_fst_1431_);
return v___x_1441_;
}
}
}
}
else
{
lean_dec(v_upper_1410_);
return v_state_1411_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0___redArg___boxed(lean_object* v_inst_1442_, lean_object* v_inst_1443_, lean_object* v_aig_1444_, lean_object* v_upper_1445_, lean_object* v_state_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0___redArg(v_inst_1442_, v_inst_1443_, v_aig_1444_, v_upper_1445_, v_state_1446_);
lean_dec_ref(v_aig_1444_);
lean_dec_ref(v_inst_1443_);
lean_dec_ref(v_inst_1442_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_x27___redArg(lean_object* v_inst_1448_, lean_object* v_inst_1449_, lean_object* v_entry_1450_, lean_object* v_state_1451_){
_start:
{
lean_object* v_ref_1452_; lean_object* v_aig_1453_; lean_object* v_gate_1454_; lean_object* v___x_1455_; 
v_ref_1452_ = lean_ctor_get(v_entry_1450_, 1);
lean_inc_ref(v_ref_1452_);
v_aig_1453_ = lean_ctor_get(v_entry_1450_, 0);
lean_inc_ref(v_aig_1453_);
lean_dec_ref(v_entry_1450_);
v_gate_1454_ = lean_ctor_get(v_ref_1452_, 0);
lean_inc(v_gate_1454_);
lean_dec_ref(v_ref_1452_);
v___x_1455_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0___redArg(v_inst_1448_, v_inst_1449_, v_aig_1453_, v_gate_1454_, v_state_1451_);
lean_dec_ref(v_aig_1453_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_x27___redArg___boxed(lean_object* v_inst_1456_, lean_object* v_inst_1457_, lean_object* v_entry_1458_, lean_object* v_state_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l_Std_Sat_AIG_toCNF_x27___redArg(v_inst_1456_, v_inst_1457_, v_entry_1458_, v_state_1459_);
lean_dec_ref(v_inst_1457_);
lean_dec_ref(v_inst_1456_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_x27(lean_object* v_00_u03b1_1461_, lean_object* v_inst_1462_, lean_object* v_inst_1463_, lean_object* v_entry_1464_, lean_object* v_state_1465_){
_start:
{
lean_object* v___x_1466_; 
v___x_1466_ = l_Std_Sat_AIG_toCNF_x27___redArg(v_inst_1462_, v_inst_1463_, v_entry_1464_, v_state_1465_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_x27___boxed(lean_object* v_00_u03b1_1467_, lean_object* v_inst_1468_, lean_object* v_inst_1469_, lean_object* v_entry_1470_, lean_object* v_state_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l_Std_Sat_AIG_toCNF_x27(v_00_u03b1_1467_, v_inst_1468_, v_inst_1469_, v_entry_1470_, v_state_1471_);
lean_dec_ref(v_inst_1469_);
lean_dec_ref(v_inst_1468_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__2(lean_object* v_00_u03b1_1473_, lean_object* v_inst_1474_, lean_object* v_inst_1475_, lean_object* v_aig_1476_, lean_object* v_root_1477_, lean_object* v_h_1478_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__2___redArg(v_aig_1476_, v_root_1477_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1480_, lean_object* v_inst_1481_, lean_object* v_inst_1482_, lean_object* v_aig_1483_, lean_object* v_root_1484_, lean_object* v_h_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_detectIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__2(v_00_u03b1_1480_, v_inst_1481_, v_inst_1482_, v_aig_1483_, v_root_1484_, v_h_1485_);
lean_dec(v_root_1484_);
lean_dec_ref(v_aig_1483_);
lean_dec_ref(v_inst_1482_);
lean_dec_ref(v_inst_1481_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0(lean_object* v_00_u03b1_1487_, lean_object* v_inst_1488_, lean_object* v_inst_1489_, lean_object* v_aig_1490_, lean_object* v_upper_1491_, lean_object* v_h_1492_, lean_object* v_state_1493_){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0___redArg(v_inst_1488_, v_inst_1489_, v_aig_1490_, v_upper_1491_, v_state_1493_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0___boxed(lean_object* v_00_u03b1_1495_, lean_object* v_inst_1496_, lean_object* v_inst_1497_, lean_object* v_aig_1498_, lean_object* v_upper_1499_, lean_object* v_h_1500_, lean_object* v_state_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0(v_00_u03b1_1495_, v_inst_1496_, v_inst_1497_, v_aig_1498_, v_upper_1499_, v_h_1500_, v_state_1501_);
lean_dec_ref(v_aig_1498_);
lean_dec_ref(v_inst_1497_);
lean_dec_ref(v_inst_1496_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1503_, lean_object* v_inst_1504_, lean_object* v_inst_1505_, lean_object* v_aig_1506_, lean_object* v_cnf_1507_, lean_object* v_cache_1508_, lean_object* v_idx_1509_, lean_object* v_h_1510_, lean_object* v_htip_1511_){
_start:
{
lean_object* v___x_1512_; 
v___x_1512_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__0_spec__1___redArg(v_cache_1508_, v_idx_1509_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1513_, lean_object* v_inst_1514_, lean_object* v_inst_1515_, lean_object* v_aig_1516_, lean_object* v_cnf_1517_, lean_object* v_cache_1518_, lean_object* v_idx_1519_, lean_object* v_h_1520_, lean_object* v_htip_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__0_spec__1(v_00_u03b1_1513_, v_inst_1514_, v_inst_1515_, v_aig_1516_, v_cnf_1517_, v_cache_1518_, v_idx_1519_, v_h_1520_, v_htip_1521_);
lean_dec(v_idx_1519_);
lean_dec_ref(v_cnf_1517_);
lean_dec_ref(v_aig_1516_);
lean_dec_ref(v_inst_1515_);
lean_dec_ref(v_inst_1514_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__0(lean_object* v_00_u03b1_1523_, lean_object* v_inst_1524_, lean_object* v_inst_1525_, lean_object* v_aig_1526_, lean_object* v_state_1527_, lean_object* v_idx_1528_, lean_object* v_h_1529_, lean_object* v_htip_1530_){
_start:
{
lean_object* v___x_1531_; 
v___x_1531_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__0___redArg(v_inst_1524_, v_inst_1525_, v_aig_1526_, v_state_1527_, v_idx_1528_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1532_, lean_object* v_inst_1533_, lean_object* v_inst_1534_, lean_object* v_aig_1535_, lean_object* v_state_1536_, lean_object* v_idx_1537_, lean_object* v_h_1538_, lean_object* v_htip_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__0(v_00_u03b1_1532_, v_inst_1533_, v_inst_1534_, v_aig_1535_, v_state_1536_, v_idx_1537_, v_h_1538_, v_htip_1539_);
lean_dec_ref(v_aig_1535_);
lean_dec_ref(v_inst_1534_);
lean_dec_ref(v_inst_1533_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_1541_, lean_object* v_inst_1542_, lean_object* v_inst_1543_, lean_object* v_aig_1544_, lean_object* v_cnf_1545_, lean_object* v_a_1546_, lean_object* v_cache_1547_, lean_object* v_idx_1548_, lean_object* v_h_1549_, lean_object* v_htip_1550_){
_start:
{
lean_object* v___x_1551_; 
v___x_1551_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__1_spec__3___redArg(v_cache_1547_, v_idx_1548_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_1552_, lean_object* v_inst_1553_, lean_object* v_inst_1554_, lean_object* v_aig_1555_, lean_object* v_cnf_1556_, lean_object* v_a_1557_, lean_object* v_cache_1558_, lean_object* v_idx_1559_, lean_object* v_h_1560_, lean_object* v_htip_1561_){
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__1_spec__3(v_00_u03b1_1552_, v_inst_1553_, v_inst_1554_, v_aig_1555_, v_cnf_1556_, v_a_1557_, v_cache_1558_, v_idx_1559_, v_h_1560_, v_htip_1561_);
lean_dec(v_idx_1559_);
lean_dec(v_a_1557_);
lean_dec_ref(v_cnf_1556_);
lean_dec_ref(v_aig_1555_);
lean_dec_ref(v_inst_1554_);
lean_dec_ref(v_inst_1553_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__1(lean_object* v_00_u03b1_1563_, lean_object* v_inst_1564_, lean_object* v_inst_1565_, lean_object* v_aig_1566_, lean_object* v_a_1567_, lean_object* v_state_1568_, lean_object* v_idx_1569_, lean_object* v_h_1570_, lean_object* v_htip_1571_){
_start:
{
lean_object* v___x_1572_; 
v___x_1572_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__1___redArg(v_inst_1564_, v_inst_1565_, v_aig_1566_, v_a_1567_, v_state_1568_, v_idx_1569_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1573_, lean_object* v_inst_1574_, lean_object* v_inst_1575_, lean_object* v_aig_1576_, lean_object* v_a_1577_, lean_object* v_state_1578_, lean_object* v_idx_1579_, lean_object* v_h_1580_, lean_object* v_htip_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__1(v_00_u03b1_1573_, v_inst_1574_, v_inst_1575_, v_aig_1576_, v_a_1577_, v_state_1578_, v_idx_1579_, v_h_1580_, v_htip_1581_);
lean_dec(v_idx_1579_);
lean_dec(v_a_1577_);
lean_dec_ref(v_aig_1576_);
lean_dec_ref(v_inst_1575_);
lean_dec_ref(v_inst_1574_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__3_spec__6(lean_object* v_00_u03b1_1583_, lean_object* v_inst_1584_, lean_object* v_inst_1585_, lean_object* v_aig_1586_, lean_object* v_cnf_1587_, lean_object* v_lhs_1588_, lean_object* v_rhs_1589_, lean_object* v_cache_1590_, lean_object* v_hlb_1591_, lean_object* v_hrb_1592_, lean_object* v_idx_1593_, lean_object* v_h_1594_, lean_object* v_htip_1595_, lean_object* v_hl_1596_, lean_object* v_hr_1597_){
_start:
{
lean_object* v___x_1598_; 
v___x_1598_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__3_spec__6___redArg(v_lhs_1588_, v_rhs_1589_, v_cache_1590_, v_idx_1593_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__3_spec__6___boxed(lean_object* v_00_u03b1_1599_, lean_object* v_inst_1600_, lean_object* v_inst_1601_, lean_object* v_aig_1602_, lean_object* v_cnf_1603_, lean_object* v_lhs_1604_, lean_object* v_rhs_1605_, lean_object* v_cache_1606_, lean_object* v_hlb_1607_, lean_object* v_hrb_1608_, lean_object* v_idx_1609_, lean_object* v_h_1610_, lean_object* v_htip_1611_, lean_object* v_hl_1612_, lean_object* v_hr_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__3_spec__6(v_00_u03b1_1599_, v_inst_1600_, v_inst_1601_, v_aig_1602_, v_cnf_1603_, v_lhs_1604_, v_rhs_1605_, v_cache_1606_, v_hlb_1607_, v_hrb_1608_, v_idx_1609_, v_h_1610_, v_htip_1611_, v_hl_1612_, v_hr_1613_);
lean_dec(v_idx_1609_);
lean_dec(v_rhs_1605_);
lean_dec(v_lhs_1604_);
lean_dec_ref(v_cnf_1603_);
lean_dec_ref(v_aig_1602_);
lean_dec_ref(v_inst_1601_);
lean_dec_ref(v_inst_1600_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__3(lean_object* v_00_u03b1_1615_, lean_object* v_inst_1616_, lean_object* v_inst_1617_, lean_object* v_aig_1618_, lean_object* v_lhs_1619_, lean_object* v_rhs_1620_, lean_object* v_state_1621_, lean_object* v_hlb_1622_, lean_object* v_hrb_1623_, lean_object* v_idx_1624_, lean_object* v_h_1625_, lean_object* v_htip_1626_, lean_object* v_hl_1627_, lean_object* v_hr_1628_){
_start:
{
lean_object* v___x_1629_; 
v___x_1629_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__3___redArg(v_inst_1616_, v_inst_1617_, v_aig_1618_, v_lhs_1619_, v_rhs_1620_, v_state_1621_, v_idx_1624_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__3___boxed(lean_object* v_00_u03b1_1630_, lean_object* v_inst_1631_, lean_object* v_inst_1632_, lean_object* v_aig_1633_, lean_object* v_lhs_1634_, lean_object* v_rhs_1635_, lean_object* v_state_1636_, lean_object* v_hlb_1637_, lean_object* v_hrb_1638_, lean_object* v_idx_1639_, lean_object* v_h_1640_, lean_object* v_htip_1641_, lean_object* v_hl_1642_, lean_object* v_hr_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__3(v_00_u03b1_1630_, v_inst_1631_, v_inst_1632_, v_aig_1633_, v_lhs_1634_, v_rhs_1635_, v_state_1636_, v_hlb_1637_, v_hrb_1638_, v_idx_1639_, v_h_1640_, v_htip_1641_, v_hl_1642_, v_hr_1643_);
lean_dec(v_rhs_1635_);
lean_dec(v_lhs_1634_);
lean_dec_ref(v_aig_1633_);
lean_dec_ref(v_inst_1632_);
lean_dec_ref(v_inst_1631_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4_spec__8(lean_object* v_00_u03b1_1645_, lean_object* v_inst_1646_, lean_object* v_inst_1647_, lean_object* v_aig_1648_, lean_object* v_cnf_1649_, lean_object* v_cache_1650_, lean_object* v_cond_1651_, lean_object* v_ifTrue_1652_, lean_object* v_ifFalse_1653_, lean_object* v_idx_1654_, lean_object* v_hcb_1655_, lean_object* v_htb_1656_, lean_object* v_hfb_1657_, lean_object* v_h_1658_, lean_object* v_hltc_1659_, lean_object* v_hltt_1660_, lean_object* v_hltf_1661_, lean_object* v_hc_1662_, lean_object* v_ht_1663_, lean_object* v_hf_1664_, lean_object* v_hdenote_1665_){
_start:
{
lean_object* v___x_1666_; 
v___x_1666_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4_spec__8___redArg(v_cache_1650_, v_cond_1651_, v_ifTrue_1652_, v_ifFalse_1653_, v_idx_1654_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4_spec__8___boxed(lean_object** _args){
lean_object* v_00_u03b1_1667_ = _args[0];
lean_object* v_inst_1668_ = _args[1];
lean_object* v_inst_1669_ = _args[2];
lean_object* v_aig_1670_ = _args[3];
lean_object* v_cnf_1671_ = _args[4];
lean_object* v_cache_1672_ = _args[5];
lean_object* v_cond_1673_ = _args[6];
lean_object* v_ifTrue_1674_ = _args[7];
lean_object* v_ifFalse_1675_ = _args[8];
lean_object* v_idx_1676_ = _args[9];
lean_object* v_hcb_1677_ = _args[10];
lean_object* v_htb_1678_ = _args[11];
lean_object* v_hfb_1679_ = _args[12];
lean_object* v_h_1680_ = _args[13];
lean_object* v_hltc_1681_ = _args[14];
lean_object* v_hltt_1682_ = _args[15];
lean_object* v_hltf_1683_ = _args[16];
lean_object* v_hc_1684_ = _args[17];
lean_object* v_ht_1685_ = _args[18];
lean_object* v_hf_1686_ = _args[19];
lean_object* v_hdenote_1687_ = _args[20];
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4_spec__8(v_00_u03b1_1667_, v_inst_1668_, v_inst_1669_, v_aig_1670_, v_cnf_1671_, v_cache_1672_, v_cond_1673_, v_ifTrue_1674_, v_ifFalse_1675_, v_idx_1676_, v_hcb_1677_, v_htb_1678_, v_hfb_1679_, v_h_1680_, v_hltc_1681_, v_hltt_1682_, v_hltf_1683_, v_hc_1684_, v_ht_1685_, v_hf_1686_, v_hdenote_1687_);
lean_dec(v_idx_1676_);
lean_dec(v_ifFalse_1675_);
lean_dec(v_ifTrue_1674_);
lean_dec(v_cond_1673_);
lean_dec_ref(v_cnf_1671_);
lean_dec_ref(v_aig_1670_);
lean_dec_ref(v_inst_1669_);
lean_dec_ref(v_inst_1668_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4(lean_object* v_00_u03b1_1689_, lean_object* v_inst_1690_, lean_object* v_inst_1691_, lean_object* v_aig_1692_, lean_object* v_state_1693_, lean_object* v_cond_1694_, lean_object* v_ifTrue_1695_, lean_object* v_ifFalse_1696_, lean_object* v_idx_1697_, lean_object* v_hcb_1698_, lean_object* v_htb_1699_, lean_object* v_hfb_1700_, lean_object* v_h_1701_, lean_object* v_hltc_1702_, lean_object* v_hltt_1703_, lean_object* v_hltf_1704_, lean_object* v_hc_1705_, lean_object* v_ht_1706_, lean_object* v_hf_1707_, lean_object* v_hdenote_1708_){
_start:
{
lean_object* v___x_1709_; 
v___x_1709_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4___redArg(v_inst_1690_, v_inst_1691_, v_aig_1692_, v_state_1693_, v_cond_1694_, v_ifTrue_1695_, v_ifFalse_1696_, v_idx_1697_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4___boxed(lean_object** _args){
lean_object* v_00_u03b1_1710_ = _args[0];
lean_object* v_inst_1711_ = _args[1];
lean_object* v_inst_1712_ = _args[2];
lean_object* v_aig_1713_ = _args[3];
lean_object* v_state_1714_ = _args[4];
lean_object* v_cond_1715_ = _args[5];
lean_object* v_ifTrue_1716_ = _args[6];
lean_object* v_ifFalse_1717_ = _args[7];
lean_object* v_idx_1718_ = _args[8];
lean_object* v_hcb_1719_ = _args[9];
lean_object* v_htb_1720_ = _args[10];
lean_object* v_hfb_1721_ = _args[11];
lean_object* v_h_1722_ = _args[12];
lean_object* v_hltc_1723_ = _args[13];
lean_object* v_hltt_1724_ = _args[14];
lean_object* v_hltf_1725_ = _args[15];
lean_object* v_hc_1726_ = _args[16];
lean_object* v_ht_1727_ = _args[17];
lean_object* v_hf_1728_ = _args[18];
lean_object* v_hdenote_1729_ = _args[19];
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addIte___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_x27_go___at___00Std_Sat_AIG_toCNF_x27_spec__0_spec__4(v_00_u03b1_1710_, v_inst_1711_, v_inst_1712_, v_aig_1713_, v_state_1714_, v_cond_1715_, v_ifTrue_1716_, v_ifFalse_1717_, v_idx_1718_, v_hcb_1719_, v_htb_1720_, v_hfb_1721_, v_h_1722_, v_hltc_1723_, v_hltt_1724_, v_hltf_1725_, v_hc_1726_, v_ht_1727_, v_hf_1728_, v_hdenote_1729_);
lean_dec(v_ifFalse_1717_);
lean_dec(v_ifTrue_1716_);
lean_dec(v_cond_1715_);
lean_dec_ref(v_aig_1713_);
lean_dec_ref(v_inst_1712_);
lean_dec_ref(v_inst_1711_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF___redArg(lean_object* v_inst_1733_, lean_object* v_inst_1734_, lean_object* v_entry_1735_){
_start:
{
lean_object* v_aig_1736_; lean_object* v_ref_1737_; lean_object* v___x_1738_; lean_object* v_state_1739_; lean_object* v_cnf_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1760_; 
v_aig_1736_ = lean_ctor_get(v_entry_1735_, 0);
v_ref_1737_ = lean_ctor_get(v_entry_1735_, 1);
lean_inc_ref(v_ref_1737_);
v___x_1738_ = l_Std_Sat_AIG_toCNF_State_empty___redArg(v_aig_1736_);
v_state_1739_ = l_Std_Sat_AIG_toCNF_x27___redArg(v_inst_1733_, v_inst_1734_, v_entry_1735_, v___x_1738_);
v_cnf_1740_ = lean_ctor_get(v_state_1739_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v_state_1739_);
if (v_isSharedCheck_1760_ == 0)
{
lean_object* v_unused_1761_; 
v_unused_1761_ = lean_ctor_get(v_state_1739_, 1);
lean_dec(v_unused_1761_);
v___x_1742_ = v_state_1739_;
v_isShared_1743_ = v_isSharedCheck_1760_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_cnf_1740_);
lean_dec(v_state_1739_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1760_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v_gate_1744_; uint8_t v_invert_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___y_1749_; uint8_t v___y_1750_; 
v_gate_1744_ = lean_ctor_get(v_ref_1737_, 0);
lean_inc(v_gate_1744_);
v_invert_1745_ = lean_ctor_get_uint8(v_ref_1737_, sizeof(void*)*1);
lean_dec_ref(v_ref_1737_);
v___x_1746_ = ((lean_object*)(l_Std_Sat_AIG_toCNF___redArg___closed__0));
v___x_1747_ = l_ByteArray_empty;
if (v_invert_1745_ == 0)
{
lean_object* v___x_1756_; uint8_t v___x_1757_; 
v___x_1756_ = lean_array_push(v___x_1746_, v_gate_1744_);
v___x_1757_ = 1;
v___y_1749_ = v___x_1756_;
v___y_1750_ = v___x_1757_;
goto v___jp_1748_;
}
else
{
lean_object* v___x_1758_; uint8_t v___x_1759_; 
v___x_1758_ = lean_array_push(v___x_1746_, v_gate_1744_);
v___x_1759_ = 0;
v___y_1749_ = v___x_1758_;
v___y_1750_ = v___x_1759_;
goto v___jp_1748_;
}
v___jp_1748_:
{
lean_object* v___x_1751_; lean_object* v___x_1753_; 
v___x_1751_ = lean_byte_array_push(v___x_1747_, v___y_1750_);
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 1, v___x_1751_);
lean_ctor_set(v___x_1742_, 0, v___y_1749_);
v___x_1753_ = v___x_1742_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v___y_1749_);
lean_ctor_set(v_reuseFailAlloc_1755_, 1, v___x_1751_);
v___x_1753_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
lean_object* v___x_1754_; 
v___x_1754_ = lean_array_push(v_cnf_1740_, v___x_1753_);
return v___x_1754_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF___redArg___boxed(lean_object* v_inst_1762_, lean_object* v_inst_1763_, lean_object* v_entry_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l_Std_Sat_AIG_toCNF___redArg(v_inst_1762_, v_inst_1763_, v_entry_1764_);
lean_dec_ref(v_inst_1763_);
lean_dec_ref(v_inst_1762_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF(lean_object* v_00_u03b1_1766_, lean_object* v_inst_1767_, lean_object* v_inst_1768_, lean_object* v_entry_1769_){
_start:
{
lean_object* v_aig_1770_; lean_object* v_ref_1771_; lean_object* v___x_1772_; lean_object* v_state_1773_; lean_object* v_cnf_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1794_; 
v_aig_1770_ = lean_ctor_get(v_entry_1769_, 0);
v_ref_1771_ = lean_ctor_get(v_entry_1769_, 1);
lean_inc_ref(v_ref_1771_);
v___x_1772_ = l_Std_Sat_AIG_toCNF_State_empty___redArg(v_aig_1770_);
v_state_1773_ = l_Std_Sat_AIG_toCNF_x27___redArg(v_inst_1767_, v_inst_1768_, v_entry_1769_, v___x_1772_);
v_cnf_1774_ = lean_ctor_get(v_state_1773_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v_state_1773_);
if (v_isSharedCheck_1794_ == 0)
{
lean_object* v_unused_1795_; 
v_unused_1795_ = lean_ctor_get(v_state_1773_, 1);
lean_dec(v_unused_1795_);
v___x_1776_ = v_state_1773_;
v_isShared_1777_ = v_isSharedCheck_1794_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_cnf_1774_);
lean_dec(v_state_1773_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1794_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v_gate_1778_; uint8_t v_invert_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___y_1783_; uint8_t v___y_1784_; 
v_gate_1778_ = lean_ctor_get(v_ref_1771_, 0);
lean_inc(v_gate_1778_);
v_invert_1779_ = lean_ctor_get_uint8(v_ref_1771_, sizeof(void*)*1);
lean_dec_ref(v_ref_1771_);
v___x_1780_ = ((lean_object*)(l_Std_Sat_AIG_toCNF___redArg___closed__0));
v___x_1781_ = l_ByteArray_empty;
if (v_invert_1779_ == 0)
{
lean_object* v___x_1790_; uint8_t v___x_1791_; 
v___x_1790_ = lean_array_push(v___x_1780_, v_gate_1778_);
v___x_1791_ = 1;
v___y_1783_ = v___x_1790_;
v___y_1784_ = v___x_1791_;
goto v___jp_1782_;
}
else
{
lean_object* v___x_1792_; uint8_t v___x_1793_; 
v___x_1792_ = lean_array_push(v___x_1780_, v_gate_1778_);
v___x_1793_ = 0;
v___y_1783_ = v___x_1792_;
v___y_1784_ = v___x_1793_;
goto v___jp_1782_;
}
v___jp_1782_:
{
lean_object* v___x_1785_; lean_object* v___x_1787_; 
v___x_1785_ = lean_byte_array_push(v___x_1781_, v___y_1784_);
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 1, v___x_1785_);
lean_ctor_set(v___x_1776_, 0, v___y_1783_);
v___x_1787_ = v___x_1776_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v___y_1783_);
lean_ctor_set(v_reuseFailAlloc_1789_, 1, v___x_1785_);
v___x_1787_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
lean_object* v___x_1788_; 
v___x_1788_ = lean_array_push(v_cnf_1774_, v___x_1787_);
return v___x_1788_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF___boxed(lean_object* v_00_u03b1_1796_, lean_object* v_inst_1797_, lean_object* v_inst_1798_, lean_object* v_entry_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l_Std_Sat_AIG_toCNF(v_00_u03b1_1796_, v_inst_1797_, v_inst_1798_, v_entry_1799_);
lean_dec_ref(v_inst_1798_);
lean_dec_ref(v_inst_1797_);
return v_res_1800_;
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
