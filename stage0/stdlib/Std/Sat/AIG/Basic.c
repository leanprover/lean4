// Lean compiler output
// Module: Std.Sat.AIG.Basic
// Imports: public import Std.Data.HashSet public import Init.Data.Vector.Basic public import Init.Data.Hashable public import Init.Data.String.Defs public import Init.Data.ToString.Macro import Init.Omega
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesIdent(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_bool_xor(uint8_t, uint8_t);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_UInt64_ofNat___boxed(lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_bool_to_nat(uint8_t);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_lxor(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Std_Sat_AIG_instHashableFanin_hash(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableFanin_hash___boxed(lean_object*);
static const lean_closure_object l_Std_Sat_AIG_instHashableFanin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Sat_AIG_instHashableFanin_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Sat_AIG_instHashableFanin___closed__0 = (const lean_object*)&l_Std_Sat_AIG_instHashableFanin___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Sat_AIG_instHashableFanin = (const lean_object*)&l_Std_Sat_AIG_instHashableFanin___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Sat_AIG_instReprFanin_repr_spec__0(lean_object*);
static const lean_string_object l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__0 = (const lean_object*)&l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__0_value;
static const lean_string_object l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "val"};
static const lean_object* l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__1 = (const lean_object*)&l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__2 = (const lean_object*)&l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__2_value)}};
static const lean_object* l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__3 = (const lean_object*)&l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__3_value;
static const lean_string_object l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__4 = (const lean_object*)&l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__5 = (const lean_object*)&l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__5_value;
static const lean_ctor_object l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__3_value),((lean_object*)&l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__6 = (const lean_object*)&l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__6_value;
static lean_once_cell_t l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__7;
static const lean_string_object l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__8 = (const lean_object*)&l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__8_value;
static lean_once_cell_t l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__9;
static lean_once_cell_t l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__10;
static const lean_ctor_object l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__11 = (const lean_object*)&l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__11_value;
static const lean_ctor_object l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__8_value)}};
static const lean_object* l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__12 = (const lean_object*)&l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__12_value;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprFanin_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprFanin_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprFanin_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Sat_AIG_instReprFanin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Sat_AIG_instReprFanin_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Sat_AIG_instReprFanin___closed__0 = (const lean_object*)&l_Std_Sat_AIG_instReprFanin___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Sat_AIG_instReprFanin = (const lean_object*)&l_Std_Sat_AIG_instReprFanin___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Sat_AIG_instDecidableEqFanin_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instDecidableEqFanin_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_instDecidableEqFanin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instDecidableEqFanin___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instInhabitedFanin_default;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instInhabitedFanin;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Fanin_mk(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Fanin_mk___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Fanin_gate(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Fanin_gate___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_Fanin_invert(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Fanin_invert___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Fanin_flip(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Fanin_flip___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_false_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_false_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_atom_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_atom_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_gate_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_gate_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Std_Sat_AIG_instHashableDecl_hash___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableDecl_hash___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Std_Sat_AIG_instHashableDecl_hash(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableDecl_hash___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableDecl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableDecl(lean_object*, lean_object*);
static const lean_string_object l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Std.Sat.AIG.Decl.false"};
static const lean_object* l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__0 = (const lean_object*)&l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__0_value;
static const lean_ctor_object l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__1 = (const lean_object*)&l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__1_value;
static lean_once_cell_t l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2;
static lean_once_cell_t l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3;
static const lean_string_object l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Std.Sat.AIG.Decl.atom"};
static const lean_object* l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__4 = (const lean_object*)&l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__5 = (const lean_object*)&l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__5_value;
static const lean_ctor_object l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__5_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__6 = (const lean_object*)&l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__6_value;
static const lean_string_object l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Std.Sat.AIG.Decl.gate"};
static const lean_object* l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__7 = (const lean_object*)&l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__7_value;
static const lean_ctor_object l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__7_value)}};
static const lean_object* l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__8 = (const lean_object*)&l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__8_value;
static const lean_ctor_object l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__8_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__9 = (const lean_object*)&l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprDecl_repr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprDecl_repr___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprDecl_repr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprDecl_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprDecl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprDecl(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_instDecidableEqDecl_decEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instDecidableEqDecl_decEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_instDecidableEqDecl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instDecidableEqDecl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_instDecidableEqDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instDecidableEqDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instInhabitedDecl_default(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instInhabitedDecl(lean_object*);
static lean_once_cell_t l_Std_Sat_AIG_Cache_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_Cache_empty___closed__0;
static lean_once_cell_t l_Std_Sat_AIG_Cache_empty___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_Cache_empty___closed__1;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_empty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_empty___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_noUpdate___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_noUpdate___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_noUpdate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_noUpdate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_Cache_insert___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_Sat_AIG_empty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Sat_AIG_empty___closed__0 = (const lean_object*)&l_Std_Sat_AIG_empty___closed__0_value;
static lean_once_cell_t l_Std_Sat_AIG_empty___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_empty___closed__1;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_empty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_empty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instMembership(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instMembership___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_cast___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_cast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_cast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_flip___redArg(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_flip___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_flip(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_flip___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_not___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_not(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_not___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_cast___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_cast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_cast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_invert___redArg(lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_invert___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_invert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_invert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_TernaryInput_cast___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_TernaryInput_cast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_TernaryInput_cast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Sat_AIG_toGraphviz_invEdgeStyle___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " [color=blue]"};
static const lean_object* l_Std_Sat_AIG_toGraphviz_invEdgeStyle___closed__0 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_invEdgeStyle___closed__0_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_invEdgeStyle___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = " [color=red]"};
static const lean_object* l_Std_Sat_AIG_toGraphviz_invEdgeStyle___closed__1 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_invEdgeStyle___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_invEdgeStyle(uint8_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_invEdgeStyle___boxed(lean_object*);
static const lean_closure_object l_Std_Sat_AIG_toGraphviz_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_ofNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Sat_AIG_toGraphviz_go___redArg___closed__0 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_go___redArg___closed__0_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_go___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " -> "};
static const lean_object* l_Std_Sat_AIG_toGraphviz_go___redArg___closed__1 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_go___redArg___closed__1_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_go___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "; "};
static const lean_object* l_Std_Sat_AIG_toGraphviz_go___redArg___closed__2 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_go___redArg___closed__2_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_go___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Std_Sat_AIG_toGraphviz_go___redArg___closed__3 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_go___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " [label=\""};
static const lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__0 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__0_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__1 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__1_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "\", shape=box];"};
static const lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__2 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__2_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "\", shape=doublecircle];"};
static const lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__3 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__3_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 21, .m_data = " ∧\",shape=trapezium];"};
static const lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__4 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Sat_AIG_toGraphviz___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Sat_AIG_toGraphviz___redArg___closed__0 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__0_value;
static lean_once_cell_t l_Std_Sat_AIG_toGraphviz___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_toGraphviz___redArg___closed__1;
static lean_once_cell_t l_Std_Sat_AIG_toGraphviz___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_toGraphviz___redArg___closed__2;
static const lean_string_object l_Std_Sat_AIG_toGraphviz___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Digraph AIG {"};
static const lean_object* l_Std_Sat_AIG_toGraphviz___redArg___closed__3 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__3_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_Std_Sat_AIG_toGraphviz___redArg___closed__4 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__4_value;
static const lean_closure_object l_Std_Sat_AIG_toGraphviz___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Sat_AIG_toGraphviz___redArg___closed__5 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__5_value;
static const lean_closure_object l_Std_Sat_AIG_toGraphviz___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Sat_AIG_toGraphviz___redArg___closed__6 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__6_value;
static const lean_closure_object l_Std_Sat_AIG_toGraphviz___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Sat_AIG_toGraphviz___redArg___closed__7 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__7_value;
static const lean_closure_object l_Std_Sat_AIG_toGraphviz___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Sat_AIG_toGraphviz___redArg___closed__8 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__8_value;
static const lean_closure_object l_Std_Sat_AIG_toGraphviz___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Sat_AIG_toGraphviz___redArg___closed__9 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__9_value;
static const lean_closure_object l_Std_Sat_AIG_toGraphviz___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Sat_AIG_toGraphviz___redArg___closed__10 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__10_value;
static const lean_closure_object l_Std_Sat_AIG_toGraphviz___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Sat_AIG_toGraphviz___redArg___closed__11 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__11_value;
static const lean_ctor_object l_Std_Sat_AIG_toGraphviz___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__5_value),((lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__6_value)}};
static const lean_object* l_Std_Sat_AIG_toGraphviz___redArg___closed__12 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__12_value;
static const lean_ctor_object l_Std_Sat_AIG_toGraphviz___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__12_value),((lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__7_value),((lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__8_value),((lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__9_value),((lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__10_value)}};
static const lean_object* l_Std_Sat_AIG_toGraphviz___redArg___closed__13 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__13_value;
static const lean_ctor_object l_Std_Sat_AIG_toGraphviz___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__13_value),((lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__11_value)}};
static const lean_object* l_Std_Sat_AIG_toGraphviz___redArg___closed__14 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__14_value;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote_go___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__0 = (const lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__0_value;
static const lean_string_object l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sat"};
static const lean_object* l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__1 = (const lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__1_value;
static const lean_string_object l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "AIG"};
static const lean_object* l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__2 = (const lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__2_value;
static const lean_string_object l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 9, .m_data = "term⟦_,_⟧"};
static const lean_object* l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__3 = (const lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__3_value;
static const lean_ctor_object l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4_value_aux_0),((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__1_value),LEAN_SCALAR_PTR_LITERAL(171, 82, 193, 103, 140, 69, 25, 78)}};
static const lean_ctor_object l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4_value_aux_1),((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__2_value),LEAN_SCALAR_PTR_LITERAL(159, 100, 232, 179, 195, 137, 50, 146)}};
static const lean_ctor_object l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4_value_aux_2),((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__3_value),LEAN_SCALAR_PTR_LITERAL(68, 57, 39, 164, 19, 235, 89, 113)}};
static const lean_object* l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4 = (const lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4_value;
static const lean_string_object l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__5 = (const lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__5_value;
static const lean_ctor_object l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__5_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__6 = (const lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__6_value;
static const lean_string_object l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟦"};
static const lean_object* l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7 = (const lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7_value;
static const lean_ctor_object l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7_value)}};
static const lean_object* l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__8 = (const lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__8_value;
static const lean_string_object l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__9 = (const lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__9_value;
static const lean_ctor_object l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__9_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__10 = (const lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__10_value;
static const lean_ctor_object l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__11 = (const lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__11_value;
static const lean_ctor_object l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__6_value),((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__8_value),((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__11_value)}};
static const lean_object* l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__12 = (const lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__12_value;
static const lean_string_object l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__13 = (const lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__13_value;
static const lean_ctor_object l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__13_value)}};
static const lean_object* l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__14 = (const lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__14_value;
static const lean_ctor_object l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__6_value),((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__12_value),((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__14_value)}};
static const lean_object* l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__15 = (const lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__15_value;
static const lean_ctor_object l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__6_value),((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__15_value),((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__11_value)}};
static const lean_object* l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__16 = (const lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__16_value;
static const lean_string_object l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟧"};
static const lean_object* l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17 = (const lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17_value;
static const lean_ctor_object l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17_value)}};
static const lean_object* l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__18 = (const lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__18_value;
static const lean_ctor_object l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__6_value),((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__16_value),((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__18_value)}};
static const lean_object* l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__19 = (const lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__19_value;
static const lean_ctor_object l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__19_value)}};
static const lean_object* l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__20 = (const lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__20_value;
LEAN_EXPORT const lean_object* l_Std_Sat_AIG_term_u27e6___x2c___u27e7 = (const lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__20_value;
static const lean_string_object l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 11, .m_data = "term⟦_,_,_⟧"};
static const lean_object* l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__0 = (const lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__0_value;
static const lean_ctor_object l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__1_value_aux_0),((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__1_value),LEAN_SCALAR_PTR_LITERAL(171, 82, 193, 103, 140, 69, 25, 78)}};
static const lean_ctor_object l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__1_value_aux_1),((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__2_value),LEAN_SCALAR_PTR_LITERAL(159, 100, 232, 179, 195, 137, 50, 146)}};
static const lean_ctor_object l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__1_value_aux_2),((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(11, 151, 104, 166, 133, 236, 24, 151)}};
static const lean_object* l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__1 = (const lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__1_value;
static const lean_ctor_object l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__6_value),((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__16_value),((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__14_value)}};
static const lean_object* l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__2 = (const lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__2_value;
static const lean_ctor_object l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__6_value),((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__2_value),((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__11_value)}};
static const lean_object* l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__3 = (const lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__3_value;
static const lean_ctor_object l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__6_value),((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__3_value),((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__18_value)}};
static const lean_object* l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__4 = (const lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__4_value;
static const lean_ctor_object l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__4_value)}};
static const lean_object* l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__5 = (const lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__5_value;
LEAN_EXPORT const lean_object* l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7 = (const lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__5_value;
static const lean_string_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__0 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__0_value;
static const lean_string_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__1 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__1_value;
static const lean_string_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2_value;
static const lean_string_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__3 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__3_value;
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4_value_aux_0),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4_value_aux_1),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4_value_aux_2),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4_value;
static const lean_string_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "denote"};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__5 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__5_value;
static lean_once_cell_t l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6;
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(104, 157, 36, 77, 177, 136, 111, 163)}};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__7 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__7_value;
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__8_value_aux_0),((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__1_value),LEAN_SCALAR_PTR_LITERAL(171, 82, 193, 103, 140, 69, 25, 78)}};
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__8_value_aux_1),((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__2_value),LEAN_SCALAR_PTR_LITERAL(159, 100, 232, 179, 195, 137, 50, 146)}};
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__8_value_aux_2),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(92, 0, 130, 77, 137, 144, 235, 232)}};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__8 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__8_value;
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__9 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__9_value;
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__8_value)}};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__10 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__10_value;
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__11 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__11_value;
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__9_value),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__11_value)}};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__12 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__12_value;
static const lean_string_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__13 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__13_value;
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__14 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__14_value;
LEAN_EXPORT lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__0 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__0_value;
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__1_value_aux_0),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__1_value_aux_1),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__1_value_aux_2),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__1 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__1_value;
static const lean_string_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__2 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__2_value;
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__3_value_aux_0),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__3_value_aux_1),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__3_value_aux_2),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__3 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__3_value;
static const lean_string_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__4 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__4_value;
static const lean_string_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__5 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__5_value;
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__6 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__6_value;
static lean_once_cell_t l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__7;
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__8_value_aux_0),((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__1_value),LEAN_SCALAR_PTR_LITERAL(171, 82, 193, 103, 140, 69, 25, 78)}};
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__8_value_aux_1),((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__2_value),LEAN_SCALAR_PTR_LITERAL(159, 100, 232, 179, 195, 137, 50, 146)}};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__8 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__8_value;
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__8_value)}};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__9 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__9_value;
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__10 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__10_value;
static const lean_string_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Entrypoint.mk"};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__11 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__11_value;
static lean_once_cell_t l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__12;
static const lean_string_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Entrypoint"};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__13 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__13_value;
static const lean_string_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__14 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__14_value;
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(32, 62, 221, 40, 56, 94, 198, 41)}};
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__15_value_aux_0),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(152, 61, 134, 182, 121, 216, 110, 135)}};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__15 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__15_value;
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__16_value_aux_0),((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__1_value),LEAN_SCALAR_PTR_LITERAL(171, 82, 193, 103, 140, 69, 25, 78)}};
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__16_value_aux_1),((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__2_value),LEAN_SCALAR_PTR_LITERAL(159, 100, 232, 179, 195, 137, 50, 146)}};
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__16_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__16_value_aux_2),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(212, 251, 170, 10, 27, 197, 61, 90)}};
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__16_value_aux_3),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(188, 70, 224, 174, 146, 223, 49, 217)}};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__16 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__16_value;
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__16_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__17 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__17_value;
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__16_value)}};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__18 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__18_value;
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__18_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__19 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__19_value;
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__17_value),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__19_value)}};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__20 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__20_value;
static const lean_string_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__21 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__21_value;
LEAN_EXPORT lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Sat_AIG_unexpandDenote___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structInst"};
static const lean_object* l_Std_Sat_AIG_unexpandDenote___closed__0 = (const lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__0_value;
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__1_value_aux_0),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__1_value_aux_1),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__1_value_aux_2),((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__0_value),LEAN_SCALAR_PTR_LITERAL(50, 43, 73, 62, 118, 124, 31, 28)}};
static const lean_object* l_Std_Sat_AIG_unexpandDenote___closed__1 = (const lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__1_value;
static const lean_string_object l_Std_Sat_AIG_unexpandDenote___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Std_Sat_AIG_unexpandDenote___closed__2 = (const lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__2_value;
static const lean_string_object l_Std_Sat_AIG_unexpandDenote___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l_Std_Sat_AIG_unexpandDenote___closed__3 = (const lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__3_value;
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__4_value_aux_0),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__4_value_aux_1),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__4_value_aux_2),((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l_Std_Sat_AIG_unexpandDenote___closed__4 = (const lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__4_value;
static const lean_string_object l_Std_Sat_AIG_unexpandDenote___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "structInstField"};
static const lean_object* l_Std_Sat_AIG_unexpandDenote___closed__5 = (const lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__5_value;
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__6_value_aux_0),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__6_value_aux_1),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__6_value_aux_2),((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__5_value),LEAN_SCALAR_PTR_LITERAL(50, 77, 20, 88, 28, 210, 230, 84)}};
static const lean_object* l_Std_Sat_AIG_unexpandDenote___closed__6 = (const lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__6_value;
static const lean_string_object l_Std_Sat_AIG_unexpandDenote___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "structInstLVal"};
static const lean_object* l_Std_Sat_AIG_unexpandDenote___closed__7 = (const lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__7_value;
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__8_value_aux_0),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__8_value_aux_1),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__8_value_aux_2),((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__7_value),LEAN_SCALAR_PTR_LITERAL(185, 133, 6, 147, 6, 183, 100, 198)}};
static const lean_object* l_Std_Sat_AIG_unexpandDenote___closed__8 = (const lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__8_value;
static const lean_string_object l_Std_Sat_AIG_unexpandDenote___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "aig"};
static const lean_object* l_Std_Sat_AIG_unexpandDenote___closed__9 = (const lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__9_value;
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__9_value),LEAN_SCALAR_PTR_LITERAL(115, 31, 37, 57, 248, 230, 152, 117)}};
static const lean_object* l_Std_Sat_AIG_unexpandDenote___closed__10 = (const lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__10_value;
static const lean_string_object l_Std_Sat_AIG_unexpandDenote___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "structInstFieldDef"};
static const lean_object* l_Std_Sat_AIG_unexpandDenote___closed__11 = (const lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__11_value;
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__12_value_aux_0),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__12_value_aux_1),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__12_value_aux_2),((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__11_value),LEAN_SCALAR_PTR_LITERAL(81, 102, 39, 227, 176, 252, 65, 103)}};
static const lean_object* l_Std_Sat_AIG_unexpandDenote___closed__12 = (const lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__12_value;
static const lean_string_object l_Std_Sat_AIG_unexpandDenote___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "start"};
static const lean_object* l_Std_Sat_AIG_unexpandDenote___closed__13 = (const lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__13_value;
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__13_value),LEAN_SCALAR_PTR_LITERAL(169, 129, 58, 248, 205, 160, 234, 176)}};
static const lean_object* l_Std_Sat_AIG_unexpandDenote___closed__14 = (const lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__14_value;
static const lean_string_object l_Std_Sat_AIG_unexpandDenote___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inv"};
static const lean_object* l_Std_Sat_AIG_unexpandDenote___closed__15 = (const lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__15_value;
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__15_value),LEAN_SCALAR_PTR_LITERAL(238, 17, 139, 80, 143, 212, 32, 86)}};
static const lean_object* l_Std_Sat_AIG_unexpandDenote___closed__16 = (const lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__16_value;
static const lean_string_object l_Std_Sat_AIG_unexpandDenote___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "optEllipsis"};
static const lean_object* l_Std_Sat_AIG_unexpandDenote___closed__17 = (const lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__17_value;
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__18_value_aux_0),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__18_value_aux_1),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__18_value_aux_2),((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__17_value),LEAN_SCALAR_PTR_LITERAL(13, 1, 242, 203, 207, 188, 181, 160)}};
static const lean_object* l_Std_Sat_AIG_unexpandDenote___closed__18 = (const lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__18_value;
static const lean_string_object l_Std_Sat_AIG_unexpandDenote___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "anonymousCtor"};
static const lean_object* l_Std_Sat_AIG_unexpandDenote___closed__19 = (const lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__19_value;
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__20_value_aux_0),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__20_value_aux_1),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__20_value_aux_2),((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__19_value),LEAN_SCALAR_PTR_LITERAL(56, 53, 154, 97, 179, 232, 94, 186)}};
static const lean_object* l_Std_Sat_AIG_unexpandDenote___closed__20 = (const lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__20_value;
static const lean_string_object l_Std_Sat_AIG_unexpandDenote___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟨"};
static const lean_object* l_Std_Sat_AIG_unexpandDenote___closed__21 = (const lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__21_value;
static const lean_string_object l_Std_Sat_AIG_unexpandDenote___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟩"};
static const lean_object* l_Std_Sat_AIG_unexpandDenote___closed__22 = (const lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__22_value;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_unexpandDenote(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_unexpandDenote___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGate___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtom___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConst___redArg(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConst___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConst(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_isConstant___redArg(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_isConstant___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_isConstant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_isConstant___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Std_Sat_AIG_instHashableFanin_hash(lean_object* v_x_1_){
_start:
{
uint64_t v___x_2_; uint64_t v___x_3_; uint64_t v___x_4_; 
v___x_2_ = 0ULL;
v___x_3_ = lean_uint64_of_nat(v_x_1_);
v___x_4_ = lean_uint64_mix_hash(v___x_2_, v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableFanin_hash___boxed(lean_object* v_x_5_){
_start:
{
uint64_t v_res_6_; lean_object* v_r_7_; 
v_res_6_ = l_Std_Sat_AIG_instHashableFanin_hash(v_x_5_);
lean_dec(v_x_5_);
v_r_7_ = lean_box_uint64(v_res_6_);
return v_r_7_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Sat_AIG_instReprFanin_repr_spec__0(lean_object* v_a_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_nat_to_int(v_a_10_);
return v___x_11_;
}
}
static lean_object* _init_l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_25_ = lean_unsigned_to_nat(7u);
v___x_26_ = lean_nat_to_int(v___x_25_);
return v___x_26_;
}
}
static lean_object* _init_l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_28_ = ((lean_object*)(l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__0));
v___x_29_ = lean_string_length(v___x_28_);
return v___x_29_;
}
}
static lean_object* _init_l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_30_ = lean_obj_once(&l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__9, &l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__9_once, _init_l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__9);
v___x_31_ = lean_nat_to_int(v___x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprFanin_repr___redArg(lean_object* v_x_36_){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; uint8_t v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_37_ = ((lean_object*)(l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__6));
v___x_38_ = lean_obj_once(&l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__7, &l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__7_once, _init_l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__7);
v___x_39_ = l_Nat_reprFast(v_x_36_);
v___x_40_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_40_, 0, v___x_39_);
v___x_41_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_41_, 0, v___x_38_);
lean_ctor_set(v___x_41_, 1, v___x_40_);
v___x_42_ = 0;
v___x_43_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_43_, 0, v___x_41_);
lean_ctor_set_uint8(v___x_43_, sizeof(void*)*1, v___x_42_);
v___x_44_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_44_, 0, v___x_37_);
lean_ctor_set(v___x_44_, 1, v___x_43_);
v___x_45_ = lean_obj_once(&l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__10, &l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__10_once, _init_l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__10);
v___x_46_ = ((lean_object*)(l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__11));
v___x_47_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
lean_ctor_set(v___x_47_, 1, v___x_44_);
v___x_48_ = ((lean_object*)(l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__12));
v___x_49_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_49_, 0, v___x_47_);
lean_ctor_set(v___x_49_, 1, v___x_48_);
v___x_50_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_50_, 0, v___x_45_);
lean_ctor_set(v___x_50_, 1, v___x_49_);
v___x_51_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_51_, 0, v___x_50_);
lean_ctor_set_uint8(v___x_51_, sizeof(void*)*1, v___x_42_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprFanin_repr(lean_object* v_x_52_, lean_object* v_prec_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = l_Std_Sat_AIG_instReprFanin_repr___redArg(v_x_52_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprFanin_repr___boxed(lean_object* v_x_55_, lean_object* v_prec_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Std_Sat_AIG_instReprFanin_repr(v_x_55_, v_prec_56_);
lean_dec(v_prec_56_);
return v_res_57_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_instDecidableEqFanin_decEq(lean_object* v_x_60_, lean_object* v_x_61_){
_start:
{
uint8_t v___x_62_; 
v___x_62_ = lean_nat_dec_eq(v_x_60_, v_x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instDecidableEqFanin_decEq___boxed(lean_object* v_x_63_, lean_object* v_x_64_){
_start:
{
uint8_t v_res_65_; lean_object* v_r_66_; 
v_res_65_ = l_Std_Sat_AIG_instDecidableEqFanin_decEq(v_x_63_, v_x_64_);
lean_dec(v_x_64_);
lean_dec(v_x_63_);
v_r_66_ = lean_box(v_res_65_);
return v_r_66_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_instDecidableEqFanin(lean_object* v_x_67_, lean_object* v_x_68_){
_start:
{
uint8_t v___x_69_; 
v___x_69_ = lean_nat_dec_eq(v_x_67_, v_x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instDecidableEqFanin___boxed(lean_object* v_x_70_, lean_object* v_x_71_){
_start:
{
uint8_t v_res_72_; lean_object* v_r_73_; 
v_res_72_ = l_Std_Sat_AIG_instDecidableEqFanin(v_x_70_, v_x_71_);
lean_dec(v_x_71_);
lean_dec(v_x_70_);
v_r_73_ = lean_box(v_res_72_);
return v_r_73_;
}
}
static lean_object* _init_l_Std_Sat_AIG_instInhabitedFanin_default(void){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_unsigned_to_nat(0u);
return v___x_74_;
}
}
static lean_object* _init_l_Std_Sat_AIG_instInhabitedFanin(void){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = lean_unsigned_to_nat(0u);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Fanin_mk(lean_object* v_gate_76_, uint8_t v_invert_77_){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_78_ = lean_unsigned_to_nat(2u);
v___x_79_ = lean_nat_mul(v_gate_76_, v___x_78_);
v___x_80_ = lean_bool_to_nat(v_invert_77_);
v___x_81_ = lean_nat_lor(v___x_79_, v___x_80_);
lean_dec(v___x_79_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Fanin_mk___boxed(lean_object* v_gate_82_, lean_object* v_invert_83_){
_start:
{
uint8_t v_invert_boxed_84_; lean_object* v_res_85_; 
v_invert_boxed_84_ = lean_unbox(v_invert_83_);
v_res_85_ = l_Std_Sat_AIG_Fanin_mk(v_gate_82_, v_invert_boxed_84_);
lean_dec(v_gate_82_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Fanin_gate(lean_object* v_f_86_){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = lean_unsigned_to_nat(1u);
v___x_88_ = lean_nat_shiftr(v_f_86_, v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Fanin_gate___boxed(lean_object* v_f_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Std_Sat_AIG_Fanin_gate(v_f_89_);
lean_dec(v_f_89_);
return v_res_90_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_Fanin_invert(lean_object* v_f_91_){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; uint8_t v___x_95_; uint8_t v___x_96_; 
v___x_92_ = lean_unsigned_to_nat(1u);
v___x_93_ = lean_nat_land(v___x_92_, v_f_91_);
v___x_94_ = lean_unsigned_to_nat(0u);
v___x_95_ = lean_nat_dec_eq(v___x_93_, v___x_94_);
lean_dec(v___x_93_);
v___x_96_ = lean_bool_not(v___x_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Fanin_invert___boxed(lean_object* v_f_97_){
_start:
{
uint8_t v_res_98_; lean_object* v_r_99_; 
v_res_98_ = l_Std_Sat_AIG_Fanin_invert(v_f_97_);
lean_dec(v_f_97_);
v_r_99_ = lean_box(v_res_98_);
return v_r_99_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Fanin_flip(lean_object* v_f_100_, uint8_t v_val_101_){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_102_ = lean_bool_to_nat(v_val_101_);
v___x_103_ = lean_nat_lxor(v_f_100_, v___x_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Fanin_flip___boxed(lean_object* v_f_104_, lean_object* v_val_105_){
_start:
{
uint8_t v_val_boxed_106_; lean_object* v_res_107_; 
v_val_boxed_106_ = lean_unbox(v_val_105_);
v_res_107_ = l_Std_Sat_AIG_Fanin_flip(v_f_104_, v_val_boxed_106_);
lean_dec(v_f_104_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_ctorIdx___redArg(lean_object* v_x_108_){
_start:
{
switch(lean_obj_tag(v_x_108_))
{
case 0:
{
lean_object* v___x_109_; 
v___x_109_ = lean_unsigned_to_nat(0u);
return v___x_109_;
}
case 1:
{
lean_object* v___x_110_; 
v___x_110_ = lean_unsigned_to_nat(1u);
return v___x_110_;
}
default: 
{
lean_object* v___x_111_; 
v___x_111_ = lean_unsigned_to_nat(2u);
return v___x_111_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_ctorIdx___redArg___boxed(lean_object* v_x_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Std_Sat_AIG_Decl_ctorIdx___redArg(v_x_112_);
lean_dec(v_x_112_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_ctorIdx(lean_object* v_00_u03b1_114_, lean_object* v_x_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = l_Std_Sat_AIG_Decl_ctorIdx___redArg(v_x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_ctorIdx___boxed(lean_object* v_00_u03b1_117_, lean_object* v_x_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Std_Sat_AIG_Decl_ctorIdx(v_00_u03b1_117_, v_x_118_);
lean_dec(v_x_118_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_ctorElim___redArg(lean_object* v_t_120_, lean_object* v_k_121_){
_start:
{
switch(lean_obj_tag(v_t_120_))
{
case 0:
{
return v_k_121_;
}
case 1:
{
lean_object* v_idx_122_; lean_object* v___x_123_; 
v_idx_122_ = lean_ctor_get(v_t_120_, 0);
lean_inc(v_idx_122_);
lean_dec_ref_known(v_t_120_, 1);
v___x_123_ = lean_apply_1(v_k_121_, v_idx_122_);
return v___x_123_;
}
default: 
{
lean_object* v_l_124_; lean_object* v_r_125_; lean_object* v___x_126_; 
v_l_124_ = lean_ctor_get(v_t_120_, 0);
lean_inc(v_l_124_);
v_r_125_ = lean_ctor_get(v_t_120_, 1);
lean_inc(v_r_125_);
lean_dec_ref_known(v_t_120_, 2);
v___x_126_ = lean_apply_2(v_k_121_, v_l_124_, v_r_125_);
return v___x_126_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_ctorElim(lean_object* v_00_u03b1_127_, lean_object* v_motive_128_, lean_object* v_ctorIdx_129_, lean_object* v_t_130_, lean_object* v_h_131_, lean_object* v_k_132_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l_Std_Sat_AIG_Decl_ctorElim___redArg(v_t_130_, v_k_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_ctorElim___boxed(lean_object* v_00_u03b1_134_, lean_object* v_motive_135_, lean_object* v_ctorIdx_136_, lean_object* v_t_137_, lean_object* v_h_138_, lean_object* v_k_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Std_Sat_AIG_Decl_ctorElim(v_00_u03b1_134_, v_motive_135_, v_ctorIdx_136_, v_t_137_, v_h_138_, v_k_139_);
lean_dec(v_ctorIdx_136_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_false_elim___redArg(lean_object* v_t_141_, lean_object* v_false_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_Std_Sat_AIG_Decl_ctorElim___redArg(v_t_141_, v_false_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_false_elim(lean_object* v_00_u03b1_144_, lean_object* v_motive_145_, lean_object* v_t_146_, lean_object* v_h_147_, lean_object* v_false_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l_Std_Sat_AIG_Decl_ctorElim___redArg(v_t_146_, v_false_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_atom_elim___redArg(lean_object* v_t_150_, lean_object* v_atom_151_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_Std_Sat_AIG_Decl_ctorElim___redArg(v_t_150_, v_atom_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_atom_elim(lean_object* v_00_u03b1_153_, lean_object* v_motive_154_, lean_object* v_t_155_, lean_object* v_h_156_, lean_object* v_atom_157_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l_Std_Sat_AIG_Decl_ctorElim___redArg(v_t_155_, v_atom_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_gate_elim___redArg(lean_object* v_t_159_, lean_object* v_gate_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Std_Sat_AIG_Decl_ctorElim___redArg(v_t_159_, v_gate_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_gate_elim(lean_object* v_00_u03b1_162_, lean_object* v_motive_163_, lean_object* v_t_164_, lean_object* v_h_165_, lean_object* v_gate_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Std_Sat_AIG_Decl_ctorElim___redArg(v_t_164_, v_gate_166_);
return v___x_167_;
}
}
LEAN_EXPORT uint64_t l_Std_Sat_AIG_instHashableDecl_hash___redArg(lean_object* v_inst_168_, lean_object* v_x_169_){
_start:
{
switch(lean_obj_tag(v_x_169_))
{
case 0:
{
uint64_t v___x_170_; 
lean_dec_ref(v_inst_168_);
v___x_170_ = 0ULL;
return v___x_170_;
}
case 1:
{
lean_object* v_idx_171_; uint64_t v___x_172_; lean_object* v___x_173_; uint64_t v___x_174_; uint64_t v___x_175_; 
v_idx_171_ = lean_ctor_get(v_x_169_, 0);
lean_inc(v_idx_171_);
lean_dec_ref_known(v_x_169_, 1);
v___x_172_ = 1ULL;
v___x_173_ = lean_apply_1(v_inst_168_, v_idx_171_);
v___x_174_ = lean_unbox_uint64(v___x_173_);
lean_dec_ref(v___x_173_);
v___x_175_ = lean_uint64_mix_hash(v___x_172_, v___x_174_);
return v___x_175_;
}
default: 
{
lean_object* v_l_176_; lean_object* v_r_177_; uint64_t v___x_178_; uint64_t v___x_179_; uint64_t v___x_180_; uint64_t v___x_181_; uint64_t v___x_182_; 
lean_dec_ref(v_inst_168_);
v_l_176_ = lean_ctor_get(v_x_169_, 0);
lean_inc(v_l_176_);
v_r_177_ = lean_ctor_get(v_x_169_, 1);
lean_inc(v_r_177_);
lean_dec_ref_known(v_x_169_, 2);
v___x_178_ = 2ULL;
v___x_179_ = l_Std_Sat_AIG_instHashableFanin_hash(v_l_176_);
lean_dec(v_l_176_);
v___x_180_ = lean_uint64_mix_hash(v___x_178_, v___x_179_);
v___x_181_ = l_Std_Sat_AIG_instHashableFanin_hash(v_r_177_);
lean_dec(v_r_177_);
v___x_182_ = lean_uint64_mix_hash(v___x_180_, v___x_181_);
return v___x_182_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableDecl_hash___redArg___boxed(lean_object* v_inst_183_, lean_object* v_x_184_){
_start:
{
uint64_t v_res_185_; lean_object* v_r_186_; 
v_res_185_ = l_Std_Sat_AIG_instHashableDecl_hash___redArg(v_inst_183_, v_x_184_);
v_r_186_ = lean_box_uint64(v_res_185_);
return v_r_186_;
}
}
LEAN_EXPORT uint64_t l_Std_Sat_AIG_instHashableDecl_hash(lean_object* v_00_u03b1_187_, lean_object* v_inst_188_, lean_object* v_x_189_){
_start:
{
uint64_t v___x_190_; 
v___x_190_ = l_Std_Sat_AIG_instHashableDecl_hash___redArg(v_inst_188_, v_x_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableDecl_hash___boxed(lean_object* v_00_u03b1_191_, lean_object* v_inst_192_, lean_object* v_x_193_){
_start:
{
uint64_t v_res_194_; lean_object* v_r_195_; 
v_res_194_ = l_Std_Sat_AIG_instHashableDecl_hash(v_00_u03b1_191_, v_inst_192_, v_x_193_);
v_r_195_ = lean_box_uint64(v_res_194_);
return v_r_195_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableDecl___redArg(lean_object* v_inst_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_197_, 0, lean_box(0));
lean_closure_set(v___x_197_, 1, v_inst_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableDecl(lean_object* v_00_u03b1_198_, lean_object* v_inst_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_200_, 0, lean_box(0));
lean_closure_set(v___x_200_, 1, v_inst_199_);
return v___x_200_;
}
}
static lean_object* _init_l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = lean_unsigned_to_nat(2u);
v___x_205_ = lean_nat_to_int(v___x_204_);
return v___x_205_;
}
}
static lean_object* _init_l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = lean_unsigned_to_nat(1u);
v___x_207_ = lean_nat_to_int(v___x_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprDecl_repr___redArg(lean_object* v_inst_220_, lean_object* v_x_221_, lean_object* v_prec_222_){
_start:
{
lean_object* v___y_224_; 
switch(lean_obj_tag(v_x_221_))
{
case 0:
{
lean_object* v___x_230_; uint8_t v___x_231_; 
lean_dec_ref(v_inst_220_);
v___x_230_ = lean_unsigned_to_nat(1024u);
v___x_231_ = lean_nat_dec_le(v___x_230_, v_prec_222_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; 
v___x_232_ = lean_obj_once(&l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2, &l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2_once, _init_l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2);
v___y_224_ = v___x_232_;
goto v___jp_223_;
}
else
{
lean_object* v___x_233_; 
v___x_233_ = lean_obj_once(&l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3, &l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3_once, _init_l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3);
v___y_224_ = v___x_233_;
goto v___jp_223_;
}
}
case 1:
{
lean_object* v_idx_234_; lean_object* v___y_236_; lean_object* v___x_245_; uint8_t v___x_246_; 
v_idx_234_ = lean_ctor_get(v_x_221_, 0);
lean_inc(v_idx_234_);
lean_dec_ref_known(v_x_221_, 1);
v___x_245_ = lean_unsigned_to_nat(1024u);
v___x_246_ = lean_nat_dec_le(v___x_245_, v_prec_222_);
if (v___x_246_ == 0)
{
lean_object* v___x_247_; 
v___x_247_ = lean_obj_once(&l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2, &l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2_once, _init_l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2);
v___y_236_ = v___x_247_;
goto v___jp_235_;
}
else
{
lean_object* v___x_248_; 
v___x_248_ = lean_obj_once(&l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3, &l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3_once, _init_l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3);
v___y_236_ = v___x_248_;
goto v___jp_235_;
}
v___jp_235_:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; uint8_t v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_237_ = ((lean_object*)(l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__6));
v___x_238_ = lean_unsigned_to_nat(1024u);
v___x_239_ = lean_apply_2(v_inst_220_, v_idx_234_, v___x_238_);
v___x_240_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_237_);
lean_ctor_set(v___x_240_, 1, v___x_239_);
lean_inc(v___y_236_);
v___x_241_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_241_, 0, v___y_236_);
lean_ctor_set(v___x_241_, 1, v___x_240_);
v___x_242_ = 0;
v___x_243_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_243_, 0, v___x_241_);
lean_ctor_set_uint8(v___x_243_, sizeof(void*)*1, v___x_242_);
v___x_244_ = l_Repr_addAppParen(v___x_243_, v_prec_222_);
return v___x_244_;
}
}
default: 
{
lean_object* v_l_249_; lean_object* v_r_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_273_; 
lean_dec_ref(v_inst_220_);
v_l_249_ = lean_ctor_get(v_x_221_, 0);
v_r_250_ = lean_ctor_get(v_x_221_, 1);
v_isSharedCheck_273_ = !lean_is_exclusive(v_x_221_);
if (v_isSharedCheck_273_ == 0)
{
v___x_252_ = v_x_221_;
v_isShared_253_ = v_isSharedCheck_273_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_r_250_);
lean_inc(v_l_249_);
lean_dec(v_x_221_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_273_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___y_255_; lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_269_ = lean_unsigned_to_nat(1024u);
v___x_270_ = lean_nat_dec_le(v___x_269_, v_prec_222_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; 
v___x_271_ = lean_obj_once(&l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2, &l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2_once, _init_l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2);
v___y_255_ = v___x_271_;
goto v___jp_254_;
}
else
{
lean_object* v___x_272_; 
v___x_272_ = lean_obj_once(&l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3, &l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3_once, _init_l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3);
v___y_255_ = v___x_272_;
goto v___jp_254_;
}
v___jp_254_:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_260_; 
v___x_256_ = lean_box(1);
v___x_257_ = ((lean_object*)(l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__9));
v___x_258_ = l_Std_Sat_AIG_instReprFanin_repr___redArg(v_l_249_);
if (v_isShared_253_ == 0)
{
lean_ctor_set_tag(v___x_252_, 5);
lean_ctor_set(v___x_252_, 1, v___x_258_);
lean_ctor_set(v___x_252_, 0, v___x_257_);
v___x_260_ = v___x_252_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_257_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v___x_258_);
v___x_260_ = v_reuseFailAlloc_268_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; uint8_t v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_261_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
lean_ctor_set(v___x_261_, 1, v___x_256_);
v___x_262_ = l_Std_Sat_AIG_instReprFanin_repr___redArg(v_r_250_);
v___x_263_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_261_);
lean_ctor_set(v___x_263_, 1, v___x_262_);
lean_inc(v___y_255_);
v___x_264_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_264_, 0, v___y_255_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
v___x_265_ = 0;
v___x_266_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_266_, 0, v___x_264_);
lean_ctor_set_uint8(v___x_266_, sizeof(void*)*1, v___x_265_);
v___x_267_ = l_Repr_addAppParen(v___x_266_, v_prec_222_);
return v___x_267_;
}
}
}
}
}
v___jp_223_:
{
lean_object* v___x_225_; lean_object* v___x_226_; uint8_t v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_225_ = ((lean_object*)(l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__1));
lean_inc(v___y_224_);
v___x_226_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_226_, 0, v___y_224_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
v___x_227_ = 0;
v___x_228_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_228_, 0, v___x_226_);
lean_ctor_set_uint8(v___x_228_, sizeof(void*)*1, v___x_227_);
v___x_229_ = l_Repr_addAppParen(v___x_228_, v_prec_222_);
return v___x_229_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprDecl_repr___redArg___boxed(lean_object* v_inst_274_, lean_object* v_x_275_, lean_object* v_prec_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Std_Sat_AIG_instReprDecl_repr___redArg(v_inst_274_, v_x_275_, v_prec_276_);
lean_dec(v_prec_276_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprDecl_repr(lean_object* v_00_u03b1_278_, lean_object* v_inst_279_, lean_object* v_x_280_, lean_object* v_prec_281_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_Std_Sat_AIG_instReprDecl_repr___redArg(v_inst_279_, v_x_280_, v_prec_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprDecl_repr___boxed(lean_object* v_00_u03b1_283_, lean_object* v_inst_284_, lean_object* v_x_285_, lean_object* v_prec_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Std_Sat_AIG_instReprDecl_repr(v_00_u03b1_283_, v_inst_284_, v_x_285_, v_prec_286_);
lean_dec(v_prec_286_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprDecl___redArg(lean_object* v_inst_288_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instReprDecl_repr___boxed), 4, 2);
lean_closure_set(v___x_289_, 0, lean_box(0));
lean_closure_set(v___x_289_, 1, v_inst_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprDecl(lean_object* v_00_u03b1_290_, lean_object* v_inst_291_){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instReprDecl_repr___boxed), 4, 2);
lean_closure_set(v___x_292_, 0, lean_box(0));
lean_closure_set(v___x_292_, 1, v_inst_291_);
return v___x_292_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(lean_object* v_inst_293_, lean_object* v_x_294_, lean_object* v_x_295_){
_start:
{
switch(lean_obj_tag(v_x_294_))
{
case 0:
{
lean_dec_ref(v_inst_293_);
if (lean_obj_tag(v_x_295_) == 0)
{
uint8_t v___x_296_; 
v___x_296_ = 1;
return v___x_296_;
}
else
{
uint8_t v___x_297_; 
lean_dec(v_x_295_);
v___x_297_ = 0;
return v___x_297_;
}
}
case 1:
{
lean_object* v_idx_298_; uint8_t v___x_299_; 
v_idx_298_ = lean_ctor_get(v_x_294_, 0);
lean_inc(v_idx_298_);
lean_dec_ref_known(v_x_294_, 1);
v___x_299_ = 0;
if (lean_obj_tag(v_x_295_) == 1)
{
lean_object* v_idx_300_; lean_object* v___x_301_; uint8_t v___x_302_; 
v_idx_300_ = lean_ctor_get(v_x_295_, 0);
lean_inc(v_idx_300_);
lean_dec_ref_known(v_x_295_, 1);
v___x_301_ = lean_apply_2(v_inst_293_, v_idx_298_, v_idx_300_);
v___x_302_ = lean_unbox(v___x_301_);
if (v___x_302_ == 0)
{
return v___x_299_;
}
else
{
uint8_t v___x_303_; 
v___x_303_ = lean_unbox(v___x_301_);
return v___x_303_;
}
}
else
{
lean_dec(v_idx_298_);
lean_dec(v_x_295_);
lean_dec_ref(v_inst_293_);
return v___x_299_;
}
}
default: 
{
lean_object* v_l_304_; lean_object* v_r_305_; uint8_t v___x_306_; 
lean_dec_ref(v_inst_293_);
v_l_304_ = lean_ctor_get(v_x_294_, 0);
lean_inc(v_l_304_);
v_r_305_ = lean_ctor_get(v_x_294_, 1);
lean_inc(v_r_305_);
lean_dec_ref_known(v_x_294_, 2);
v___x_306_ = 0;
if (lean_obj_tag(v_x_295_) == 2)
{
lean_object* v_l_307_; lean_object* v_r_308_; uint8_t v___x_309_; 
v_l_307_ = lean_ctor_get(v_x_295_, 0);
lean_inc(v_l_307_);
v_r_308_ = lean_ctor_get(v_x_295_, 1);
lean_inc(v_r_308_);
lean_dec_ref_known(v_x_295_, 2);
v___x_309_ = lean_nat_dec_eq(v_l_304_, v_l_307_);
lean_dec(v_l_307_);
lean_dec(v_l_304_);
if (v___x_309_ == 0)
{
lean_dec(v_r_308_);
lean_dec(v_r_305_);
return v___x_306_;
}
else
{
uint8_t v___x_310_; 
v___x_310_ = lean_nat_dec_eq(v_r_305_, v_r_308_);
lean_dec(v_r_308_);
lean_dec(v_r_305_);
if (v___x_310_ == 0)
{
return v___x_306_;
}
else
{
return v___x_310_;
}
}
}
else
{
lean_dec(v_r_305_);
lean_dec(v_l_304_);
lean_dec(v_x_295_);
return v___x_306_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg___boxed(lean_object* v_inst_311_, lean_object* v_x_312_, lean_object* v_x_313_){
_start:
{
uint8_t v_res_314_; lean_object* v_r_315_; 
v_res_314_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v_inst_311_, v_x_312_, v_x_313_);
v_r_315_ = lean_box(v_res_314_);
return v_r_315_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_instDecidableEqDecl_decEq(lean_object* v_00_u03b1_316_, lean_object* v_inst_317_, lean_object* v_x_318_, lean_object* v_x_319_){
_start:
{
uint8_t v___x_320_; 
v___x_320_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v_inst_317_, v_x_318_, v_x_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instDecidableEqDecl_decEq___boxed(lean_object* v_00_u03b1_321_, lean_object* v_inst_322_, lean_object* v_x_323_, lean_object* v_x_324_){
_start:
{
uint8_t v_res_325_; lean_object* v_r_326_; 
v_res_325_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq(v_00_u03b1_321_, v_inst_322_, v_x_323_, v_x_324_);
v_r_326_ = lean_box(v_res_325_);
return v_r_326_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_instDecidableEqDecl___redArg(lean_object* v_inst_327_, lean_object* v_x_328_, lean_object* v_x_329_){
_start:
{
uint8_t v___x_330_; 
v___x_330_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v_inst_327_, v_x_328_, v_x_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instDecidableEqDecl___redArg___boxed(lean_object* v_inst_331_, lean_object* v_x_332_, lean_object* v_x_333_){
_start:
{
uint8_t v_res_334_; lean_object* v_r_335_; 
v_res_334_ = l_Std_Sat_AIG_instDecidableEqDecl___redArg(v_inst_331_, v_x_332_, v_x_333_);
v_r_335_ = lean_box(v_res_334_);
return v_r_335_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_instDecidableEqDecl(lean_object* v_00_u03b1_336_, lean_object* v_inst_337_, lean_object* v_x_338_, lean_object* v_x_339_){
_start:
{
uint8_t v___x_340_; 
v___x_340_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v_inst_337_, v_x_338_, v_x_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instDecidableEqDecl___boxed(lean_object* v_00_u03b1_341_, lean_object* v_inst_342_, lean_object* v_x_343_, lean_object* v_x_344_){
_start:
{
uint8_t v_res_345_; lean_object* v_r_346_; 
v_res_345_ = l_Std_Sat_AIG_instDecidableEqDecl(v_00_u03b1_341_, v_inst_342_, v_x_343_, v_x_344_);
v_r_346_ = lean_box(v_res_345_);
return v_r_346_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instInhabitedDecl_default(lean_object* v_00_u03b1_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = lean_box(0);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instInhabitedDecl(lean_object* v_a_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = lean_box(0);
return v___x_350_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___closed__0(void){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_351_ = lean_box(0);
v___x_352_ = lean_unsigned_to_nat(16u);
v___x_353_ = lean_mk_array(v___x_352_, v___x_351_);
return v___x_353_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___closed__1(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_354_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___closed__0, &l_Std_Sat_AIG_Cache_empty___closed__0_once, _init_l_Std_Sat_AIG_Cache_empty___closed__0);
v___x_355_ = lean_unsigned_to_nat(0u);
v___x_356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
lean_ctor_set(v___x_356_, 1, v___x_354_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_empty(lean_object* v_00_u03b1_357_, lean_object* v_inst_358_, lean_object* v_inst_359_, lean_object* v_decls_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___closed__1, &l_Std_Sat_AIG_Cache_empty___closed__1_once, _init_l_Std_Sat_AIG_Cache_empty___closed__1);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_empty___boxed(lean_object* v_00_u03b1_362_, lean_object* v_inst_363_, lean_object* v_inst_364_, lean_object* v_decls_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Std_Sat_AIG_Cache_empty(v_00_u03b1_362_, v_inst_363_, v_inst_364_, v_decls_365_);
lean_dec_ref(v_decls_365_);
lean_dec_ref(v_inst_364_);
lean_dec_ref(v_inst_363_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_noUpdate___redArg(lean_object* v_cache_367_){
_start:
{
lean_inc_ref(v_cache_367_);
return v_cache_367_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_noUpdate___redArg___boxed(lean_object* v_cache_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Std_Sat_AIG_Cache_noUpdate___redArg(v_cache_368_);
lean_dec_ref(v_cache_368_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_noUpdate(lean_object* v_00_u03b1_370_, lean_object* v_inst_371_, lean_object* v_inst_372_, lean_object* v_decls_373_, lean_object* v_decl_374_, lean_object* v_cache_375_){
_start:
{
lean_inc_ref(v_cache_375_);
return v_cache_375_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_noUpdate___boxed(lean_object* v_00_u03b1_376_, lean_object* v_inst_377_, lean_object* v_inst_378_, lean_object* v_decls_379_, lean_object* v_decl_380_, lean_object* v_cache_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Std_Sat_AIG_Cache_noUpdate(v_00_u03b1_376_, v_inst_377_, v_inst_378_, v_decls_379_, v_decl_380_, v_cache_381_);
lean_dec_ref(v_cache_381_);
lean_dec(v_decl_380_);
lean_dec_ref(v_decls_379_);
lean_dec_ref(v_inst_378_);
lean_dec_ref(v_inst_377_);
return v_res_382_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_Cache_insert___redArg___lam__0(lean_object* v_inst_383_, lean_object* v_a_384_, lean_object* v_b_385_){
_start:
{
uint8_t v___x_386_; 
v___x_386_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v_inst_383_, v_a_384_, v_b_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed(lean_object* v_inst_387_, lean_object* v_a_388_, lean_object* v_b_389_){
_start:
{
uint8_t v_res_390_; lean_object* v_r_391_; 
v_res_390_ = l_Std_Sat_AIG_Cache_insert___redArg___lam__0(v_inst_387_, v_a_388_, v_b_389_);
v_r_391_ = lean_box(v_res_390_);
return v_r_391_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___redArg(lean_object* v_inst_392_, lean_object* v_inst_393_, lean_object* v_decls_394_, lean_object* v_cache_395_, lean_object* v_decl_396_){
_start:
{
lean_object* v___f_397_; lean_object* v___x_398_; lean_object* v___f_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___f_397_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_397_, 0, v_inst_393_);
v___x_398_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_398_, 0, lean_box(0));
lean_closure_set(v___x_398_, 1, v_inst_392_);
v___f_399_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_399_, 0, v___f_397_);
v___x_400_ = lean_array_get_size(v_decls_394_);
v___x_401_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_399_, v___x_398_, v_cache_395_, v_decl_396_, v___x_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___redArg___boxed(lean_object* v_inst_402_, lean_object* v_inst_403_, lean_object* v_decls_404_, lean_object* v_cache_405_, lean_object* v_decl_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Std_Sat_AIG_Cache_insert___redArg(v_inst_402_, v_inst_403_, v_decls_404_, v_cache_405_, v_decl_406_);
lean_dec_ref(v_decls_404_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert(lean_object* v_00_u03b1_408_, lean_object* v_inst_409_, lean_object* v_inst_410_, lean_object* v_decls_411_, lean_object* v_cache_412_, lean_object* v_decl_413_){
_start:
{
lean_object* v___f_414_; lean_object* v___x_415_; lean_object* v___f_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___f_414_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_414_, 0, v_inst_410_);
v___x_415_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_415_, 0, lean_box(0));
lean_closure_set(v___x_415_, 1, v_inst_409_);
v___f_416_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_416_, 0, v___f_414_);
v___x_417_ = lean_array_get_size(v_decls_411_);
v___x_418_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_416_, v___x_415_, v_cache_412_, v_decl_413_, v___x_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___boxed(lean_object* v_00_u03b1_419_, lean_object* v_inst_420_, lean_object* v_inst_421_, lean_object* v_decls_422_, lean_object* v_cache_423_, lean_object* v_decl_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Std_Sat_AIG_Cache_insert(v_00_u03b1_419_, v_inst_420_, v_inst_421_, v_decls_422_, v_cache_423_, v_decl_424_);
lean_dec_ref(v_decls_422_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f___redArg(lean_object* v_inst_426_, lean_object* v_inst_427_, lean_object* v_cache_428_, lean_object* v_decl_429_){
_start:
{
lean_object* v___f_430_; lean_object* v___x_431_; lean_object* v___f_432_; lean_object* v___x_433_; 
v___f_430_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_430_, 0, v_inst_427_);
v___x_431_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_431_, 0, lean_box(0));
lean_closure_set(v___x_431_, 1, v_inst_426_);
v___f_432_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_432_, 0, v___f_430_);
v___x_433_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_432_, v___x_431_, v_cache_428_, v_decl_429_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v___x_434_; 
v___x_434_ = lean_box(0);
return v___x_434_;
}
else
{
lean_object* v_val_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_442_; 
v_val_435_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_442_ == 0)
{
v___x_437_ = v___x_433_;
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_val_435_);
lean_dec(v___x_433_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_440_; 
if (v_isShared_438_ == 0)
{
v___x_440_ = v___x_437_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_val_435_);
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
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f___redArg___boxed(lean_object* v_inst_443_, lean_object* v_inst_444_, lean_object* v_cache_445_, lean_object* v_decl_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Std_Sat_AIG_Cache_get_x3f___redArg(v_inst_443_, v_inst_444_, v_cache_445_, v_decl_446_);
lean_dec_ref(v_cache_445_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f(lean_object* v_00_u03b1_448_, lean_object* v_inst_449_, lean_object* v_inst_450_, lean_object* v_decls_451_, lean_object* v_cache_452_, lean_object* v_decl_453_){
_start:
{
lean_object* v___f_454_; lean_object* v___x_455_; lean_object* v___f_456_; lean_object* v___x_457_; 
v___f_454_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_454_, 0, v_inst_450_);
v___x_455_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_455_, 0, lean_box(0));
lean_closure_set(v___x_455_, 1, v_inst_449_);
v___f_456_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_456_, 0, v___f_454_);
v___x_457_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_456_, v___x_455_, v_cache_452_, v_decl_453_);
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v___x_458_; 
v___x_458_ = lean_box(0);
return v___x_458_;
}
else
{
lean_object* v_val_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_466_; 
v_val_459_ = lean_ctor_get(v___x_457_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_466_ == 0)
{
v___x_461_ = v___x_457_;
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_val_459_);
lean_dec(v___x_457_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_464_; 
if (v_isShared_462_ == 0)
{
v___x_464_ = v___x_461_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_val_459_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f___boxed(lean_object* v_00_u03b1_467_, lean_object* v_inst_468_, lean_object* v_inst_469_, lean_object* v_decls_470_, lean_object* v_cache_471_, lean_object* v_decl_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Std_Sat_AIG_Cache_get_x3f(v_00_u03b1_467_, v_inst_468_, v_inst_469_, v_decls_470_, v_cache_471_, v_decl_472_);
lean_dec_ref(v_cache_471_);
lean_dec_ref(v_decls_470_);
return v_res_473_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___closed__1(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_478_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___closed__1, &l_Std_Sat_AIG_Cache_empty___closed__1_once, _init_l_Std_Sat_AIG_Cache_empty___closed__1);
v___x_479_ = ((lean_object*)(l_Std_Sat_AIG_empty___closed__0));
v___x_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
lean_ctor_set(v___x_480_, 1, v___x_478_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_empty(lean_object* v_00_u03b1_481_, lean_object* v_inst_482_, lean_object* v_inst_483_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = lean_obj_once(&l_Std_Sat_AIG_empty___closed__1, &l_Std_Sat_AIG_empty___closed__1_once, _init_l_Std_Sat_AIG_empty___closed__1);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_empty___boxed(lean_object* v_00_u03b1_485_, lean_object* v_inst_486_, lean_object* v_inst_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Std_Sat_AIG_empty(v_00_u03b1_485_, v_inst_486_, v_inst_487_);
lean_dec_ref(v_inst_487_);
lean_dec_ref(v_inst_486_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instMembership(lean_object* v_00_u03b1_489_, lean_object* v_inst_490_, lean_object* v_inst_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = lean_box(0);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instMembership___boxed(lean_object* v_00_u03b1_493_, lean_object* v_inst_494_, lean_object* v_inst_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Std_Sat_AIG_instMembership(v_00_u03b1_493_, v_inst_494_, v_inst_495_);
lean_dec_ref(v_inst_495_);
lean_dec_ref(v_inst_494_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_cast___redArg(lean_object* v_ref_497_){
_start:
{
lean_object* v_gate_498_; uint8_t v_invert_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_506_; 
v_gate_498_ = lean_ctor_get(v_ref_497_, 0);
v_invert_499_ = lean_ctor_get_uint8(v_ref_497_, sizeof(void*)*1);
v_isSharedCheck_506_ = !lean_is_exclusive(v_ref_497_);
if (v_isSharedCheck_506_ == 0)
{
v___x_501_ = v_ref_497_;
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_gate_498_);
lean_dec(v_ref_497_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_504_; 
if (v_isShared_502_ == 0)
{
v___x_504_ = v___x_501_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_gate_498_);
lean_ctor_set_uint8(v_reuseFailAlloc_505_, sizeof(void*)*1, v_invert_499_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_cast(lean_object* v_00_u03b1_507_, lean_object* v_inst_508_, lean_object* v_inst_509_, lean_object* v_aig1_510_, lean_object* v_aig2_511_, lean_object* v_ref_512_, lean_object* v_h_513_){
_start:
{
lean_object* v_gate_514_; uint8_t v_invert_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_522_; 
v_gate_514_ = lean_ctor_get(v_ref_512_, 0);
v_invert_515_ = lean_ctor_get_uint8(v_ref_512_, sizeof(void*)*1);
v_isSharedCheck_522_ = !lean_is_exclusive(v_ref_512_);
if (v_isSharedCheck_522_ == 0)
{
v___x_517_ = v_ref_512_;
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_gate_514_);
lean_dec(v_ref_512_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_520_; 
if (v_isShared_518_ == 0)
{
v___x_520_ = v___x_517_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_gate_514_);
lean_ctor_set_uint8(v_reuseFailAlloc_521_, sizeof(void*)*1, v_invert_515_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_cast___boxed(lean_object* v_00_u03b1_523_, lean_object* v_inst_524_, lean_object* v_inst_525_, lean_object* v_aig1_526_, lean_object* v_aig2_527_, lean_object* v_ref_528_, lean_object* v_h_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Std_Sat_AIG_Ref_cast(v_00_u03b1_523_, v_inst_524_, v_inst_525_, v_aig1_526_, v_aig2_527_, v_ref_528_, v_h_529_);
lean_dec_ref(v_aig2_527_);
lean_dec_ref(v_aig1_526_);
lean_dec_ref(v_inst_525_);
lean_dec_ref(v_inst_524_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_flip___redArg(lean_object* v_ref_531_, uint8_t v_inv_532_){
_start:
{
lean_object* v_gate_533_; uint8_t v_invert_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_542_; 
v_gate_533_ = lean_ctor_get(v_ref_531_, 0);
v_invert_534_ = lean_ctor_get_uint8(v_ref_531_, sizeof(void*)*1);
v_isSharedCheck_542_ = !lean_is_exclusive(v_ref_531_);
if (v_isSharedCheck_542_ == 0)
{
v___x_536_ = v_ref_531_;
v_isShared_537_ = v_isSharedCheck_542_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_gate_533_);
lean_dec(v_ref_531_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_542_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
uint8_t v___x_538_; lean_object* v___x_540_; 
v___x_538_ = lean_bool_xor(v_inv_532_, v_invert_534_);
if (v_isShared_537_ == 0)
{
v___x_540_ = v___x_536_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_gate_533_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
lean_ctor_set_uint8(v___x_540_, sizeof(void*)*1, v___x_538_);
return v___x_540_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_flip___redArg___boxed(lean_object* v_ref_543_, lean_object* v_inv_544_){
_start:
{
uint8_t v_inv_boxed_545_; lean_object* v_res_546_; 
v_inv_boxed_545_ = lean_unbox(v_inv_544_);
v_res_546_ = l_Std_Sat_AIG_Ref_flip___redArg(v_ref_543_, v_inv_boxed_545_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_flip(lean_object* v_00_u03b1_547_, lean_object* v_inst_548_, lean_object* v_inst_549_, lean_object* v_aig_550_, lean_object* v_ref_551_, uint8_t v_inv_552_){
_start:
{
lean_object* v_gate_553_; uint8_t v_invert_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_562_; 
v_gate_553_ = lean_ctor_get(v_ref_551_, 0);
v_invert_554_ = lean_ctor_get_uint8(v_ref_551_, sizeof(void*)*1);
v_isSharedCheck_562_ = !lean_is_exclusive(v_ref_551_);
if (v_isSharedCheck_562_ == 0)
{
v___x_556_ = v_ref_551_;
v_isShared_557_ = v_isSharedCheck_562_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_gate_553_);
lean_dec(v_ref_551_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_562_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
uint8_t v___x_558_; lean_object* v___x_560_; 
v___x_558_ = lean_bool_xor(v_inv_552_, v_invert_554_);
if (v_isShared_557_ == 0)
{
v___x_560_ = v___x_556_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_gate_553_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
lean_ctor_set_uint8(v___x_560_, sizeof(void*)*1, v___x_558_);
return v___x_560_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_flip___boxed(lean_object* v_00_u03b1_563_, lean_object* v_inst_564_, lean_object* v_inst_565_, lean_object* v_aig_566_, lean_object* v_ref_567_, lean_object* v_inv_568_){
_start:
{
uint8_t v_inv_boxed_569_; lean_object* v_res_570_; 
v_inv_boxed_569_ = lean_unbox(v_inv_568_);
v_res_570_ = l_Std_Sat_AIG_Ref_flip(v_00_u03b1_563_, v_inst_564_, v_inst_565_, v_aig_566_, v_ref_567_, v_inv_boxed_569_);
lean_dec_ref(v_aig_566_);
lean_dec_ref(v_inst_565_);
lean_dec_ref(v_inst_564_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_not___redArg(lean_object* v_ref_571_){
_start:
{
lean_object* v_gate_572_; uint8_t v_invert_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_582_; 
v_gate_572_ = lean_ctor_get(v_ref_571_, 0);
v_invert_573_ = lean_ctor_get_uint8(v_ref_571_, sizeof(void*)*1);
v_isSharedCheck_582_ = !lean_is_exclusive(v_ref_571_);
if (v_isSharedCheck_582_ == 0)
{
v___x_575_ = v_ref_571_;
v_isShared_576_ = v_isSharedCheck_582_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_gate_572_);
lean_dec(v_ref_571_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_582_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
uint8_t v___x_577_; uint8_t v___x_578_; lean_object* v___x_580_; 
v___x_577_ = 1;
v___x_578_ = lean_bool_xor(v___x_577_, v_invert_573_);
if (v_isShared_576_ == 0)
{
v___x_580_ = v___x_575_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_gate_572_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
lean_ctor_set_uint8(v___x_580_, sizeof(void*)*1, v___x_578_);
return v___x_580_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_not(lean_object* v_00_u03b1_583_, lean_object* v_inst_584_, lean_object* v_inst_585_, lean_object* v_aig_586_, lean_object* v_ref_587_){
_start:
{
lean_object* v_gate_588_; uint8_t v_invert_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_598_; 
v_gate_588_ = lean_ctor_get(v_ref_587_, 0);
v_invert_589_ = lean_ctor_get_uint8(v_ref_587_, sizeof(void*)*1);
v_isSharedCheck_598_ = !lean_is_exclusive(v_ref_587_);
if (v_isSharedCheck_598_ == 0)
{
v___x_591_ = v_ref_587_;
v_isShared_592_ = v_isSharedCheck_598_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_gate_588_);
lean_dec(v_ref_587_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_598_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
uint8_t v___x_593_; uint8_t v___x_594_; lean_object* v___x_596_; 
v___x_593_ = 1;
v___x_594_ = lean_bool_xor(v___x_593_, v_invert_589_);
if (v_isShared_592_ == 0)
{
v___x_596_ = v___x_591_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_gate_588_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
lean_ctor_set_uint8(v___x_596_, sizeof(void*)*1, v___x_594_);
return v___x_596_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_not___boxed(lean_object* v_00_u03b1_599_, lean_object* v_inst_600_, lean_object* v_inst_601_, lean_object* v_aig_602_, lean_object* v_ref_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Std_Sat_AIG_Ref_not(v_00_u03b1_599_, v_inst_600_, v_inst_601_, v_aig_602_, v_ref_603_);
lean_dec_ref(v_aig_602_);
lean_dec_ref(v_inst_601_);
lean_dec_ref(v_inst_600_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_cast___redArg(lean_object* v_input_605_){
_start:
{
lean_object* v_lhs_606_; lean_object* v_rhs_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_632_; 
v_lhs_606_ = lean_ctor_get(v_input_605_, 0);
v_rhs_607_ = lean_ctor_get(v_input_605_, 1);
v_isSharedCheck_632_ = !lean_is_exclusive(v_input_605_);
if (v_isSharedCheck_632_ == 0)
{
v___x_609_ = v_input_605_;
v_isShared_610_ = v_isSharedCheck_632_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_rhs_607_);
lean_inc(v_lhs_606_);
lean_dec(v_input_605_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_632_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v_gate_611_; uint8_t v_invert_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_631_; 
v_gate_611_ = lean_ctor_get(v_lhs_606_, 0);
v_invert_612_ = lean_ctor_get_uint8(v_lhs_606_, sizeof(void*)*1);
v_isSharedCheck_631_ = !lean_is_exclusive(v_lhs_606_);
if (v_isSharedCheck_631_ == 0)
{
v___x_614_ = v_lhs_606_;
v_isShared_615_ = v_isSharedCheck_631_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_gate_611_);
lean_dec(v_lhs_606_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_631_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v_gate_616_; uint8_t v_invert_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_630_; 
v_gate_616_ = lean_ctor_get(v_rhs_607_, 0);
v_invert_617_ = lean_ctor_get_uint8(v_rhs_607_, sizeof(void*)*1);
v_isSharedCheck_630_ = !lean_is_exclusive(v_rhs_607_);
if (v_isSharedCheck_630_ == 0)
{
v___x_619_ = v_rhs_607_;
v_isShared_620_ = v_isSharedCheck_630_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_gate_616_);
lean_dec(v_rhs_607_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_630_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_622_; 
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 0, v_gate_611_);
v___x_622_ = v___x_619_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_gate_611_);
v___x_622_ = v_reuseFailAlloc_629_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
lean_object* v___x_624_; 
lean_ctor_set_uint8(v___x_622_, sizeof(void*)*1, v_invert_612_);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 0, v_gate_616_);
v___x_624_ = v___x_614_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_gate_616_);
v___x_624_ = v_reuseFailAlloc_628_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
lean_object* v___x_626_; 
lean_ctor_set_uint8(v___x_624_, sizeof(void*)*1, v_invert_617_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 1, v___x_624_);
lean_ctor_set(v___x_609_, 0, v___x_622_);
v___x_626_ = v___x_609_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_622_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v___x_624_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_cast(lean_object* v_00_u03b1_633_, lean_object* v_inst_634_, lean_object* v_inst_635_, lean_object* v_aig1_636_, lean_object* v_aig2_637_, lean_object* v_input_638_, lean_object* v_h_639_){
_start:
{
lean_object* v_lhs_640_; lean_object* v_rhs_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_666_; 
v_lhs_640_ = lean_ctor_get(v_input_638_, 0);
v_rhs_641_ = lean_ctor_get(v_input_638_, 1);
v_isSharedCheck_666_ = !lean_is_exclusive(v_input_638_);
if (v_isSharedCheck_666_ == 0)
{
v___x_643_ = v_input_638_;
v_isShared_644_ = v_isSharedCheck_666_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_rhs_641_);
lean_inc(v_lhs_640_);
lean_dec(v_input_638_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_666_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v_gate_645_; uint8_t v_invert_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_665_; 
v_gate_645_ = lean_ctor_get(v_lhs_640_, 0);
v_invert_646_ = lean_ctor_get_uint8(v_lhs_640_, sizeof(void*)*1);
v_isSharedCheck_665_ = !lean_is_exclusive(v_lhs_640_);
if (v_isSharedCheck_665_ == 0)
{
v___x_648_ = v_lhs_640_;
v_isShared_649_ = v_isSharedCheck_665_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_gate_645_);
lean_dec(v_lhs_640_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_665_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v_gate_650_; uint8_t v_invert_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_664_; 
v_gate_650_ = lean_ctor_get(v_rhs_641_, 0);
v_invert_651_ = lean_ctor_get_uint8(v_rhs_641_, sizeof(void*)*1);
v_isSharedCheck_664_ = !lean_is_exclusive(v_rhs_641_);
if (v_isSharedCheck_664_ == 0)
{
v___x_653_ = v_rhs_641_;
v_isShared_654_ = v_isSharedCheck_664_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_gate_650_);
lean_dec(v_rhs_641_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_664_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_656_; 
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 0, v_gate_645_);
v___x_656_ = v___x_653_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_gate_645_);
v___x_656_ = v_reuseFailAlloc_663_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
lean_object* v___x_658_; 
lean_ctor_set_uint8(v___x_656_, sizeof(void*)*1, v_invert_646_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 0, v_gate_650_);
v___x_658_ = v___x_648_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_gate_650_);
v___x_658_ = v_reuseFailAlloc_662_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
lean_object* v___x_660_; 
lean_ctor_set_uint8(v___x_658_, sizeof(void*)*1, v_invert_651_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 1, v___x_658_);
lean_ctor_set(v___x_643_, 0, v___x_656_);
v___x_660_ = v___x_643_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v___x_656_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v___x_658_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_cast___boxed(lean_object* v_00_u03b1_667_, lean_object* v_inst_668_, lean_object* v_inst_669_, lean_object* v_aig1_670_, lean_object* v_aig2_671_, lean_object* v_input_672_, lean_object* v_h_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Std_Sat_AIG_BinaryInput_cast(v_00_u03b1_667_, v_inst_668_, v_inst_669_, v_aig1_670_, v_aig2_671_, v_input_672_, v_h_673_);
lean_dec_ref(v_aig2_671_);
lean_dec_ref(v_aig1_670_);
lean_dec_ref(v_inst_669_);
lean_dec_ref(v_inst_668_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_invert___redArg(lean_object* v_input_675_, uint8_t v_linv_676_, uint8_t v_rinv_677_){
_start:
{
lean_object* v_lhs_678_; lean_object* v_rhs_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_706_; 
v_lhs_678_ = lean_ctor_get(v_input_675_, 0);
v_rhs_679_ = lean_ctor_get(v_input_675_, 1);
v_isSharedCheck_706_ = !lean_is_exclusive(v_input_675_);
if (v_isSharedCheck_706_ == 0)
{
v___x_681_ = v_input_675_;
v_isShared_682_ = v_isSharedCheck_706_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_rhs_679_);
lean_inc(v_lhs_678_);
lean_dec(v_input_675_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_706_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v_gate_683_; uint8_t v_invert_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_705_; 
v_gate_683_ = lean_ctor_get(v_lhs_678_, 0);
v_invert_684_ = lean_ctor_get_uint8(v_lhs_678_, sizeof(void*)*1);
v_isSharedCheck_705_ = !lean_is_exclusive(v_lhs_678_);
if (v_isSharedCheck_705_ == 0)
{
v___x_686_ = v_lhs_678_;
v_isShared_687_ = v_isSharedCheck_705_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_gate_683_);
lean_dec(v_lhs_678_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_705_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v_gate_688_; uint8_t v_invert_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_704_; 
v_gate_688_ = lean_ctor_get(v_rhs_679_, 0);
v_invert_689_ = lean_ctor_get_uint8(v_rhs_679_, sizeof(void*)*1);
v_isSharedCheck_704_ = !lean_is_exclusive(v_rhs_679_);
if (v_isSharedCheck_704_ == 0)
{
v___x_691_ = v_rhs_679_;
v_isShared_692_ = v_isSharedCheck_704_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_gate_688_);
lean_dec(v_rhs_679_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_704_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
uint8_t v___x_693_; lean_object* v___x_695_; 
v___x_693_ = lean_bool_xor(v_linv_676_, v_invert_684_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v_gate_683_);
v___x_695_ = v___x_691_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_gate_683_);
v___x_695_ = v_reuseFailAlloc_703_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
uint8_t v___x_696_; lean_object* v___x_698_; 
lean_ctor_set_uint8(v___x_695_, sizeof(void*)*1, v___x_693_);
v___x_696_ = lean_bool_xor(v_rinv_677_, v_invert_689_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 0, v_gate_688_);
v___x_698_ = v___x_686_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_gate_688_);
v___x_698_ = v_reuseFailAlloc_702_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
lean_object* v___x_700_; 
lean_ctor_set_uint8(v___x_698_, sizeof(void*)*1, v___x_696_);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 1, v___x_698_);
lean_ctor_set(v___x_681_, 0, v___x_695_);
v___x_700_ = v___x_681_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_695_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v___x_698_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_invert___redArg___boxed(lean_object* v_input_707_, lean_object* v_linv_708_, lean_object* v_rinv_709_){
_start:
{
uint8_t v_linv_boxed_710_; uint8_t v_rinv_boxed_711_; lean_object* v_res_712_; 
v_linv_boxed_710_ = lean_unbox(v_linv_708_);
v_rinv_boxed_711_ = lean_unbox(v_rinv_709_);
v_res_712_ = l_Std_Sat_AIG_BinaryInput_invert___redArg(v_input_707_, v_linv_boxed_710_, v_rinv_boxed_711_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_invert(lean_object* v_00_u03b1_713_, lean_object* v_inst_714_, lean_object* v_inst_715_, lean_object* v_aig_716_, lean_object* v_input_717_, uint8_t v_linv_718_, uint8_t v_rinv_719_){
_start:
{
lean_object* v_lhs_720_; lean_object* v_rhs_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_748_; 
v_lhs_720_ = lean_ctor_get(v_input_717_, 0);
v_rhs_721_ = lean_ctor_get(v_input_717_, 1);
v_isSharedCheck_748_ = !lean_is_exclusive(v_input_717_);
if (v_isSharedCheck_748_ == 0)
{
v___x_723_ = v_input_717_;
v_isShared_724_ = v_isSharedCheck_748_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_rhs_721_);
lean_inc(v_lhs_720_);
lean_dec(v_input_717_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_748_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v_gate_725_; uint8_t v_invert_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_747_; 
v_gate_725_ = lean_ctor_get(v_lhs_720_, 0);
v_invert_726_ = lean_ctor_get_uint8(v_lhs_720_, sizeof(void*)*1);
v_isSharedCheck_747_ = !lean_is_exclusive(v_lhs_720_);
if (v_isSharedCheck_747_ == 0)
{
v___x_728_ = v_lhs_720_;
v_isShared_729_ = v_isSharedCheck_747_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_gate_725_);
lean_dec(v_lhs_720_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_747_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v_gate_730_; uint8_t v_invert_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_746_; 
v_gate_730_ = lean_ctor_get(v_rhs_721_, 0);
v_invert_731_ = lean_ctor_get_uint8(v_rhs_721_, sizeof(void*)*1);
v_isSharedCheck_746_ = !lean_is_exclusive(v_rhs_721_);
if (v_isSharedCheck_746_ == 0)
{
v___x_733_ = v_rhs_721_;
v_isShared_734_ = v_isSharedCheck_746_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_gate_730_);
lean_dec(v_rhs_721_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_746_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
uint8_t v___x_735_; lean_object* v___x_737_; 
v___x_735_ = lean_bool_xor(v_linv_718_, v_invert_726_);
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 0, v_gate_725_);
v___x_737_ = v___x_733_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_gate_725_);
v___x_737_ = v_reuseFailAlloc_745_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
uint8_t v___x_738_; lean_object* v___x_740_; 
lean_ctor_set_uint8(v___x_737_, sizeof(void*)*1, v___x_735_);
v___x_738_ = lean_bool_xor(v_rinv_719_, v_invert_731_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 0, v_gate_730_);
v___x_740_ = v___x_728_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_gate_730_);
v___x_740_ = v_reuseFailAlloc_744_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
lean_object* v___x_742_; 
lean_ctor_set_uint8(v___x_740_, sizeof(void*)*1, v___x_738_);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 1, v___x_740_);
lean_ctor_set(v___x_723_, 0, v___x_737_);
v___x_742_ = v___x_723_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_737_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v___x_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_invert___boxed(lean_object* v_00_u03b1_749_, lean_object* v_inst_750_, lean_object* v_inst_751_, lean_object* v_aig_752_, lean_object* v_input_753_, lean_object* v_linv_754_, lean_object* v_rinv_755_){
_start:
{
uint8_t v_linv_boxed_756_; uint8_t v_rinv_boxed_757_; lean_object* v_res_758_; 
v_linv_boxed_756_ = lean_unbox(v_linv_754_);
v_rinv_boxed_757_ = lean_unbox(v_rinv_755_);
v_res_758_ = l_Std_Sat_AIG_BinaryInput_invert(v_00_u03b1_749_, v_inst_750_, v_inst_751_, v_aig_752_, v_input_753_, v_linv_boxed_756_, v_rinv_boxed_757_);
lean_dec_ref(v_aig_752_);
lean_dec_ref(v_inst_751_);
lean_dec_ref(v_inst_750_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_TernaryInput_cast___redArg(lean_object* v_input_759_){
_start:
{
lean_object* v_discr_760_; lean_object* v_lhs_761_; lean_object* v_rhs_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_796_; 
v_discr_760_ = lean_ctor_get(v_input_759_, 0);
v_lhs_761_ = lean_ctor_get(v_input_759_, 1);
v_rhs_762_ = lean_ctor_get(v_input_759_, 2);
v_isSharedCheck_796_ = !lean_is_exclusive(v_input_759_);
if (v_isSharedCheck_796_ == 0)
{
v___x_764_ = v_input_759_;
v_isShared_765_ = v_isSharedCheck_796_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_rhs_762_);
lean_inc(v_lhs_761_);
lean_inc(v_discr_760_);
lean_dec(v_input_759_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_796_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v_gate_766_; uint8_t v_invert_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_795_; 
v_gate_766_ = lean_ctor_get(v_discr_760_, 0);
v_invert_767_ = lean_ctor_get_uint8(v_discr_760_, sizeof(void*)*1);
v_isSharedCheck_795_ = !lean_is_exclusive(v_discr_760_);
if (v_isSharedCheck_795_ == 0)
{
v___x_769_ = v_discr_760_;
v_isShared_770_ = v_isSharedCheck_795_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_gate_766_);
lean_dec(v_discr_760_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_795_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v_gate_771_; uint8_t v_invert_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_794_; 
v_gate_771_ = lean_ctor_get(v_lhs_761_, 0);
v_invert_772_ = lean_ctor_get_uint8(v_lhs_761_, sizeof(void*)*1);
v_isSharedCheck_794_ = !lean_is_exclusive(v_lhs_761_);
if (v_isSharedCheck_794_ == 0)
{
v___x_774_ = v_lhs_761_;
v_isShared_775_ = v_isSharedCheck_794_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_gate_771_);
lean_dec(v_lhs_761_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_794_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v_gate_776_; uint8_t v_invert_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_793_; 
v_gate_776_ = lean_ctor_get(v_rhs_762_, 0);
v_invert_777_ = lean_ctor_get_uint8(v_rhs_762_, sizeof(void*)*1);
v_isSharedCheck_793_ = !lean_is_exclusive(v_rhs_762_);
if (v_isSharedCheck_793_ == 0)
{
v___x_779_ = v_rhs_762_;
v_isShared_780_ = v_isSharedCheck_793_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_gate_776_);
lean_dec(v_rhs_762_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_793_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_782_; 
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 0, v_gate_766_);
v___x_782_ = v___x_779_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_gate_766_);
v___x_782_ = v_reuseFailAlloc_792_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
lean_object* v___x_784_; 
lean_ctor_set_uint8(v___x_782_, sizeof(void*)*1, v_invert_767_);
if (v_isShared_775_ == 0)
{
v___x_784_ = v___x_774_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_gate_771_);
lean_ctor_set_uint8(v_reuseFailAlloc_791_, sizeof(void*)*1, v_invert_772_);
v___x_784_ = v_reuseFailAlloc_791_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
lean_object* v___x_786_; 
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 0, v_gate_776_);
v___x_786_ = v___x_769_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_gate_776_);
v___x_786_ = v_reuseFailAlloc_790_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
lean_object* v___x_788_; 
lean_ctor_set_uint8(v___x_786_, sizeof(void*)*1, v_invert_777_);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 2, v___x_786_);
lean_ctor_set(v___x_764_, 1, v___x_784_);
lean_ctor_set(v___x_764_, 0, v___x_782_);
v___x_788_ = v___x_764_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_782_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v___x_784_);
lean_ctor_set(v_reuseFailAlloc_789_, 2, v___x_786_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_TernaryInput_cast(lean_object* v_00_u03b1_797_, lean_object* v_inst_798_, lean_object* v_inst_799_, lean_object* v_aig1_800_, lean_object* v_aig2_801_, lean_object* v_input_802_, lean_object* v_h_803_){
_start:
{
lean_object* v_discr_804_; lean_object* v_lhs_805_; lean_object* v_rhs_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_840_; 
v_discr_804_ = lean_ctor_get(v_input_802_, 0);
v_lhs_805_ = lean_ctor_get(v_input_802_, 1);
v_rhs_806_ = lean_ctor_get(v_input_802_, 2);
v_isSharedCheck_840_ = !lean_is_exclusive(v_input_802_);
if (v_isSharedCheck_840_ == 0)
{
v___x_808_ = v_input_802_;
v_isShared_809_ = v_isSharedCheck_840_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_rhs_806_);
lean_inc(v_lhs_805_);
lean_inc(v_discr_804_);
lean_dec(v_input_802_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_840_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v_gate_810_; uint8_t v_invert_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_839_; 
v_gate_810_ = lean_ctor_get(v_discr_804_, 0);
v_invert_811_ = lean_ctor_get_uint8(v_discr_804_, sizeof(void*)*1);
v_isSharedCheck_839_ = !lean_is_exclusive(v_discr_804_);
if (v_isSharedCheck_839_ == 0)
{
v___x_813_ = v_discr_804_;
v_isShared_814_ = v_isSharedCheck_839_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_gate_810_);
lean_dec(v_discr_804_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_839_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v_gate_815_; uint8_t v_invert_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_838_; 
v_gate_815_ = lean_ctor_get(v_lhs_805_, 0);
v_invert_816_ = lean_ctor_get_uint8(v_lhs_805_, sizeof(void*)*1);
v_isSharedCheck_838_ = !lean_is_exclusive(v_lhs_805_);
if (v_isSharedCheck_838_ == 0)
{
v___x_818_ = v_lhs_805_;
v_isShared_819_ = v_isSharedCheck_838_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_gate_815_);
lean_dec(v_lhs_805_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_838_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v_gate_820_; uint8_t v_invert_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_837_; 
v_gate_820_ = lean_ctor_get(v_rhs_806_, 0);
v_invert_821_ = lean_ctor_get_uint8(v_rhs_806_, sizeof(void*)*1);
v_isSharedCheck_837_ = !lean_is_exclusive(v_rhs_806_);
if (v_isSharedCheck_837_ == 0)
{
v___x_823_ = v_rhs_806_;
v_isShared_824_ = v_isSharedCheck_837_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_gate_820_);
lean_dec(v_rhs_806_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_837_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 0, v_gate_810_);
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_gate_810_);
v___x_826_ = v_reuseFailAlloc_836_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
lean_object* v___x_828_; 
lean_ctor_set_uint8(v___x_826_, sizeof(void*)*1, v_invert_811_);
if (v_isShared_819_ == 0)
{
v___x_828_ = v___x_818_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_gate_815_);
lean_ctor_set_uint8(v_reuseFailAlloc_835_, sizeof(void*)*1, v_invert_816_);
v___x_828_ = v_reuseFailAlloc_835_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
lean_object* v___x_830_; 
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v_gate_820_);
v___x_830_ = v___x_813_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_gate_820_);
v___x_830_ = v_reuseFailAlloc_834_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
lean_object* v___x_832_; 
lean_ctor_set_uint8(v___x_830_, sizeof(void*)*1, v_invert_821_);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 2, v___x_830_);
lean_ctor_set(v___x_808_, 1, v___x_828_);
lean_ctor_set(v___x_808_, 0, v___x_826_);
v___x_832_ = v___x_808_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_826_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v___x_828_);
lean_ctor_set(v_reuseFailAlloc_833_, 2, v___x_830_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_TernaryInput_cast___boxed(lean_object* v_00_u03b1_841_, lean_object* v_inst_842_, lean_object* v_inst_843_, lean_object* v_aig1_844_, lean_object* v_aig2_845_, lean_object* v_input_846_, lean_object* v_h_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Std_Sat_AIG_TernaryInput_cast(v_00_u03b1_841_, v_inst_842_, v_inst_843_, v_aig1_844_, v_aig2_845_, v_input_846_, v_h_847_);
lean_dec_ref(v_aig2_845_);
lean_dec_ref(v_aig1_844_);
lean_dec_ref(v_inst_843_);
lean_dec_ref(v_inst_842_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_invEdgeStyle(uint8_t v_isInv_851_){
_start:
{
if (v_isInv_851_ == 0)
{
lean_object* v___x_852_; 
v___x_852_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_invEdgeStyle___closed__0));
return v___x_852_;
}
else
{
lean_object* v___x_853_; 
v___x_853_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_invEdgeStyle___closed__1));
return v___x_853_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_invEdgeStyle___boxed(lean_object* v_isInv_854_){
_start:
{
uint8_t v_isInv_boxed_855_; lean_object* v_res_856_; 
v_isInv_boxed_855_ = lean_unbox(v_isInv_854_);
v_res_856_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v_isInv_boxed_855_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___redArg(lean_object* v_acc_861_, lean_object* v_decls_862_, lean_object* v_idx_863_, lean_object* v_a_864_){
_start:
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___f_867_; lean_object* v___f_868_; uint8_t v___x_869_; 
v___x_865_ = lean_array_get_size(v_decls_862_);
v___x_866_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_866_, 0, v___x_865_);
v___f_867_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_867_, 0, v___x_866_);
v___f_868_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___redArg___closed__0));
lean_inc(v_idx_863_);
lean_inc_ref(v___f_867_);
v___x_869_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_867_, v___f_868_, v_a_864_, v_idx_863_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_870_ = lean_box(0);
lean_inc(v_idx_863_);
v___x_871_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___f_867_, v___f_868_, v_a_864_, v_idx_863_, v___x_870_);
v___x_872_ = lean_array_fget_borrowed(v_decls_862_, v_idx_863_);
if (lean_obj_tag(v___x_872_) == 2)
{
lean_object* v_l_873_; lean_object* v_r_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; uint8_t v___x_879_; uint8_t v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; uint8_t v___x_883_; uint8_t v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v_fst_904_; lean_object* v_snd_905_; 
v_l_873_ = lean_ctor_get(v___x_872_, 0);
v_r_874_ = lean_ctor_get(v___x_872_, 1);
v___x_875_ = lean_unsigned_to_nat(1u);
v___x_876_ = lean_nat_shiftr(v_l_873_, v___x_875_);
v___x_877_ = lean_nat_land(v___x_875_, v_l_873_);
v___x_878_ = lean_unsigned_to_nat(0u);
v___x_879_ = lean_nat_dec_eq(v___x_877_, v___x_878_);
lean_dec(v___x_877_);
v___x_880_ = lean_bool_not(v___x_879_);
v___x_881_ = lean_nat_shiftr(v_r_874_, v___x_875_);
v___x_882_ = lean_nat_land(v___x_875_, v_r_874_);
v___x_883_ = lean_nat_dec_eq(v___x_882_, v___x_878_);
lean_dec(v___x_882_);
v___x_884_ = lean_bool_not(v___x_883_);
v___x_885_ = l_Nat_reprFast(v_idx_863_);
v___x_886_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___redArg___closed__1));
lean_inc_ref(v___x_885_);
v___x_887_ = lean_string_append(v___x_885_, v___x_886_);
lean_inc(v___x_876_);
v___x_888_ = l_Nat_reprFast(v___x_876_);
v___x_889_ = lean_string_append(v___x_887_, v___x_888_);
lean_dec_ref(v___x_888_);
v___x_890_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___x_880_);
v___x_891_ = lean_string_append(v___x_889_, v___x_890_);
lean_dec_ref(v___x_890_);
v___x_892_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___redArg___closed__2));
v___x_893_ = lean_string_append(v___x_891_, v___x_892_);
v___x_894_ = lean_string_append(v___x_893_, v___x_885_);
lean_dec_ref(v___x_885_);
v___x_895_ = lean_string_append(v___x_894_, v___x_886_);
lean_inc(v___x_881_);
v___x_896_ = l_Nat_reprFast(v___x_881_);
v___x_897_ = lean_string_append(v___x_895_, v___x_896_);
lean_dec_ref(v___x_896_);
v___x_898_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___x_884_);
v___x_899_ = lean_string_append(v___x_897_, v___x_898_);
lean_dec_ref(v___x_898_);
v___x_900_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___redArg___closed__3));
v___x_901_ = lean_string_append(v___x_899_, v___x_900_);
v___x_902_ = lean_string_append(v_acc_861_, v___x_901_);
lean_dec_ref(v___x_901_);
v___x_903_ = l_Std_Sat_AIG_toGraphviz_go___redArg(v___x_902_, v_decls_862_, v___x_876_, v___x_871_);
v_fst_904_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_fst_904_);
v_snd_905_ = lean_ctor_get(v___x_903_, 1);
lean_inc(v_snd_905_);
lean_dec_ref(v___x_903_);
v_acc_861_ = v_fst_904_;
v_idx_863_ = v___x_881_;
v_a_864_ = v_snd_905_;
goto _start;
}
else
{
lean_object* v___x_907_; 
lean_dec(v_idx_863_);
v___x_907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_907_, 0, v_acc_861_);
lean_ctor_set(v___x_907_, 1, v___x_871_);
return v___x_907_;
}
}
else
{
lean_object* v___x_908_; 
lean_dec_ref(v___f_867_);
lean_dec(v_idx_863_);
v___x_908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_908_, 0, v_acc_861_);
lean_ctor_set(v___x_908_, 1, v_a_864_);
return v___x_908_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___redArg___boxed(lean_object* v_acc_909_, lean_object* v_decls_910_, lean_object* v_idx_911_, lean_object* v_a_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Std_Sat_AIG_toGraphviz_go___redArg(v_acc_909_, v_decls_910_, v_idx_911_, v_a_912_);
lean_dec_ref(v_decls_910_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go(lean_object* v_00_u03b1_914_, lean_object* v_inst_915_, lean_object* v_inst_916_, lean_object* v_inst_917_, lean_object* v_acc_918_, lean_object* v_decls_919_, lean_object* v_hinv_920_, lean_object* v_idx_921_, lean_object* v_hidx_922_, lean_object* v_a_923_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l_Std_Sat_AIG_toGraphviz_go___redArg(v_acc_918_, v_decls_919_, v_idx_921_, v_a_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___boxed(lean_object* v_00_u03b1_925_, lean_object* v_inst_926_, lean_object* v_inst_927_, lean_object* v_inst_928_, lean_object* v_acc_929_, lean_object* v_decls_930_, lean_object* v_hinv_931_, lean_object* v_idx_932_, lean_object* v_hidx_933_, lean_object* v_a_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Std_Sat_AIG_toGraphviz_go(v_00_u03b1_925_, v_inst_926_, v_inst_927_, v_inst_928_, v_acc_929_, v_decls_930_, v_hinv_931_, v_idx_932_, v_hidx_933_, v_a_934_);
lean_dec_ref(v_decls_930_);
lean_dec_ref(v_inst_928_);
lean_dec_ref(v_inst_927_);
lean_dec_ref(v_inst_926_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter___redArg(lean_object* v_x_936_, lean_object* v_h__1_937_, lean_object* v_h__2_938_, lean_object* v_h__3_939_){
_start:
{
switch(lean_obj_tag(v_x_936_))
{
case 0:
{
lean_object* v___x_940_; 
lean_dec(v_h__3_939_);
lean_dec(v_h__2_938_);
v___x_940_ = lean_apply_1(v_h__1_937_, lean_box(0));
return v___x_940_;
}
case 1:
{
lean_object* v_idx_941_; lean_object* v___x_942_; 
lean_dec(v_h__3_939_);
lean_dec(v_h__1_937_);
v_idx_941_ = lean_ctor_get(v_x_936_, 0);
lean_inc(v_idx_941_);
lean_dec_ref_known(v_x_936_, 1);
v___x_942_ = lean_apply_2(v_h__2_938_, v_idx_941_, lean_box(0));
return v___x_942_;
}
default: 
{
lean_object* v_l_943_; lean_object* v_r_944_; lean_object* v___x_945_; 
lean_dec(v_h__2_938_);
lean_dec(v_h__1_937_);
v_l_943_ = lean_ctor_get(v_x_936_, 0);
lean_inc(v_l_943_);
v_r_944_ = lean_ctor_get(v_x_936_, 1);
lean_inc(v_r_944_);
lean_dec_ref_known(v_x_936_, 2);
v___x_945_ = lean_apply_3(v_h__3_939_, v_l_943_, v_r_944_, lean_box(0));
return v___x_945_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter(lean_object* v_00_u03b1_946_, lean_object* v_motive_947_, lean_object* v_x_948_, lean_object* v_h__1_949_, lean_object* v_h__2_950_, lean_object* v_h__3_951_){
_start:
{
switch(lean_obj_tag(v_x_948_))
{
case 0:
{
lean_object* v___x_952_; 
lean_dec(v_h__3_951_);
lean_dec(v_h__2_950_);
v___x_952_ = lean_apply_1(v_h__1_949_, lean_box(0));
return v___x_952_;
}
case 1:
{
lean_object* v_idx_953_; lean_object* v___x_954_; 
lean_dec(v_h__3_951_);
lean_dec(v_h__1_949_);
v_idx_953_ = lean_ctor_get(v_x_948_, 0);
lean_inc(v_idx_953_);
lean_dec_ref_known(v_x_948_, 1);
v___x_954_ = lean_apply_2(v_h__2_950_, v_idx_953_, lean_box(0));
return v___x_954_;
}
default: 
{
lean_object* v_l_955_; lean_object* v_r_956_; lean_object* v___x_957_; 
lean_dec(v_h__2_950_);
lean_dec(v_h__1_949_);
v_l_955_ = lean_ctor_get(v_x_948_, 0);
lean_inc(v_l_955_);
v_r_956_ = lean_ctor_get(v_x_948_, 1);
lean_inc(v_r_956_);
lean_dec_ref_known(v_x_948_, 2);
v___x_957_ = lean_apply_3(v_h__3_951_, v_l_955_, v_r_956_, lean_box(0));
return v___x_957_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg(lean_object* v_inst_963_, lean_object* v_decls_964_, lean_object* v_idx_965_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = lean_array_fget_borrowed(v_decls_964_, v_idx_965_);
switch(lean_obj_tag(v___x_966_))
{
case 0:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
lean_dec_ref(v_inst_963_);
v___x_967_ = l_Nat_reprFast(v_idx_965_);
v___x_968_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__0));
v___x_969_ = lean_string_append(v___x_967_, v___x_968_);
v___x_970_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__1));
v___x_971_ = lean_string_append(v___x_969_, v___x_970_);
v___x_972_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__2));
v___x_973_ = lean_string_append(v___x_971_, v___x_972_);
return v___x_973_;
}
case 1:
{
lean_object* v_idx_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v_idx_974_ = lean_ctor_get(v___x_966_, 0);
v___x_975_ = l_Nat_reprFast(v_idx_965_);
v___x_976_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__0));
v___x_977_ = lean_string_append(v___x_975_, v___x_976_);
lean_inc(v_idx_974_);
v___x_978_ = lean_apply_1(v_inst_963_, v_idx_974_);
v___x_979_ = lean_string_append(v___x_977_, v___x_978_);
lean_dec_ref(v___x_978_);
v___x_980_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__3));
v___x_981_ = lean_string_append(v___x_979_, v___x_980_);
return v___x_981_;
}
default: 
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
lean_dec_ref(v_inst_963_);
v___x_982_ = l_Nat_reprFast(v_idx_965_);
v___x_983_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__0));
lean_inc_ref(v___x_982_);
v___x_984_ = lean_string_append(v___x_982_, v___x_983_);
v___x_985_ = lean_string_append(v___x_984_, v___x_982_);
lean_dec_ref(v___x_982_);
v___x_986_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__4));
v___x_987_ = lean_string_append(v___x_985_, v___x_986_);
return v___x_987_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___boxed(lean_object* v_inst_988_, lean_object* v_decls_989_, lean_object* v_idx_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg(v_inst_988_, v_decls_989_, v_idx_990_);
lean_dec_ref(v_decls_989_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString(lean_object* v_00_u03b1_992_, lean_object* v_inst_993_, lean_object* v_inst_994_, lean_object* v_inst_995_, lean_object* v_decls_996_, lean_object* v_idx_997_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg(v_inst_994_, v_decls_996_, v_idx_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___boxed(lean_object* v_00_u03b1_999_, lean_object* v_inst_1000_, lean_object* v_inst_1001_, lean_object* v_inst_1002_, lean_object* v_decls_1003_, lean_object* v_idx_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString(v_00_u03b1_999_, v_inst_1000_, v_inst_1001_, v_inst_1002_, v_decls_1003_, v_idx_1004_);
lean_dec_ref(v_decls_1003_);
lean_dec_ref(v_inst_1002_);
lean_dec_ref(v_inst_1000_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___redArg___lam__0(lean_object* v_inst_1006_, lean_object* v_decls_1007_, lean_object* v_x1_1008_, lean_object* v_x2_1009_, lean_object* v_x3_1010_){
_start:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1011_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg(v_inst_1006_, v_decls_1007_, v_x2_1009_);
v___x_1012_ = lean_string_append(v_x1_1008_, v___x_1011_);
lean_dec_ref(v___x_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___redArg___lam__0___boxed(lean_object* v_inst_1013_, lean_object* v_decls_1014_, lean_object* v_x1_1015_, lean_object* v_x2_1016_, lean_object* v_x3_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Std_Sat_AIG_toGraphviz___redArg___lam__0(v_inst_1013_, v_decls_1014_, v_x1_1015_, v_x2_1016_, v_x3_1017_);
lean_dec_ref(v_decls_1014_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___redArg___lam__1(lean_object* v___x_1019_, lean_object* v___f_1020_, lean_object* v_acc_1021_, lean_object* v_l_1022_){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1019_, v___f_1020_, v_acc_1021_, v_l_1022_);
return v___x_1023_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___redArg___closed__1(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1025_ = lean_box(0);
v___x_1026_ = lean_unsigned_to_nat(16u);
v___x_1027_ = lean_mk_array(v___x_1026_, v___x_1025_);
return v___x_1027_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___redArg___closed__2(void){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1028_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___redArg___closed__1, &l_Std_Sat_AIG_toGraphviz___redArg___closed__1_once, _init_l_Std_Sat_AIG_toGraphviz___redArg___closed__1);
v___x_1029_ = lean_unsigned_to_nat(0u);
v___x_1030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
lean_ctor_set(v___x_1030_, 1, v___x_1028_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___redArg(lean_object* v_inst_1052_, lean_object* v_entry_1053_){
_start:
{
lean_object* v_aig_1054_; lean_object* v_ref_1055_; lean_object* v_decls_1056_; lean_object* v_gate_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v_fst_1062_; lean_object* v_snd_1063_; lean_object* v___y_1065_; lean_object* v___x_1071_; lean_object* v_buckets_1072_; lean_object* v___x_1073_; uint8_t v___x_1074_; 
v_aig_1054_ = lean_ctor_get(v_entry_1053_, 0);
lean_inc_ref(v_aig_1054_);
v_ref_1055_ = lean_ctor_get(v_entry_1053_, 1);
lean_inc_ref(v_ref_1055_);
lean_dec_ref(v_entry_1053_);
v_decls_1056_ = lean_ctor_get(v_aig_1054_, 0);
lean_inc_ref(v_decls_1056_);
lean_dec_ref(v_aig_1054_);
v_gate_1057_ = lean_ctor_get(v_ref_1055_, 0);
lean_inc(v_gate_1057_);
lean_dec_ref(v_ref_1055_);
v___x_1058_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___redArg___closed__0));
v___x_1059_ = lean_unsigned_to_nat(0u);
v___x_1060_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___redArg___closed__2, &l_Std_Sat_AIG_toGraphviz___redArg___closed__2_once, _init_l_Std_Sat_AIG_toGraphviz___redArg___closed__2);
v___x_1061_ = l_Std_Sat_AIG_toGraphviz_go___redArg(v___x_1058_, v_decls_1056_, v_gate_1057_, v___x_1060_);
v_fst_1062_ = lean_ctor_get(v___x_1061_, 0);
lean_inc(v_fst_1062_);
v_snd_1063_ = lean_ctor_get(v___x_1061_, 1);
lean_inc(v_snd_1063_);
lean_dec_ref(v___x_1061_);
v___x_1071_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___redArg___closed__14));
v_buckets_1072_ = lean_ctor_get(v_snd_1063_, 1);
lean_inc_ref(v_buckets_1072_);
lean_dec(v_snd_1063_);
v___x_1073_ = lean_array_get_size(v_buckets_1072_);
v___x_1074_ = lean_nat_dec_lt(v___x_1059_, v___x_1073_);
if (v___x_1074_ == 0)
{
lean_dec_ref(v_buckets_1072_);
lean_dec_ref(v_decls_1056_);
lean_dec_ref(v_inst_1052_);
v___y_1065_ = v___x_1058_;
goto v___jp_1064_;
}
else
{
lean_object* v___f_1075_; lean_object* v___f_1076_; uint8_t v___x_1077_; 
v___f_1075_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_toGraphviz___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1075_, 0, v_inst_1052_);
lean_closure_set(v___f_1075_, 1, v_decls_1056_);
v___f_1076_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_toGraphviz___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1076_, 0, v___x_1071_);
lean_closure_set(v___f_1076_, 1, v___f_1075_);
v___x_1077_ = lean_nat_dec_le(v___x_1073_, v___x_1073_);
if (v___x_1077_ == 0)
{
if (v___x_1074_ == 0)
{
lean_dec_ref(v___f_1076_);
lean_dec_ref(v_buckets_1072_);
v___y_1065_ = v___x_1058_;
goto v___jp_1064_;
}
else
{
size_t v___x_1078_; size_t v___x_1079_; lean_object* v___x_1080_; 
v___x_1078_ = ((size_t)0ULL);
v___x_1079_ = lean_usize_of_nat(v___x_1073_);
v___x_1080_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1071_, v___f_1076_, v_buckets_1072_, v___x_1078_, v___x_1079_, v___x_1058_);
v___y_1065_ = v___x_1080_;
goto v___jp_1064_;
}
}
else
{
size_t v___x_1081_; size_t v___x_1082_; lean_object* v___x_1083_; 
v___x_1081_ = ((size_t)0ULL);
v___x_1082_ = lean_usize_of_nat(v___x_1073_);
v___x_1083_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1071_, v___f_1076_, v_buckets_1072_, v___x_1081_, v___x_1082_, v___x_1058_);
v___y_1065_ = v___x_1083_;
goto v___jp_1064_;
}
}
v___jp_1064_:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1066_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___redArg___closed__3));
v___x_1067_ = lean_string_append(v___x_1066_, v___y_1065_);
lean_dec_ref(v___y_1065_);
v___x_1068_ = lean_string_append(v___x_1067_, v_fst_1062_);
lean_dec(v_fst_1062_);
v___x_1069_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___redArg___closed__4));
v___x_1070_ = lean_string_append(v___x_1068_, v___x_1069_);
return v___x_1070_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz(lean_object* v_00_u03b1_1084_, lean_object* v_inst_1085_, lean_object* v_inst_1086_, lean_object* v_inst_1087_, lean_object* v_entry_1088_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = l_Std_Sat_AIG_toGraphviz___redArg(v_inst_1086_, v_entry_1088_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___boxed(lean_object* v_00_u03b1_1090_, lean_object* v_inst_1091_, lean_object* v_inst_1092_, lean_object* v_inst_1093_, lean_object* v_entry_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Std_Sat_AIG_toGraphviz(v_00_u03b1_1090_, v_inst_1091_, v_inst_1092_, v_inst_1093_, v_entry_1094_);
lean_dec_ref(v_inst_1093_);
lean_dec_ref(v_inst_1091_);
return v_res_1095_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote_go___redArg(lean_object* v_x_1096_, lean_object* v_decls_1097_, lean_object* v_assign_1098_){
_start:
{
lean_object* v___x_1099_; 
v___x_1099_ = lean_array_fget_borrowed(v_decls_1097_, v_x_1096_);
switch(lean_obj_tag(v___x_1099_))
{
case 0:
{
uint8_t v___x_1100_; 
lean_dec_ref(v_assign_1098_);
v___x_1100_ = 0;
return v___x_1100_;
}
case 1:
{
lean_object* v_idx_1101_; lean_object* v___x_1102_; uint8_t v___x_1103_; 
v_idx_1101_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_idx_1101_);
v___x_1102_ = lean_apply_1(v_assign_1098_, v_idx_1101_);
v___x_1103_ = lean_unbox(v___x_1102_);
return v___x_1103_;
}
default: 
{
lean_object* v_l_1104_; lean_object* v_r_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; uint8_t v_lval_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; uint8_t v___x_1111_; uint8_t v___x_1112_; uint8_t v___x_1113_; 
v_l_1104_ = lean_ctor_get(v___x_1099_, 0);
v_r_1105_ = lean_ctor_get(v___x_1099_, 1);
v___x_1106_ = lean_unsigned_to_nat(1u);
v___x_1107_ = lean_nat_shiftr(v_l_1104_, v___x_1106_);
lean_inc_ref(v_assign_1098_);
v_lval_1108_ = l_Std_Sat_AIG_denote_go___redArg(v___x_1107_, v_decls_1097_, v_assign_1098_);
lean_dec(v___x_1107_);
v___x_1109_ = lean_nat_land(v___x_1106_, v_l_1104_);
v___x_1110_ = lean_unsigned_to_nat(0u);
v___x_1111_ = lean_nat_dec_eq(v___x_1109_, v___x_1110_);
lean_dec(v___x_1109_);
v___x_1112_ = lean_bool_not(v___x_1111_);
v___x_1113_ = lean_bool_xor(v_lval_1108_, v___x_1112_);
if (v___x_1113_ == 0)
{
lean_dec_ref(v_assign_1098_);
return v___x_1113_;
}
else
{
lean_object* v___x_1114_; uint8_t v_rval_1115_; lean_object* v___x_1116_; uint8_t v___x_1117_; uint8_t v___x_1118_; uint8_t v___x_1119_; 
v___x_1114_ = lean_nat_shiftr(v_r_1105_, v___x_1106_);
v_rval_1115_ = l_Std_Sat_AIG_denote_go___redArg(v___x_1114_, v_decls_1097_, v_assign_1098_);
lean_dec(v___x_1114_);
v___x_1116_ = lean_nat_land(v___x_1106_, v_r_1105_);
v___x_1117_ = lean_nat_dec_eq(v___x_1116_, v___x_1110_);
lean_dec(v___x_1116_);
v___x_1118_ = lean_bool_not(v___x_1117_);
v___x_1119_ = lean_bool_xor(v_rval_1115_, v___x_1118_);
return v___x_1119_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote_go___redArg___boxed(lean_object* v_x_1120_, lean_object* v_decls_1121_, lean_object* v_assign_1122_){
_start:
{
uint8_t v_res_1123_; lean_object* v_r_1124_; 
v_res_1123_ = l_Std_Sat_AIG_denote_go___redArg(v_x_1120_, v_decls_1121_, v_assign_1122_);
lean_dec_ref(v_decls_1121_);
lean_dec(v_x_1120_);
v_r_1124_ = lean_box(v_res_1123_);
return v_r_1124_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote_go(lean_object* v_00_u03b1_1125_, lean_object* v_x_1126_, lean_object* v_decls_1127_, lean_object* v_assign_1128_, lean_object* v_h1_1129_, lean_object* v_h2_1130_){
_start:
{
uint8_t v___x_1131_; 
v___x_1131_ = l_Std_Sat_AIG_denote_go___redArg(v_x_1126_, v_decls_1127_, v_assign_1128_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote_go___boxed(lean_object* v_00_u03b1_1132_, lean_object* v_x_1133_, lean_object* v_decls_1134_, lean_object* v_assign_1135_, lean_object* v_h1_1136_, lean_object* v_h2_1137_){
_start:
{
uint8_t v_res_1138_; lean_object* v_r_1139_; 
v_res_1138_ = l_Std_Sat_AIG_denote_go(v_00_u03b1_1132_, v_x_1133_, v_decls_1134_, v_assign_1135_, v_h1_1136_, v_h2_1137_);
lean_dec_ref(v_decls_1134_);
lean_dec(v_x_1133_);
v_r_1139_ = lean_box(v_res_1138_);
return v_r_1139_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote___redArg(lean_object* v_assign_1140_, lean_object* v_entry_1141_){
_start:
{
lean_object* v_ref_1142_; lean_object* v_aig_1143_; lean_object* v_gate_1144_; uint8_t v_invert_1145_; lean_object* v_decls_1146_; uint8_t v___x_1147_; uint8_t v___x_1148_; 
v_ref_1142_ = lean_ctor_get(v_entry_1141_, 1);
v_aig_1143_ = lean_ctor_get(v_entry_1141_, 0);
v_gate_1144_ = lean_ctor_get(v_ref_1142_, 0);
v_invert_1145_ = lean_ctor_get_uint8(v_ref_1142_, sizeof(void*)*1);
v_decls_1146_ = lean_ctor_get(v_aig_1143_, 0);
v___x_1147_ = l_Std_Sat_AIG_denote_go___redArg(v_gate_1144_, v_decls_1146_, v_assign_1140_);
v___x_1148_ = lean_bool_xor(v___x_1147_, v_invert_1145_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote___redArg___boxed(lean_object* v_assign_1149_, lean_object* v_entry_1150_){
_start:
{
uint8_t v_res_1151_; lean_object* v_r_1152_; 
v_res_1151_ = l_Std_Sat_AIG_denote___redArg(v_assign_1149_, v_entry_1150_);
lean_dec_ref(v_entry_1150_);
v_r_1152_ = lean_box(v_res_1151_);
return v_r_1152_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote(lean_object* v_00_u03b1_1153_, lean_object* v_inst_1154_, lean_object* v_inst_1155_, lean_object* v_assign_1156_, lean_object* v_entry_1157_){
_start:
{
uint8_t v___x_1158_; 
v___x_1158_ = l_Std_Sat_AIG_denote___redArg(v_assign_1156_, v_entry_1157_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote___boxed(lean_object* v_00_u03b1_1159_, lean_object* v_inst_1160_, lean_object* v_inst_1161_, lean_object* v_assign_1162_, lean_object* v_entry_1163_){
_start:
{
uint8_t v_res_1164_; lean_object* v_r_1165_; 
v_res_1164_ = l_Std_Sat_AIG_denote(v_00_u03b1_1159_, v_inst_1160_, v_inst_1161_, v_assign_1162_, v_entry_1163_);
lean_dec_ref(v_entry_1163_);
lean_dec_ref(v_inst_1161_);
lean_dec_ref(v_inst_1160_);
v_r_1165_ = lean_box(v_res_1164_);
return v_r_1165_;
}
}
static lean_object* _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6(void){
_start:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1247_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__5));
v___x_1248_ = l_String_toRawSubstring_x27(v___x_1247_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1(lean_object* v_x_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_){
_start:
{
lean_object* v___x_1273_; uint8_t v___x_1274_; 
v___x_1273_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
lean_inc(v_x_1270_);
v___x_1274_ = l_Lean_Syntax_isOfKind(v_x_1270_, v___x_1273_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
lean_dec(v_x_1270_);
v___x_1275_ = lean_box(1);
v___x_1276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1275_);
lean_ctor_set(v___x_1276_, 1, v_a_1272_);
return v___x_1276_;
}
else
{
lean_object* v_quotContext_1277_; lean_object* v_currMacroScope_1278_; lean_object* v_ref_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; uint8_t v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v_quotContext_1277_ = lean_ctor_get(v_a_1271_, 1);
v_currMacroScope_1278_ = lean_ctor_get(v_a_1271_, 2);
v_ref_1279_ = lean_ctor_get(v_a_1271_, 5);
v___x_1280_ = lean_unsigned_to_nat(1u);
v___x_1281_ = l_Lean_Syntax_getArg(v_x_1270_, v___x_1280_);
v___x_1282_ = lean_unsigned_to_nat(3u);
v___x_1283_ = l_Lean_Syntax_getArg(v_x_1270_, v___x_1282_);
lean_dec(v_x_1270_);
v___x_1284_ = 0;
v___x_1285_ = l_Lean_SourceInfo_fromRef(v_ref_1279_, v___x_1284_);
v___x_1286_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4));
v___x_1287_ = lean_obj_once(&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6, &l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6_once, _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6);
v___x_1288_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__7));
lean_inc(v_currMacroScope_1278_);
lean_inc(v_quotContext_1277_);
v___x_1289_ = l_Lean_addMacroScope(v_quotContext_1277_, v___x_1288_, v_currMacroScope_1278_);
v___x_1290_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__12));
lean_inc_n(v___x_1285_, 2);
v___x_1291_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1285_);
lean_ctor_set(v___x_1291_, 1, v___x_1287_);
lean_ctor_set(v___x_1291_, 2, v___x_1289_);
lean_ctor_set(v___x_1291_, 3, v___x_1290_);
v___x_1292_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__14));
v___x_1293_ = l_Lean_Syntax_node2(v___x_1285_, v___x_1292_, v___x_1283_, v___x_1281_);
v___x_1294_ = l_Lean_Syntax_node2(v___x_1285_, v___x_1286_, v___x_1291_, v___x_1293_);
v___x_1295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
lean_ctor_set(v___x_1295_, 1, v_a_1272_);
return v___x_1295_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___boxed(lean_object* v_x_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1(v_x_1296_, v_a_1297_, v_a_1298_);
lean_dec_ref(v_a_1297_);
return v_res_1299_;
}
}
static lean_object* _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__7(void){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___redArg___closed__0));
v___x_1317_ = l_String_toRawSubstring_x27(v___x_1316_);
return v___x_1317_;
}
}
static lean_object* _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__12(void){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1328_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__11));
v___x_1329_ = l_String_toRawSubstring_x27(v___x_1328_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1(lean_object* v_x_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_){
_start:
{
lean_object* v___x_1356_; uint8_t v___x_1357_; 
v___x_1356_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__1));
lean_inc(v_x_1353_);
v___x_1357_ = l_Lean_Syntax_isOfKind(v_x_1353_, v___x_1356_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
lean_dec(v_x_1353_);
v___x_1358_ = lean_box(1);
v___x_1359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1358_);
lean_ctor_set(v___x_1359_, 1, v_a_1355_);
return v___x_1359_;
}
else
{
lean_object* v_quotContext_1360_; lean_object* v_currMacroScope_1361_; lean_object* v_ref_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; uint8_t v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v_quotContext_1360_ = lean_ctor_get(v_a_1354_, 1);
v_currMacroScope_1361_ = lean_ctor_get(v_a_1354_, 2);
v_ref_1362_ = lean_ctor_get(v_a_1354_, 5);
v___x_1363_ = lean_unsigned_to_nat(1u);
v___x_1364_ = l_Lean_Syntax_getArg(v_x_1353_, v___x_1363_);
v___x_1365_ = lean_unsigned_to_nat(3u);
v___x_1366_ = l_Lean_Syntax_getArg(v_x_1353_, v___x_1365_);
v___x_1367_ = lean_unsigned_to_nat(5u);
v___x_1368_ = l_Lean_Syntax_getArg(v_x_1353_, v___x_1367_);
lean_dec(v_x_1353_);
v___x_1369_ = 0;
v___x_1370_ = l_Lean_SourceInfo_fromRef(v_ref_1362_, v___x_1369_);
v___x_1371_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4));
v___x_1372_ = lean_obj_once(&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6, &l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6_once, _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6);
v___x_1373_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__7));
lean_inc_n(v_currMacroScope_1361_, 3);
lean_inc_n(v_quotContext_1360_, 3);
v___x_1374_ = l_Lean_addMacroScope(v_quotContext_1360_, v___x_1373_, v_currMacroScope_1361_);
v___x_1375_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__12));
lean_inc_n(v___x_1370_, 11);
v___x_1376_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1370_);
lean_ctor_set(v___x_1376_, 1, v___x_1372_);
lean_ctor_set(v___x_1376_, 2, v___x_1374_);
lean_ctor_set(v___x_1376_, 3, v___x_1375_);
v___x_1377_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__14));
v___x_1378_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__1));
v___x_1379_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__3));
v___x_1380_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__4));
v___x_1381_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1370_);
lean_ctor_set(v___x_1381_, 1, v___x_1380_);
v___x_1382_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__6));
v___x_1383_ = lean_obj_once(&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__7, &l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__7_once, _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__7);
v___x_1384_ = lean_box(0);
v___x_1385_ = l_Lean_addMacroScope(v_quotContext_1360_, v___x_1384_, v_currMacroScope_1361_);
v___x_1386_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__10));
v___x_1387_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1370_);
lean_ctor_set(v___x_1387_, 1, v___x_1383_);
lean_ctor_set(v___x_1387_, 2, v___x_1385_);
lean_ctor_set(v___x_1387_, 3, v___x_1386_);
v___x_1388_ = l_Lean_Syntax_node1(v___x_1370_, v___x_1382_, v___x_1387_);
v___x_1389_ = l_Lean_Syntax_node2(v___x_1370_, v___x_1379_, v___x_1381_, v___x_1388_);
v___x_1390_ = lean_obj_once(&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__12, &l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__12_once, _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__12);
v___x_1391_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__15));
v___x_1392_ = l_Lean_addMacroScope(v_quotContext_1360_, v___x_1391_, v_currMacroScope_1361_);
v___x_1393_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__20));
v___x_1394_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1370_);
lean_ctor_set(v___x_1394_, 1, v___x_1390_);
lean_ctor_set(v___x_1394_, 2, v___x_1392_);
lean_ctor_set(v___x_1394_, 3, v___x_1393_);
v___x_1395_ = l_Lean_Syntax_node2(v___x_1370_, v___x_1377_, v___x_1364_, v___x_1366_);
v___x_1396_ = l_Lean_Syntax_node2(v___x_1370_, v___x_1371_, v___x_1394_, v___x_1395_);
v___x_1397_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__21));
v___x_1398_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1370_);
lean_ctor_set(v___x_1398_, 1, v___x_1397_);
v___x_1399_ = l_Lean_Syntax_node3(v___x_1370_, v___x_1378_, v___x_1389_, v___x_1396_, v___x_1398_);
v___x_1400_ = l_Lean_Syntax_node2(v___x_1370_, v___x_1377_, v___x_1368_, v___x_1399_);
v___x_1401_ = l_Lean_Syntax_node2(v___x_1370_, v___x_1371_, v___x_1376_, v___x_1400_);
v___x_1402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1401_);
lean_ctor_set(v___x_1402_, 1, v_a_1355_);
return v___x_1402_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___boxed(lean_object* v_x_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1(v_x_1403_, v_a_1404_, v_a_1405_);
lean_dec_ref(v_a_1404_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_unexpandDenote(lean_object* v_x_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_){
_start:
{
lean_object* v___x_1464_; uint8_t v___x_1465_; 
v___x_1464_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4));
lean_inc(v_x_1461_);
v___x_1465_ = l_Lean_Syntax_isOfKind(v_x_1461_, v___x_1464_);
if (v___x_1465_ == 0)
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
lean_dec(v_x_1461_);
v___x_1466_ = lean_box(0);
v___x_1467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1466_);
lean_ctor_set(v___x_1467_, 1, v_a_1463_);
return v___x_1467_;
}
else
{
lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; uint8_t v___x_1471_; 
v___x_1468_ = lean_unsigned_to_nat(1u);
v___x_1469_ = l_Lean_Syntax_getArg(v_x_1461_, v___x_1468_);
lean_dec(v_x_1461_);
v___x_1470_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1469_);
v___x_1471_ = l_Lean_Syntax_matchesNull(v___x_1469_, v___x_1470_);
if (v___x_1471_ == 0)
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
lean_dec(v___x_1469_);
v___x_1472_ = lean_box(0);
v___x_1473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1472_);
lean_ctor_set(v___x_1473_, 1, v_a_1463_);
return v___x_1473_;
}
else
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; uint8_t v___x_1477_; 
v___x_1474_ = lean_unsigned_to_nat(0u);
v___x_1475_ = l_Lean_Syntax_getArg(v___x_1469_, v___x_1474_);
v___x_1476_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__1));
lean_inc(v___x_1475_);
v___x_1477_ = l_Lean_Syntax_isOfKind(v___x_1475_, v___x_1476_);
if (v___x_1477_ == 0)
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1478_ = l_Lean_Syntax_getArg(v___x_1469_, v___x_1468_);
lean_dec(v___x_1469_);
v___x_1479_ = l_Lean_SourceInfo_fromRef(v_a_1462_, v___x_1477_);
v___x_1480_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1481_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1479_, 3);
v___x_1482_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1479_);
lean_ctor_set(v___x_1482_, 1, v___x_1481_);
v___x_1483_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1484_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1479_);
lean_ctor_set(v___x_1484_, 1, v___x_1483_);
v___x_1485_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1486_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1479_);
lean_ctor_set(v___x_1486_, 1, v___x_1485_);
v___x_1487_ = l_Lean_Syntax_node5(v___x_1479_, v___x_1480_, v___x_1482_, v___x_1475_, v___x_1484_, v___x_1478_, v___x_1486_);
v___x_1488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1487_);
lean_ctor_set(v___x_1488_, 1, v_a_1463_);
return v___x_1488_;
}
else
{
lean_object* v___x_1489_; uint8_t v___x_1490_; 
v___x_1489_ = l_Lean_Syntax_getArg(v___x_1475_, v___x_1468_);
v___x_1490_ = l_Lean_Syntax_matchesNull(v___x_1489_, v___x_1474_);
if (v___x_1490_ == 0)
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1491_ = l_Lean_Syntax_getArg(v___x_1469_, v___x_1468_);
lean_dec(v___x_1469_);
v___x_1492_ = l_Lean_SourceInfo_fromRef(v_a_1462_, v___x_1490_);
v___x_1493_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1494_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1492_, 3);
v___x_1495_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1492_);
lean_ctor_set(v___x_1495_, 1, v___x_1494_);
v___x_1496_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1497_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1492_);
lean_ctor_set(v___x_1497_, 1, v___x_1496_);
v___x_1498_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1499_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1492_);
lean_ctor_set(v___x_1499_, 1, v___x_1498_);
v___x_1500_ = l_Lean_Syntax_node5(v___x_1492_, v___x_1493_, v___x_1495_, v___x_1475_, v___x_1497_, v___x_1491_, v___x_1499_);
v___x_1501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1500_);
lean_ctor_set(v___x_1501_, 1, v_a_1463_);
return v___x_1501_;
}
else
{
lean_object* v___x_1502_; lean_object* v___x_1503_; uint8_t v___x_1504_; 
v___x_1502_ = l_Lean_Syntax_getArg(v___x_1475_, v___x_1470_);
v___x_1503_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__4));
lean_inc(v___x_1502_);
v___x_1504_ = l_Lean_Syntax_isOfKind(v___x_1502_, v___x_1503_);
if (v___x_1504_ == 0)
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
lean_dec(v___x_1502_);
v___x_1505_ = l_Lean_Syntax_getArg(v___x_1469_, v___x_1468_);
lean_dec(v___x_1469_);
v___x_1506_ = l_Lean_SourceInfo_fromRef(v_a_1462_, v___x_1504_);
v___x_1507_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1508_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1506_, 3);
v___x_1509_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1506_);
lean_ctor_set(v___x_1509_, 1, v___x_1508_);
v___x_1510_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1511_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1506_);
lean_ctor_set(v___x_1511_, 1, v___x_1510_);
v___x_1512_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1513_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1506_);
lean_ctor_set(v___x_1513_, 1, v___x_1512_);
v___x_1514_ = l_Lean_Syntax_node5(v___x_1506_, v___x_1507_, v___x_1509_, v___x_1475_, v___x_1511_, v___x_1505_, v___x_1513_);
v___x_1515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1514_);
lean_ctor_set(v___x_1515_, 1, v_a_1463_);
return v___x_1515_;
}
else
{
lean_object* v___x_1516_; lean_object* v___x_1517_; uint8_t v___x_1518_; 
v___x_1516_ = l_Lean_Syntax_getArg(v___x_1502_, v___x_1474_);
lean_dec(v___x_1502_);
v___x_1517_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_1516_);
v___x_1518_ = l_Lean_Syntax_matchesNull(v___x_1516_, v___x_1517_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
lean_dec(v___x_1516_);
v___x_1519_ = l_Lean_Syntax_getArg(v___x_1469_, v___x_1468_);
lean_dec(v___x_1469_);
v___x_1520_ = l_Lean_SourceInfo_fromRef(v_a_1462_, v___x_1518_);
v___x_1521_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1522_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1520_, 3);
v___x_1523_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1520_);
lean_ctor_set(v___x_1523_, 1, v___x_1522_);
v___x_1524_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1525_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1520_);
lean_ctor_set(v___x_1525_, 1, v___x_1524_);
v___x_1526_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1527_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1520_);
lean_ctor_set(v___x_1527_, 1, v___x_1526_);
v___x_1528_ = l_Lean_Syntax_node5(v___x_1520_, v___x_1521_, v___x_1523_, v___x_1475_, v___x_1525_, v___x_1519_, v___x_1527_);
v___x_1529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1528_);
lean_ctor_set(v___x_1529_, 1, v_a_1463_);
return v___x_1529_;
}
else
{
lean_object* v___x_1530_; lean_object* v___x_1531_; uint8_t v___x_1532_; 
v___x_1530_ = l_Lean_Syntax_getArg(v___x_1516_, v___x_1474_);
v___x_1531_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__6));
lean_inc(v___x_1530_);
v___x_1532_ = l_Lean_Syntax_isOfKind(v___x_1530_, v___x_1531_);
if (v___x_1532_ == 0)
{
lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
lean_dec(v___x_1530_);
lean_dec(v___x_1516_);
v___x_1533_ = l_Lean_Syntax_getArg(v___x_1469_, v___x_1468_);
lean_dec(v___x_1469_);
v___x_1534_ = l_Lean_SourceInfo_fromRef(v_a_1462_, v___x_1532_);
v___x_1535_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1536_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1534_, 3);
v___x_1537_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1534_);
lean_ctor_set(v___x_1537_, 1, v___x_1536_);
v___x_1538_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1539_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1534_);
lean_ctor_set(v___x_1539_, 1, v___x_1538_);
v___x_1540_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1541_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1534_);
lean_ctor_set(v___x_1541_, 1, v___x_1540_);
v___x_1542_ = l_Lean_Syntax_node5(v___x_1534_, v___x_1535_, v___x_1537_, v___x_1475_, v___x_1539_, v___x_1533_, v___x_1541_);
v___x_1543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1542_);
lean_ctor_set(v___x_1543_, 1, v_a_1463_);
return v___x_1543_;
}
else
{
lean_object* v___x_1544_; lean_object* v___x_1545_; uint8_t v___x_1546_; 
v___x_1544_ = l_Lean_Syntax_getArg(v___x_1530_, v___x_1474_);
v___x_1545_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__8));
lean_inc(v___x_1544_);
v___x_1546_ = l_Lean_Syntax_isOfKind(v___x_1544_, v___x_1545_);
if (v___x_1546_ == 0)
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
lean_dec(v___x_1544_);
lean_dec(v___x_1530_);
lean_dec(v___x_1516_);
v___x_1547_ = l_Lean_Syntax_getArg(v___x_1469_, v___x_1468_);
lean_dec(v___x_1469_);
v___x_1548_ = l_Lean_SourceInfo_fromRef(v_a_1462_, v___x_1546_);
v___x_1549_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1550_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1548_, 3);
v___x_1551_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1548_);
lean_ctor_set(v___x_1551_, 1, v___x_1550_);
v___x_1552_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1553_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1548_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
v___x_1554_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1555_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1548_);
lean_ctor_set(v___x_1555_, 1, v___x_1554_);
v___x_1556_ = l_Lean_Syntax_node5(v___x_1548_, v___x_1549_, v___x_1551_, v___x_1475_, v___x_1553_, v___x_1547_, v___x_1555_);
v___x_1557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1556_);
lean_ctor_set(v___x_1557_, 1, v_a_1463_);
return v___x_1557_;
}
else
{
lean_object* v___x_1558_; lean_object* v___x_1559_; uint8_t v___x_1560_; 
v___x_1558_ = l_Lean_Syntax_getArg(v___x_1544_, v___x_1474_);
v___x_1559_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__10));
v___x_1560_ = l_Lean_Syntax_matchesIdent(v___x_1558_, v___x_1559_);
lean_dec(v___x_1558_);
if (v___x_1560_ == 0)
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
lean_dec(v___x_1544_);
lean_dec(v___x_1530_);
lean_dec(v___x_1516_);
v___x_1561_ = l_Lean_Syntax_getArg(v___x_1469_, v___x_1468_);
lean_dec(v___x_1469_);
v___x_1562_ = l_Lean_SourceInfo_fromRef(v_a_1462_, v___x_1560_);
v___x_1563_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1564_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1562_, 3);
v___x_1565_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1562_);
lean_ctor_set(v___x_1565_, 1, v___x_1564_);
v___x_1566_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1567_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1562_);
lean_ctor_set(v___x_1567_, 1, v___x_1566_);
v___x_1568_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1569_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1562_);
lean_ctor_set(v___x_1569_, 1, v___x_1568_);
v___x_1570_ = l_Lean_Syntax_node5(v___x_1562_, v___x_1563_, v___x_1565_, v___x_1475_, v___x_1567_, v___x_1561_, v___x_1569_);
v___x_1571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1570_);
lean_ctor_set(v___x_1571_, 1, v_a_1463_);
return v___x_1571_;
}
else
{
lean_object* v___x_1572_; uint8_t v___x_1573_; 
v___x_1572_ = l_Lean_Syntax_getArg(v___x_1544_, v___x_1468_);
lean_dec(v___x_1544_);
v___x_1573_ = l_Lean_Syntax_matchesNull(v___x_1572_, v___x_1474_);
if (v___x_1573_ == 0)
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
lean_dec(v___x_1530_);
lean_dec(v___x_1516_);
v___x_1574_ = l_Lean_Syntax_getArg(v___x_1469_, v___x_1468_);
lean_dec(v___x_1469_);
v___x_1575_ = l_Lean_SourceInfo_fromRef(v_a_1462_, v___x_1573_);
v___x_1576_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1577_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1575_, 3);
v___x_1578_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1575_);
lean_ctor_set(v___x_1578_, 1, v___x_1577_);
v___x_1579_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1580_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1575_);
lean_ctor_set(v___x_1580_, 1, v___x_1579_);
v___x_1581_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1582_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1575_);
lean_ctor_set(v___x_1582_, 1, v___x_1581_);
v___x_1583_ = l_Lean_Syntax_node5(v___x_1575_, v___x_1576_, v___x_1578_, v___x_1475_, v___x_1580_, v___x_1574_, v___x_1582_);
v___x_1584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1583_);
lean_ctor_set(v___x_1584_, 1, v_a_1463_);
return v___x_1584_;
}
else
{
lean_object* v___x_1585_; lean_object* v___x_1586_; uint8_t v___x_1587_; 
v___x_1585_ = l_Lean_Syntax_getArg(v___x_1530_, v___x_1468_);
lean_dec(v___x_1530_);
v___x_1586_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_1585_);
v___x_1587_ = l_Lean_Syntax_matchesNull(v___x_1585_, v___x_1586_);
if (v___x_1587_ == 0)
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
lean_dec(v___x_1585_);
lean_dec(v___x_1516_);
v___x_1588_ = l_Lean_Syntax_getArg(v___x_1469_, v___x_1468_);
lean_dec(v___x_1469_);
v___x_1589_ = l_Lean_SourceInfo_fromRef(v_a_1462_, v___x_1587_);
v___x_1590_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1591_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1589_, 3);
v___x_1592_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1589_);
lean_ctor_set(v___x_1592_, 1, v___x_1591_);
v___x_1593_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1594_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1589_);
lean_ctor_set(v___x_1594_, 1, v___x_1593_);
v___x_1595_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1596_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1589_);
lean_ctor_set(v___x_1596_, 1, v___x_1595_);
v___x_1597_ = l_Lean_Syntax_node5(v___x_1589_, v___x_1590_, v___x_1592_, v___x_1475_, v___x_1594_, v___x_1588_, v___x_1596_);
v___x_1598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1597_);
lean_ctor_set(v___x_1598_, 1, v_a_1463_);
return v___x_1598_;
}
else
{
lean_object* v___x_1599_; uint8_t v___x_1600_; 
v___x_1599_ = l_Lean_Syntax_getArg(v___x_1585_, v___x_1474_);
v___x_1600_ = l_Lean_Syntax_matchesNull(v___x_1599_, v___x_1474_);
if (v___x_1600_ == 0)
{
lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
lean_dec(v___x_1585_);
lean_dec(v___x_1516_);
v___x_1601_ = l_Lean_Syntax_getArg(v___x_1469_, v___x_1468_);
lean_dec(v___x_1469_);
v___x_1602_ = l_Lean_SourceInfo_fromRef(v_a_1462_, v___x_1600_);
v___x_1603_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1604_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1602_, 3);
v___x_1605_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1602_);
lean_ctor_set(v___x_1605_, 1, v___x_1604_);
v___x_1606_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1607_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1602_);
lean_ctor_set(v___x_1607_, 1, v___x_1606_);
v___x_1608_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1609_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1602_);
lean_ctor_set(v___x_1609_, 1, v___x_1608_);
v___x_1610_ = l_Lean_Syntax_node5(v___x_1602_, v___x_1603_, v___x_1605_, v___x_1475_, v___x_1607_, v___x_1601_, v___x_1609_);
v___x_1611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1610_);
lean_ctor_set(v___x_1611_, 1, v_a_1463_);
return v___x_1611_;
}
else
{
lean_object* v___x_1612_; uint8_t v___x_1613_; 
v___x_1612_ = l_Lean_Syntax_getArg(v___x_1585_, v___x_1468_);
v___x_1613_ = l_Lean_Syntax_matchesNull(v___x_1612_, v___x_1474_);
if (v___x_1613_ == 0)
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
lean_dec(v___x_1585_);
lean_dec(v___x_1516_);
v___x_1614_ = l_Lean_Syntax_getArg(v___x_1469_, v___x_1468_);
lean_dec(v___x_1469_);
v___x_1615_ = l_Lean_SourceInfo_fromRef(v_a_1462_, v___x_1613_);
v___x_1616_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1617_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1615_, 3);
v___x_1618_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1615_);
lean_ctor_set(v___x_1618_, 1, v___x_1617_);
v___x_1619_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1620_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1615_);
lean_ctor_set(v___x_1620_, 1, v___x_1619_);
v___x_1621_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1622_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1615_);
lean_ctor_set(v___x_1622_, 1, v___x_1621_);
v___x_1623_ = l_Lean_Syntax_node5(v___x_1615_, v___x_1616_, v___x_1618_, v___x_1475_, v___x_1620_, v___x_1614_, v___x_1622_);
v___x_1624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1623_);
lean_ctor_set(v___x_1624_, 1, v_a_1463_);
return v___x_1624_;
}
else
{
lean_object* v___x_1625_; lean_object* v___x_1626_; uint8_t v___x_1627_; 
v___x_1625_ = l_Lean_Syntax_getArg(v___x_1585_, v___x_1470_);
lean_dec(v___x_1585_);
v___x_1626_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__12));
lean_inc(v___x_1625_);
v___x_1627_ = l_Lean_Syntax_isOfKind(v___x_1625_, v___x_1626_);
if (v___x_1627_ == 0)
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
lean_dec(v___x_1625_);
lean_dec(v___x_1516_);
v___x_1628_ = l_Lean_Syntax_getArg(v___x_1469_, v___x_1468_);
lean_dec(v___x_1469_);
v___x_1629_ = l_Lean_SourceInfo_fromRef(v_a_1462_, v___x_1627_);
v___x_1630_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1631_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1629_, 3);
v___x_1632_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1629_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
v___x_1633_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1634_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1629_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
v___x_1635_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1636_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1629_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
v___x_1637_ = l_Lean_Syntax_node5(v___x_1629_, v___x_1630_, v___x_1632_, v___x_1475_, v___x_1634_, v___x_1628_, v___x_1636_);
v___x_1638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1637_);
lean_ctor_set(v___x_1638_, 1, v_a_1463_);
return v___x_1638_;
}
else
{
lean_object* v___x_1639_; uint8_t v___x_1640_; 
v___x_1639_ = l_Lean_Syntax_getArg(v___x_1625_, v___x_1468_);
v___x_1640_ = l_Lean_Syntax_matchesNull(v___x_1639_, v___x_1474_);
if (v___x_1640_ == 0)
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
lean_dec(v___x_1625_);
lean_dec(v___x_1516_);
v___x_1641_ = l_Lean_Syntax_getArg(v___x_1469_, v___x_1468_);
lean_dec(v___x_1469_);
v___x_1642_ = l_Lean_SourceInfo_fromRef(v_a_1462_, v___x_1640_);
v___x_1643_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1644_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1642_, 3);
v___x_1645_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1642_);
lean_ctor_set(v___x_1645_, 1, v___x_1644_);
v___x_1646_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1647_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1642_);
lean_ctor_set(v___x_1647_, 1, v___x_1646_);
v___x_1648_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1649_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1642_);
lean_ctor_set(v___x_1649_, 1, v___x_1648_);
v___x_1650_ = l_Lean_Syntax_node5(v___x_1642_, v___x_1643_, v___x_1645_, v___x_1475_, v___x_1647_, v___x_1641_, v___x_1649_);
v___x_1651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1650_);
lean_ctor_set(v___x_1651_, 1, v_a_1463_);
return v___x_1651_;
}
else
{
lean_object* v___x_1652_; uint8_t v___x_1653_; 
v___x_1652_ = l_Lean_Syntax_getArg(v___x_1516_, v___x_1470_);
lean_inc(v___x_1652_);
v___x_1653_ = l_Lean_Syntax_isOfKind(v___x_1652_, v___x_1531_);
if (v___x_1653_ == 0)
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
lean_dec(v___x_1652_);
lean_dec(v___x_1625_);
lean_dec(v___x_1516_);
v___x_1654_ = l_Lean_Syntax_getArg(v___x_1469_, v___x_1468_);
lean_dec(v___x_1469_);
v___x_1655_ = l_Lean_SourceInfo_fromRef(v_a_1462_, v___x_1653_);
v___x_1656_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1657_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1655_, 3);
v___x_1658_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1655_);
lean_ctor_set(v___x_1658_, 1, v___x_1657_);
v___x_1659_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1660_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1655_);
lean_ctor_set(v___x_1660_, 1, v___x_1659_);
v___x_1661_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1662_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1655_);
lean_ctor_set(v___x_1662_, 1, v___x_1661_);
v___x_1663_ = l_Lean_Syntax_node5(v___x_1655_, v___x_1656_, v___x_1658_, v___x_1475_, v___x_1660_, v___x_1654_, v___x_1662_);
v___x_1664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1663_);
lean_ctor_set(v___x_1664_, 1, v_a_1463_);
return v___x_1664_;
}
else
{
lean_object* v___x_1665_; uint8_t v___x_1666_; 
v___x_1665_ = l_Lean_Syntax_getArg(v___x_1652_, v___x_1474_);
lean_inc(v___x_1665_);
v___x_1666_ = l_Lean_Syntax_isOfKind(v___x_1665_, v___x_1545_);
if (v___x_1666_ == 0)
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
lean_dec(v___x_1665_);
lean_dec(v___x_1652_);
lean_dec(v___x_1625_);
lean_dec(v___x_1516_);
v___x_1667_ = l_Lean_Syntax_getArg(v___x_1469_, v___x_1468_);
lean_dec(v___x_1469_);
v___x_1668_ = l_Lean_SourceInfo_fromRef(v_a_1462_, v___x_1666_);
v___x_1669_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1670_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1668_, 3);
v___x_1671_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1668_);
lean_ctor_set(v___x_1671_, 1, v___x_1670_);
v___x_1672_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1673_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1668_);
lean_ctor_set(v___x_1673_, 1, v___x_1672_);
v___x_1674_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1675_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1668_);
lean_ctor_set(v___x_1675_, 1, v___x_1674_);
v___x_1676_ = l_Lean_Syntax_node5(v___x_1668_, v___x_1669_, v___x_1671_, v___x_1475_, v___x_1673_, v___x_1667_, v___x_1675_);
v___x_1677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1676_);
lean_ctor_set(v___x_1677_, 1, v_a_1463_);
return v___x_1677_;
}
else
{
lean_object* v___x_1678_; lean_object* v___x_1679_; uint8_t v___x_1680_; 
v___x_1678_ = l_Lean_Syntax_getArg(v___x_1665_, v___x_1474_);
v___x_1679_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__14));
v___x_1680_ = l_Lean_Syntax_matchesIdent(v___x_1678_, v___x_1679_);
lean_dec(v___x_1678_);
if (v___x_1680_ == 0)
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
lean_dec(v___x_1665_);
lean_dec(v___x_1652_);
lean_dec(v___x_1625_);
lean_dec(v___x_1516_);
v___x_1681_ = l_Lean_Syntax_getArg(v___x_1469_, v___x_1468_);
lean_dec(v___x_1469_);
v___x_1682_ = l_Lean_SourceInfo_fromRef(v_a_1462_, v___x_1680_);
v___x_1683_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1684_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1682_, 3);
v___x_1685_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1682_);
lean_ctor_set(v___x_1685_, 1, v___x_1684_);
v___x_1686_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1687_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1682_);
lean_ctor_set(v___x_1687_, 1, v___x_1686_);
v___x_1688_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1689_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1682_);
lean_ctor_set(v___x_1689_, 1, v___x_1688_);
v___x_1690_ = l_Lean_Syntax_node5(v___x_1682_, v___x_1683_, v___x_1685_, v___x_1475_, v___x_1687_, v___x_1681_, v___x_1689_);
v___x_1691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1690_);
lean_ctor_set(v___x_1691_, 1, v_a_1463_);
return v___x_1691_;
}
else
{
lean_object* v___x_1692_; uint8_t v___x_1693_; 
v___x_1692_ = l_Lean_Syntax_getArg(v___x_1665_, v___x_1468_);
lean_dec(v___x_1665_);
v___x_1693_ = l_Lean_Syntax_matchesNull(v___x_1692_, v___x_1474_);
if (v___x_1693_ == 0)
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
lean_dec(v___x_1652_);
lean_dec(v___x_1625_);
lean_dec(v___x_1516_);
v___x_1694_ = l_Lean_Syntax_getArg(v___x_1469_, v___x_1468_);
lean_dec(v___x_1469_);
v___x_1695_ = l_Lean_SourceInfo_fromRef(v_a_1462_, v___x_1693_);
v___x_1696_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1697_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1695_, 3);
v___x_1698_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1695_);
lean_ctor_set(v___x_1698_, 1, v___x_1697_);
v___x_1699_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1700_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1695_);
lean_ctor_set(v___x_1700_, 1, v___x_1699_);
v___x_1701_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1702_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1695_);
lean_ctor_set(v___x_1702_, 1, v___x_1701_);
v___x_1703_ = l_Lean_Syntax_node5(v___x_1695_, v___x_1696_, v___x_1698_, v___x_1475_, v___x_1700_, v___x_1694_, v___x_1702_);
v___x_1704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1703_);
lean_ctor_set(v___x_1704_, 1, v_a_1463_);
return v___x_1704_;
}
else
{
lean_object* v___x_1705_; uint8_t v___x_1706_; 
v___x_1705_ = l_Lean_Syntax_getArg(v___x_1652_, v___x_1468_);
lean_dec(v___x_1652_);
lean_inc(v___x_1705_);
v___x_1706_ = l_Lean_Syntax_matchesNull(v___x_1705_, v___x_1586_);
if (v___x_1706_ == 0)
{
lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
lean_dec(v___x_1705_);
lean_dec(v___x_1625_);
lean_dec(v___x_1516_);
v___x_1707_ = l_Lean_Syntax_getArg(v___x_1469_, v___x_1468_);
lean_dec(v___x_1469_);
v___x_1708_ = l_Lean_SourceInfo_fromRef(v_a_1462_, v___x_1706_);
v___x_1709_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1710_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1708_, 3);
v___x_1711_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1708_);
lean_ctor_set(v___x_1711_, 1, v___x_1710_);
v___x_1712_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1713_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1708_);
lean_ctor_set(v___x_1713_, 1, v___x_1712_);
v___x_1714_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1715_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1708_);
lean_ctor_set(v___x_1715_, 1, v___x_1714_);
v___x_1716_ = l_Lean_Syntax_node5(v___x_1708_, v___x_1709_, v___x_1711_, v___x_1475_, v___x_1713_, v___x_1707_, v___x_1715_);
v___x_1717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1716_);
lean_ctor_set(v___x_1717_, 1, v_a_1463_);
return v___x_1717_;
}
else
{
lean_object* v___x_1718_; uint8_t v___x_1719_; 
v___x_1718_ = l_Lean_Syntax_getArg(v___x_1705_, v___x_1474_);
v___x_1719_ = l_Lean_Syntax_matchesNull(v___x_1718_, v___x_1474_);
if (v___x_1719_ == 0)
{
lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
lean_dec(v___x_1705_);
lean_dec(v___x_1625_);
lean_dec(v___x_1516_);
v___x_1720_ = l_Lean_Syntax_getArg(v___x_1469_, v___x_1468_);
lean_dec(v___x_1469_);
v___x_1721_ = l_Lean_SourceInfo_fromRef(v_a_1462_, v___x_1719_);
v___x_1722_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1723_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1721_, 3);
v___x_1724_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1721_);
lean_ctor_set(v___x_1724_, 1, v___x_1723_);
v___x_1725_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1726_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1721_);
lean_ctor_set(v___x_1726_, 1, v___x_1725_);
v___x_1727_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1728_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1721_);
lean_ctor_set(v___x_1728_, 1, v___x_1727_);
v___x_1729_ = l_Lean_Syntax_node5(v___x_1721_, v___x_1722_, v___x_1724_, v___x_1475_, v___x_1726_, v___x_1720_, v___x_1728_);
v___x_1730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1729_);
lean_ctor_set(v___x_1730_, 1, v_a_1463_);
return v___x_1730_;
}
else
{
lean_object* v___x_1731_; uint8_t v___x_1732_; 
v___x_1731_ = l_Lean_Syntax_getArg(v___x_1705_, v___x_1468_);
v___x_1732_ = l_Lean_Syntax_matchesNull(v___x_1731_, v___x_1474_);
if (v___x_1732_ == 0)
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
lean_dec(v___x_1705_);
lean_dec(v___x_1625_);
lean_dec(v___x_1516_);
v___x_1733_ = l_Lean_Syntax_getArg(v___x_1469_, v___x_1468_);
lean_dec(v___x_1469_);
v___x_1734_ = l_Lean_SourceInfo_fromRef(v_a_1462_, v___x_1732_);
v___x_1735_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1736_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1734_, 3);
v___x_1737_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1734_);
lean_ctor_set(v___x_1737_, 1, v___x_1736_);
v___x_1738_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1739_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1734_);
lean_ctor_set(v___x_1739_, 1, v___x_1738_);
v___x_1740_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1741_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1734_);
lean_ctor_set(v___x_1741_, 1, v___x_1740_);
v___x_1742_ = l_Lean_Syntax_node5(v___x_1734_, v___x_1735_, v___x_1737_, v___x_1475_, v___x_1739_, v___x_1733_, v___x_1741_);
v___x_1743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1742_);
lean_ctor_set(v___x_1743_, 1, v_a_1463_);
return v___x_1743_;
}
else
{
lean_object* v___x_1744_; uint8_t v___x_1745_; 
v___x_1744_ = l_Lean_Syntax_getArg(v___x_1705_, v___x_1470_);
lean_dec(v___x_1705_);
lean_inc(v___x_1744_);
v___x_1745_ = l_Lean_Syntax_isOfKind(v___x_1744_, v___x_1626_);
if (v___x_1745_ == 0)
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
lean_dec(v___x_1744_);
lean_dec(v___x_1625_);
lean_dec(v___x_1516_);
v___x_1746_ = l_Lean_Syntax_getArg(v___x_1469_, v___x_1468_);
lean_dec(v___x_1469_);
v___x_1747_ = l_Lean_SourceInfo_fromRef(v_a_1462_, v___x_1745_);
v___x_1748_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1749_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1747_, 3);
v___x_1750_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1747_);
lean_ctor_set(v___x_1750_, 1, v___x_1749_);
v___x_1751_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1752_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1747_);
lean_ctor_set(v___x_1752_, 1, v___x_1751_);
v___x_1753_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1754_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1747_);
lean_ctor_set(v___x_1754_, 1, v___x_1753_);
v___x_1755_ = l_Lean_Syntax_node5(v___x_1747_, v___x_1748_, v___x_1750_, v___x_1475_, v___x_1752_, v___x_1746_, v___x_1754_);
v___x_1756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1755_);
lean_ctor_set(v___x_1756_, 1, v_a_1463_);
return v___x_1756_;
}
else
{
lean_object* v___x_1757_; uint8_t v___x_1758_; 
v___x_1757_ = l_Lean_Syntax_getArg(v___x_1744_, v___x_1468_);
v___x_1758_ = l_Lean_Syntax_matchesNull(v___x_1757_, v___x_1474_);
if (v___x_1758_ == 0)
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
lean_dec(v___x_1744_);
lean_dec(v___x_1625_);
lean_dec(v___x_1516_);
v___x_1759_ = l_Lean_Syntax_getArg(v___x_1469_, v___x_1468_);
lean_dec(v___x_1469_);
v___x_1760_ = l_Lean_SourceInfo_fromRef(v_a_1462_, v___x_1758_);
v___x_1761_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1762_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1760_, 3);
v___x_1763_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1760_);
lean_ctor_set(v___x_1763_, 1, v___x_1762_);
v___x_1764_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1765_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1760_);
lean_ctor_set(v___x_1765_, 1, v___x_1764_);
v___x_1766_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1767_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1760_);
lean_ctor_set(v___x_1767_, 1, v___x_1766_);
v___x_1768_ = l_Lean_Syntax_node5(v___x_1760_, v___x_1761_, v___x_1763_, v___x_1475_, v___x_1765_, v___x_1759_, v___x_1767_);
v___x_1769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1768_);
lean_ctor_set(v___x_1769_, 1, v_a_1463_);
return v___x_1769_;
}
else
{
lean_object* v___x_1770_; lean_object* v___x_1771_; uint8_t v___x_1772_; 
v___x_1770_ = lean_unsigned_to_nat(4u);
v___x_1771_ = l_Lean_Syntax_getArg(v___x_1516_, v___x_1770_);
lean_dec(v___x_1516_);
lean_inc(v___x_1771_);
v___x_1772_ = l_Lean_Syntax_isOfKind(v___x_1771_, v___x_1531_);
if (v___x_1772_ == 0)
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
lean_dec(v___x_1771_);
lean_dec(v___x_1744_);
lean_dec(v___x_1625_);
v___x_1773_ = l_Lean_Syntax_getArg(v___x_1469_, v___x_1468_);
lean_dec(v___x_1469_);
v___x_1774_ = l_Lean_SourceInfo_fromRef(v_a_1462_, v___x_1772_);
v___x_1775_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1776_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1774_, 3);
v___x_1777_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1774_);
lean_ctor_set(v___x_1777_, 1, v___x_1776_);
v___x_1778_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1779_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1774_);
lean_ctor_set(v___x_1779_, 1, v___x_1778_);
v___x_1780_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1781_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1774_);
lean_ctor_set(v___x_1781_, 1, v___x_1780_);
v___x_1782_ = l_Lean_Syntax_node5(v___x_1774_, v___x_1775_, v___x_1777_, v___x_1475_, v___x_1779_, v___x_1773_, v___x_1781_);
v___x_1783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1782_);
lean_ctor_set(v___x_1783_, 1, v_a_1463_);
return v___x_1783_;
}
else
{
lean_object* v___x_1784_; uint8_t v___x_1785_; 
v___x_1784_ = l_Lean_Syntax_getArg(v___x_1771_, v___x_1474_);
lean_inc(v___x_1784_);
v___x_1785_ = l_Lean_Syntax_isOfKind(v___x_1784_, v___x_1545_);
if (v___x_1785_ == 0)
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
lean_dec(v___x_1784_);
lean_dec(v___x_1771_);
lean_dec(v___x_1744_);
lean_dec(v___x_1625_);
v___x_1786_ = l_Lean_Syntax_getArg(v___x_1469_, v___x_1468_);
lean_dec(v___x_1469_);
v___x_1787_ = l_Lean_SourceInfo_fromRef(v_a_1462_, v___x_1785_);
v___x_1788_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1789_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1787_, 3);
v___x_1790_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1787_);
lean_ctor_set(v___x_1790_, 1, v___x_1789_);
v___x_1791_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1792_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1787_);
lean_ctor_set(v___x_1792_, 1, v___x_1791_);
v___x_1793_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1794_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1787_);
lean_ctor_set(v___x_1794_, 1, v___x_1793_);
v___x_1795_ = l_Lean_Syntax_node5(v___x_1787_, v___x_1788_, v___x_1790_, v___x_1475_, v___x_1792_, v___x_1786_, v___x_1794_);
v___x_1796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1795_);
lean_ctor_set(v___x_1796_, 1, v_a_1463_);
return v___x_1796_;
}
else
{
lean_object* v___x_1797_; lean_object* v___x_1798_; uint8_t v___x_1799_; 
v___x_1797_ = l_Lean_Syntax_getArg(v___x_1784_, v___x_1474_);
v___x_1798_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__16));
v___x_1799_ = l_Lean_Syntax_matchesIdent(v___x_1797_, v___x_1798_);
lean_dec(v___x_1797_);
if (v___x_1799_ == 0)
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
lean_dec(v___x_1784_);
lean_dec(v___x_1771_);
lean_dec(v___x_1744_);
lean_dec(v___x_1625_);
v___x_1800_ = l_Lean_Syntax_getArg(v___x_1469_, v___x_1468_);
lean_dec(v___x_1469_);
v___x_1801_ = l_Lean_SourceInfo_fromRef(v_a_1462_, v___x_1799_);
v___x_1802_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1803_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1801_, 3);
v___x_1804_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1801_);
lean_ctor_set(v___x_1804_, 1, v___x_1803_);
v___x_1805_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1806_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1801_);
lean_ctor_set(v___x_1806_, 1, v___x_1805_);
v___x_1807_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1808_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1801_);
lean_ctor_set(v___x_1808_, 1, v___x_1807_);
v___x_1809_ = l_Lean_Syntax_node5(v___x_1801_, v___x_1802_, v___x_1804_, v___x_1475_, v___x_1806_, v___x_1800_, v___x_1808_);
v___x_1810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1809_);
lean_ctor_set(v___x_1810_, 1, v_a_1463_);
return v___x_1810_;
}
else
{
lean_object* v___x_1811_; uint8_t v___x_1812_; 
v___x_1811_ = l_Lean_Syntax_getArg(v___x_1784_, v___x_1468_);
lean_dec(v___x_1784_);
v___x_1812_ = l_Lean_Syntax_matchesNull(v___x_1811_, v___x_1474_);
if (v___x_1812_ == 0)
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
lean_dec(v___x_1771_);
lean_dec(v___x_1744_);
lean_dec(v___x_1625_);
v___x_1813_ = l_Lean_Syntax_getArg(v___x_1469_, v___x_1468_);
lean_dec(v___x_1469_);
v___x_1814_ = l_Lean_SourceInfo_fromRef(v_a_1462_, v___x_1812_);
v___x_1815_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1816_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1814_, 3);
v___x_1817_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1814_);
lean_ctor_set(v___x_1817_, 1, v___x_1816_);
v___x_1818_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1819_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1814_);
lean_ctor_set(v___x_1819_, 1, v___x_1818_);
v___x_1820_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1821_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1814_);
lean_ctor_set(v___x_1821_, 1, v___x_1820_);
v___x_1822_ = l_Lean_Syntax_node5(v___x_1814_, v___x_1815_, v___x_1817_, v___x_1475_, v___x_1819_, v___x_1813_, v___x_1821_);
v___x_1823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
lean_ctor_set(v___x_1823_, 1, v_a_1463_);
return v___x_1823_;
}
else
{
lean_object* v___x_1824_; uint8_t v___x_1825_; 
v___x_1824_ = l_Lean_Syntax_getArg(v___x_1771_, v___x_1468_);
lean_dec(v___x_1771_);
lean_inc(v___x_1824_);
v___x_1825_ = l_Lean_Syntax_matchesNull(v___x_1824_, v___x_1586_);
if (v___x_1825_ == 0)
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
lean_dec(v___x_1824_);
lean_dec(v___x_1744_);
lean_dec(v___x_1625_);
v___x_1826_ = l_Lean_Syntax_getArg(v___x_1469_, v___x_1468_);
lean_dec(v___x_1469_);
v___x_1827_ = l_Lean_SourceInfo_fromRef(v_a_1462_, v___x_1825_);
v___x_1828_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1829_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1827_, 3);
v___x_1830_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1827_);
lean_ctor_set(v___x_1830_, 1, v___x_1829_);
v___x_1831_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1832_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1827_);
lean_ctor_set(v___x_1832_, 1, v___x_1831_);
v___x_1833_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1834_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1827_);
lean_ctor_set(v___x_1834_, 1, v___x_1833_);
v___x_1835_ = l_Lean_Syntax_node5(v___x_1827_, v___x_1828_, v___x_1830_, v___x_1475_, v___x_1832_, v___x_1826_, v___x_1834_);
v___x_1836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1835_);
lean_ctor_set(v___x_1836_, 1, v_a_1463_);
return v___x_1836_;
}
else
{
lean_object* v___x_1837_; uint8_t v___x_1838_; 
v___x_1837_ = l_Lean_Syntax_getArg(v___x_1824_, v___x_1474_);
v___x_1838_ = l_Lean_Syntax_matchesNull(v___x_1837_, v___x_1474_);
if (v___x_1838_ == 0)
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
lean_dec(v___x_1824_);
lean_dec(v___x_1744_);
lean_dec(v___x_1625_);
v___x_1839_ = l_Lean_Syntax_getArg(v___x_1469_, v___x_1468_);
lean_dec(v___x_1469_);
v___x_1840_ = l_Lean_SourceInfo_fromRef(v_a_1462_, v___x_1838_);
v___x_1841_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1842_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1840_, 3);
v___x_1843_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1840_);
lean_ctor_set(v___x_1843_, 1, v___x_1842_);
v___x_1844_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1845_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1840_);
lean_ctor_set(v___x_1845_, 1, v___x_1844_);
v___x_1846_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1847_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1840_);
lean_ctor_set(v___x_1847_, 1, v___x_1846_);
v___x_1848_ = l_Lean_Syntax_node5(v___x_1840_, v___x_1841_, v___x_1843_, v___x_1475_, v___x_1845_, v___x_1839_, v___x_1847_);
v___x_1849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1848_);
lean_ctor_set(v___x_1849_, 1, v_a_1463_);
return v___x_1849_;
}
else
{
lean_object* v___x_1850_; uint8_t v___x_1851_; 
v___x_1850_ = l_Lean_Syntax_getArg(v___x_1824_, v___x_1468_);
v___x_1851_ = l_Lean_Syntax_matchesNull(v___x_1850_, v___x_1474_);
if (v___x_1851_ == 0)
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
lean_dec(v___x_1824_);
lean_dec(v___x_1744_);
lean_dec(v___x_1625_);
v___x_1852_ = l_Lean_Syntax_getArg(v___x_1469_, v___x_1468_);
lean_dec(v___x_1469_);
v___x_1853_ = l_Lean_SourceInfo_fromRef(v_a_1462_, v___x_1851_);
v___x_1854_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1855_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1853_, 3);
v___x_1856_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1853_);
lean_ctor_set(v___x_1856_, 1, v___x_1855_);
v___x_1857_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1858_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1853_);
lean_ctor_set(v___x_1858_, 1, v___x_1857_);
v___x_1859_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1860_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1853_);
lean_ctor_set(v___x_1860_, 1, v___x_1859_);
v___x_1861_ = l_Lean_Syntax_node5(v___x_1853_, v___x_1854_, v___x_1856_, v___x_1475_, v___x_1858_, v___x_1852_, v___x_1860_);
v___x_1862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1861_);
lean_ctor_set(v___x_1862_, 1, v_a_1463_);
return v___x_1862_;
}
else
{
lean_object* v___x_1863_; uint8_t v___x_1864_; 
v___x_1863_ = l_Lean_Syntax_getArg(v___x_1824_, v___x_1470_);
lean_dec(v___x_1824_);
lean_inc(v___x_1863_);
v___x_1864_ = l_Lean_Syntax_isOfKind(v___x_1863_, v___x_1626_);
if (v___x_1864_ == 0)
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
lean_dec(v___x_1863_);
lean_dec(v___x_1744_);
lean_dec(v___x_1625_);
v___x_1865_ = l_Lean_Syntax_getArg(v___x_1469_, v___x_1468_);
lean_dec(v___x_1469_);
v___x_1866_ = l_Lean_SourceInfo_fromRef(v_a_1462_, v___x_1864_);
v___x_1867_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1868_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1866_, 3);
v___x_1869_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1866_);
lean_ctor_set(v___x_1869_, 1, v___x_1868_);
v___x_1870_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1871_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1866_);
lean_ctor_set(v___x_1871_, 1, v___x_1870_);
v___x_1872_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1873_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1866_);
lean_ctor_set(v___x_1873_, 1, v___x_1872_);
v___x_1874_ = l_Lean_Syntax_node5(v___x_1866_, v___x_1867_, v___x_1869_, v___x_1475_, v___x_1871_, v___x_1865_, v___x_1873_);
v___x_1875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
lean_ctor_set(v___x_1875_, 1, v_a_1463_);
return v___x_1875_;
}
else
{
lean_object* v___x_1876_; uint8_t v___x_1877_; 
v___x_1876_ = l_Lean_Syntax_getArg(v___x_1863_, v___x_1468_);
v___x_1877_ = l_Lean_Syntax_matchesNull(v___x_1876_, v___x_1474_);
if (v___x_1877_ == 0)
{
lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
lean_dec(v___x_1863_);
lean_dec(v___x_1744_);
lean_dec(v___x_1625_);
v___x_1878_ = l_Lean_Syntax_getArg(v___x_1469_, v___x_1468_);
lean_dec(v___x_1469_);
v___x_1879_ = l_Lean_SourceInfo_fromRef(v_a_1462_, v___x_1877_);
v___x_1880_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1881_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1879_, 3);
v___x_1882_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1879_);
lean_ctor_set(v___x_1882_, 1, v___x_1881_);
v___x_1883_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1884_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1879_);
lean_ctor_set(v___x_1884_, 1, v___x_1883_);
v___x_1885_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1886_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1879_);
lean_ctor_set(v___x_1886_, 1, v___x_1885_);
v___x_1887_ = l_Lean_Syntax_node5(v___x_1879_, v___x_1880_, v___x_1882_, v___x_1475_, v___x_1884_, v___x_1878_, v___x_1886_);
v___x_1888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1887_);
lean_ctor_set(v___x_1888_, 1, v_a_1463_);
return v___x_1888_;
}
else
{
lean_object* v___x_1889_; lean_object* v___x_1890_; uint8_t v___x_1891_; 
v___x_1889_ = l_Lean_Syntax_getArg(v___x_1475_, v___x_1586_);
v___x_1890_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__18));
lean_inc(v___x_1889_);
v___x_1891_ = l_Lean_Syntax_isOfKind(v___x_1889_, v___x_1890_);
if (v___x_1891_ == 0)
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
lean_dec(v___x_1889_);
lean_dec(v___x_1863_);
lean_dec(v___x_1744_);
lean_dec(v___x_1625_);
v___x_1892_ = l_Lean_Syntax_getArg(v___x_1469_, v___x_1468_);
lean_dec(v___x_1469_);
v___x_1893_ = l_Lean_SourceInfo_fromRef(v_a_1462_, v___x_1891_);
v___x_1894_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1895_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1893_, 3);
v___x_1896_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1893_);
lean_ctor_set(v___x_1896_, 1, v___x_1895_);
v___x_1897_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1898_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1893_);
lean_ctor_set(v___x_1898_, 1, v___x_1897_);
v___x_1899_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1900_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1893_);
lean_ctor_set(v___x_1900_, 1, v___x_1899_);
v___x_1901_ = l_Lean_Syntax_node5(v___x_1893_, v___x_1894_, v___x_1896_, v___x_1475_, v___x_1898_, v___x_1892_, v___x_1900_);
v___x_1902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1901_);
lean_ctor_set(v___x_1902_, 1, v_a_1463_);
return v___x_1902_;
}
else
{
lean_object* v___x_1903_; uint8_t v___x_1904_; 
v___x_1903_ = l_Lean_Syntax_getArg(v___x_1889_, v___x_1474_);
lean_dec(v___x_1889_);
v___x_1904_ = l_Lean_Syntax_matchesNull(v___x_1903_, v___x_1474_);
if (v___x_1904_ == 0)
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
lean_dec(v___x_1863_);
lean_dec(v___x_1744_);
lean_dec(v___x_1625_);
v___x_1905_ = l_Lean_Syntax_getArg(v___x_1469_, v___x_1468_);
lean_dec(v___x_1469_);
v___x_1906_ = l_Lean_SourceInfo_fromRef(v_a_1462_, v___x_1904_);
v___x_1907_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1908_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1906_, 3);
v___x_1909_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1906_);
lean_ctor_set(v___x_1909_, 1, v___x_1908_);
v___x_1910_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1911_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1906_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
v___x_1912_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1913_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1906_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
v___x_1914_ = l_Lean_Syntax_node5(v___x_1906_, v___x_1907_, v___x_1909_, v___x_1475_, v___x_1911_, v___x_1905_, v___x_1913_);
v___x_1915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1914_);
lean_ctor_set(v___x_1915_, 1, v_a_1463_);
return v___x_1915_;
}
else
{
lean_object* v___x_1916_; uint8_t v___x_1917_; 
v___x_1916_ = l_Lean_Syntax_getArg(v___x_1475_, v___x_1770_);
v___x_1917_ = l_Lean_Syntax_matchesNull(v___x_1916_, v___x_1474_);
if (v___x_1917_ == 0)
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
lean_dec(v___x_1863_);
lean_dec(v___x_1744_);
lean_dec(v___x_1625_);
v___x_1918_ = l_Lean_Syntax_getArg(v___x_1469_, v___x_1468_);
lean_dec(v___x_1469_);
v___x_1919_ = l_Lean_SourceInfo_fromRef(v_a_1462_, v___x_1917_);
v___x_1920_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1921_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1919_, 3);
v___x_1922_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1919_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
v___x_1923_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1924_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1919_);
lean_ctor_set(v___x_1924_, 1, v___x_1923_);
v___x_1925_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1926_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1919_);
lean_ctor_set(v___x_1926_, 1, v___x_1925_);
v___x_1927_ = l_Lean_Syntax_node5(v___x_1919_, v___x_1920_, v___x_1922_, v___x_1475_, v___x_1924_, v___x_1918_, v___x_1926_);
v___x_1928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1927_);
lean_ctor_set(v___x_1928_, 1, v_a_1463_);
return v___x_1928_;
}
else
{
lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; uint8_t v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; 
lean_dec(v___x_1475_);
v___x_1929_ = l_Lean_Syntax_getArg(v___x_1625_, v___x_1470_);
lean_dec(v___x_1625_);
v___x_1930_ = l_Lean_Syntax_getArg(v___x_1744_, v___x_1470_);
lean_dec(v___x_1744_);
v___x_1931_ = l_Lean_Syntax_getArg(v___x_1863_, v___x_1470_);
lean_dec(v___x_1863_);
v___x_1932_ = l_Lean_Syntax_getArg(v___x_1469_, v___x_1468_);
lean_dec(v___x_1469_);
v___x_1933_ = 0;
v___x_1934_ = l_Lean_SourceInfo_fromRef(v_a_1462_, v___x_1933_);
v___x_1935_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__1));
v___x_1936_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1934_, 7);
v___x_1937_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1934_);
lean_ctor_set(v___x_1937_, 1, v___x_1936_);
v___x_1938_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1939_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1934_);
lean_ctor_set(v___x_1939_, 1, v___x_1938_);
v___x_1940_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__20));
v___x_1941_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__21));
v___x_1942_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1934_);
lean_ctor_set(v___x_1942_, 1, v___x_1941_);
v___x_1943_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__14));
lean_inc_ref_n(v___x_1939_, 2);
v___x_1944_ = l_Lean_Syntax_node3(v___x_1934_, v___x_1943_, v___x_1930_, v___x_1939_, v___x_1931_);
v___x_1945_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__22));
v___x_1946_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1946_, 0, v___x_1934_);
lean_ctor_set(v___x_1946_, 1, v___x_1945_);
v___x_1947_ = l_Lean_Syntax_node3(v___x_1934_, v___x_1940_, v___x_1942_, v___x_1944_, v___x_1946_);
v___x_1948_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1949_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1934_);
lean_ctor_set(v___x_1949_, 1, v___x_1948_);
v___x_1950_ = l_Lean_Syntax_node7(v___x_1934_, v___x_1935_, v___x_1937_, v___x_1929_, v___x_1939_, v___x_1947_, v___x_1939_, v___x_1932_, v___x_1949_);
v___x_1951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1950_);
lean_ctor_set(v___x_1951_, 1, v_a_1463_);
return v___x_1951_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_unexpandDenote___boxed(lean_object* v_x_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l_Std_Sat_AIG_unexpandDenote(v_x_1952_, v_a_1953_, v_a_1954_);
lean_dec(v_a_1953_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGate___redArg(lean_object* v_aig_1956_, lean_object* v_input_1957_){
_start:
{
lean_object* v_lhs_1958_; lean_object* v_rhs_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1997_; 
v_lhs_1958_ = lean_ctor_get(v_input_1957_, 0);
v_rhs_1959_ = lean_ctor_get(v_input_1957_, 1);
v_isSharedCheck_1997_ = !lean_is_exclusive(v_input_1957_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1961_ = v_input_1957_;
v_isShared_1962_ = v_isSharedCheck_1997_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_rhs_1959_);
lean_inc(v_lhs_1958_);
lean_dec(v_input_1957_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1997_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v_decls_1963_; lean_object* v_cache_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1996_; 
v_decls_1963_ = lean_ctor_get(v_aig_1956_, 0);
v_cache_1964_ = lean_ctor_get(v_aig_1956_, 1);
v_isSharedCheck_1996_ = !lean_is_exclusive(v_aig_1956_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1966_ = v_aig_1956_;
v_isShared_1967_ = v_isSharedCheck_1996_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_cache_1964_);
lean_inc(v_decls_1963_);
lean_dec(v_aig_1956_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1996_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v_gate_1968_; uint8_t v_invert_1969_; lean_object* v_gate_1970_; uint8_t v_invert_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1995_; 
v_gate_1968_ = lean_ctor_get(v_lhs_1958_, 0);
lean_inc(v_gate_1968_);
v_invert_1969_ = lean_ctor_get_uint8(v_lhs_1958_, sizeof(void*)*1);
lean_dec_ref(v_lhs_1958_);
v_gate_1970_ = lean_ctor_get(v_rhs_1959_, 0);
v_invert_1971_ = lean_ctor_get_uint8(v_rhs_1959_, sizeof(void*)*1);
v_isSharedCheck_1995_ = !lean_is_exclusive(v_rhs_1959_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1973_ = v_rhs_1959_;
v_isShared_1974_ = v_isSharedCheck_1995_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_gate_1970_);
lean_dec(v_rhs_1959_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1995_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v_g_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1984_; 
v_g_1975_ = lean_array_get_size(v_decls_1963_);
v___x_1976_ = lean_unsigned_to_nat(2u);
v___x_1977_ = lean_nat_mul(v_gate_1968_, v___x_1976_);
lean_dec(v_gate_1968_);
v___x_1978_ = lean_bool_to_nat(v_invert_1969_);
v___x_1979_ = lean_nat_lor(v___x_1977_, v___x_1978_);
lean_dec(v___x_1977_);
v___x_1980_ = lean_nat_mul(v_gate_1970_, v___x_1976_);
lean_dec(v_gate_1970_);
v___x_1981_ = lean_bool_to_nat(v_invert_1971_);
v___x_1982_ = lean_nat_lor(v___x_1980_, v___x_1981_);
lean_dec(v___x_1980_);
if (v_isShared_1962_ == 0)
{
lean_ctor_set_tag(v___x_1961_, 2);
lean_ctor_set(v___x_1961_, 1, v___x_1982_);
lean_ctor_set(v___x_1961_, 0, v___x_1979_);
v___x_1984_ = v___x_1961_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1979_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v___x_1982_);
v___x_1984_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
lean_object* v_decls_1985_; lean_object* v___x_1987_; 
v_decls_1985_ = lean_array_push(v_decls_1963_, v___x_1984_);
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 0, v_decls_1985_);
v___x_1987_ = v___x_1966_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_decls_1985_);
lean_ctor_set(v_reuseFailAlloc_1993_, 1, v_cache_1964_);
v___x_1987_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
uint8_t v___x_1988_; lean_object* v___x_1990_; 
v___x_1988_ = 0;
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 0, v_g_1975_);
v___x_1990_ = v___x_1973_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_g_1975_);
v___x_1990_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
lean_object* v___x_1991_; 
lean_ctor_set_uint8(v___x_1990_, sizeof(void*)*1, v___x_1988_);
v___x_1991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1987_);
lean_ctor_set(v___x_1991_, 1, v___x_1990_);
return v___x_1991_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGate(lean_object* v_00_u03b1_1998_, lean_object* v_inst_1999_, lean_object* v_inst_2000_, lean_object* v_aig_2001_, lean_object* v_input_2002_){
_start:
{
lean_object* v___x_2003_; 
v___x_2003_ = l_Std_Sat_AIG_mkGate___redArg(v_aig_2001_, v_input_2002_);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGate___boxed(lean_object* v_00_u03b1_2004_, lean_object* v_inst_2005_, lean_object* v_inst_2006_, lean_object* v_aig_2007_, lean_object* v_input_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l_Std_Sat_AIG_mkGate(v_00_u03b1_2004_, v_inst_2005_, v_inst_2006_, v_aig_2007_, v_input_2008_);
lean_dec_ref(v_inst_2006_);
lean_dec_ref(v_inst_2005_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtom___redArg(lean_object* v_aig_2010_, lean_object* v_n_2011_){
_start:
{
lean_object* v_decls_2012_; lean_object* v_cache_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2026_; 
v_decls_2012_ = lean_ctor_get(v_aig_2010_, 0);
v_cache_2013_ = lean_ctor_get(v_aig_2010_, 1);
v_isSharedCheck_2026_ = !lean_is_exclusive(v_aig_2010_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2015_ = v_aig_2010_;
v_isShared_2016_ = v_isSharedCheck_2026_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_cache_2013_);
lean_inc(v_decls_2012_);
lean_dec(v_aig_2010_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2026_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v_g_2017_; lean_object* v___x_2018_; lean_object* v_decls_2019_; lean_object* v___x_2021_; 
v_g_2017_ = lean_array_get_size(v_decls_2012_);
v___x_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2018_, 0, v_n_2011_);
v_decls_2019_ = lean_array_push(v_decls_2012_, v___x_2018_);
if (v_isShared_2016_ == 0)
{
lean_ctor_set(v___x_2015_, 0, v_decls_2019_);
v___x_2021_ = v___x_2015_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_decls_2019_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v_cache_2013_);
v___x_2021_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
uint8_t v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___x_2022_ = 0;
v___x_2023_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2023_, 0, v_g_2017_);
lean_ctor_set_uint8(v___x_2023_, sizeof(void*)*1, v___x_2022_);
v___x_2024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2024_, 0, v___x_2021_);
lean_ctor_set(v___x_2024_, 1, v___x_2023_);
return v___x_2024_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtom(lean_object* v_00_u03b1_2027_, lean_object* v_inst_2028_, lean_object* v_inst_2029_, lean_object* v_aig_2030_, lean_object* v_n_2031_){
_start:
{
lean_object* v___x_2032_; 
v___x_2032_ = l_Std_Sat_AIG_mkAtom___redArg(v_aig_2030_, v_n_2031_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtom___boxed(lean_object* v_00_u03b1_2033_, lean_object* v_inst_2034_, lean_object* v_inst_2035_, lean_object* v_aig_2036_, lean_object* v_n_2037_){
_start:
{
lean_object* v_res_2038_; 
v_res_2038_ = l_Std_Sat_AIG_mkAtom(v_00_u03b1_2033_, v_inst_2034_, v_inst_2035_, v_aig_2036_, v_n_2037_);
lean_dec_ref(v_inst_2035_);
lean_dec_ref(v_inst_2034_);
return v_res_2038_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConst___redArg(lean_object* v_aig_2039_, uint8_t v_val_2040_){
_start:
{
lean_object* v_decls_2041_; lean_object* v_cache_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2054_; 
v_decls_2041_ = lean_ctor_get(v_aig_2039_, 0);
v_cache_2042_ = lean_ctor_get(v_aig_2039_, 1);
v_isSharedCheck_2054_ = !lean_is_exclusive(v_aig_2039_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2044_ = v_aig_2039_;
v_isShared_2045_ = v_isSharedCheck_2054_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_cache_2042_);
lean_inc(v_decls_2041_);
lean_dec(v_aig_2039_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2054_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v_g_2046_; lean_object* v___x_2047_; lean_object* v_decls_2048_; lean_object* v___x_2050_; 
v_g_2046_ = lean_array_get_size(v_decls_2041_);
v___x_2047_ = lean_box(0);
v_decls_2048_ = lean_array_push(v_decls_2041_, v___x_2047_);
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 0, v_decls_2048_);
v___x_2050_ = v___x_2044_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_decls_2048_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v_cache_2042_);
v___x_2050_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2051_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2051_, 0, v_g_2046_);
lean_ctor_set_uint8(v___x_2051_, sizeof(void*)*1, v_val_2040_);
v___x_2052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2050_);
lean_ctor_set(v___x_2052_, 1, v___x_2051_);
return v___x_2052_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConst___redArg___boxed(lean_object* v_aig_2055_, lean_object* v_val_2056_){
_start:
{
uint8_t v_val_boxed_2057_; lean_object* v_res_2058_; 
v_val_boxed_2057_ = lean_unbox(v_val_2056_);
v_res_2058_ = l_Std_Sat_AIG_mkConst___redArg(v_aig_2055_, v_val_boxed_2057_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConst(lean_object* v_00_u03b1_2059_, lean_object* v_inst_2060_, lean_object* v_inst_2061_, lean_object* v_aig_2062_, uint8_t v_val_2063_){
_start:
{
lean_object* v___x_2064_; 
v___x_2064_ = l_Std_Sat_AIG_mkConst___redArg(v_aig_2062_, v_val_2063_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConst___boxed(lean_object* v_00_u03b1_2065_, lean_object* v_inst_2066_, lean_object* v_inst_2067_, lean_object* v_aig_2068_, lean_object* v_val_2069_){
_start:
{
uint8_t v_val_boxed_2070_; lean_object* v_res_2071_; 
v_val_boxed_2070_ = lean_unbox(v_val_2069_);
v_res_2071_ = l_Std_Sat_AIG_mkConst(v_00_u03b1_2065_, v_inst_2066_, v_inst_2067_, v_aig_2068_, v_val_boxed_2070_);
lean_dec_ref(v_inst_2067_);
lean_dec_ref(v_inst_2066_);
return v_res_2071_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_isConstant___redArg(lean_object* v_aig_2072_, lean_object* v_ref_2073_, uint8_t v_b_2074_){
_start:
{
lean_object* v_gate_2075_; uint8_t v_invert_2076_; lean_object* v_decls_2077_; lean_object* v_decl_2078_; uint8_t v___y_2080_; 
v_gate_2075_ = lean_ctor_get(v_ref_2073_, 0);
v_invert_2076_ = lean_ctor_get_uint8(v_ref_2073_, sizeof(void*)*1);
v_decls_2077_ = lean_ctor_get(v_aig_2072_, 0);
v_decl_2078_ = lean_array_fget_borrowed(v_decls_2077_, v_gate_2075_);
if (v_invert_2076_ == 0)
{
if (v_b_2074_ == 0)
{
uint8_t v___x_2082_; 
v___x_2082_ = 1;
v___y_2080_ = v___x_2082_;
goto v___jp_2079_;
}
else
{
v___y_2080_ = v_invert_2076_;
goto v___jp_2079_;
}
}
else
{
v___y_2080_ = v_b_2074_;
goto v___jp_2079_;
}
v___jp_2079_:
{
if (lean_obj_tag(v_decl_2078_) == 0)
{
return v___y_2080_;
}
else
{
uint8_t v___x_2081_; 
v___x_2081_ = 0;
return v___x_2081_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_isConstant___redArg___boxed(lean_object* v_aig_2083_, lean_object* v_ref_2084_, lean_object* v_b_2085_){
_start:
{
uint8_t v_b_boxed_2086_; uint8_t v_res_2087_; lean_object* v_r_2088_; 
v_b_boxed_2086_ = lean_unbox(v_b_2085_);
v_res_2087_ = l_Std_Sat_AIG_isConstant___redArg(v_aig_2083_, v_ref_2084_, v_b_boxed_2086_);
lean_dec_ref(v_ref_2084_);
lean_dec_ref(v_aig_2083_);
v_r_2088_ = lean_box(v_res_2087_);
return v_r_2088_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_isConstant(lean_object* v_00_u03b1_2089_, lean_object* v_inst_2090_, lean_object* v_inst_2091_, lean_object* v_aig_2092_, lean_object* v_ref_2093_, uint8_t v_b_2094_){
_start:
{
uint8_t v___x_2095_; 
v___x_2095_ = l_Std_Sat_AIG_isConstant___redArg(v_aig_2092_, v_ref_2093_, v_b_2094_);
return v___x_2095_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_isConstant___boxed(lean_object* v_00_u03b1_2096_, lean_object* v_inst_2097_, lean_object* v_inst_2098_, lean_object* v_aig_2099_, lean_object* v_ref_2100_, lean_object* v_b_2101_){
_start:
{
uint8_t v_b_boxed_2102_; uint8_t v_res_2103_; lean_object* v_r_2104_; 
v_b_boxed_2102_ = lean_unbox(v_b_2101_);
v_res_2103_ = l_Std_Sat_AIG_isConstant(v_00_u03b1_2096_, v_inst_2097_, v_inst_2098_, v_aig_2099_, v_ref_2100_, v_b_boxed_2102_);
lean_dec_ref(v_ref_2100_);
lean_dec_ref(v_aig_2099_);
lean_dec_ref(v_inst_2098_);
lean_dec_ref(v_inst_2097_);
v_r_2104_ = lean_box(v_res_2103_);
return v_r_2104_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___redArg(lean_object* v_aig_2105_, lean_object* v_ref_2106_){
_start:
{
lean_object* v_gate_2107_; uint8_t v_invert_2108_; lean_object* v_decls_2109_; lean_object* v_decl_2110_; 
v_gate_2107_ = lean_ctor_get(v_ref_2106_, 0);
v_invert_2108_ = lean_ctor_get_uint8(v_ref_2106_, sizeof(void*)*1);
v_decls_2109_ = lean_ctor_get(v_aig_2105_, 0);
v_decl_2110_ = lean_array_fget_borrowed(v_decls_2109_, v_gate_2107_);
if (lean_obj_tag(v_decl_2110_) == 0)
{
lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2111_ = lean_box(v_invert_2108_);
v___x_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2111_);
return v___x_2112_;
}
else
{
lean_object* v___x_2113_; 
v___x_2113_ = lean_box(0);
return v___x_2113_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___redArg___boxed(lean_object* v_aig_2114_, lean_object* v_ref_2115_){
_start:
{
lean_object* v_res_2116_; 
v_res_2116_ = l_Std_Sat_AIG_getConstant___redArg(v_aig_2114_, v_ref_2115_);
lean_dec_ref(v_ref_2115_);
lean_dec_ref(v_aig_2114_);
return v_res_2116_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant(lean_object* v_00_u03b1_2117_, lean_object* v_inst_2118_, lean_object* v_inst_2119_, lean_object* v_aig_2120_, lean_object* v_ref_2121_){
_start:
{
lean_object* v___x_2122_; 
v___x_2122_ = l_Std_Sat_AIG_getConstant___redArg(v_aig_2120_, v_ref_2121_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___boxed(lean_object* v_00_u03b1_2123_, lean_object* v_inst_2124_, lean_object* v_inst_2125_, lean_object* v_aig_2126_, lean_object* v_ref_2127_){
_start:
{
lean_object* v_res_2128_; 
v_res_2128_ = l_Std_Sat_AIG_getConstant(v_00_u03b1_2123_, v_inst_2124_, v_inst_2125_, v_aig_2126_, v_ref_2127_);
lean_dec_ref(v_ref_2127_);
lean_dec_ref(v_aig_2126_);
lean_dec_ref(v_inst_2125_);
lean_dec_ref(v_inst_2124_);
return v_res_2128_;
}
}
lean_object* runtime_initialize_Std_Data_HashSet(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sat_AIG_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_HashSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Sat_AIG_instInhabitedFanin_default = _init_l_Std_Sat_AIG_instInhabitedFanin_default();
lean_mark_persistent(l_Std_Sat_AIG_instInhabitedFanin_default);
l_Std_Sat_AIG_instInhabitedFanin = _init_l_Std_Sat_AIG_instInhabitedFanin();
lean_mark_persistent(l_Std_Sat_AIG_instInhabitedFanin);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Sat_AIG_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_HashSet(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_AIG_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_HashSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_AIG_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sat_AIG_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sat_AIG_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
