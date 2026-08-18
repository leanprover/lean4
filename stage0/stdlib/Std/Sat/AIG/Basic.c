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
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_UInt64_ofNat___boxed(lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Bool_toNat(uint8_t);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Std_Sat_AIG_Cache_empty___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_Cache_empty___closed__2;
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
static const lean_string_object l_Std_Sat_AIG_toGraphviz_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " -> "};
static const lean_object* l_Std_Sat_AIG_toGraphviz_go___redArg___closed__0 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_go___redArg___closed__0_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_go___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "; "};
static const lean_object* l_Std_Sat_AIG_toGraphviz_go___redArg___closed__1 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_go___redArg___closed__1_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_go___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Std_Sat_AIG_toGraphviz_go___redArg___closed__2 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_go___redArg___closed__2_value;
static const lean_closure_object l_Std_Sat_AIG_toGraphviz_go___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_ofNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_string_object l_Std_Sat_AIG_toGraphviz___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Sat_AIG_toGraphviz___redArg___closed__0 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__0_value;
static lean_once_cell_t l_Std_Sat_AIG_toGraphviz___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_toGraphviz___redArg___closed__1;
static lean_once_cell_t l_Std_Sat_AIG_toGraphviz___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_toGraphviz___redArg___closed__2;
static lean_once_cell_t l_Std_Sat_AIG_toGraphviz___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_toGraphviz___redArg___closed__3;
static const lean_closure_object l_Std_Sat_AIG_toGraphviz___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Sat_AIG_toGraphviz___redArg___closed__4 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__4_value;
static const lean_closure_object l_Std_Sat_AIG_toGraphviz___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Sat_AIG_toGraphviz___redArg___closed__5 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__5_value;
static const lean_closure_object l_Std_Sat_AIG_toGraphviz___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Sat_AIG_toGraphviz___redArg___closed__6 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__6_value;
static const lean_closure_object l_Std_Sat_AIG_toGraphviz___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Sat_AIG_toGraphviz___redArg___closed__7 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__7_value;
static const lean_closure_object l_Std_Sat_AIG_toGraphviz___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Sat_AIG_toGraphviz___redArg___closed__8 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__8_value;
static const lean_closure_object l_Std_Sat_AIG_toGraphviz___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Sat_AIG_toGraphviz___redArg___closed__9 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__9_value;
static const lean_closure_object l_Std_Sat_AIG_toGraphviz___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Sat_AIG_toGraphviz___redArg___closed__10 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__10_value;
static const lean_ctor_object l_Std_Sat_AIG_toGraphviz___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__4_value),((lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__5_value)}};
static const lean_object* l_Std_Sat_AIG_toGraphviz___redArg___closed__11 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__11_value;
static const lean_ctor_object l_Std_Sat_AIG_toGraphviz___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__11_value),((lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__6_value),((lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__7_value),((lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__8_value),((lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__9_value)}};
static const lean_object* l_Std_Sat_AIG_toGraphviz___redArg___closed__12 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__12_value;
static const lean_ctor_object l_Std_Sat_AIG_toGraphviz___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__12_value),((lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__10_value)}};
static const lean_object* l_Std_Sat_AIG_toGraphviz___redArg___closed__13 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__13_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Digraph AIG {"};
static const lean_object* l_Std_Sat_AIG_toGraphviz___redArg___closed__14 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__14_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_Std_Sat_AIG_toGraphviz___redArg___closed__15 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz___redArg___closed__15_value;
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
v___x_80_ = l_Bool_toNat(v_invert_77_);
v___x_81_ = lean_nat_lor(v___x_79_, v___x_80_);
lean_dec(v___x_80_);
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
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; uint8_t v___x_95_; 
v___x_92_ = lean_unsigned_to_nat(1u);
v___x_93_ = lean_nat_land(v___x_92_, v_f_91_);
v___x_94_ = lean_unsigned_to_nat(0u);
v___x_95_ = lean_nat_dec_eq(v___x_93_, v___x_94_);
lean_dec(v___x_93_);
if (v___x_95_ == 0)
{
uint8_t v___x_96_; 
v___x_96_ = 1;
return v___x_96_;
}
else
{
uint8_t v___x_97_; 
v___x_97_ = 0;
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Fanin_invert___boxed(lean_object* v_f_98_){
_start:
{
uint8_t v_res_99_; lean_object* v_r_100_; 
v_res_99_ = l_Std_Sat_AIG_Fanin_invert(v_f_98_);
lean_dec(v_f_98_);
v_r_100_ = lean_box(v_res_99_);
return v_r_100_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Fanin_flip(lean_object* v_f_101_, uint8_t v_val_102_){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = l_Bool_toNat(v_val_102_);
v___x_104_ = lean_nat_lxor(v_f_101_, v___x_103_);
lean_dec(v___x_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Fanin_flip___boxed(lean_object* v_f_105_, lean_object* v_val_106_){
_start:
{
uint8_t v_val_boxed_107_; lean_object* v_res_108_; 
v_val_boxed_107_ = lean_unbox(v_val_106_);
v_res_108_ = l_Std_Sat_AIG_Fanin_flip(v_f_105_, v_val_boxed_107_);
lean_dec(v_f_105_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_ctorIdx___redArg(lean_object* v_x_109_){
_start:
{
switch(lean_obj_tag(v_x_109_))
{
case 0:
{
lean_object* v___x_110_; 
v___x_110_ = lean_unsigned_to_nat(0u);
return v___x_110_;
}
case 1:
{
lean_object* v___x_111_; 
v___x_111_ = lean_unsigned_to_nat(1u);
return v___x_111_;
}
default: 
{
lean_object* v___x_112_; 
v___x_112_ = lean_unsigned_to_nat(2u);
return v___x_112_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_ctorIdx___redArg___boxed(lean_object* v_x_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Std_Sat_AIG_Decl_ctorIdx___redArg(v_x_113_);
lean_dec(v_x_113_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_ctorIdx(lean_object* v_00_u03b1_115_, lean_object* v_x_116_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l_Std_Sat_AIG_Decl_ctorIdx___redArg(v_x_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_ctorIdx___boxed(lean_object* v_00_u03b1_118_, lean_object* v_x_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Std_Sat_AIG_Decl_ctorIdx(v_00_u03b1_118_, v_x_119_);
lean_dec(v_x_119_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_ctorElim___redArg(lean_object* v_t_121_, lean_object* v_k_122_){
_start:
{
switch(lean_obj_tag(v_t_121_))
{
case 0:
{
return v_k_122_;
}
case 1:
{
lean_object* v_idx_123_; lean_object* v___x_124_; 
v_idx_123_ = lean_ctor_get(v_t_121_, 0);
lean_inc(v_idx_123_);
lean_dec_ref_known(v_t_121_, 1);
v___x_124_ = lean_apply_1(v_k_122_, v_idx_123_);
return v___x_124_;
}
default: 
{
lean_object* v_l_125_; lean_object* v_r_126_; lean_object* v___x_127_; 
v_l_125_ = lean_ctor_get(v_t_121_, 0);
lean_inc(v_l_125_);
v_r_126_ = lean_ctor_get(v_t_121_, 1);
lean_inc(v_r_126_);
lean_dec_ref_known(v_t_121_, 2);
v___x_127_ = lean_apply_2(v_k_122_, v_l_125_, v_r_126_);
return v___x_127_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_ctorElim(lean_object* v_00_u03b1_128_, lean_object* v_motive_129_, lean_object* v_ctorIdx_130_, lean_object* v_t_131_, lean_object* v_h_132_, lean_object* v_k_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Std_Sat_AIG_Decl_ctorElim___redArg(v_t_131_, v_k_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_ctorElim___boxed(lean_object* v_00_u03b1_135_, lean_object* v_motive_136_, lean_object* v_ctorIdx_137_, lean_object* v_t_138_, lean_object* v_h_139_, lean_object* v_k_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Std_Sat_AIG_Decl_ctorElim(v_00_u03b1_135_, v_motive_136_, v_ctorIdx_137_, v_t_138_, v_h_139_, v_k_140_);
lean_dec(v_ctorIdx_137_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_false_elim___redArg(lean_object* v_t_142_, lean_object* v_false_143_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = l_Std_Sat_AIG_Decl_ctorElim___redArg(v_t_142_, v_false_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_false_elim(lean_object* v_00_u03b1_145_, lean_object* v_motive_146_, lean_object* v_t_147_, lean_object* v_h_148_, lean_object* v_false_149_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = l_Std_Sat_AIG_Decl_ctorElim___redArg(v_t_147_, v_false_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_atom_elim___redArg(lean_object* v_t_151_, lean_object* v_atom_152_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = l_Std_Sat_AIG_Decl_ctorElim___redArg(v_t_151_, v_atom_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_atom_elim(lean_object* v_00_u03b1_154_, lean_object* v_motive_155_, lean_object* v_t_156_, lean_object* v_h_157_, lean_object* v_atom_158_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l_Std_Sat_AIG_Decl_ctorElim___redArg(v_t_156_, v_atom_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_gate_elim___redArg(lean_object* v_t_160_, lean_object* v_gate_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l_Std_Sat_AIG_Decl_ctorElim___redArg(v_t_160_, v_gate_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_gate_elim(lean_object* v_00_u03b1_163_, lean_object* v_motive_164_, lean_object* v_t_165_, lean_object* v_h_166_, lean_object* v_gate_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l_Std_Sat_AIG_Decl_ctorElim___redArg(v_t_165_, v_gate_167_);
return v___x_168_;
}
}
LEAN_EXPORT uint64_t l_Std_Sat_AIG_instHashableDecl_hash___redArg(lean_object* v_inst_169_, lean_object* v_x_170_){
_start:
{
switch(lean_obj_tag(v_x_170_))
{
case 0:
{
uint64_t v___x_171_; 
lean_dec_ref(v_inst_169_);
v___x_171_ = 0ULL;
return v___x_171_;
}
case 1:
{
lean_object* v_idx_172_; uint64_t v___x_173_; lean_object* v___x_174_; uint64_t v___x_175_; uint64_t v___x_176_; 
v_idx_172_ = lean_ctor_get(v_x_170_, 0);
lean_inc(v_idx_172_);
lean_dec_ref_known(v_x_170_, 1);
v___x_173_ = 1ULL;
v___x_174_ = lean_apply_1(v_inst_169_, v_idx_172_);
v___x_175_ = lean_unbox_uint64(v___x_174_);
lean_dec_ref(v___x_174_);
v___x_176_ = lean_uint64_mix_hash(v___x_173_, v___x_175_);
return v___x_176_;
}
default: 
{
lean_object* v_l_177_; lean_object* v_r_178_; uint64_t v___x_179_; uint64_t v___x_180_; uint64_t v___x_181_; uint64_t v___x_182_; uint64_t v___x_183_; 
lean_dec_ref(v_inst_169_);
v_l_177_ = lean_ctor_get(v_x_170_, 0);
lean_inc(v_l_177_);
v_r_178_ = lean_ctor_get(v_x_170_, 1);
lean_inc(v_r_178_);
lean_dec_ref_known(v_x_170_, 2);
v___x_179_ = 2ULL;
v___x_180_ = l_Std_Sat_AIG_instHashableFanin_hash(v_l_177_);
lean_dec(v_l_177_);
v___x_181_ = lean_uint64_mix_hash(v___x_179_, v___x_180_);
v___x_182_ = l_Std_Sat_AIG_instHashableFanin_hash(v_r_178_);
lean_dec(v_r_178_);
v___x_183_ = lean_uint64_mix_hash(v___x_181_, v___x_182_);
return v___x_183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableDecl_hash___redArg___boxed(lean_object* v_inst_184_, lean_object* v_x_185_){
_start:
{
uint64_t v_res_186_; lean_object* v_r_187_; 
v_res_186_ = l_Std_Sat_AIG_instHashableDecl_hash___redArg(v_inst_184_, v_x_185_);
v_r_187_ = lean_box_uint64(v_res_186_);
return v_r_187_;
}
}
LEAN_EXPORT uint64_t l_Std_Sat_AIG_instHashableDecl_hash(lean_object* v_00_u03b1_188_, lean_object* v_inst_189_, lean_object* v_x_190_){
_start:
{
uint64_t v___x_191_; 
v___x_191_ = l_Std_Sat_AIG_instHashableDecl_hash___redArg(v_inst_189_, v_x_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableDecl_hash___boxed(lean_object* v_00_u03b1_192_, lean_object* v_inst_193_, lean_object* v_x_194_){
_start:
{
uint64_t v_res_195_; lean_object* v_r_196_; 
v_res_195_ = l_Std_Sat_AIG_instHashableDecl_hash(v_00_u03b1_192_, v_inst_193_, v_x_194_);
v_r_196_ = lean_box_uint64(v_res_195_);
return v_r_196_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableDecl___redArg(lean_object* v_inst_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_198_, 0, lean_box(0));
lean_closure_set(v___x_198_, 1, v_inst_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableDecl(lean_object* v_00_u03b1_199_, lean_object* v_inst_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_201_, 0, lean_box(0));
lean_closure_set(v___x_201_, 1, v_inst_200_);
return v___x_201_;
}
}
static lean_object* _init_l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2(void){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = lean_unsigned_to_nat(2u);
v___x_206_ = lean_nat_to_int(v___x_205_);
return v___x_206_;
}
}
static lean_object* _init_l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = lean_unsigned_to_nat(1u);
v___x_208_ = lean_nat_to_int(v___x_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprDecl_repr___redArg(lean_object* v_inst_221_, lean_object* v_x_222_, lean_object* v_prec_223_){
_start:
{
lean_object* v___y_225_; 
switch(lean_obj_tag(v_x_222_))
{
case 0:
{
lean_object* v___x_231_; uint8_t v___x_232_; 
lean_dec_ref(v_inst_221_);
v___x_231_ = lean_unsigned_to_nat(1024u);
v___x_232_ = lean_nat_dec_le(v___x_231_, v_prec_223_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; 
v___x_233_ = lean_obj_once(&l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2, &l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2_once, _init_l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2);
v___y_225_ = v___x_233_;
goto v___jp_224_;
}
else
{
lean_object* v___x_234_; 
v___x_234_ = lean_obj_once(&l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3, &l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3_once, _init_l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3);
v___y_225_ = v___x_234_;
goto v___jp_224_;
}
}
case 1:
{
lean_object* v_idx_235_; lean_object* v___y_237_; lean_object* v___x_246_; uint8_t v___x_247_; 
v_idx_235_ = lean_ctor_get(v_x_222_, 0);
lean_inc(v_idx_235_);
lean_dec_ref_known(v_x_222_, 1);
v___x_246_ = lean_unsigned_to_nat(1024u);
v___x_247_ = lean_nat_dec_le(v___x_246_, v_prec_223_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; 
v___x_248_ = lean_obj_once(&l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2, &l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2_once, _init_l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2);
v___y_237_ = v___x_248_;
goto v___jp_236_;
}
else
{
lean_object* v___x_249_; 
v___x_249_ = lean_obj_once(&l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3, &l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3_once, _init_l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3);
v___y_237_ = v___x_249_;
goto v___jp_236_;
}
v___jp_236_:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; uint8_t v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_238_ = ((lean_object*)(l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__6));
v___x_239_ = lean_unsigned_to_nat(1024u);
v___x_240_ = lean_apply_2(v_inst_221_, v_idx_235_, v___x_239_);
v___x_241_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_241_, 0, v___x_238_);
lean_ctor_set(v___x_241_, 1, v___x_240_);
lean_inc(v___y_237_);
v___x_242_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_242_, 0, v___y_237_);
lean_ctor_set(v___x_242_, 1, v___x_241_);
v___x_243_ = 0;
v___x_244_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_244_, 0, v___x_242_);
lean_ctor_set_uint8(v___x_244_, sizeof(void*)*1, v___x_243_);
v___x_245_ = l_Repr_addAppParen(v___x_244_, v_prec_223_);
return v___x_245_;
}
}
default: 
{
lean_object* v_l_250_; lean_object* v_r_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_274_; 
lean_dec_ref(v_inst_221_);
v_l_250_ = lean_ctor_get(v_x_222_, 0);
v_r_251_ = lean_ctor_get(v_x_222_, 1);
v_isSharedCheck_274_ = !lean_is_exclusive(v_x_222_);
if (v_isSharedCheck_274_ == 0)
{
v___x_253_ = v_x_222_;
v_isShared_254_ = v_isSharedCheck_274_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_r_251_);
lean_inc(v_l_250_);
lean_dec(v_x_222_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_274_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___y_256_; lean_object* v___x_270_; uint8_t v___x_271_; 
v___x_270_ = lean_unsigned_to_nat(1024u);
v___x_271_ = lean_nat_dec_le(v___x_270_, v_prec_223_);
if (v___x_271_ == 0)
{
lean_object* v___x_272_; 
v___x_272_ = lean_obj_once(&l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2, &l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2_once, _init_l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2);
v___y_256_ = v___x_272_;
goto v___jp_255_;
}
else
{
lean_object* v___x_273_; 
v___x_273_ = lean_obj_once(&l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3, &l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3_once, _init_l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3);
v___y_256_ = v___x_273_;
goto v___jp_255_;
}
v___jp_255_:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_261_; 
v___x_257_ = lean_box(1);
v___x_258_ = ((lean_object*)(l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__9));
v___x_259_ = l_Std_Sat_AIG_instReprFanin_repr___redArg(v_l_250_);
if (v_isShared_254_ == 0)
{
lean_ctor_set_tag(v___x_253_, 5);
lean_ctor_set(v___x_253_, 1, v___x_259_);
lean_ctor_set(v___x_253_, 0, v___x_258_);
v___x_261_ = v___x_253_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v___x_258_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v___x_259_);
v___x_261_ = v_reuseFailAlloc_269_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; uint8_t v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_262_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
lean_ctor_set(v___x_262_, 1, v___x_257_);
v___x_263_ = l_Std_Sat_AIG_instReprFanin_repr___redArg(v_r_251_);
v___x_264_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_262_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
lean_inc(v___y_256_);
v___x_265_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_265_, 0, v___y_256_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
v___x_266_ = 0;
v___x_267_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_267_, 0, v___x_265_);
lean_ctor_set_uint8(v___x_267_, sizeof(void*)*1, v___x_266_);
v___x_268_ = l_Repr_addAppParen(v___x_267_, v_prec_223_);
return v___x_268_;
}
}
}
}
}
v___jp_224_:
{
lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_226_ = ((lean_object*)(l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__1));
lean_inc(v___y_225_);
v___x_227_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_227_, 0, v___y_225_);
lean_ctor_set(v___x_227_, 1, v___x_226_);
v___x_228_ = 0;
v___x_229_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_229_, 0, v___x_227_);
lean_ctor_set_uint8(v___x_229_, sizeof(void*)*1, v___x_228_);
v___x_230_ = l_Repr_addAppParen(v___x_229_, v_prec_223_);
return v___x_230_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprDecl_repr___redArg___boxed(lean_object* v_inst_275_, lean_object* v_x_276_, lean_object* v_prec_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Std_Sat_AIG_instReprDecl_repr___redArg(v_inst_275_, v_x_276_, v_prec_277_);
lean_dec(v_prec_277_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprDecl_repr(lean_object* v_00_u03b1_279_, lean_object* v_inst_280_, lean_object* v_x_281_, lean_object* v_prec_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_Std_Sat_AIG_instReprDecl_repr___redArg(v_inst_280_, v_x_281_, v_prec_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprDecl_repr___boxed(lean_object* v_00_u03b1_284_, lean_object* v_inst_285_, lean_object* v_x_286_, lean_object* v_prec_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Std_Sat_AIG_instReprDecl_repr(v_00_u03b1_284_, v_inst_285_, v_x_286_, v_prec_287_);
lean_dec(v_prec_287_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprDecl___redArg(lean_object* v_inst_289_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instReprDecl_repr___boxed), 4, 2);
lean_closure_set(v___x_290_, 0, lean_box(0));
lean_closure_set(v___x_290_, 1, v_inst_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprDecl(lean_object* v_00_u03b1_291_, lean_object* v_inst_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instReprDecl_repr___boxed), 4, 2);
lean_closure_set(v___x_293_, 0, lean_box(0));
lean_closure_set(v___x_293_, 1, v_inst_292_);
return v___x_293_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(lean_object* v_inst_294_, lean_object* v_x_295_, lean_object* v_x_296_){
_start:
{
switch(lean_obj_tag(v_x_295_))
{
case 0:
{
lean_dec_ref(v_inst_294_);
if (lean_obj_tag(v_x_296_) == 0)
{
uint8_t v___x_297_; 
v___x_297_ = 1;
return v___x_297_;
}
else
{
uint8_t v___x_298_; 
lean_dec(v_x_296_);
v___x_298_ = 0;
return v___x_298_;
}
}
case 1:
{
lean_object* v_idx_299_; uint8_t v___x_300_; 
v_idx_299_ = lean_ctor_get(v_x_295_, 0);
lean_inc(v_idx_299_);
lean_dec_ref_known(v_x_295_, 1);
v___x_300_ = 0;
if (lean_obj_tag(v_x_296_) == 1)
{
lean_object* v_idx_301_; lean_object* v___x_302_; uint8_t v___x_303_; 
v_idx_301_ = lean_ctor_get(v_x_296_, 0);
lean_inc(v_idx_301_);
lean_dec_ref_known(v_x_296_, 1);
v___x_302_ = lean_apply_2(v_inst_294_, v_idx_299_, v_idx_301_);
v___x_303_ = lean_unbox(v___x_302_);
if (v___x_303_ == 0)
{
return v___x_300_;
}
else
{
uint8_t v___x_304_; 
v___x_304_ = lean_unbox(v___x_302_);
return v___x_304_;
}
}
else
{
lean_dec(v_idx_299_);
lean_dec(v_x_296_);
lean_dec_ref(v_inst_294_);
return v___x_300_;
}
}
default: 
{
lean_object* v_l_305_; lean_object* v_r_306_; uint8_t v___x_307_; 
lean_dec_ref(v_inst_294_);
v_l_305_ = lean_ctor_get(v_x_295_, 0);
lean_inc(v_l_305_);
v_r_306_ = lean_ctor_get(v_x_295_, 1);
lean_inc(v_r_306_);
lean_dec_ref_known(v_x_295_, 2);
v___x_307_ = 0;
if (lean_obj_tag(v_x_296_) == 2)
{
lean_object* v_l_308_; lean_object* v_r_309_; uint8_t v___x_310_; 
v_l_308_ = lean_ctor_get(v_x_296_, 0);
lean_inc(v_l_308_);
v_r_309_ = lean_ctor_get(v_x_296_, 1);
lean_inc(v_r_309_);
lean_dec_ref_known(v_x_296_, 2);
v___x_310_ = lean_nat_dec_eq(v_l_305_, v_l_308_);
lean_dec(v_l_308_);
lean_dec(v_l_305_);
if (v___x_310_ == 0)
{
lean_dec(v_r_309_);
lean_dec(v_r_306_);
return v___x_307_;
}
else
{
uint8_t v___x_311_; 
v___x_311_ = lean_nat_dec_eq(v_r_306_, v_r_309_);
lean_dec(v_r_309_);
lean_dec(v_r_306_);
if (v___x_311_ == 0)
{
return v___x_307_;
}
else
{
return v___x_311_;
}
}
}
else
{
lean_dec(v_r_306_);
lean_dec(v_l_305_);
lean_dec(v_x_296_);
return v___x_307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg___boxed(lean_object* v_inst_312_, lean_object* v_x_313_, lean_object* v_x_314_){
_start:
{
uint8_t v_res_315_; lean_object* v_r_316_; 
v_res_315_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v_inst_312_, v_x_313_, v_x_314_);
v_r_316_ = lean_box(v_res_315_);
return v_r_316_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_instDecidableEqDecl_decEq(lean_object* v_00_u03b1_317_, lean_object* v_inst_318_, lean_object* v_x_319_, lean_object* v_x_320_){
_start:
{
uint8_t v___x_321_; 
v___x_321_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v_inst_318_, v_x_319_, v_x_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instDecidableEqDecl_decEq___boxed(lean_object* v_00_u03b1_322_, lean_object* v_inst_323_, lean_object* v_x_324_, lean_object* v_x_325_){
_start:
{
uint8_t v_res_326_; lean_object* v_r_327_; 
v_res_326_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq(v_00_u03b1_322_, v_inst_323_, v_x_324_, v_x_325_);
v_r_327_ = lean_box(v_res_326_);
return v_r_327_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_instDecidableEqDecl___redArg(lean_object* v_inst_328_, lean_object* v_x_329_, lean_object* v_x_330_){
_start:
{
uint8_t v___x_331_; 
v___x_331_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v_inst_328_, v_x_329_, v_x_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instDecidableEqDecl___redArg___boxed(lean_object* v_inst_332_, lean_object* v_x_333_, lean_object* v_x_334_){
_start:
{
uint8_t v_res_335_; lean_object* v_r_336_; 
v_res_335_ = l_Std_Sat_AIG_instDecidableEqDecl___redArg(v_inst_332_, v_x_333_, v_x_334_);
v_r_336_ = lean_box(v_res_335_);
return v_r_336_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_instDecidableEqDecl(lean_object* v_00_u03b1_337_, lean_object* v_inst_338_, lean_object* v_x_339_, lean_object* v_x_340_){
_start:
{
uint8_t v___x_341_; 
v___x_341_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v_inst_338_, v_x_339_, v_x_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instDecidableEqDecl___boxed(lean_object* v_00_u03b1_342_, lean_object* v_inst_343_, lean_object* v_x_344_, lean_object* v_x_345_){
_start:
{
uint8_t v_res_346_; lean_object* v_r_347_; 
v_res_346_ = l_Std_Sat_AIG_instDecidableEqDecl(v_00_u03b1_342_, v_inst_343_, v_x_344_, v_x_345_);
v_r_347_ = lean_box(v_res_346_);
return v_r_347_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instInhabitedDecl_default(lean_object* v_00_u03b1_348_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = lean_box(0);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instInhabitedDecl(lean_object* v_a_350_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = lean_box(0);
return v___x_351_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___closed__0(void){
_start:
{
lean_object* v_cellCount_352_; lean_object* v___x_353_; 
v_cellCount_352_ = lean_unsigned_to_nat(16u);
v___x_353_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_352_);
return v___x_353_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___closed__1(void){
_start:
{
lean_object* v_cellCount_354_; lean_object* v___x_355_; 
v_cellCount_354_ = lean_unsigned_to_nat(16u);
v___x_355_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_354_);
return v___x_355_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___closed__2(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_356_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___closed__1, &l_Std_Sat_AIG_Cache_empty___closed__1_once, _init_l_Std_Sat_AIG_Cache_empty___closed__1);
v___x_357_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___closed__0, &l_Std_Sat_AIG_Cache_empty___closed__0_once, _init_l_Std_Sat_AIG_Cache_empty___closed__0);
v___x_358_ = lean_unsigned_to_nat(0u);
v___x_359_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
lean_ctor_set(v___x_359_, 1, v___x_357_);
lean_ctor_set(v___x_359_, 2, v___x_356_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_empty(lean_object* v_00_u03b1_360_, lean_object* v_inst_361_, lean_object* v_inst_362_, lean_object* v_decls_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___closed__2, &l_Std_Sat_AIG_Cache_empty___closed__2_once, _init_l_Std_Sat_AIG_Cache_empty___closed__2);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_empty___boxed(lean_object* v_00_u03b1_365_, lean_object* v_inst_366_, lean_object* v_inst_367_, lean_object* v_decls_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Std_Sat_AIG_Cache_empty(v_00_u03b1_365_, v_inst_366_, v_inst_367_, v_decls_368_);
lean_dec_ref(v_decls_368_);
lean_dec_ref(v_inst_367_);
lean_dec_ref(v_inst_366_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_noUpdate___redArg(lean_object* v_cache_370_){
_start:
{
lean_inc_ref(v_cache_370_);
return v_cache_370_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_noUpdate___redArg___boxed(lean_object* v_cache_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Std_Sat_AIG_Cache_noUpdate___redArg(v_cache_371_);
lean_dec_ref(v_cache_371_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_noUpdate(lean_object* v_00_u03b1_373_, lean_object* v_inst_374_, lean_object* v_inst_375_, lean_object* v_decls_376_, lean_object* v_decl_377_, lean_object* v_cache_378_){
_start:
{
lean_inc_ref(v_cache_378_);
return v_cache_378_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_noUpdate___boxed(lean_object* v_00_u03b1_379_, lean_object* v_inst_380_, lean_object* v_inst_381_, lean_object* v_decls_382_, lean_object* v_decl_383_, lean_object* v_cache_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Std_Sat_AIG_Cache_noUpdate(v_00_u03b1_379_, v_inst_380_, v_inst_381_, v_decls_382_, v_decl_383_, v_cache_384_);
lean_dec_ref(v_cache_384_);
lean_dec(v_decl_383_);
lean_dec_ref(v_decls_382_);
lean_dec_ref(v_inst_381_);
lean_dec_ref(v_inst_380_);
return v_res_385_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_Cache_insert___redArg___lam__0(lean_object* v_inst_386_, lean_object* v_a_387_, lean_object* v_b_388_){
_start:
{
uint8_t v___x_389_; 
v___x_389_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v_inst_386_, v_a_387_, v_b_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed(lean_object* v_inst_390_, lean_object* v_a_391_, lean_object* v_b_392_){
_start:
{
uint8_t v_res_393_; lean_object* v_r_394_; 
v_res_393_ = l_Std_Sat_AIG_Cache_insert___redArg___lam__0(v_inst_390_, v_a_391_, v_b_392_);
v_r_394_ = lean_box(v_res_393_);
return v_r_394_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___redArg(lean_object* v_inst_395_, lean_object* v_inst_396_, lean_object* v_decls_397_, lean_object* v_cache_398_, lean_object* v_decl_399_){
_start:
{
lean_object* v___f_400_; lean_object* v___x_401_; lean_object* v___f_402_; lean_object* v___x_403_; lean_object* v___y_405_; lean_object* v_i_406_; lean_object* v___y_412_; lean_object* v___y_422_; lean_object* v_i_423_; lean_object* v___x_438_; 
v___f_400_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_400_, 0, v_inst_396_);
v___x_401_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_401_, 0, lean_box(0));
lean_closure_set(v___x_401_, 1, v_inst_395_);
v___f_402_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_402_, 0, v___f_400_);
v___x_403_ = lean_array_get_size(v_decls_397_);
lean_inc(v_decl_399_);
lean_inc_ref(v___x_401_);
lean_inc_ref(v___f_402_);
v___x_438_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_402_, v___x_401_, v_cache_398_, v_decl_399_);
switch(lean_obj_tag(v___x_438_))
{
case 0:
{
lean_object* v_index_439_; lean_object* v_size_440_; lean_object* v___x_441_; 
lean_dec_ref(v___f_402_);
lean_dec_ref(v___x_401_);
v_index_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_index_439_);
lean_dec_ref_known(v___x_438_, 3);
v_size_440_ = lean_ctor_get(v_cache_398_, 0);
lean_inc(v_size_440_);
v___x_441_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cache_398_, v_size_440_, v_index_439_, v_decl_399_, v___x_403_);
lean_dec(v_index_439_);
return v___x_441_;
}
case 1:
{
lean_object* v_index_442_; lean_object* v_size_443_; lean_object* v_keyArray_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; uint8_t v___x_448_; 
v_index_442_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_index_442_);
lean_dec_ref_known(v___x_438_, 1);
v_size_443_ = lean_ctor_get(v_cache_398_, 0);
v_keyArray_444_ = lean_ctor_get(v_cache_398_, 1);
v___x_445_ = lean_unsigned_to_nat(1u);
v___x_446_ = lean_nat_add(v_size_443_, v___x_445_);
v___x_447_ = lean_array_get_size(v_keyArray_444_);
v___x_448_ = lean_nat_dec_lt(v___x_446_, v___x_447_);
if (v___x_448_ == 0)
{
lean_dec(v___x_446_);
lean_dec(v_index_442_);
goto v___jp_428_;
}
else
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_449_ = lean_unsigned_to_nat(4u);
v___x_450_ = lean_nat_mul(v___x_446_, v___x_449_);
v___x_451_ = lean_unsigned_to_nat(3u);
v___x_452_ = lean_nat_mul(v___x_447_, v___x_451_);
v___x_453_ = lean_nat_dec_le(v___x_450_, v___x_452_);
lean_dec(v___x_452_);
lean_dec(v___x_450_);
if (v___x_453_ == 0)
{
lean_dec(v___x_446_);
lean_dec(v_index_442_);
goto v___jp_428_;
}
else
{
lean_object* v___x_454_; 
lean_dec_ref(v___f_402_);
lean_dec_ref(v___x_401_);
v___x_454_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cache_398_, v___x_446_, v_index_442_, v_decl_399_, v___x_403_);
lean_dec(v_index_442_);
return v___x_454_;
}
}
}
default: 
{
lean_object* v_size_455_; lean_object* v_keyArray_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; uint8_t v___x_460_; 
v_size_455_ = lean_ctor_get(v_cache_398_, 0);
v_keyArray_456_ = lean_ctor_get(v_cache_398_, 1);
v___x_457_ = lean_unsigned_to_nat(1u);
v___x_458_ = lean_nat_add(v_size_455_, v___x_457_);
v___x_459_ = lean_array_get_size(v_keyArray_456_);
v___x_460_ = lean_nat_dec_lt(v___x_458_, v___x_459_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; 
lean_dec(v___x_458_);
lean_inc_ref(v___x_401_);
lean_inc_ref(v___f_402_);
v___x_461_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_402_, v___x_401_, v_cache_398_);
v___y_412_ = v___x_461_;
goto v___jp_411_;
}
else
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; uint8_t v___x_466_; 
v___x_462_ = lean_unsigned_to_nat(4u);
v___x_463_ = lean_nat_mul(v___x_458_, v___x_462_);
lean_dec(v___x_458_);
v___x_464_ = lean_unsigned_to_nat(3u);
v___x_465_ = lean_nat_mul(v___x_459_, v___x_464_);
v___x_466_ = lean_nat_dec_le(v___x_463_, v___x_465_);
lean_dec(v___x_465_);
lean_dec(v___x_463_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; 
lean_inc_ref(v___x_401_);
lean_inc_ref(v___f_402_);
v___x_467_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_402_, v___x_401_, v_cache_398_);
v___y_412_ = v___x_467_;
goto v___jp_411_;
}
else
{
v___y_412_ = v_cache_398_;
goto v___jp_411_;
}
}
}
}
v___jp_404_:
{
lean_object* v_size_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v_size_407_ = lean_ctor_get(v___y_405_, 0);
v___x_408_ = lean_unsigned_to_nat(1u);
v___x_409_ = lean_nat_add(v_size_407_, v___x_408_);
v___x_410_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_405_, v___x_409_, v_i_406_, v_decl_399_, v___x_403_);
lean_dec(v_i_406_);
return v___x_410_;
}
v___jp_411_:
{
lean_object* v___x_413_; 
lean_inc(v_decl_399_);
v___x_413_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_402_, v___x_401_, v___y_412_, v_decl_399_);
switch(lean_obj_tag(v___x_413_))
{
case 0:
{
lean_object* v_index_414_; lean_object* v_size_415_; lean_object* v___x_416_; 
v_index_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc(v_index_414_);
lean_dec_ref_known(v___x_413_, 3);
v_size_415_ = lean_ctor_get(v___y_412_, 0);
lean_inc(v_size_415_);
v___x_416_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_412_, v_size_415_, v_index_414_, v_decl_399_, v___x_403_);
lean_dec(v_index_414_);
return v___x_416_;
}
case 1:
{
lean_object* v_index_417_; 
v_index_417_ = lean_ctor_get(v___x_413_, 0);
lean_inc(v_index_417_);
lean_dec_ref_known(v___x_413_, 1);
v___y_405_ = v___y_412_;
v_i_406_ = v_index_417_;
goto v___jp_404_;
}
default: 
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = lean_unsigned_to_nat(0u);
v___x_419_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_412_, v___x_418_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_index_420_; 
v_index_420_ = lean_ctor_get(v___x_419_, 0);
lean_inc(v_index_420_);
lean_dec_ref_known(v___x_419_, 1);
v___y_405_ = v___y_412_;
v_i_406_ = v_index_420_;
goto v___jp_404_;
}
else
{
lean_dec(v_decl_399_);
return v___y_412_;
}
}
}
}
v___jp_421_:
{
lean_object* v_size_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v_size_424_ = lean_ctor_get(v___y_422_, 0);
v___x_425_ = lean_unsigned_to_nat(1u);
v___x_426_ = lean_nat_add(v_size_424_, v___x_425_);
v___x_427_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_422_, v___x_426_, v_i_423_, v_decl_399_, v___x_403_);
lean_dec(v_i_423_);
return v___x_427_;
}
v___jp_428_:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
lean_inc_ref(v___x_401_);
lean_inc_ref(v___f_402_);
v___x_429_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_402_, v___x_401_, v_cache_398_);
lean_inc(v_decl_399_);
v___x_430_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_402_, v___x_401_, v___x_429_, v_decl_399_);
switch(lean_obj_tag(v___x_430_))
{
case 0:
{
lean_object* v_index_431_; lean_object* v_size_432_; lean_object* v___x_433_; 
v_index_431_ = lean_ctor_get(v___x_430_, 0);
lean_inc(v_index_431_);
lean_dec_ref_known(v___x_430_, 3);
v_size_432_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_size_432_);
v___x_433_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_429_, v_size_432_, v_index_431_, v_decl_399_, v___x_403_);
lean_dec(v_index_431_);
return v___x_433_;
}
case 1:
{
lean_object* v_index_434_; 
v_index_434_ = lean_ctor_get(v___x_430_, 0);
lean_inc(v_index_434_);
lean_dec_ref_known(v___x_430_, 1);
v___y_422_ = v___x_429_;
v_i_423_ = v_index_434_;
goto v___jp_421_;
}
default: 
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = lean_unsigned_to_nat(0u);
v___x_436_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_429_, v___x_435_);
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v_index_437_; 
v_index_437_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_index_437_);
lean_dec_ref_known(v___x_436_, 1);
v___y_422_ = v___x_429_;
v_i_423_ = v_index_437_;
goto v___jp_421_;
}
else
{
lean_dec(v_decl_399_);
return v___x_429_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___redArg___boxed(lean_object* v_inst_468_, lean_object* v_inst_469_, lean_object* v_decls_470_, lean_object* v_cache_471_, lean_object* v_decl_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Std_Sat_AIG_Cache_insert___redArg(v_inst_468_, v_inst_469_, v_decls_470_, v_cache_471_, v_decl_472_);
lean_dec_ref(v_decls_470_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert(lean_object* v_00_u03b1_474_, lean_object* v_inst_475_, lean_object* v_inst_476_, lean_object* v_decls_477_, lean_object* v_cache_478_, lean_object* v_decl_479_){
_start:
{
lean_object* v___f_480_; lean_object* v___x_481_; lean_object* v___f_482_; lean_object* v___x_483_; lean_object* v___y_485_; lean_object* v_i_486_; lean_object* v___y_492_; lean_object* v___y_502_; lean_object* v_i_503_; lean_object* v___x_518_; 
v___f_480_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_480_, 0, v_inst_476_);
v___x_481_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_481_, 0, lean_box(0));
lean_closure_set(v___x_481_, 1, v_inst_475_);
v___f_482_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_482_, 0, v___f_480_);
v___x_483_ = lean_array_get_size(v_decls_477_);
lean_inc(v_decl_479_);
lean_inc_ref(v___x_481_);
lean_inc_ref(v___f_482_);
v___x_518_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_482_, v___x_481_, v_cache_478_, v_decl_479_);
switch(lean_obj_tag(v___x_518_))
{
case 0:
{
lean_object* v_index_519_; lean_object* v_size_520_; lean_object* v___x_521_; 
lean_dec_ref(v___f_482_);
lean_dec_ref(v___x_481_);
v_index_519_ = lean_ctor_get(v___x_518_, 0);
lean_inc(v_index_519_);
lean_dec_ref_known(v___x_518_, 3);
v_size_520_ = lean_ctor_get(v_cache_478_, 0);
lean_inc(v_size_520_);
v___x_521_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cache_478_, v_size_520_, v_index_519_, v_decl_479_, v___x_483_);
lean_dec(v_index_519_);
return v___x_521_;
}
case 1:
{
lean_object* v_index_522_; lean_object* v_size_523_; lean_object* v_keyArray_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; uint8_t v___x_528_; 
v_index_522_ = lean_ctor_get(v___x_518_, 0);
lean_inc(v_index_522_);
lean_dec_ref_known(v___x_518_, 1);
v_size_523_ = lean_ctor_get(v_cache_478_, 0);
v_keyArray_524_ = lean_ctor_get(v_cache_478_, 1);
v___x_525_ = lean_unsigned_to_nat(1u);
v___x_526_ = lean_nat_add(v_size_523_, v___x_525_);
v___x_527_ = lean_array_get_size(v_keyArray_524_);
v___x_528_ = lean_nat_dec_lt(v___x_526_, v___x_527_);
if (v___x_528_ == 0)
{
lean_dec(v___x_526_);
lean_dec(v_index_522_);
goto v___jp_508_;
}
else
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; uint8_t v___x_533_; 
v___x_529_ = lean_unsigned_to_nat(4u);
v___x_530_ = lean_nat_mul(v___x_526_, v___x_529_);
v___x_531_ = lean_unsigned_to_nat(3u);
v___x_532_ = lean_nat_mul(v___x_527_, v___x_531_);
v___x_533_ = lean_nat_dec_le(v___x_530_, v___x_532_);
lean_dec(v___x_532_);
lean_dec(v___x_530_);
if (v___x_533_ == 0)
{
lean_dec(v___x_526_);
lean_dec(v_index_522_);
goto v___jp_508_;
}
else
{
lean_object* v___x_534_; 
lean_dec_ref(v___f_482_);
lean_dec_ref(v___x_481_);
v___x_534_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cache_478_, v___x_526_, v_index_522_, v_decl_479_, v___x_483_);
lean_dec(v_index_522_);
return v___x_534_;
}
}
}
default: 
{
lean_object* v_size_535_; lean_object* v_keyArray_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; uint8_t v___x_540_; 
v_size_535_ = lean_ctor_get(v_cache_478_, 0);
v_keyArray_536_ = lean_ctor_get(v_cache_478_, 1);
v___x_537_ = lean_unsigned_to_nat(1u);
v___x_538_ = lean_nat_add(v_size_535_, v___x_537_);
v___x_539_ = lean_array_get_size(v_keyArray_536_);
v___x_540_ = lean_nat_dec_lt(v___x_538_, v___x_539_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; 
lean_dec(v___x_538_);
lean_inc_ref(v___x_481_);
lean_inc_ref(v___f_482_);
v___x_541_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_482_, v___x_481_, v_cache_478_);
v___y_492_ = v___x_541_;
goto v___jp_491_;
}
else
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; uint8_t v___x_546_; 
v___x_542_ = lean_unsigned_to_nat(4u);
v___x_543_ = lean_nat_mul(v___x_538_, v___x_542_);
lean_dec(v___x_538_);
v___x_544_ = lean_unsigned_to_nat(3u);
v___x_545_ = lean_nat_mul(v___x_539_, v___x_544_);
v___x_546_ = lean_nat_dec_le(v___x_543_, v___x_545_);
lean_dec(v___x_545_);
lean_dec(v___x_543_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; 
lean_inc_ref(v___x_481_);
lean_inc_ref(v___f_482_);
v___x_547_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_482_, v___x_481_, v_cache_478_);
v___y_492_ = v___x_547_;
goto v___jp_491_;
}
else
{
v___y_492_ = v_cache_478_;
goto v___jp_491_;
}
}
}
}
v___jp_484_:
{
lean_object* v_size_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v_size_487_ = lean_ctor_get(v___y_485_, 0);
v___x_488_ = lean_unsigned_to_nat(1u);
v___x_489_ = lean_nat_add(v_size_487_, v___x_488_);
v___x_490_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_485_, v___x_489_, v_i_486_, v_decl_479_, v___x_483_);
lean_dec(v_i_486_);
return v___x_490_;
}
v___jp_491_:
{
lean_object* v___x_493_; 
lean_inc(v_decl_479_);
v___x_493_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_482_, v___x_481_, v___y_492_, v_decl_479_);
switch(lean_obj_tag(v___x_493_))
{
case 0:
{
lean_object* v_index_494_; lean_object* v_size_495_; lean_object* v___x_496_; 
v_index_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_index_494_);
lean_dec_ref_known(v___x_493_, 3);
v_size_495_ = lean_ctor_get(v___y_492_, 0);
lean_inc(v_size_495_);
v___x_496_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_492_, v_size_495_, v_index_494_, v_decl_479_, v___x_483_);
lean_dec(v_index_494_);
return v___x_496_;
}
case 1:
{
lean_object* v_index_497_; 
v_index_497_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_index_497_);
lean_dec_ref_known(v___x_493_, 1);
v___y_485_ = v___y_492_;
v_i_486_ = v_index_497_;
goto v___jp_484_;
}
default: 
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = lean_unsigned_to_nat(0u);
v___x_499_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_492_, v___x_498_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_index_500_; 
v_index_500_ = lean_ctor_get(v___x_499_, 0);
lean_inc(v_index_500_);
lean_dec_ref_known(v___x_499_, 1);
v___y_485_ = v___y_492_;
v_i_486_ = v_index_500_;
goto v___jp_484_;
}
else
{
lean_dec(v_decl_479_);
return v___y_492_;
}
}
}
}
v___jp_501_:
{
lean_object* v_size_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v_size_504_ = lean_ctor_get(v___y_502_, 0);
v___x_505_ = lean_unsigned_to_nat(1u);
v___x_506_ = lean_nat_add(v_size_504_, v___x_505_);
v___x_507_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_502_, v___x_506_, v_i_503_, v_decl_479_, v___x_483_);
lean_dec(v_i_503_);
return v___x_507_;
}
v___jp_508_:
{
lean_object* v___x_509_; lean_object* v___x_510_; 
lean_inc_ref(v___x_481_);
lean_inc_ref(v___f_482_);
v___x_509_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_482_, v___x_481_, v_cache_478_);
lean_inc(v_decl_479_);
v___x_510_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_482_, v___x_481_, v___x_509_, v_decl_479_);
switch(lean_obj_tag(v___x_510_))
{
case 0:
{
lean_object* v_index_511_; lean_object* v_size_512_; lean_object* v___x_513_; 
v_index_511_ = lean_ctor_get(v___x_510_, 0);
lean_inc(v_index_511_);
lean_dec_ref_known(v___x_510_, 3);
v_size_512_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_size_512_);
v___x_513_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_509_, v_size_512_, v_index_511_, v_decl_479_, v___x_483_);
lean_dec(v_index_511_);
return v___x_513_;
}
case 1:
{
lean_object* v_index_514_; 
v_index_514_ = lean_ctor_get(v___x_510_, 0);
lean_inc(v_index_514_);
lean_dec_ref_known(v___x_510_, 1);
v___y_502_ = v___x_509_;
v_i_503_ = v_index_514_;
goto v___jp_501_;
}
default: 
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_unsigned_to_nat(0u);
v___x_516_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_509_, v___x_515_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v_index_517_; 
v_index_517_ = lean_ctor_get(v___x_516_, 0);
lean_inc(v_index_517_);
lean_dec_ref_known(v___x_516_, 1);
v___y_502_ = v___x_509_;
v_i_503_ = v_index_517_;
goto v___jp_501_;
}
else
{
lean_dec(v_decl_479_);
return v___x_509_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___boxed(lean_object* v_00_u03b1_548_, lean_object* v_inst_549_, lean_object* v_inst_550_, lean_object* v_decls_551_, lean_object* v_cache_552_, lean_object* v_decl_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Std_Sat_AIG_Cache_insert(v_00_u03b1_548_, v_inst_549_, v_inst_550_, v_decls_551_, v_cache_552_, v_decl_553_);
lean_dec_ref(v_decls_551_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f___redArg(lean_object* v_inst_555_, lean_object* v_inst_556_, lean_object* v_cache_557_, lean_object* v_decl_558_){
_start:
{
lean_object* v___f_559_; lean_object* v___x_560_; lean_object* v___f_561_; lean_object* v___x_562_; 
v___f_559_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_559_, 0, v_inst_556_);
v___x_560_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_560_, 0, lean_box(0));
lean_closure_set(v___x_560_, 1, v_inst_555_);
v___f_561_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_561_, 0, v___f_559_);
v___x_562_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_561_, v___x_560_, v_cache_557_, v_decl_558_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v___x_563_; 
v___x_563_ = lean_box(0);
return v___x_563_;
}
else
{
lean_object* v_val_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
v_val_564_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v___x_562_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_val_564_);
lean_dec(v___x_562_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_567_ == 0)
{
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_val_564_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f___redArg___boxed(lean_object* v_inst_572_, lean_object* v_inst_573_, lean_object* v_cache_574_, lean_object* v_decl_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Std_Sat_AIG_Cache_get_x3f___redArg(v_inst_572_, v_inst_573_, v_cache_574_, v_decl_575_);
lean_dec_ref(v_cache_574_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f(lean_object* v_00_u03b1_577_, lean_object* v_inst_578_, lean_object* v_inst_579_, lean_object* v_decls_580_, lean_object* v_cache_581_, lean_object* v_decl_582_){
_start:
{
lean_object* v___f_583_; lean_object* v___x_584_; lean_object* v___f_585_; lean_object* v___x_586_; 
v___f_583_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_583_, 0, v_inst_579_);
v___x_584_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_584_, 0, lean_box(0));
lean_closure_set(v___x_584_, 1, v_inst_578_);
v___f_585_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_585_, 0, v___f_583_);
v___x_586_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_585_, v___x_584_, v_cache_581_, v_decl_582_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v___x_587_; 
v___x_587_ = lean_box(0);
return v___x_587_;
}
else
{
lean_object* v_val_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_595_; 
v_val_588_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_595_ == 0)
{
v___x_590_ = v___x_586_;
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_val_588_);
lean_dec(v___x_586_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_593_; 
if (v_isShared_591_ == 0)
{
v___x_593_ = v___x_590_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_val_588_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f___boxed(lean_object* v_00_u03b1_596_, lean_object* v_inst_597_, lean_object* v_inst_598_, lean_object* v_decls_599_, lean_object* v_cache_600_, lean_object* v_decl_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Std_Sat_AIG_Cache_get_x3f(v_00_u03b1_596_, v_inst_597_, v_inst_598_, v_decls_599_, v_cache_600_, v_decl_601_);
lean_dec_ref(v_cache_600_);
lean_dec_ref(v_decls_599_);
return v_res_602_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___closed__1(void){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_607_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___closed__2, &l_Std_Sat_AIG_Cache_empty___closed__2_once, _init_l_Std_Sat_AIG_Cache_empty___closed__2);
v___x_608_ = ((lean_object*)(l_Std_Sat_AIG_empty___closed__0));
v___x_609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
lean_ctor_set(v___x_609_, 1, v___x_607_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_empty(lean_object* v_00_u03b1_610_, lean_object* v_inst_611_, lean_object* v_inst_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = lean_obj_once(&l_Std_Sat_AIG_empty___closed__1, &l_Std_Sat_AIG_empty___closed__1_once, _init_l_Std_Sat_AIG_empty___closed__1);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_empty___boxed(lean_object* v_00_u03b1_614_, lean_object* v_inst_615_, lean_object* v_inst_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Std_Sat_AIG_empty(v_00_u03b1_614_, v_inst_615_, v_inst_616_);
lean_dec_ref(v_inst_616_);
lean_dec_ref(v_inst_615_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instMembership(lean_object* v_00_u03b1_618_, lean_object* v_inst_619_, lean_object* v_inst_620_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = lean_box(0);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instMembership___boxed(lean_object* v_00_u03b1_622_, lean_object* v_inst_623_, lean_object* v_inst_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Std_Sat_AIG_instMembership(v_00_u03b1_622_, v_inst_623_, v_inst_624_);
lean_dec_ref(v_inst_624_);
lean_dec_ref(v_inst_623_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_cast___redArg(lean_object* v_ref_626_){
_start:
{
lean_object* v_gate_627_; uint8_t v_invert_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_635_; 
v_gate_627_ = lean_ctor_get(v_ref_626_, 0);
v_invert_628_ = lean_ctor_get_uint8(v_ref_626_, sizeof(void*)*1);
v_isSharedCheck_635_ = !lean_is_exclusive(v_ref_626_);
if (v_isSharedCheck_635_ == 0)
{
v___x_630_ = v_ref_626_;
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_gate_627_);
lean_dec(v_ref_626_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_633_; 
if (v_isShared_631_ == 0)
{
v___x_633_ = v___x_630_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_gate_627_);
lean_ctor_set_uint8(v_reuseFailAlloc_634_, sizeof(void*)*1, v_invert_628_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_cast(lean_object* v_00_u03b1_636_, lean_object* v_inst_637_, lean_object* v_inst_638_, lean_object* v_aig1_639_, lean_object* v_aig2_640_, lean_object* v_ref_641_, lean_object* v_h_642_){
_start:
{
lean_object* v_gate_643_; uint8_t v_invert_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_651_; 
v_gate_643_ = lean_ctor_get(v_ref_641_, 0);
v_invert_644_ = lean_ctor_get_uint8(v_ref_641_, sizeof(void*)*1);
v_isSharedCheck_651_ = !lean_is_exclusive(v_ref_641_);
if (v_isSharedCheck_651_ == 0)
{
v___x_646_ = v_ref_641_;
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_gate_643_);
lean_dec(v_ref_641_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_649_; 
if (v_isShared_647_ == 0)
{
v___x_649_ = v___x_646_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_gate_643_);
lean_ctor_set_uint8(v_reuseFailAlloc_650_, sizeof(void*)*1, v_invert_644_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_cast___boxed(lean_object* v_00_u03b1_652_, lean_object* v_inst_653_, lean_object* v_inst_654_, lean_object* v_aig1_655_, lean_object* v_aig2_656_, lean_object* v_ref_657_, lean_object* v_h_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Std_Sat_AIG_Ref_cast(v_00_u03b1_652_, v_inst_653_, v_inst_654_, v_aig1_655_, v_aig2_656_, v_ref_657_, v_h_658_);
lean_dec_ref(v_aig2_656_);
lean_dec_ref(v_aig1_655_);
lean_dec_ref(v_inst_654_);
lean_dec_ref(v_inst_653_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_flip___redArg(lean_object* v_ref_660_, uint8_t v_inv_661_){
_start:
{
lean_object* v_gate_662_; uint8_t v_invert_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_675_; 
v_gate_662_ = lean_ctor_get(v_ref_660_, 0);
v_invert_663_ = lean_ctor_get_uint8(v_ref_660_, sizeof(void*)*1);
v_isSharedCheck_675_ = !lean_is_exclusive(v_ref_660_);
if (v_isSharedCheck_675_ == 0)
{
v___x_665_ = v_ref_660_;
v_isShared_666_ = v_isSharedCheck_675_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_gate_662_);
lean_dec(v_ref_660_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_675_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
if (v_inv_661_ == 0)
{
if (v_invert_663_ == 0)
{
lean_del_object(v___x_665_);
goto v___jp_672_;
}
else
{
goto v___jp_667_;
}
}
else
{
if (v_invert_663_ == 0)
{
goto v___jp_667_;
}
else
{
lean_del_object(v___x_665_);
goto v___jp_672_;
}
}
v___jp_667_:
{
uint8_t v___x_668_; lean_object* v___x_670_; 
v___x_668_ = 1;
if (v_isShared_666_ == 0)
{
v___x_670_ = v___x_665_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_gate_662_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
lean_ctor_set_uint8(v___x_670_, sizeof(void*)*1, v___x_668_);
return v___x_670_;
}
}
v___jp_672_:
{
uint8_t v___x_673_; lean_object* v___x_674_; 
v___x_673_ = 0;
v___x_674_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_674_, 0, v_gate_662_);
lean_ctor_set_uint8(v___x_674_, sizeof(void*)*1, v___x_673_);
return v___x_674_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_flip___redArg___boxed(lean_object* v_ref_676_, lean_object* v_inv_677_){
_start:
{
uint8_t v_inv_boxed_678_; lean_object* v_res_679_; 
v_inv_boxed_678_ = lean_unbox(v_inv_677_);
v_res_679_ = l_Std_Sat_AIG_Ref_flip___redArg(v_ref_676_, v_inv_boxed_678_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_flip(lean_object* v_00_u03b1_680_, lean_object* v_inst_681_, lean_object* v_inst_682_, lean_object* v_aig_683_, lean_object* v_ref_684_, uint8_t v_inv_685_){
_start:
{
lean_object* v_gate_686_; uint8_t v_invert_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_699_; 
v_gate_686_ = lean_ctor_get(v_ref_684_, 0);
v_invert_687_ = lean_ctor_get_uint8(v_ref_684_, sizeof(void*)*1);
v_isSharedCheck_699_ = !lean_is_exclusive(v_ref_684_);
if (v_isSharedCheck_699_ == 0)
{
v___x_689_ = v_ref_684_;
v_isShared_690_ = v_isSharedCheck_699_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_gate_686_);
lean_dec(v_ref_684_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_699_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
if (v_inv_685_ == 0)
{
if (v_invert_687_ == 0)
{
lean_del_object(v___x_689_);
goto v___jp_696_;
}
else
{
goto v___jp_691_;
}
}
else
{
if (v_invert_687_ == 0)
{
goto v___jp_691_;
}
else
{
lean_del_object(v___x_689_);
goto v___jp_696_;
}
}
v___jp_691_:
{
uint8_t v___x_692_; lean_object* v___x_694_; 
v___x_692_ = 1;
if (v_isShared_690_ == 0)
{
v___x_694_ = v___x_689_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_gate_686_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
lean_ctor_set_uint8(v___x_694_, sizeof(void*)*1, v___x_692_);
return v___x_694_;
}
}
v___jp_696_:
{
uint8_t v___x_697_; lean_object* v___x_698_; 
v___x_697_ = 0;
v___x_698_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_698_, 0, v_gate_686_);
lean_ctor_set_uint8(v___x_698_, sizeof(void*)*1, v___x_697_);
return v___x_698_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_flip___boxed(lean_object* v_00_u03b1_700_, lean_object* v_inst_701_, lean_object* v_inst_702_, lean_object* v_aig_703_, lean_object* v_ref_704_, lean_object* v_inv_705_){
_start:
{
uint8_t v_inv_boxed_706_; lean_object* v_res_707_; 
v_inv_boxed_706_ = lean_unbox(v_inv_705_);
v_res_707_ = l_Std_Sat_AIG_Ref_flip(v_00_u03b1_700_, v_inst_701_, v_inst_702_, v_aig_703_, v_ref_704_, v_inv_boxed_706_);
lean_dec_ref(v_aig_703_);
lean_dec_ref(v_inst_702_);
lean_dec_ref(v_inst_701_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_not___redArg(lean_object* v_ref_708_){
_start:
{
uint8_t v_invert_709_; 
v_invert_709_ = lean_ctor_get_uint8(v_ref_708_, sizeof(void*)*1);
if (v_invert_709_ == 0)
{
lean_object* v_gate_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_718_; 
v_gate_710_ = lean_ctor_get(v_ref_708_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v_ref_708_);
if (v_isSharedCheck_718_ == 0)
{
v___x_712_ = v_ref_708_;
v_isShared_713_ = v_isSharedCheck_718_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_gate_710_);
lean_dec(v_ref_708_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_718_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
uint8_t v___x_714_; lean_object* v___x_716_; 
v___x_714_ = 1;
if (v_isShared_713_ == 0)
{
v___x_716_ = v___x_712_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_gate_710_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_ctor_set_uint8(v___x_716_, sizeof(void*)*1, v___x_714_);
return v___x_716_;
}
}
}
else
{
lean_object* v_gate_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_727_; 
v_gate_719_ = lean_ctor_get(v_ref_708_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v_ref_708_);
if (v_isSharedCheck_727_ == 0)
{
v___x_721_ = v_ref_708_;
v_isShared_722_ = v_isSharedCheck_727_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_gate_719_);
lean_dec(v_ref_708_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_727_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
uint8_t v___x_723_; lean_object* v___x_725_; 
v___x_723_ = 0;
if (v_isShared_722_ == 0)
{
v___x_725_ = v___x_721_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_gate_719_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
lean_ctor_set_uint8(v___x_725_, sizeof(void*)*1, v___x_723_);
return v___x_725_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_not(lean_object* v_00_u03b1_728_, lean_object* v_inst_729_, lean_object* v_inst_730_, lean_object* v_aig_731_, lean_object* v_ref_732_){
_start:
{
uint8_t v_invert_733_; 
v_invert_733_ = lean_ctor_get_uint8(v_ref_732_, sizeof(void*)*1);
if (v_invert_733_ == 0)
{
lean_object* v_gate_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_742_; 
v_gate_734_ = lean_ctor_get(v_ref_732_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v_ref_732_);
if (v_isSharedCheck_742_ == 0)
{
v___x_736_ = v_ref_732_;
v_isShared_737_ = v_isSharedCheck_742_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_gate_734_);
lean_dec(v_ref_732_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_742_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
uint8_t v___x_738_; lean_object* v___x_740_; 
v___x_738_ = 1;
if (v_isShared_737_ == 0)
{
v___x_740_ = v___x_736_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_gate_734_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
lean_ctor_set_uint8(v___x_740_, sizeof(void*)*1, v___x_738_);
return v___x_740_;
}
}
}
else
{
lean_object* v_gate_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_751_; 
v_gate_743_ = lean_ctor_get(v_ref_732_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v_ref_732_);
if (v_isSharedCheck_751_ == 0)
{
v___x_745_ = v_ref_732_;
v_isShared_746_ = v_isSharedCheck_751_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_gate_743_);
lean_dec(v_ref_732_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_751_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
uint8_t v___x_747_; lean_object* v___x_749_; 
v___x_747_ = 0;
if (v_isShared_746_ == 0)
{
v___x_749_ = v___x_745_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_gate_743_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_ctor_set_uint8(v___x_749_, sizeof(void*)*1, v___x_747_);
return v___x_749_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_not___boxed(lean_object* v_00_u03b1_752_, lean_object* v_inst_753_, lean_object* v_inst_754_, lean_object* v_aig_755_, lean_object* v_ref_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Std_Sat_AIG_Ref_not(v_00_u03b1_752_, v_inst_753_, v_inst_754_, v_aig_755_, v_ref_756_);
lean_dec_ref(v_aig_755_);
lean_dec_ref(v_inst_754_);
lean_dec_ref(v_inst_753_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_cast___redArg(lean_object* v_input_758_){
_start:
{
lean_object* v_lhs_759_; lean_object* v_rhs_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_785_; 
v_lhs_759_ = lean_ctor_get(v_input_758_, 0);
v_rhs_760_ = lean_ctor_get(v_input_758_, 1);
v_isSharedCheck_785_ = !lean_is_exclusive(v_input_758_);
if (v_isSharedCheck_785_ == 0)
{
v___x_762_ = v_input_758_;
v_isShared_763_ = v_isSharedCheck_785_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_rhs_760_);
lean_inc(v_lhs_759_);
lean_dec(v_input_758_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_785_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v_gate_764_; uint8_t v_invert_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_784_; 
v_gate_764_ = lean_ctor_get(v_lhs_759_, 0);
v_invert_765_ = lean_ctor_get_uint8(v_lhs_759_, sizeof(void*)*1);
v_isSharedCheck_784_ = !lean_is_exclusive(v_lhs_759_);
if (v_isSharedCheck_784_ == 0)
{
v___x_767_ = v_lhs_759_;
v_isShared_768_ = v_isSharedCheck_784_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_gate_764_);
lean_dec(v_lhs_759_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_784_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v_gate_769_; uint8_t v_invert_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_783_; 
v_gate_769_ = lean_ctor_get(v_rhs_760_, 0);
v_invert_770_ = lean_ctor_get_uint8(v_rhs_760_, sizeof(void*)*1);
v_isSharedCheck_783_ = !lean_is_exclusive(v_rhs_760_);
if (v_isSharedCheck_783_ == 0)
{
v___x_772_ = v_rhs_760_;
v_isShared_773_ = v_isSharedCheck_783_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_gate_769_);
lean_dec(v_rhs_760_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_783_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v_gate_764_);
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_gate_764_);
v___x_775_ = v_reuseFailAlloc_782_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
lean_object* v___x_777_; 
lean_ctor_set_uint8(v___x_775_, sizeof(void*)*1, v_invert_765_);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 0, v_gate_769_);
v___x_777_ = v___x_767_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_gate_769_);
v___x_777_ = v_reuseFailAlloc_781_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
lean_object* v___x_779_; 
lean_ctor_set_uint8(v___x_777_, sizeof(void*)*1, v_invert_770_);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 1, v___x_777_);
lean_ctor_set(v___x_762_, 0, v___x_775_);
v___x_779_ = v___x_762_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_775_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v___x_777_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_cast(lean_object* v_00_u03b1_786_, lean_object* v_inst_787_, lean_object* v_inst_788_, lean_object* v_aig1_789_, lean_object* v_aig2_790_, lean_object* v_input_791_, lean_object* v_h_792_){
_start:
{
lean_object* v_lhs_793_; lean_object* v_rhs_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_819_; 
v_lhs_793_ = lean_ctor_get(v_input_791_, 0);
v_rhs_794_ = lean_ctor_get(v_input_791_, 1);
v_isSharedCheck_819_ = !lean_is_exclusive(v_input_791_);
if (v_isSharedCheck_819_ == 0)
{
v___x_796_ = v_input_791_;
v_isShared_797_ = v_isSharedCheck_819_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_rhs_794_);
lean_inc(v_lhs_793_);
lean_dec(v_input_791_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_819_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v_gate_798_; uint8_t v_invert_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_818_; 
v_gate_798_ = lean_ctor_get(v_lhs_793_, 0);
v_invert_799_ = lean_ctor_get_uint8(v_lhs_793_, sizeof(void*)*1);
v_isSharedCheck_818_ = !lean_is_exclusive(v_lhs_793_);
if (v_isSharedCheck_818_ == 0)
{
v___x_801_ = v_lhs_793_;
v_isShared_802_ = v_isSharedCheck_818_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_gate_798_);
lean_dec(v_lhs_793_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_818_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v_gate_803_; uint8_t v_invert_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_817_; 
v_gate_803_ = lean_ctor_get(v_rhs_794_, 0);
v_invert_804_ = lean_ctor_get_uint8(v_rhs_794_, sizeof(void*)*1);
v_isSharedCheck_817_ = !lean_is_exclusive(v_rhs_794_);
if (v_isSharedCheck_817_ == 0)
{
v___x_806_ = v_rhs_794_;
v_isShared_807_ = v_isSharedCheck_817_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_gate_803_);
lean_dec(v_rhs_794_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_817_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 0, v_gate_798_);
v___x_809_ = v___x_806_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_gate_798_);
v___x_809_ = v_reuseFailAlloc_816_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
lean_object* v___x_811_; 
lean_ctor_set_uint8(v___x_809_, sizeof(void*)*1, v_invert_799_);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 0, v_gate_803_);
v___x_811_ = v___x_801_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_gate_803_);
v___x_811_ = v_reuseFailAlloc_815_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
lean_object* v___x_813_; 
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*1, v_invert_804_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 1, v___x_811_);
lean_ctor_set(v___x_796_, 0, v___x_809_);
v___x_813_ = v___x_796_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_809_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v___x_811_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_cast___boxed(lean_object* v_00_u03b1_820_, lean_object* v_inst_821_, lean_object* v_inst_822_, lean_object* v_aig1_823_, lean_object* v_aig2_824_, lean_object* v_input_825_, lean_object* v_h_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Std_Sat_AIG_BinaryInput_cast(v_00_u03b1_820_, v_inst_821_, v_inst_822_, v_aig1_823_, v_aig2_824_, v_input_825_, v_h_826_);
lean_dec_ref(v_aig2_824_);
lean_dec_ref(v_aig1_823_);
lean_dec_ref(v_inst_822_);
lean_dec_ref(v_inst_821_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_invert___redArg(lean_object* v_input_828_, uint8_t v_linv_829_, uint8_t v_rinv_830_){
_start:
{
lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v_lhs_843_; lean_object* v_rhs_844_; lean_object* v___y_846_; lean_object* v_gate_853_; uint8_t v_invert_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_866_; 
v_lhs_843_ = lean_ctor_get(v_input_828_, 0);
lean_inc_ref(v_lhs_843_);
v_rhs_844_ = lean_ctor_get(v_input_828_, 1);
lean_inc_ref(v_rhs_844_);
lean_dec_ref(v_input_828_);
v_gate_853_ = lean_ctor_get(v_lhs_843_, 0);
v_invert_854_ = lean_ctor_get_uint8(v_lhs_843_, sizeof(void*)*1);
v_isSharedCheck_866_ = !lean_is_exclusive(v_lhs_843_);
if (v_isSharedCheck_866_ == 0)
{
v___x_856_ = v_lhs_843_;
v_isShared_857_ = v_isSharedCheck_866_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_gate_853_);
lean_dec(v_lhs_843_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_866_;
goto v_resetjp_855_;
}
v___jp_831_:
{
uint8_t v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_834_ = 0;
v___x_835_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_835_, 0, v___y_833_);
lean_ctor_set_uint8(v___x_835_, sizeof(void*)*1, v___x_834_);
v___x_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_836_, 0, v___y_832_);
lean_ctor_set(v___x_836_, 1, v___x_835_);
return v___x_836_;
}
v___jp_837_:
{
uint8_t v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_840_ = 1;
v___x_841_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_841_, 0, v___y_839_);
lean_ctor_set_uint8(v___x_841_, sizeof(void*)*1, v___x_840_);
v___x_842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_842_, 0, v___y_838_);
lean_ctor_set(v___x_842_, 1, v___x_841_);
return v___x_842_;
}
v___jp_845_:
{
if (v_rinv_830_ == 0)
{
uint8_t v_invert_847_; 
v_invert_847_ = lean_ctor_get_uint8(v_rhs_844_, sizeof(void*)*1);
if (v_invert_847_ == 0)
{
lean_object* v_gate_848_; 
v_gate_848_ = lean_ctor_get(v_rhs_844_, 0);
lean_inc(v_gate_848_);
lean_dec_ref(v_rhs_844_);
v___y_832_ = v___y_846_;
v___y_833_ = v_gate_848_;
goto v___jp_831_;
}
else
{
lean_object* v_gate_849_; 
v_gate_849_ = lean_ctor_get(v_rhs_844_, 0);
lean_inc(v_gate_849_);
lean_dec_ref(v_rhs_844_);
v___y_838_ = v___y_846_;
v___y_839_ = v_gate_849_;
goto v___jp_837_;
}
}
else
{
uint8_t v_invert_850_; 
v_invert_850_ = lean_ctor_get_uint8(v_rhs_844_, sizeof(void*)*1);
if (v_invert_850_ == 0)
{
lean_object* v_gate_851_; 
v_gate_851_ = lean_ctor_get(v_rhs_844_, 0);
lean_inc(v_gate_851_);
lean_dec_ref(v_rhs_844_);
v___y_838_ = v___y_846_;
v___y_839_ = v_gate_851_;
goto v___jp_837_;
}
else
{
lean_object* v_gate_852_; 
v_gate_852_ = lean_ctor_get(v_rhs_844_, 0);
lean_inc(v_gate_852_);
lean_dec_ref(v_rhs_844_);
v___y_832_ = v___y_846_;
v___y_833_ = v_gate_852_;
goto v___jp_831_;
}
}
}
v_resetjp_855_:
{
if (v_linv_829_ == 0)
{
if (v_invert_854_ == 0)
{
lean_del_object(v___x_856_);
goto v___jp_863_;
}
else
{
goto v___jp_858_;
}
}
else
{
if (v_invert_854_ == 0)
{
goto v___jp_858_;
}
else
{
lean_del_object(v___x_856_);
goto v___jp_863_;
}
}
v___jp_858_:
{
uint8_t v___x_859_; lean_object* v___x_861_; 
v___x_859_ = 1;
if (v_isShared_857_ == 0)
{
v___x_861_ = v___x_856_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_gate_853_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
lean_ctor_set_uint8(v___x_861_, sizeof(void*)*1, v___x_859_);
v___y_846_ = v___x_861_;
goto v___jp_845_;
}
}
v___jp_863_:
{
uint8_t v___x_864_; lean_object* v___x_865_; 
v___x_864_ = 0;
v___x_865_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_865_, 0, v_gate_853_);
lean_ctor_set_uint8(v___x_865_, sizeof(void*)*1, v___x_864_);
v___y_846_ = v___x_865_;
goto v___jp_845_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_invert___redArg___boxed(lean_object* v_input_867_, lean_object* v_linv_868_, lean_object* v_rinv_869_){
_start:
{
uint8_t v_linv_boxed_870_; uint8_t v_rinv_boxed_871_; lean_object* v_res_872_; 
v_linv_boxed_870_ = lean_unbox(v_linv_868_);
v_rinv_boxed_871_ = lean_unbox(v_rinv_869_);
v_res_872_ = l_Std_Sat_AIG_BinaryInput_invert___redArg(v_input_867_, v_linv_boxed_870_, v_rinv_boxed_871_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_invert(lean_object* v_00_u03b1_873_, lean_object* v_inst_874_, lean_object* v_inst_875_, lean_object* v_aig_876_, lean_object* v_input_877_, uint8_t v_linv_878_, uint8_t v_rinv_879_){
_start:
{
lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v_lhs_892_; lean_object* v_rhs_893_; lean_object* v___y_895_; lean_object* v_gate_902_; uint8_t v_invert_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_915_; 
v_lhs_892_ = lean_ctor_get(v_input_877_, 0);
lean_inc_ref(v_lhs_892_);
v_rhs_893_ = lean_ctor_get(v_input_877_, 1);
lean_inc_ref(v_rhs_893_);
lean_dec_ref(v_input_877_);
v_gate_902_ = lean_ctor_get(v_lhs_892_, 0);
v_invert_903_ = lean_ctor_get_uint8(v_lhs_892_, sizeof(void*)*1);
v_isSharedCheck_915_ = !lean_is_exclusive(v_lhs_892_);
if (v_isSharedCheck_915_ == 0)
{
v___x_905_ = v_lhs_892_;
v_isShared_906_ = v_isSharedCheck_915_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_gate_902_);
lean_dec(v_lhs_892_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_915_;
goto v_resetjp_904_;
}
v___jp_880_:
{
uint8_t v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_883_ = 0;
v___x_884_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_884_, 0, v___y_882_);
lean_ctor_set_uint8(v___x_884_, sizeof(void*)*1, v___x_883_);
v___x_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_885_, 0, v___y_881_);
lean_ctor_set(v___x_885_, 1, v___x_884_);
return v___x_885_;
}
v___jp_886_:
{
uint8_t v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_889_ = 1;
v___x_890_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_890_, 0, v___y_888_);
lean_ctor_set_uint8(v___x_890_, sizeof(void*)*1, v___x_889_);
v___x_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_891_, 0, v___y_887_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
return v___x_891_;
}
v___jp_894_:
{
if (v_rinv_879_ == 0)
{
uint8_t v_invert_896_; 
v_invert_896_ = lean_ctor_get_uint8(v_rhs_893_, sizeof(void*)*1);
if (v_invert_896_ == 0)
{
lean_object* v_gate_897_; 
v_gate_897_ = lean_ctor_get(v_rhs_893_, 0);
lean_inc(v_gate_897_);
lean_dec_ref(v_rhs_893_);
v___y_881_ = v___y_895_;
v___y_882_ = v_gate_897_;
goto v___jp_880_;
}
else
{
lean_object* v_gate_898_; 
v_gate_898_ = lean_ctor_get(v_rhs_893_, 0);
lean_inc(v_gate_898_);
lean_dec_ref(v_rhs_893_);
v___y_887_ = v___y_895_;
v___y_888_ = v_gate_898_;
goto v___jp_886_;
}
}
else
{
uint8_t v_invert_899_; 
v_invert_899_ = lean_ctor_get_uint8(v_rhs_893_, sizeof(void*)*1);
if (v_invert_899_ == 0)
{
lean_object* v_gate_900_; 
v_gate_900_ = lean_ctor_get(v_rhs_893_, 0);
lean_inc(v_gate_900_);
lean_dec_ref(v_rhs_893_);
v___y_887_ = v___y_895_;
v___y_888_ = v_gate_900_;
goto v___jp_886_;
}
else
{
lean_object* v_gate_901_; 
v_gate_901_ = lean_ctor_get(v_rhs_893_, 0);
lean_inc(v_gate_901_);
lean_dec_ref(v_rhs_893_);
v___y_881_ = v___y_895_;
v___y_882_ = v_gate_901_;
goto v___jp_880_;
}
}
}
v_resetjp_904_:
{
if (v_linv_878_ == 0)
{
if (v_invert_903_ == 0)
{
lean_del_object(v___x_905_);
goto v___jp_912_;
}
else
{
goto v___jp_907_;
}
}
else
{
if (v_invert_903_ == 0)
{
goto v___jp_907_;
}
else
{
lean_del_object(v___x_905_);
goto v___jp_912_;
}
}
v___jp_907_:
{
uint8_t v___x_908_; lean_object* v___x_910_; 
v___x_908_ = 1;
if (v_isShared_906_ == 0)
{
v___x_910_ = v___x_905_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_gate_902_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*1, v___x_908_);
v___y_895_ = v___x_910_;
goto v___jp_894_;
}
}
v___jp_912_:
{
uint8_t v___x_913_; lean_object* v___x_914_; 
v___x_913_ = 0;
v___x_914_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_914_, 0, v_gate_902_);
lean_ctor_set_uint8(v___x_914_, sizeof(void*)*1, v___x_913_);
v___y_895_ = v___x_914_;
goto v___jp_894_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_invert___boxed(lean_object* v_00_u03b1_916_, lean_object* v_inst_917_, lean_object* v_inst_918_, lean_object* v_aig_919_, lean_object* v_input_920_, lean_object* v_linv_921_, lean_object* v_rinv_922_){
_start:
{
uint8_t v_linv_boxed_923_; uint8_t v_rinv_boxed_924_; lean_object* v_res_925_; 
v_linv_boxed_923_ = lean_unbox(v_linv_921_);
v_rinv_boxed_924_ = lean_unbox(v_rinv_922_);
v_res_925_ = l_Std_Sat_AIG_BinaryInput_invert(v_00_u03b1_916_, v_inst_917_, v_inst_918_, v_aig_919_, v_input_920_, v_linv_boxed_923_, v_rinv_boxed_924_);
lean_dec_ref(v_aig_919_);
lean_dec_ref(v_inst_918_);
lean_dec_ref(v_inst_917_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_TernaryInput_cast___redArg(lean_object* v_input_926_){
_start:
{
lean_object* v_discr_927_; lean_object* v_lhs_928_; lean_object* v_rhs_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_963_; 
v_discr_927_ = lean_ctor_get(v_input_926_, 0);
v_lhs_928_ = lean_ctor_get(v_input_926_, 1);
v_rhs_929_ = lean_ctor_get(v_input_926_, 2);
v_isSharedCheck_963_ = !lean_is_exclusive(v_input_926_);
if (v_isSharedCheck_963_ == 0)
{
v___x_931_ = v_input_926_;
v_isShared_932_ = v_isSharedCheck_963_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_rhs_929_);
lean_inc(v_lhs_928_);
lean_inc(v_discr_927_);
lean_dec(v_input_926_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_963_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v_gate_933_; uint8_t v_invert_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_962_; 
v_gate_933_ = lean_ctor_get(v_discr_927_, 0);
v_invert_934_ = lean_ctor_get_uint8(v_discr_927_, sizeof(void*)*1);
v_isSharedCheck_962_ = !lean_is_exclusive(v_discr_927_);
if (v_isSharedCheck_962_ == 0)
{
v___x_936_ = v_discr_927_;
v_isShared_937_ = v_isSharedCheck_962_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_gate_933_);
lean_dec(v_discr_927_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_962_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v_gate_938_; uint8_t v_invert_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_961_; 
v_gate_938_ = lean_ctor_get(v_lhs_928_, 0);
v_invert_939_ = lean_ctor_get_uint8(v_lhs_928_, sizeof(void*)*1);
v_isSharedCheck_961_ = !lean_is_exclusive(v_lhs_928_);
if (v_isSharedCheck_961_ == 0)
{
v___x_941_ = v_lhs_928_;
v_isShared_942_ = v_isSharedCheck_961_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_gate_938_);
lean_dec(v_lhs_928_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_961_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v_gate_943_; uint8_t v_invert_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_960_; 
v_gate_943_ = lean_ctor_get(v_rhs_929_, 0);
v_invert_944_ = lean_ctor_get_uint8(v_rhs_929_, sizeof(void*)*1);
v_isSharedCheck_960_ = !lean_is_exclusive(v_rhs_929_);
if (v_isSharedCheck_960_ == 0)
{
v___x_946_ = v_rhs_929_;
v_isShared_947_ = v_isSharedCheck_960_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_gate_943_);
lean_dec(v_rhs_929_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_960_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_949_; 
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 0, v_gate_933_);
v___x_949_ = v___x_946_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_gate_933_);
v___x_949_ = v_reuseFailAlloc_959_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
lean_object* v___x_951_; 
lean_ctor_set_uint8(v___x_949_, sizeof(void*)*1, v_invert_934_);
if (v_isShared_942_ == 0)
{
v___x_951_ = v___x_941_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_gate_938_);
lean_ctor_set_uint8(v_reuseFailAlloc_958_, sizeof(void*)*1, v_invert_939_);
v___x_951_ = v_reuseFailAlloc_958_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
lean_object* v___x_953_; 
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v_gate_943_);
v___x_953_ = v___x_936_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_gate_943_);
v___x_953_ = v_reuseFailAlloc_957_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
lean_object* v___x_955_; 
lean_ctor_set_uint8(v___x_953_, sizeof(void*)*1, v_invert_944_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 2, v___x_953_);
lean_ctor_set(v___x_931_, 1, v___x_951_);
lean_ctor_set(v___x_931_, 0, v___x_949_);
v___x_955_ = v___x_931_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v___x_949_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v___x_951_);
lean_ctor_set(v_reuseFailAlloc_956_, 2, v___x_953_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_TernaryInput_cast(lean_object* v_00_u03b1_964_, lean_object* v_inst_965_, lean_object* v_inst_966_, lean_object* v_aig1_967_, lean_object* v_aig2_968_, lean_object* v_input_969_, lean_object* v_h_970_){
_start:
{
lean_object* v_discr_971_; lean_object* v_lhs_972_; lean_object* v_rhs_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_1007_; 
v_discr_971_ = lean_ctor_get(v_input_969_, 0);
v_lhs_972_ = lean_ctor_get(v_input_969_, 1);
v_rhs_973_ = lean_ctor_get(v_input_969_, 2);
v_isSharedCheck_1007_ = !lean_is_exclusive(v_input_969_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_975_ = v_input_969_;
v_isShared_976_ = v_isSharedCheck_1007_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_rhs_973_);
lean_inc(v_lhs_972_);
lean_inc(v_discr_971_);
lean_dec(v_input_969_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_1007_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v_gate_977_; uint8_t v_invert_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_1006_; 
v_gate_977_ = lean_ctor_get(v_discr_971_, 0);
v_invert_978_ = lean_ctor_get_uint8(v_discr_971_, sizeof(void*)*1);
v_isSharedCheck_1006_ = !lean_is_exclusive(v_discr_971_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_980_ = v_discr_971_;
v_isShared_981_ = v_isSharedCheck_1006_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_gate_977_);
lean_dec(v_discr_971_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_1006_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v_gate_982_; uint8_t v_invert_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_1005_; 
v_gate_982_ = lean_ctor_get(v_lhs_972_, 0);
v_invert_983_ = lean_ctor_get_uint8(v_lhs_972_, sizeof(void*)*1);
v_isSharedCheck_1005_ = !lean_is_exclusive(v_lhs_972_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_985_ = v_lhs_972_;
v_isShared_986_ = v_isSharedCheck_1005_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_gate_982_);
lean_dec(v_lhs_972_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_1005_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v_gate_987_; uint8_t v_invert_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_1004_; 
v_gate_987_ = lean_ctor_get(v_rhs_973_, 0);
v_invert_988_ = lean_ctor_get_uint8(v_rhs_973_, sizeof(void*)*1);
v_isSharedCheck_1004_ = !lean_is_exclusive(v_rhs_973_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_990_ = v_rhs_973_;
v_isShared_991_ = v_isSharedCheck_1004_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_gate_987_);
lean_dec(v_rhs_973_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_1004_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 0, v_gate_977_);
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_gate_977_);
v___x_993_ = v_reuseFailAlloc_1003_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
lean_object* v___x_995_; 
lean_ctor_set_uint8(v___x_993_, sizeof(void*)*1, v_invert_978_);
if (v_isShared_986_ == 0)
{
v___x_995_ = v___x_985_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_gate_982_);
lean_ctor_set_uint8(v_reuseFailAlloc_1002_, sizeof(void*)*1, v_invert_983_);
v___x_995_ = v_reuseFailAlloc_1002_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
lean_object* v___x_997_; 
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 0, v_gate_987_);
v___x_997_ = v___x_980_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_gate_987_);
v___x_997_ = v_reuseFailAlloc_1001_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
lean_object* v___x_999_; 
lean_ctor_set_uint8(v___x_997_, sizeof(void*)*1, v_invert_988_);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 2, v___x_997_);
lean_ctor_set(v___x_975_, 1, v___x_995_);
lean_ctor_set(v___x_975_, 0, v___x_993_);
v___x_999_ = v___x_975_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_993_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v___x_995_);
lean_ctor_set(v_reuseFailAlloc_1000_, 2, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_TernaryInput_cast___boxed(lean_object* v_00_u03b1_1008_, lean_object* v_inst_1009_, lean_object* v_inst_1010_, lean_object* v_aig1_1011_, lean_object* v_aig2_1012_, lean_object* v_input_1013_, lean_object* v_h_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Std_Sat_AIG_TernaryInput_cast(v_00_u03b1_1008_, v_inst_1009_, v_inst_1010_, v_aig1_1011_, v_aig2_1012_, v_input_1013_, v_h_1014_);
lean_dec_ref(v_aig2_1012_);
lean_dec_ref(v_aig1_1011_);
lean_dec_ref(v_inst_1010_);
lean_dec_ref(v_inst_1009_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_invEdgeStyle(uint8_t v_isInv_1018_){
_start:
{
if (v_isInv_1018_ == 0)
{
lean_object* v___x_1019_; 
v___x_1019_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_invEdgeStyle___closed__0));
return v___x_1019_;
}
else
{
lean_object* v___x_1020_; 
v___x_1020_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_invEdgeStyle___closed__1));
return v___x_1020_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_invEdgeStyle___boxed(lean_object* v_isInv_1021_){
_start:
{
uint8_t v_isInv_boxed_1022_; lean_object* v_res_1023_; 
v_isInv_boxed_1022_ = lean_unbox(v_isInv_1021_);
v_res_1023_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v_isInv_boxed_1022_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___redArg(lean_object* v_acc_1028_, lean_object* v_decls_1029_, lean_object* v_idx_1030_, lean_object* v_a_1031_){
_start:
{
lean_object* v___y_1033_; uint8_t v___y_1034_; lean_object* v___y_1035_; lean_object* v___y_1036_; uint8_t v___y_1037_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___f_1062_; lean_object* v___f_1063_; uint8_t v___x_1064_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1069_; uint8_t v___y_1070_; lean_object* v___y_1077_; 
v___x_1060_ = lean_array_get_size(v_decls_1029_);
v___x_1061_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_1061_, 0, v___x_1060_);
v___f_1062_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1062_, 0, v___x_1061_);
v___f_1063_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___redArg___closed__3));
lean_inc(v_idx_1030_);
lean_inc_ref(v___f_1062_);
v___x_1064_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1062_, v___f_1063_, v_a_1031_, v_idx_1030_);
if (v___x_1064_ == 0)
{
lean_object* v___x_1088_; lean_object* v___y_1090_; lean_object* v_i_1091_; lean_object* v___y_1097_; lean_object* v___y_1107_; lean_object* v_i_1108_; lean_object* v___x_1123_; 
v___x_1088_ = lean_box(0);
lean_inc(v_idx_1030_);
lean_inc_ref(v___f_1062_);
v___x_1123_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_1062_, v___f_1063_, v_a_1031_, v_idx_1030_);
switch(lean_obj_tag(v___x_1123_))
{
case 0:
{
lean_dec_ref_known(v___x_1123_, 3);
lean_dec_ref(v___f_1062_);
v___y_1077_ = v_a_1031_;
goto v___jp_1076_;
}
case 1:
{
lean_object* v_index_1124_; lean_object* v_size_1125_; lean_object* v_keyArray_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; uint8_t v___x_1130_; 
v_index_1124_ = lean_ctor_get(v___x_1123_, 0);
lean_inc(v_index_1124_);
lean_dec_ref_known(v___x_1123_, 1);
v_size_1125_ = lean_ctor_get(v_a_1031_, 0);
v_keyArray_1126_ = lean_ctor_get(v_a_1031_, 1);
v___x_1127_ = lean_unsigned_to_nat(1u);
v___x_1128_ = lean_nat_add(v_size_1125_, v___x_1127_);
v___x_1129_ = lean_array_get_size(v_keyArray_1126_);
v___x_1130_ = lean_nat_dec_lt(v___x_1128_, v___x_1129_);
if (v___x_1130_ == 0)
{
lean_dec(v___x_1128_);
lean_dec(v_index_1124_);
goto v___jp_1113_;
}
else
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; uint8_t v___x_1135_; 
v___x_1131_ = lean_unsigned_to_nat(4u);
v___x_1132_ = lean_nat_mul(v___x_1128_, v___x_1131_);
v___x_1133_ = lean_unsigned_to_nat(3u);
v___x_1134_ = lean_nat_mul(v___x_1129_, v___x_1133_);
v___x_1135_ = lean_nat_dec_le(v___x_1132_, v___x_1134_);
lean_dec(v___x_1134_);
lean_dec(v___x_1132_);
if (v___x_1135_ == 0)
{
lean_dec(v___x_1128_);
lean_dec(v_index_1124_);
goto v___jp_1113_;
}
else
{
lean_object* v___x_1136_; 
lean_dec_ref(v___f_1062_);
lean_inc(v_idx_1030_);
v___x_1136_ = l_Std_DHashMap_Raw_setEntry___redArg(v_a_1031_, v___x_1128_, v_index_1124_, v_idx_1030_, v___x_1088_);
lean_dec(v_index_1124_);
v___y_1077_ = v___x_1136_;
goto v___jp_1076_;
}
}
}
default: 
{
lean_object* v_size_1137_; lean_object* v_keyArray_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; uint8_t v___x_1142_; 
v_size_1137_ = lean_ctor_get(v_a_1031_, 0);
v_keyArray_1138_ = lean_ctor_get(v_a_1031_, 1);
v___x_1139_ = lean_unsigned_to_nat(1u);
v___x_1140_ = lean_nat_add(v_size_1137_, v___x_1139_);
v___x_1141_ = lean_array_get_size(v_keyArray_1138_);
v___x_1142_ = lean_nat_dec_lt(v___x_1140_, v___x_1141_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1143_; 
lean_dec(v___x_1140_);
lean_inc_ref(v___f_1062_);
v___x_1143_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_1062_, v___f_1063_, v_a_1031_);
v___y_1097_ = v___x_1143_;
goto v___jp_1096_;
}
else
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; uint8_t v___x_1148_; 
v___x_1144_ = lean_unsigned_to_nat(4u);
v___x_1145_ = lean_nat_mul(v___x_1140_, v___x_1144_);
lean_dec(v___x_1140_);
v___x_1146_ = lean_unsigned_to_nat(3u);
v___x_1147_ = lean_nat_mul(v___x_1141_, v___x_1146_);
v___x_1148_ = lean_nat_dec_le(v___x_1145_, v___x_1147_);
lean_dec(v___x_1147_);
lean_dec(v___x_1145_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; 
lean_inc_ref(v___f_1062_);
v___x_1149_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_1062_, v___f_1063_, v_a_1031_);
v___y_1097_ = v___x_1149_;
goto v___jp_1096_;
}
else
{
v___y_1097_ = v_a_1031_;
goto v___jp_1096_;
}
}
}
}
v___jp_1089_:
{
lean_object* v_size_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v_size_1092_ = lean_ctor_get(v___y_1090_, 0);
v___x_1093_ = lean_unsigned_to_nat(1u);
v___x_1094_ = lean_nat_add(v_size_1092_, v___x_1093_);
lean_inc(v_idx_1030_);
v___x_1095_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1090_, v___x_1094_, v_i_1091_, v_idx_1030_, v___x_1088_);
lean_dec(v_i_1091_);
v___y_1077_ = v___x_1095_;
goto v___jp_1076_;
}
v___jp_1096_:
{
lean_object* v___x_1098_; 
lean_inc(v_idx_1030_);
v___x_1098_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_1062_, v___f_1063_, v___y_1097_, v_idx_1030_);
switch(lean_obj_tag(v___x_1098_))
{
case 0:
{
lean_object* v_index_1099_; lean_object* v_size_1100_; lean_object* v___x_1101_; 
v_index_1099_ = lean_ctor_get(v___x_1098_, 0);
lean_inc(v_index_1099_);
lean_dec_ref_known(v___x_1098_, 3);
v_size_1100_ = lean_ctor_get(v___y_1097_, 0);
lean_inc(v_size_1100_);
lean_inc(v_idx_1030_);
v___x_1101_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1097_, v_size_1100_, v_index_1099_, v_idx_1030_, v___x_1088_);
lean_dec(v_index_1099_);
v___y_1077_ = v___x_1101_;
goto v___jp_1076_;
}
case 1:
{
lean_object* v_index_1102_; 
v_index_1102_ = lean_ctor_get(v___x_1098_, 0);
lean_inc(v_index_1102_);
lean_dec_ref_known(v___x_1098_, 1);
v___y_1090_ = v___y_1097_;
v_i_1091_ = v_index_1102_;
goto v___jp_1089_;
}
default: 
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = lean_unsigned_to_nat(0u);
v___x_1104_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1097_, v___x_1103_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v_index_1105_; 
v_index_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_index_1105_);
lean_dec_ref_known(v___x_1104_, 1);
v___y_1090_ = v___y_1097_;
v_i_1091_ = v_index_1105_;
goto v___jp_1089_;
}
else
{
v___y_1077_ = v___y_1097_;
goto v___jp_1076_;
}
}
}
}
v___jp_1106_:
{
lean_object* v_size_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v_size_1109_ = lean_ctor_get(v___y_1107_, 0);
v___x_1110_ = lean_unsigned_to_nat(1u);
v___x_1111_ = lean_nat_add(v_size_1109_, v___x_1110_);
lean_inc(v_idx_1030_);
v___x_1112_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1107_, v___x_1111_, v_i_1108_, v_idx_1030_, v___x_1088_);
lean_dec(v_i_1108_);
v___y_1077_ = v___x_1112_;
goto v___jp_1076_;
}
v___jp_1113_:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
lean_inc_ref(v___f_1062_);
v___x_1114_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_1062_, v___f_1063_, v_a_1031_);
lean_inc(v_idx_1030_);
v___x_1115_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_1062_, v___f_1063_, v___x_1114_, v_idx_1030_);
switch(lean_obj_tag(v___x_1115_))
{
case 0:
{
lean_object* v_index_1116_; lean_object* v_size_1117_; lean_object* v___x_1118_; 
v_index_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_index_1116_);
lean_dec_ref_known(v___x_1115_, 3);
v_size_1117_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_size_1117_);
lean_inc(v_idx_1030_);
v___x_1118_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1114_, v_size_1117_, v_index_1116_, v_idx_1030_, v___x_1088_);
lean_dec(v_index_1116_);
v___y_1077_ = v___x_1118_;
goto v___jp_1076_;
}
case 1:
{
lean_object* v_index_1119_; 
v_index_1119_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_index_1119_);
lean_dec_ref_known(v___x_1115_, 1);
v___y_1107_ = v___x_1114_;
v_i_1108_ = v_index_1119_;
goto v___jp_1106_;
}
default: 
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1120_ = lean_unsigned_to_nat(0u);
v___x_1121_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1114_, v___x_1120_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v_index_1122_; 
v_index_1122_ = lean_ctor_get(v___x_1121_, 0);
lean_inc(v_index_1122_);
lean_dec_ref_known(v___x_1121_, 1);
v___y_1107_ = v___x_1114_;
v_i_1108_ = v_index_1122_;
goto v___jp_1106_;
}
else
{
v___y_1077_ = v___x_1114_;
goto v___jp_1076_;
}
}
}
}
}
else
{
lean_object* v___x_1150_; 
lean_dec_ref(v___f_1062_);
lean_dec(v_idx_1030_);
v___x_1150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1150_, 0, v_acc_1028_);
lean_ctor_set(v___x_1150_, 1, v_a_1031_);
return v___x_1150_;
}
v___jp_1032_:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v_fst_1057_; lean_object* v_snd_1058_; 
v___x_1038_ = l_Nat_reprFast(v_idx_1030_);
v___x_1039_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___redArg___closed__0));
lean_inc_ref(v___x_1038_);
v___x_1040_ = lean_string_append(v___x_1038_, v___x_1039_);
lean_inc(v___y_1033_);
v___x_1041_ = l_Nat_reprFast(v___y_1033_);
v___x_1042_ = lean_string_append(v___x_1040_, v___x_1041_);
lean_dec_ref(v___x_1041_);
v___x_1043_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_1034_);
v___x_1044_ = lean_string_append(v___x_1042_, v___x_1043_);
lean_dec_ref(v___x_1043_);
v___x_1045_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___redArg___closed__1));
v___x_1046_ = lean_string_append(v___x_1044_, v___x_1045_);
v___x_1047_ = lean_string_append(v___x_1046_, v___x_1038_);
lean_dec_ref(v___x_1038_);
v___x_1048_ = lean_string_append(v___x_1047_, v___x_1039_);
lean_inc(v___y_1035_);
v___x_1049_ = l_Nat_reprFast(v___y_1035_);
v___x_1050_ = lean_string_append(v___x_1048_, v___x_1049_);
lean_dec_ref(v___x_1049_);
v___x_1051_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_1037_);
v___x_1052_ = lean_string_append(v___x_1050_, v___x_1051_);
lean_dec_ref(v___x_1051_);
v___x_1053_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___redArg___closed__2));
v___x_1054_ = lean_string_append(v___x_1052_, v___x_1053_);
v___x_1055_ = lean_string_append(v_acc_1028_, v___x_1054_);
lean_dec_ref(v___x_1054_);
v___x_1056_ = l_Std_Sat_AIG_toGraphviz_go___redArg(v___x_1055_, v_decls_1029_, v___y_1033_, v___y_1036_);
v_fst_1057_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_fst_1057_);
v_snd_1058_ = lean_ctor_get(v___x_1056_, 1);
lean_inc(v_snd_1058_);
lean_dec_ref(v___x_1056_);
v_acc_1028_ = v_fst_1057_;
v_idx_1030_ = v___y_1035_;
v_a_1031_ = v_snd_1058_;
goto _start;
}
v___jp_1065_:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; uint8_t v___x_1074_; 
v___x_1071_ = lean_nat_shiftr(v___y_1068_, v___y_1069_);
v___x_1072_ = lean_nat_land(v___y_1069_, v___y_1068_);
v___x_1073_ = lean_unsigned_to_nat(0u);
v___x_1074_ = lean_nat_dec_eq(v___x_1072_, v___x_1073_);
lean_dec(v___x_1072_);
if (v___x_1074_ == 0)
{
uint8_t v___x_1075_; 
v___x_1075_ = 1;
v___y_1033_ = v___y_1066_;
v___y_1034_ = v___y_1070_;
v___y_1035_ = v___x_1071_;
v___y_1036_ = v___y_1067_;
v___y_1037_ = v___x_1075_;
goto v___jp_1032_;
}
else
{
v___y_1033_ = v___y_1066_;
v___y_1034_ = v___y_1070_;
v___y_1035_ = v___x_1071_;
v___y_1036_ = v___y_1067_;
v___y_1037_ = v___x_1064_;
goto v___jp_1032_;
}
}
v___jp_1076_:
{
lean_object* v___x_1078_; 
v___x_1078_ = lean_array_fget_borrowed(v_decls_1029_, v_idx_1030_);
if (lean_obj_tag(v___x_1078_) == 2)
{
lean_object* v_l_1079_; lean_object* v_r_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; uint8_t v___x_1085_; 
v_l_1079_ = lean_ctor_get(v___x_1078_, 0);
v_r_1080_ = lean_ctor_get(v___x_1078_, 1);
v___x_1081_ = lean_unsigned_to_nat(1u);
v___x_1082_ = lean_nat_shiftr(v_l_1079_, v___x_1081_);
v___x_1083_ = lean_nat_land(v___x_1081_, v_l_1079_);
v___x_1084_ = lean_unsigned_to_nat(0u);
v___x_1085_ = lean_nat_dec_eq(v___x_1083_, v___x_1084_);
lean_dec(v___x_1083_);
if (v___x_1085_ == 0)
{
uint8_t v___x_1086_; 
v___x_1086_ = 1;
v___y_1066_ = v___x_1082_;
v___y_1067_ = v___y_1077_;
v___y_1068_ = v_r_1080_;
v___y_1069_ = v___x_1081_;
v___y_1070_ = v___x_1086_;
goto v___jp_1065_;
}
else
{
v___y_1066_ = v___x_1082_;
v___y_1067_ = v___y_1077_;
v___y_1068_ = v_r_1080_;
v___y_1069_ = v___x_1081_;
v___y_1070_ = v___x_1064_;
goto v___jp_1065_;
}
}
else
{
lean_object* v___x_1087_; 
lean_dec(v_idx_1030_);
v___x_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1087_, 0, v_acc_1028_);
lean_ctor_set(v___x_1087_, 1, v___y_1077_);
return v___x_1087_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___redArg___boxed(lean_object* v_acc_1151_, lean_object* v_decls_1152_, lean_object* v_idx_1153_, lean_object* v_a_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Std_Sat_AIG_toGraphviz_go___redArg(v_acc_1151_, v_decls_1152_, v_idx_1153_, v_a_1154_);
lean_dec_ref(v_decls_1152_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go(lean_object* v_00_u03b1_1156_, lean_object* v_inst_1157_, lean_object* v_inst_1158_, lean_object* v_inst_1159_, lean_object* v_acc_1160_, lean_object* v_decls_1161_, lean_object* v_hinv_1162_, lean_object* v_idx_1163_, lean_object* v_hidx_1164_, lean_object* v_a_1165_){
_start:
{
lean_object* v___x_1166_; 
v___x_1166_ = l_Std_Sat_AIG_toGraphviz_go___redArg(v_acc_1160_, v_decls_1161_, v_idx_1163_, v_a_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___boxed(lean_object* v_00_u03b1_1167_, lean_object* v_inst_1168_, lean_object* v_inst_1169_, lean_object* v_inst_1170_, lean_object* v_acc_1171_, lean_object* v_decls_1172_, lean_object* v_hinv_1173_, lean_object* v_idx_1174_, lean_object* v_hidx_1175_, lean_object* v_a_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Std_Sat_AIG_toGraphviz_go(v_00_u03b1_1167_, v_inst_1168_, v_inst_1169_, v_inst_1170_, v_acc_1171_, v_decls_1172_, v_hinv_1173_, v_idx_1174_, v_hidx_1175_, v_a_1176_);
lean_dec_ref(v_decls_1172_);
lean_dec_ref(v_inst_1170_);
lean_dec_ref(v_inst_1169_);
lean_dec_ref(v_inst_1168_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter___redArg(lean_object* v_x_1178_, lean_object* v_h__1_1179_, lean_object* v_h__2_1180_, lean_object* v_h__3_1181_){
_start:
{
switch(lean_obj_tag(v_x_1178_))
{
case 0:
{
lean_object* v___x_1182_; 
lean_dec(v_h__3_1181_);
lean_dec(v_h__2_1180_);
v___x_1182_ = lean_apply_1(v_h__1_1179_, lean_box(0));
return v___x_1182_;
}
case 1:
{
lean_object* v_idx_1183_; lean_object* v___x_1184_; 
lean_dec(v_h__3_1181_);
lean_dec(v_h__1_1179_);
v_idx_1183_ = lean_ctor_get(v_x_1178_, 0);
lean_inc(v_idx_1183_);
lean_dec_ref_known(v_x_1178_, 1);
v___x_1184_ = lean_apply_2(v_h__2_1180_, v_idx_1183_, lean_box(0));
return v___x_1184_;
}
default: 
{
lean_object* v_l_1185_; lean_object* v_r_1186_; lean_object* v___x_1187_; 
lean_dec(v_h__2_1180_);
lean_dec(v_h__1_1179_);
v_l_1185_ = lean_ctor_get(v_x_1178_, 0);
lean_inc(v_l_1185_);
v_r_1186_ = lean_ctor_get(v_x_1178_, 1);
lean_inc(v_r_1186_);
lean_dec_ref_known(v_x_1178_, 2);
v___x_1187_ = lean_apply_3(v_h__3_1181_, v_l_1185_, v_r_1186_, lean_box(0));
return v___x_1187_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter(lean_object* v_00_u03b1_1188_, lean_object* v_motive_1189_, lean_object* v_x_1190_, lean_object* v_h__1_1191_, lean_object* v_h__2_1192_, lean_object* v_h__3_1193_){
_start:
{
switch(lean_obj_tag(v_x_1190_))
{
case 0:
{
lean_object* v___x_1194_; 
lean_dec(v_h__3_1193_);
lean_dec(v_h__2_1192_);
v___x_1194_ = lean_apply_1(v_h__1_1191_, lean_box(0));
return v___x_1194_;
}
case 1:
{
lean_object* v_idx_1195_; lean_object* v___x_1196_; 
lean_dec(v_h__3_1193_);
lean_dec(v_h__1_1191_);
v_idx_1195_ = lean_ctor_get(v_x_1190_, 0);
lean_inc(v_idx_1195_);
lean_dec_ref_known(v_x_1190_, 1);
v___x_1196_ = lean_apply_2(v_h__2_1192_, v_idx_1195_, lean_box(0));
return v___x_1196_;
}
default: 
{
lean_object* v_l_1197_; lean_object* v_r_1198_; lean_object* v___x_1199_; 
lean_dec(v_h__2_1192_);
lean_dec(v_h__1_1191_);
v_l_1197_ = lean_ctor_get(v_x_1190_, 0);
lean_inc(v_l_1197_);
v_r_1198_ = lean_ctor_get(v_x_1190_, 1);
lean_inc(v_r_1198_);
lean_dec_ref_known(v_x_1190_, 2);
v___x_1199_ = lean_apply_3(v_h__3_1193_, v_l_1197_, v_r_1198_, lean_box(0));
return v___x_1199_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg(lean_object* v_inst_1205_, lean_object* v_decls_1206_, lean_object* v_idx_1207_){
_start:
{
lean_object* v___x_1208_; 
v___x_1208_ = lean_array_fget_borrowed(v_decls_1206_, v_idx_1207_);
switch(lean_obj_tag(v___x_1208_))
{
case 0:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
lean_dec_ref(v_inst_1205_);
v___x_1209_ = l_Nat_reprFast(v_idx_1207_);
v___x_1210_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__0));
v___x_1211_ = lean_string_append(v___x_1209_, v___x_1210_);
v___x_1212_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__1));
v___x_1213_ = lean_string_append(v___x_1211_, v___x_1212_);
v___x_1214_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__2));
v___x_1215_ = lean_string_append(v___x_1213_, v___x_1214_);
return v___x_1215_;
}
case 1:
{
lean_object* v_idx_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v_idx_1216_ = lean_ctor_get(v___x_1208_, 0);
v___x_1217_ = l_Nat_reprFast(v_idx_1207_);
v___x_1218_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__0));
v___x_1219_ = lean_string_append(v___x_1217_, v___x_1218_);
lean_inc(v_idx_1216_);
v___x_1220_ = lean_apply_1(v_inst_1205_, v_idx_1216_);
v___x_1221_ = lean_string_append(v___x_1219_, v___x_1220_);
lean_dec_ref(v___x_1220_);
v___x_1222_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__3));
v___x_1223_ = lean_string_append(v___x_1221_, v___x_1222_);
return v___x_1223_;
}
default: 
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
lean_dec_ref(v_inst_1205_);
v___x_1224_ = l_Nat_reprFast(v_idx_1207_);
v___x_1225_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__0));
lean_inc_ref(v___x_1224_);
v___x_1226_ = lean_string_append(v___x_1224_, v___x_1225_);
v___x_1227_ = lean_string_append(v___x_1226_, v___x_1224_);
lean_dec_ref(v___x_1224_);
v___x_1228_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__4));
v___x_1229_ = lean_string_append(v___x_1227_, v___x_1228_);
return v___x_1229_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___boxed(lean_object* v_inst_1230_, lean_object* v_decls_1231_, lean_object* v_idx_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg(v_inst_1230_, v_decls_1231_, v_idx_1232_);
lean_dec_ref(v_decls_1231_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString(lean_object* v_00_u03b1_1234_, lean_object* v_inst_1235_, lean_object* v_inst_1236_, lean_object* v_inst_1237_, lean_object* v_decls_1238_, lean_object* v_idx_1239_){
_start:
{
lean_object* v___x_1240_; 
v___x_1240_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg(v_inst_1236_, v_decls_1238_, v_idx_1239_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___boxed(lean_object* v_00_u03b1_1241_, lean_object* v_inst_1242_, lean_object* v_inst_1243_, lean_object* v_inst_1244_, lean_object* v_decls_1245_, lean_object* v_idx_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString(v_00_u03b1_1241_, v_inst_1242_, v_inst_1243_, v_inst_1244_, v_decls_1245_, v_idx_1246_);
lean_dec_ref(v_decls_1245_);
lean_dec_ref(v_inst_1244_);
lean_dec_ref(v_inst_1242_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___redArg___lam__0(lean_object* v_inst_1248_, lean_object* v_decls_1249_, lean_object* v_x1_1250_, lean_object* v_x2_1251_, lean_object* v_x3_1252_){
_start:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1253_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg(v_inst_1248_, v_decls_1249_, v_x2_1251_);
v___x_1254_ = lean_string_append(v_x1_1250_, v___x_1253_);
lean_dec_ref(v___x_1253_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___redArg___lam__0___boxed(lean_object* v_inst_1255_, lean_object* v_decls_1256_, lean_object* v_x1_1257_, lean_object* v_x2_1258_, lean_object* v_x3_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_Std_Sat_AIG_toGraphviz___redArg___lam__0(v_inst_1255_, v_decls_1256_, v_x1_1257_, v_x2_1258_, v_x3_1259_);
lean_dec_ref(v_decls_1256_);
return v_res_1260_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___redArg___closed__1(void){
_start:
{
lean_object* v_cellCount_1262_; lean_object* v___x_1263_; 
v_cellCount_1262_ = lean_unsigned_to_nat(16u);
v___x_1263_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1262_);
return v___x_1263_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___redArg___closed__2(void){
_start:
{
lean_object* v_cellCount_1264_; lean_object* v___x_1265_; 
v_cellCount_1264_ = lean_unsigned_to_nat(16u);
v___x_1265_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1264_);
return v___x_1265_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___redArg___closed__3(void){
_start:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1266_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___redArg___closed__2, &l_Std_Sat_AIG_toGraphviz___redArg___closed__2_once, _init_l_Std_Sat_AIG_toGraphviz___redArg___closed__2);
v___x_1267_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___redArg___closed__1, &l_Std_Sat_AIG_toGraphviz___redArg___closed__1_once, _init_l_Std_Sat_AIG_toGraphviz___redArg___closed__1);
v___x_1268_ = lean_unsigned_to_nat(0u);
v___x_1269_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1268_);
lean_ctor_set(v___x_1269_, 1, v___x_1267_);
lean_ctor_set(v___x_1269_, 2, v___x_1266_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___redArg(lean_object* v_inst_1291_, lean_object* v_entry_1292_){
_start:
{
lean_object* v_aig_1293_; lean_object* v_ref_1294_; lean_object* v_decls_1295_; lean_object* v_gate_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v_fst_1300_; lean_object* v_snd_1301_; lean_object* v___f_1302_; lean_object* v___x_1303_; lean_object* v_nodes_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v_aig_1293_ = lean_ctor_get(v_entry_1292_, 0);
lean_inc_ref(v_aig_1293_);
v_ref_1294_ = lean_ctor_get(v_entry_1292_, 1);
lean_inc_ref(v_ref_1294_);
lean_dec_ref(v_entry_1292_);
v_decls_1295_ = lean_ctor_get(v_aig_1293_, 0);
lean_inc_ref(v_decls_1295_);
lean_dec_ref(v_aig_1293_);
v_gate_1296_ = lean_ctor_get(v_ref_1294_, 0);
lean_inc(v_gate_1296_);
lean_dec_ref(v_ref_1294_);
v___x_1297_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___redArg___closed__0));
v___x_1298_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___redArg___closed__3, &l_Std_Sat_AIG_toGraphviz___redArg___closed__3_once, _init_l_Std_Sat_AIG_toGraphviz___redArg___closed__3);
v___x_1299_ = l_Std_Sat_AIG_toGraphviz_go___redArg(v___x_1297_, v_decls_1295_, v_gate_1296_, v___x_1298_);
v_fst_1300_ = lean_ctor_get(v___x_1299_, 0);
lean_inc(v_fst_1300_);
v_snd_1301_ = lean_ctor_get(v___x_1299_, 1);
lean_inc(v_snd_1301_);
lean_dec_ref(v___x_1299_);
v___f_1302_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_toGraphviz___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1302_, 0, v_inst_1291_);
lean_closure_set(v___f_1302_, 1, v_decls_1295_);
v___x_1303_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___redArg___closed__13));
v_nodes_1304_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_1303_, v___f_1302_, v___x_1297_, v_snd_1301_);
v___x_1305_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___redArg___closed__14));
v___x_1306_ = lean_string_append(v___x_1305_, v_nodes_1304_);
lean_dec(v_nodes_1304_);
v___x_1307_ = lean_string_append(v___x_1306_, v_fst_1300_);
lean_dec(v_fst_1300_);
v___x_1308_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___redArg___closed__15));
v___x_1309_ = lean_string_append(v___x_1307_, v___x_1308_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz(lean_object* v_00_u03b1_1310_, lean_object* v_inst_1311_, lean_object* v_inst_1312_, lean_object* v_inst_1313_, lean_object* v_entry_1314_){
_start:
{
lean_object* v___x_1315_; 
v___x_1315_ = l_Std_Sat_AIG_toGraphviz___redArg(v_inst_1312_, v_entry_1314_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___boxed(lean_object* v_00_u03b1_1316_, lean_object* v_inst_1317_, lean_object* v_inst_1318_, lean_object* v_inst_1319_, lean_object* v_entry_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_Std_Sat_AIG_toGraphviz(v_00_u03b1_1316_, v_inst_1317_, v_inst_1318_, v_inst_1319_, v_entry_1320_);
lean_dec_ref(v_inst_1319_);
lean_dec_ref(v_inst_1317_);
return v_res_1321_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote_go___redArg(lean_object* v_x_1322_, lean_object* v_decls_1323_, lean_object* v_assign_1324_){
_start:
{
uint8_t v___y_1326_; uint8_t v___y_1327_; lean_object* v___x_1329_; 
v___x_1329_ = lean_array_fget_borrowed(v_decls_1323_, v_x_1322_);
switch(lean_obj_tag(v___x_1329_))
{
case 0:
{
uint8_t v___x_1330_; 
lean_dec_ref(v_assign_1324_);
v___x_1330_ = 0;
return v___x_1330_;
}
case 1:
{
lean_object* v_idx_1331_; lean_object* v___x_1332_; uint8_t v___x_1333_; 
v_idx_1331_ = lean_ctor_get(v___x_1329_, 0);
lean_inc(v_idx_1331_);
v___x_1332_ = lean_apply_1(v_assign_1324_, v_idx_1331_);
v___x_1333_ = lean_unbox(v___x_1332_);
return v___x_1333_;
}
default: 
{
lean_object* v_l_1334_; lean_object* v_r_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; uint8_t v_lval_1338_; lean_object* v___x_1339_; uint8_t v_rval_1340_; uint8_t v___y_1342_; uint8_t v___y_1343_; uint8_t v___y_1345_; uint8_t v___y_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; uint8_t v___x_1355_; 
v_l_1334_ = lean_ctor_get(v___x_1329_, 0);
v_r_1335_ = lean_ctor_get(v___x_1329_, 1);
v___x_1336_ = lean_unsigned_to_nat(1u);
v___x_1337_ = lean_nat_shiftr(v_l_1334_, v___x_1336_);
lean_inc_ref(v_assign_1324_);
v_lval_1338_ = l_Std_Sat_AIG_denote_go___redArg(v___x_1337_, v_decls_1323_, v_assign_1324_);
lean_dec(v___x_1337_);
v___x_1339_ = lean_nat_shiftr(v_r_1335_, v___x_1336_);
v_rval_1340_ = l_Std_Sat_AIG_denote_go___redArg(v___x_1339_, v_decls_1323_, v_assign_1324_);
lean_dec(v___x_1339_);
v___x_1353_ = lean_nat_land(v___x_1336_, v_l_1334_);
v___x_1354_ = lean_unsigned_to_nat(0u);
v___x_1355_ = lean_nat_dec_eq(v___x_1353_, v___x_1354_);
lean_dec(v___x_1353_);
if (v___x_1355_ == 0)
{
uint8_t v___x_1356_; 
v___x_1356_ = 1;
v___y_1352_ = v___x_1356_;
goto v___jp_1351_;
}
else
{
uint8_t v___x_1357_; 
v___x_1357_ = 0;
v___y_1352_ = v___x_1357_;
goto v___jp_1351_;
}
v___jp_1341_:
{
if (v_rval_1340_ == 0)
{
if (v___y_1343_ == 0)
{
return v___y_1342_;
}
else
{
v___y_1326_ = v___y_1342_;
v___y_1327_ = v_rval_1340_;
goto v___jp_1325_;
}
}
else
{
v___y_1326_ = v___y_1342_;
v___y_1327_ = v___y_1343_;
goto v___jp_1325_;
}
}
v___jp_1344_:
{
if (v___y_1345_ == 0)
{
lean_object* v___x_1346_; lean_object* v___x_1347_; uint8_t v___x_1348_; 
v___x_1346_ = lean_nat_land(v___x_1336_, v_r_1335_);
v___x_1347_ = lean_unsigned_to_nat(0u);
v___x_1348_ = lean_nat_dec_eq(v___x_1346_, v___x_1347_);
lean_dec(v___x_1346_);
if (v___x_1348_ == 0)
{
uint8_t v___x_1349_; 
v___x_1349_ = 1;
v___y_1342_ = v___y_1345_;
v___y_1343_ = v___x_1349_;
goto v___jp_1341_;
}
else
{
v___y_1342_ = v___y_1345_;
v___y_1343_ = v___y_1345_;
goto v___jp_1341_;
}
}
else
{
uint8_t v___x_1350_; 
v___x_1350_ = 0;
return v___x_1350_;
}
}
v___jp_1351_:
{
if (v_lval_1338_ == 0)
{
if (v___y_1352_ == 0)
{
return v___y_1352_;
}
else
{
v___y_1345_ = v_lval_1338_;
goto v___jp_1344_;
}
}
else
{
v___y_1345_ = v___y_1352_;
goto v___jp_1344_;
}
}
}
}
v___jp_1325_:
{
if (v___y_1327_ == 0)
{
uint8_t v___x_1328_; 
v___x_1328_ = 1;
return v___x_1328_;
}
else
{
return v___y_1326_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote_go___redArg___boxed(lean_object* v_x_1358_, lean_object* v_decls_1359_, lean_object* v_assign_1360_){
_start:
{
uint8_t v_res_1361_; lean_object* v_r_1362_; 
v_res_1361_ = l_Std_Sat_AIG_denote_go___redArg(v_x_1358_, v_decls_1359_, v_assign_1360_);
lean_dec_ref(v_decls_1359_);
lean_dec(v_x_1358_);
v_r_1362_ = lean_box(v_res_1361_);
return v_r_1362_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote_go(lean_object* v_00_u03b1_1363_, lean_object* v_x_1364_, lean_object* v_decls_1365_, lean_object* v_assign_1366_, lean_object* v_h1_1367_, lean_object* v_h2_1368_){
_start:
{
uint8_t v___x_1369_; 
v___x_1369_ = l_Std_Sat_AIG_denote_go___redArg(v_x_1364_, v_decls_1365_, v_assign_1366_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote_go___boxed(lean_object* v_00_u03b1_1370_, lean_object* v_x_1371_, lean_object* v_decls_1372_, lean_object* v_assign_1373_, lean_object* v_h1_1374_, lean_object* v_h2_1375_){
_start:
{
uint8_t v_res_1376_; lean_object* v_r_1377_; 
v_res_1376_ = l_Std_Sat_AIG_denote_go(v_00_u03b1_1370_, v_x_1371_, v_decls_1372_, v_assign_1373_, v_h1_1374_, v_h2_1375_);
lean_dec_ref(v_decls_1372_);
lean_dec(v_x_1371_);
v_r_1377_ = lean_box(v_res_1376_);
return v_r_1377_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote___redArg(lean_object* v_assign_1378_, lean_object* v_entry_1379_){
_start:
{
uint8_t v___y_1381_; lean_object* v_ref_1384_; lean_object* v_aig_1385_; lean_object* v_gate_1386_; uint8_t v_invert_1387_; lean_object* v_decls_1388_; uint8_t v___x_1389_; 
v_ref_1384_ = lean_ctor_get(v_entry_1379_, 1);
v_aig_1385_ = lean_ctor_get(v_entry_1379_, 0);
v_gate_1386_ = lean_ctor_get(v_ref_1384_, 0);
v_invert_1387_ = lean_ctor_get_uint8(v_ref_1384_, sizeof(void*)*1);
v_decls_1388_ = lean_ctor_get(v_aig_1385_, 0);
v___x_1389_ = l_Std_Sat_AIG_denote_go___redArg(v_gate_1386_, v_decls_1388_, v_assign_1378_);
if (v___x_1389_ == 0)
{
if (v_invert_1387_ == 0)
{
return v_invert_1387_;
}
else
{
v___y_1381_ = v___x_1389_;
goto v___jp_1380_;
}
}
else
{
v___y_1381_ = v_invert_1387_;
goto v___jp_1380_;
}
v___jp_1380_:
{
if (v___y_1381_ == 0)
{
uint8_t v___x_1382_; 
v___x_1382_ = 1;
return v___x_1382_;
}
else
{
uint8_t v___x_1383_; 
v___x_1383_ = 0;
return v___x_1383_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote___redArg___boxed(lean_object* v_assign_1390_, lean_object* v_entry_1391_){
_start:
{
uint8_t v_res_1392_; lean_object* v_r_1393_; 
v_res_1392_ = l_Std_Sat_AIG_denote___redArg(v_assign_1390_, v_entry_1391_);
lean_dec_ref(v_entry_1391_);
v_r_1393_ = lean_box(v_res_1392_);
return v_r_1393_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote(lean_object* v_00_u03b1_1394_, lean_object* v_inst_1395_, lean_object* v_inst_1396_, lean_object* v_assign_1397_, lean_object* v_entry_1398_){
_start:
{
uint8_t v___x_1399_; 
v___x_1399_ = l_Std_Sat_AIG_denote___redArg(v_assign_1397_, v_entry_1398_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote___boxed(lean_object* v_00_u03b1_1400_, lean_object* v_inst_1401_, lean_object* v_inst_1402_, lean_object* v_assign_1403_, lean_object* v_entry_1404_){
_start:
{
uint8_t v_res_1405_; lean_object* v_r_1406_; 
v_res_1405_ = l_Std_Sat_AIG_denote(v_00_u03b1_1400_, v_inst_1401_, v_inst_1402_, v_assign_1403_, v_entry_1404_);
lean_dec_ref(v_entry_1404_);
lean_dec_ref(v_inst_1402_);
lean_dec_ref(v_inst_1401_);
v_r_1406_ = lean_box(v_res_1405_);
return v_r_1406_;
}
}
static lean_object* _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6(void){
_start:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1488_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__5));
v___x_1489_ = l_String_toRawSubstring_x27(v___x_1488_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1(lean_object* v_x_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_){
_start:
{
lean_object* v___x_1514_; uint8_t v___x_1515_; 
v___x_1514_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
lean_inc(v_x_1511_);
v___x_1515_ = l_Lean_Syntax_isOfKind(v_x_1511_, v___x_1514_);
if (v___x_1515_ == 0)
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
lean_dec(v_x_1511_);
v___x_1516_ = lean_box(1);
v___x_1517_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1516_);
lean_ctor_set(v___x_1517_, 1, v_a_1513_);
return v___x_1517_;
}
else
{
lean_object* v_quotContext_1518_; lean_object* v_currMacroScope_1519_; lean_object* v_ref_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; uint8_t v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v_quotContext_1518_ = lean_ctor_get(v_a_1512_, 1);
v_currMacroScope_1519_ = lean_ctor_get(v_a_1512_, 2);
v_ref_1520_ = lean_ctor_get(v_a_1512_, 5);
v___x_1521_ = lean_unsigned_to_nat(1u);
v___x_1522_ = l_Lean_Syntax_getArg(v_x_1511_, v___x_1521_);
v___x_1523_ = lean_unsigned_to_nat(3u);
v___x_1524_ = l_Lean_Syntax_getArg(v_x_1511_, v___x_1523_);
lean_dec(v_x_1511_);
v___x_1525_ = 0;
v___x_1526_ = l_Lean_SourceInfo_fromRef(v_ref_1520_, v___x_1525_);
v___x_1527_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4));
v___x_1528_ = lean_obj_once(&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6, &l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6_once, _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6);
v___x_1529_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__7));
lean_inc(v_currMacroScope_1519_);
lean_inc(v_quotContext_1518_);
v___x_1530_ = l_Lean_addMacroScope(v_quotContext_1518_, v___x_1529_, v_currMacroScope_1519_);
v___x_1531_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__12));
lean_inc_n(v___x_1526_, 2);
v___x_1532_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1526_);
lean_ctor_set(v___x_1532_, 1, v___x_1528_);
lean_ctor_set(v___x_1532_, 2, v___x_1530_);
lean_ctor_set(v___x_1532_, 3, v___x_1531_);
v___x_1533_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__14));
v___x_1534_ = l_Lean_Syntax_node2(v___x_1526_, v___x_1533_, v___x_1524_, v___x_1522_);
v___x_1535_ = l_Lean_Syntax_node2(v___x_1526_, v___x_1527_, v___x_1532_, v___x_1534_);
v___x_1536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1535_);
lean_ctor_set(v___x_1536_, 1, v_a_1513_);
return v___x_1536_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___boxed(lean_object* v_x_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1(v_x_1537_, v_a_1538_, v_a_1539_);
lean_dec_ref(v_a_1538_);
return v_res_1540_;
}
}
static lean_object* _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__7(void){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1557_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___redArg___closed__0));
v___x_1558_ = l_String_toRawSubstring_x27(v___x_1557_);
return v___x_1558_;
}
}
static lean_object* _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__12(void){
_start:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1569_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__11));
v___x_1570_ = l_String_toRawSubstring_x27(v___x_1569_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1(lean_object* v_x_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_){
_start:
{
lean_object* v___x_1597_; uint8_t v___x_1598_; 
v___x_1597_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__1));
lean_inc(v_x_1594_);
v___x_1598_ = l_Lean_Syntax_isOfKind(v_x_1594_, v___x_1597_);
if (v___x_1598_ == 0)
{
lean_object* v___x_1599_; lean_object* v___x_1600_; 
lean_dec(v_x_1594_);
v___x_1599_ = lean_box(1);
v___x_1600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1599_);
lean_ctor_set(v___x_1600_, 1, v_a_1596_);
return v___x_1600_;
}
else
{
lean_object* v_quotContext_1601_; lean_object* v_currMacroScope_1602_; lean_object* v_ref_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; uint8_t v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v_quotContext_1601_ = lean_ctor_get(v_a_1595_, 1);
v_currMacroScope_1602_ = lean_ctor_get(v_a_1595_, 2);
v_ref_1603_ = lean_ctor_get(v_a_1595_, 5);
v___x_1604_ = lean_unsigned_to_nat(1u);
v___x_1605_ = l_Lean_Syntax_getArg(v_x_1594_, v___x_1604_);
v___x_1606_ = lean_unsigned_to_nat(3u);
v___x_1607_ = l_Lean_Syntax_getArg(v_x_1594_, v___x_1606_);
v___x_1608_ = lean_unsigned_to_nat(5u);
v___x_1609_ = l_Lean_Syntax_getArg(v_x_1594_, v___x_1608_);
lean_dec(v_x_1594_);
v___x_1610_ = 0;
v___x_1611_ = l_Lean_SourceInfo_fromRef(v_ref_1603_, v___x_1610_);
v___x_1612_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4));
v___x_1613_ = lean_obj_once(&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6, &l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6_once, _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6);
v___x_1614_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__7));
lean_inc_n(v_currMacroScope_1602_, 3);
lean_inc_n(v_quotContext_1601_, 3);
v___x_1615_ = l_Lean_addMacroScope(v_quotContext_1601_, v___x_1614_, v_currMacroScope_1602_);
v___x_1616_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__12));
lean_inc_n(v___x_1611_, 11);
v___x_1617_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1611_);
lean_ctor_set(v___x_1617_, 1, v___x_1613_);
lean_ctor_set(v___x_1617_, 2, v___x_1615_);
lean_ctor_set(v___x_1617_, 3, v___x_1616_);
v___x_1618_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__14));
v___x_1619_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__1));
v___x_1620_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__3));
v___x_1621_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__4));
v___x_1622_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1611_);
lean_ctor_set(v___x_1622_, 1, v___x_1621_);
v___x_1623_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__6));
v___x_1624_ = lean_obj_once(&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__7, &l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__7_once, _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__7);
v___x_1625_ = lean_box(0);
v___x_1626_ = l_Lean_addMacroScope(v_quotContext_1601_, v___x_1625_, v_currMacroScope_1602_);
v___x_1627_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__10));
v___x_1628_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1611_);
lean_ctor_set(v___x_1628_, 1, v___x_1624_);
lean_ctor_set(v___x_1628_, 2, v___x_1626_);
lean_ctor_set(v___x_1628_, 3, v___x_1627_);
v___x_1629_ = l_Lean_Syntax_node1(v___x_1611_, v___x_1623_, v___x_1628_);
v___x_1630_ = l_Lean_Syntax_node2(v___x_1611_, v___x_1620_, v___x_1622_, v___x_1629_);
v___x_1631_ = lean_obj_once(&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__12, &l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__12_once, _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__12);
v___x_1632_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__15));
v___x_1633_ = l_Lean_addMacroScope(v_quotContext_1601_, v___x_1632_, v_currMacroScope_1602_);
v___x_1634_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__20));
v___x_1635_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1611_);
lean_ctor_set(v___x_1635_, 1, v___x_1631_);
lean_ctor_set(v___x_1635_, 2, v___x_1633_);
lean_ctor_set(v___x_1635_, 3, v___x_1634_);
v___x_1636_ = l_Lean_Syntax_node2(v___x_1611_, v___x_1618_, v___x_1605_, v___x_1607_);
v___x_1637_ = l_Lean_Syntax_node2(v___x_1611_, v___x_1612_, v___x_1635_, v___x_1636_);
v___x_1638_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__21));
v___x_1639_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1611_);
lean_ctor_set(v___x_1639_, 1, v___x_1638_);
v___x_1640_ = l_Lean_Syntax_node3(v___x_1611_, v___x_1619_, v___x_1630_, v___x_1637_, v___x_1639_);
v___x_1641_ = l_Lean_Syntax_node2(v___x_1611_, v___x_1618_, v___x_1609_, v___x_1640_);
v___x_1642_ = l_Lean_Syntax_node2(v___x_1611_, v___x_1612_, v___x_1617_, v___x_1641_);
v___x_1643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1642_);
lean_ctor_set(v___x_1643_, 1, v_a_1596_);
return v___x_1643_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___boxed(lean_object* v_x_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1(v_x_1644_, v_a_1645_, v_a_1646_);
lean_dec_ref(v_a_1645_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_unexpandDenote(lean_object* v_x_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_){
_start:
{
lean_object* v___x_1705_; uint8_t v___x_1706_; 
v___x_1705_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4));
lean_inc(v_x_1702_);
v___x_1706_ = l_Lean_Syntax_isOfKind(v_x_1702_, v___x_1705_);
if (v___x_1706_ == 0)
{
lean_object* v___x_1707_; lean_object* v___x_1708_; 
lean_dec(v_x_1702_);
v___x_1707_ = lean_box(0);
v___x_1708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1707_);
lean_ctor_set(v___x_1708_, 1, v_a_1704_);
return v___x_1708_;
}
else
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; uint8_t v___x_1712_; 
v___x_1709_ = lean_unsigned_to_nat(1u);
v___x_1710_ = l_Lean_Syntax_getArg(v_x_1702_, v___x_1709_);
lean_dec(v_x_1702_);
v___x_1711_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1710_);
v___x_1712_ = l_Lean_Syntax_matchesNull(v___x_1710_, v___x_1711_);
if (v___x_1712_ == 0)
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
lean_dec(v___x_1710_);
v___x_1713_ = lean_box(0);
v___x_1714_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1714_, 0, v___x_1713_);
lean_ctor_set(v___x_1714_, 1, v_a_1704_);
return v___x_1714_;
}
else
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; uint8_t v___x_1718_; 
v___x_1715_ = lean_unsigned_to_nat(0u);
v___x_1716_ = l_Lean_Syntax_getArg(v___x_1710_, v___x_1715_);
v___x_1717_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__1));
lean_inc(v___x_1716_);
v___x_1718_ = l_Lean_Syntax_isOfKind(v___x_1716_, v___x_1717_);
if (v___x_1718_ == 0)
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1719_ = l_Lean_Syntax_getArg(v___x_1710_, v___x_1709_);
lean_dec(v___x_1710_);
v___x_1720_ = l_Lean_SourceInfo_fromRef(v_a_1703_, v___x_1718_);
v___x_1721_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1722_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1720_, 3);
v___x_1723_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1720_);
lean_ctor_set(v___x_1723_, 1, v___x_1722_);
v___x_1724_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1725_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1720_);
lean_ctor_set(v___x_1725_, 1, v___x_1724_);
v___x_1726_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1727_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1720_);
lean_ctor_set(v___x_1727_, 1, v___x_1726_);
v___x_1728_ = l_Lean_Syntax_node5(v___x_1720_, v___x_1721_, v___x_1723_, v___x_1716_, v___x_1725_, v___x_1719_, v___x_1727_);
v___x_1729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1728_);
lean_ctor_set(v___x_1729_, 1, v_a_1704_);
return v___x_1729_;
}
else
{
lean_object* v___x_1730_; uint8_t v___x_1731_; 
v___x_1730_ = l_Lean_Syntax_getArg(v___x_1716_, v___x_1709_);
v___x_1731_ = l_Lean_Syntax_matchesNull(v___x_1730_, v___x_1715_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1732_ = l_Lean_Syntax_getArg(v___x_1710_, v___x_1709_);
lean_dec(v___x_1710_);
v___x_1733_ = l_Lean_SourceInfo_fromRef(v_a_1703_, v___x_1731_);
v___x_1734_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1735_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1733_, 3);
v___x_1736_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1733_);
lean_ctor_set(v___x_1736_, 1, v___x_1735_);
v___x_1737_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1738_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1733_);
lean_ctor_set(v___x_1738_, 1, v___x_1737_);
v___x_1739_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1740_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1733_);
lean_ctor_set(v___x_1740_, 1, v___x_1739_);
v___x_1741_ = l_Lean_Syntax_node5(v___x_1733_, v___x_1734_, v___x_1736_, v___x_1716_, v___x_1738_, v___x_1732_, v___x_1740_);
v___x_1742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1741_);
lean_ctor_set(v___x_1742_, 1, v_a_1704_);
return v___x_1742_;
}
else
{
lean_object* v___x_1743_; lean_object* v___x_1744_; uint8_t v___x_1745_; 
v___x_1743_ = l_Lean_Syntax_getArg(v___x_1716_, v___x_1711_);
v___x_1744_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__4));
lean_inc(v___x_1743_);
v___x_1745_ = l_Lean_Syntax_isOfKind(v___x_1743_, v___x_1744_);
if (v___x_1745_ == 0)
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
lean_dec(v___x_1743_);
v___x_1746_ = l_Lean_Syntax_getArg(v___x_1710_, v___x_1709_);
lean_dec(v___x_1710_);
v___x_1747_ = l_Lean_SourceInfo_fromRef(v_a_1703_, v___x_1745_);
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
v___x_1755_ = l_Lean_Syntax_node5(v___x_1747_, v___x_1748_, v___x_1750_, v___x_1716_, v___x_1752_, v___x_1746_, v___x_1754_);
v___x_1756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1755_);
lean_ctor_set(v___x_1756_, 1, v_a_1704_);
return v___x_1756_;
}
else
{
lean_object* v___x_1757_; lean_object* v___x_1758_; uint8_t v___x_1759_; 
v___x_1757_ = l_Lean_Syntax_getArg(v___x_1743_, v___x_1715_);
lean_dec(v___x_1743_);
v___x_1758_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_1757_);
v___x_1759_ = l_Lean_Syntax_matchesNull(v___x_1757_, v___x_1758_);
if (v___x_1759_ == 0)
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
lean_dec(v___x_1757_);
v___x_1760_ = l_Lean_Syntax_getArg(v___x_1710_, v___x_1709_);
lean_dec(v___x_1710_);
v___x_1761_ = l_Lean_SourceInfo_fromRef(v_a_1703_, v___x_1759_);
v___x_1762_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1763_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1761_, 3);
v___x_1764_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1764_, 0, v___x_1761_);
lean_ctor_set(v___x_1764_, 1, v___x_1763_);
v___x_1765_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1766_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1766_, 0, v___x_1761_);
lean_ctor_set(v___x_1766_, 1, v___x_1765_);
v___x_1767_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1768_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1761_);
lean_ctor_set(v___x_1768_, 1, v___x_1767_);
v___x_1769_ = l_Lean_Syntax_node5(v___x_1761_, v___x_1762_, v___x_1764_, v___x_1716_, v___x_1766_, v___x_1760_, v___x_1768_);
v___x_1770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1769_);
lean_ctor_set(v___x_1770_, 1, v_a_1704_);
return v___x_1770_;
}
else
{
lean_object* v___x_1771_; lean_object* v___x_1772_; uint8_t v___x_1773_; 
v___x_1771_ = l_Lean_Syntax_getArg(v___x_1757_, v___x_1715_);
v___x_1772_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__6));
lean_inc(v___x_1771_);
v___x_1773_ = l_Lean_Syntax_isOfKind(v___x_1771_, v___x_1772_);
if (v___x_1773_ == 0)
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
lean_dec(v___x_1771_);
lean_dec(v___x_1757_);
v___x_1774_ = l_Lean_Syntax_getArg(v___x_1710_, v___x_1709_);
lean_dec(v___x_1710_);
v___x_1775_ = l_Lean_SourceInfo_fromRef(v_a_1703_, v___x_1773_);
v___x_1776_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1777_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1775_, 3);
v___x_1778_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1775_);
lean_ctor_set(v___x_1778_, 1, v___x_1777_);
v___x_1779_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1780_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1775_);
lean_ctor_set(v___x_1780_, 1, v___x_1779_);
v___x_1781_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1782_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1775_);
lean_ctor_set(v___x_1782_, 1, v___x_1781_);
v___x_1783_ = l_Lean_Syntax_node5(v___x_1775_, v___x_1776_, v___x_1778_, v___x_1716_, v___x_1780_, v___x_1774_, v___x_1782_);
v___x_1784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1783_);
lean_ctor_set(v___x_1784_, 1, v_a_1704_);
return v___x_1784_;
}
else
{
lean_object* v___x_1785_; lean_object* v___x_1786_; uint8_t v___x_1787_; 
v___x_1785_ = l_Lean_Syntax_getArg(v___x_1771_, v___x_1715_);
v___x_1786_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__8));
lean_inc(v___x_1785_);
v___x_1787_ = l_Lean_Syntax_isOfKind(v___x_1785_, v___x_1786_);
if (v___x_1787_ == 0)
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
lean_dec(v___x_1785_);
lean_dec(v___x_1771_);
lean_dec(v___x_1757_);
v___x_1788_ = l_Lean_Syntax_getArg(v___x_1710_, v___x_1709_);
lean_dec(v___x_1710_);
v___x_1789_ = l_Lean_SourceInfo_fromRef(v_a_1703_, v___x_1787_);
v___x_1790_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1791_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1789_, 3);
v___x_1792_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1789_);
lean_ctor_set(v___x_1792_, 1, v___x_1791_);
v___x_1793_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1794_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1789_);
lean_ctor_set(v___x_1794_, 1, v___x_1793_);
v___x_1795_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1796_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1789_);
lean_ctor_set(v___x_1796_, 1, v___x_1795_);
v___x_1797_ = l_Lean_Syntax_node5(v___x_1789_, v___x_1790_, v___x_1792_, v___x_1716_, v___x_1794_, v___x_1788_, v___x_1796_);
v___x_1798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1797_);
lean_ctor_set(v___x_1798_, 1, v_a_1704_);
return v___x_1798_;
}
else
{
lean_object* v___x_1799_; lean_object* v___x_1800_; uint8_t v___x_1801_; 
v___x_1799_ = l_Lean_Syntax_getArg(v___x_1785_, v___x_1715_);
v___x_1800_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__10));
v___x_1801_ = l_Lean_Syntax_matchesIdent(v___x_1799_, v___x_1800_);
lean_dec(v___x_1799_);
if (v___x_1801_ == 0)
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
lean_dec(v___x_1785_);
lean_dec(v___x_1771_);
lean_dec(v___x_1757_);
v___x_1802_ = l_Lean_Syntax_getArg(v___x_1710_, v___x_1709_);
lean_dec(v___x_1710_);
v___x_1803_ = l_Lean_SourceInfo_fromRef(v_a_1703_, v___x_1801_);
v___x_1804_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1805_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1803_, 3);
v___x_1806_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1803_);
lean_ctor_set(v___x_1806_, 1, v___x_1805_);
v___x_1807_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1808_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1803_);
lean_ctor_set(v___x_1808_, 1, v___x_1807_);
v___x_1809_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1810_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1803_);
lean_ctor_set(v___x_1810_, 1, v___x_1809_);
v___x_1811_ = l_Lean_Syntax_node5(v___x_1803_, v___x_1804_, v___x_1806_, v___x_1716_, v___x_1808_, v___x_1802_, v___x_1810_);
v___x_1812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1811_);
lean_ctor_set(v___x_1812_, 1, v_a_1704_);
return v___x_1812_;
}
else
{
lean_object* v___x_1813_; uint8_t v___x_1814_; 
v___x_1813_ = l_Lean_Syntax_getArg(v___x_1785_, v___x_1709_);
lean_dec(v___x_1785_);
v___x_1814_ = l_Lean_Syntax_matchesNull(v___x_1813_, v___x_1715_);
if (v___x_1814_ == 0)
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
lean_dec(v___x_1771_);
lean_dec(v___x_1757_);
v___x_1815_ = l_Lean_Syntax_getArg(v___x_1710_, v___x_1709_);
lean_dec(v___x_1710_);
v___x_1816_ = l_Lean_SourceInfo_fromRef(v_a_1703_, v___x_1814_);
v___x_1817_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1818_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1816_, 3);
v___x_1819_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1816_);
lean_ctor_set(v___x_1819_, 1, v___x_1818_);
v___x_1820_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1821_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1816_);
lean_ctor_set(v___x_1821_, 1, v___x_1820_);
v___x_1822_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1823_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1816_);
lean_ctor_set(v___x_1823_, 1, v___x_1822_);
v___x_1824_ = l_Lean_Syntax_node5(v___x_1816_, v___x_1817_, v___x_1819_, v___x_1716_, v___x_1821_, v___x_1815_, v___x_1823_);
v___x_1825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1824_);
lean_ctor_set(v___x_1825_, 1, v_a_1704_);
return v___x_1825_;
}
else
{
lean_object* v___x_1826_; lean_object* v___x_1827_; uint8_t v___x_1828_; 
v___x_1826_ = l_Lean_Syntax_getArg(v___x_1771_, v___x_1709_);
lean_dec(v___x_1771_);
v___x_1827_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_1826_);
v___x_1828_ = l_Lean_Syntax_matchesNull(v___x_1826_, v___x_1827_);
if (v___x_1828_ == 0)
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
lean_dec(v___x_1826_);
lean_dec(v___x_1757_);
v___x_1829_ = l_Lean_Syntax_getArg(v___x_1710_, v___x_1709_);
lean_dec(v___x_1710_);
v___x_1830_ = l_Lean_SourceInfo_fromRef(v_a_1703_, v___x_1828_);
v___x_1831_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1832_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1830_, 3);
v___x_1833_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1830_);
lean_ctor_set(v___x_1833_, 1, v___x_1832_);
v___x_1834_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1835_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1830_);
lean_ctor_set(v___x_1835_, 1, v___x_1834_);
v___x_1836_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1837_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1830_);
lean_ctor_set(v___x_1837_, 1, v___x_1836_);
v___x_1838_ = l_Lean_Syntax_node5(v___x_1830_, v___x_1831_, v___x_1833_, v___x_1716_, v___x_1835_, v___x_1829_, v___x_1837_);
v___x_1839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1838_);
lean_ctor_set(v___x_1839_, 1, v_a_1704_);
return v___x_1839_;
}
else
{
lean_object* v___x_1840_; uint8_t v___x_1841_; 
v___x_1840_ = l_Lean_Syntax_getArg(v___x_1826_, v___x_1715_);
v___x_1841_ = l_Lean_Syntax_matchesNull(v___x_1840_, v___x_1715_);
if (v___x_1841_ == 0)
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
lean_dec(v___x_1826_);
lean_dec(v___x_1757_);
v___x_1842_ = l_Lean_Syntax_getArg(v___x_1710_, v___x_1709_);
lean_dec(v___x_1710_);
v___x_1843_ = l_Lean_SourceInfo_fromRef(v_a_1703_, v___x_1841_);
v___x_1844_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1845_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1843_, 3);
v___x_1846_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1843_);
lean_ctor_set(v___x_1846_, 1, v___x_1845_);
v___x_1847_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1848_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1843_);
lean_ctor_set(v___x_1848_, 1, v___x_1847_);
v___x_1849_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1850_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1843_);
lean_ctor_set(v___x_1850_, 1, v___x_1849_);
v___x_1851_ = l_Lean_Syntax_node5(v___x_1843_, v___x_1844_, v___x_1846_, v___x_1716_, v___x_1848_, v___x_1842_, v___x_1850_);
v___x_1852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
lean_ctor_set(v___x_1852_, 1, v_a_1704_);
return v___x_1852_;
}
else
{
lean_object* v___x_1853_; uint8_t v___x_1854_; 
v___x_1853_ = l_Lean_Syntax_getArg(v___x_1826_, v___x_1709_);
v___x_1854_ = l_Lean_Syntax_matchesNull(v___x_1853_, v___x_1715_);
if (v___x_1854_ == 0)
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
lean_dec(v___x_1826_);
lean_dec(v___x_1757_);
v___x_1855_ = l_Lean_Syntax_getArg(v___x_1710_, v___x_1709_);
lean_dec(v___x_1710_);
v___x_1856_ = l_Lean_SourceInfo_fromRef(v_a_1703_, v___x_1854_);
v___x_1857_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1858_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1856_, 3);
v___x_1859_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1856_);
lean_ctor_set(v___x_1859_, 1, v___x_1858_);
v___x_1860_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1861_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1856_);
lean_ctor_set(v___x_1861_, 1, v___x_1860_);
v___x_1862_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1863_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1856_);
lean_ctor_set(v___x_1863_, 1, v___x_1862_);
v___x_1864_ = l_Lean_Syntax_node5(v___x_1856_, v___x_1857_, v___x_1859_, v___x_1716_, v___x_1861_, v___x_1855_, v___x_1863_);
v___x_1865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1864_);
lean_ctor_set(v___x_1865_, 1, v_a_1704_);
return v___x_1865_;
}
else
{
lean_object* v___x_1866_; lean_object* v___x_1867_; uint8_t v___x_1868_; 
v___x_1866_ = l_Lean_Syntax_getArg(v___x_1826_, v___x_1711_);
lean_dec(v___x_1826_);
v___x_1867_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__12));
lean_inc(v___x_1866_);
v___x_1868_ = l_Lean_Syntax_isOfKind(v___x_1866_, v___x_1867_);
if (v___x_1868_ == 0)
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
lean_dec(v___x_1866_);
lean_dec(v___x_1757_);
v___x_1869_ = l_Lean_Syntax_getArg(v___x_1710_, v___x_1709_);
lean_dec(v___x_1710_);
v___x_1870_ = l_Lean_SourceInfo_fromRef(v_a_1703_, v___x_1868_);
v___x_1871_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1872_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1870_, 3);
v___x_1873_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1870_);
lean_ctor_set(v___x_1873_, 1, v___x_1872_);
v___x_1874_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1875_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1870_);
lean_ctor_set(v___x_1875_, 1, v___x_1874_);
v___x_1876_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1877_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1870_);
lean_ctor_set(v___x_1877_, 1, v___x_1876_);
v___x_1878_ = l_Lean_Syntax_node5(v___x_1870_, v___x_1871_, v___x_1873_, v___x_1716_, v___x_1875_, v___x_1869_, v___x_1877_);
v___x_1879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1878_);
lean_ctor_set(v___x_1879_, 1, v_a_1704_);
return v___x_1879_;
}
else
{
lean_object* v___x_1880_; uint8_t v___x_1881_; 
v___x_1880_ = l_Lean_Syntax_getArg(v___x_1866_, v___x_1709_);
v___x_1881_ = l_Lean_Syntax_matchesNull(v___x_1880_, v___x_1715_);
if (v___x_1881_ == 0)
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
lean_dec(v___x_1866_);
lean_dec(v___x_1757_);
v___x_1882_ = l_Lean_Syntax_getArg(v___x_1710_, v___x_1709_);
lean_dec(v___x_1710_);
v___x_1883_ = l_Lean_SourceInfo_fromRef(v_a_1703_, v___x_1881_);
v___x_1884_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1885_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1883_, 3);
v___x_1886_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1883_);
lean_ctor_set(v___x_1886_, 1, v___x_1885_);
v___x_1887_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1888_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1883_);
lean_ctor_set(v___x_1888_, 1, v___x_1887_);
v___x_1889_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1890_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1883_);
lean_ctor_set(v___x_1890_, 1, v___x_1889_);
v___x_1891_ = l_Lean_Syntax_node5(v___x_1883_, v___x_1884_, v___x_1886_, v___x_1716_, v___x_1888_, v___x_1882_, v___x_1890_);
v___x_1892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1891_);
lean_ctor_set(v___x_1892_, 1, v_a_1704_);
return v___x_1892_;
}
else
{
lean_object* v___x_1893_; uint8_t v___x_1894_; 
v___x_1893_ = l_Lean_Syntax_getArg(v___x_1757_, v___x_1711_);
lean_inc(v___x_1893_);
v___x_1894_ = l_Lean_Syntax_isOfKind(v___x_1893_, v___x_1772_);
if (v___x_1894_ == 0)
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
lean_dec(v___x_1893_);
lean_dec(v___x_1866_);
lean_dec(v___x_1757_);
v___x_1895_ = l_Lean_Syntax_getArg(v___x_1710_, v___x_1709_);
lean_dec(v___x_1710_);
v___x_1896_ = l_Lean_SourceInfo_fromRef(v_a_1703_, v___x_1894_);
v___x_1897_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1898_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1896_, 3);
v___x_1899_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1896_);
lean_ctor_set(v___x_1899_, 1, v___x_1898_);
v___x_1900_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1901_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1896_);
lean_ctor_set(v___x_1901_, 1, v___x_1900_);
v___x_1902_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1903_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1896_);
lean_ctor_set(v___x_1903_, 1, v___x_1902_);
v___x_1904_ = l_Lean_Syntax_node5(v___x_1896_, v___x_1897_, v___x_1899_, v___x_1716_, v___x_1901_, v___x_1895_, v___x_1903_);
v___x_1905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1904_);
lean_ctor_set(v___x_1905_, 1, v_a_1704_);
return v___x_1905_;
}
else
{
lean_object* v___x_1906_; uint8_t v___x_1907_; 
v___x_1906_ = l_Lean_Syntax_getArg(v___x_1893_, v___x_1715_);
lean_inc(v___x_1906_);
v___x_1907_ = l_Lean_Syntax_isOfKind(v___x_1906_, v___x_1786_);
if (v___x_1907_ == 0)
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
lean_dec(v___x_1906_);
lean_dec(v___x_1893_);
lean_dec(v___x_1866_);
lean_dec(v___x_1757_);
v___x_1908_ = l_Lean_Syntax_getArg(v___x_1710_, v___x_1709_);
lean_dec(v___x_1710_);
v___x_1909_ = l_Lean_SourceInfo_fromRef(v_a_1703_, v___x_1907_);
v___x_1910_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1911_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1909_, 3);
v___x_1912_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1909_);
lean_ctor_set(v___x_1912_, 1, v___x_1911_);
v___x_1913_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1914_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1909_);
lean_ctor_set(v___x_1914_, 1, v___x_1913_);
v___x_1915_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1916_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1909_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
v___x_1917_ = l_Lean_Syntax_node5(v___x_1909_, v___x_1910_, v___x_1912_, v___x_1716_, v___x_1914_, v___x_1908_, v___x_1916_);
v___x_1918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1917_);
lean_ctor_set(v___x_1918_, 1, v_a_1704_);
return v___x_1918_;
}
else
{
lean_object* v___x_1919_; lean_object* v___x_1920_; uint8_t v___x_1921_; 
v___x_1919_ = l_Lean_Syntax_getArg(v___x_1906_, v___x_1715_);
v___x_1920_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__14));
v___x_1921_ = l_Lean_Syntax_matchesIdent(v___x_1919_, v___x_1920_);
lean_dec(v___x_1919_);
if (v___x_1921_ == 0)
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
lean_dec(v___x_1906_);
lean_dec(v___x_1893_);
lean_dec(v___x_1866_);
lean_dec(v___x_1757_);
v___x_1922_ = l_Lean_Syntax_getArg(v___x_1710_, v___x_1709_);
lean_dec(v___x_1710_);
v___x_1923_ = l_Lean_SourceInfo_fromRef(v_a_1703_, v___x_1921_);
v___x_1924_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1925_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1923_, 3);
v___x_1926_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1923_);
lean_ctor_set(v___x_1926_, 1, v___x_1925_);
v___x_1927_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1928_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1923_);
lean_ctor_set(v___x_1928_, 1, v___x_1927_);
v___x_1929_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1930_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1923_);
lean_ctor_set(v___x_1930_, 1, v___x_1929_);
v___x_1931_ = l_Lean_Syntax_node5(v___x_1923_, v___x_1924_, v___x_1926_, v___x_1716_, v___x_1928_, v___x_1922_, v___x_1930_);
v___x_1932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1931_);
lean_ctor_set(v___x_1932_, 1, v_a_1704_);
return v___x_1932_;
}
else
{
lean_object* v___x_1933_; uint8_t v___x_1934_; 
v___x_1933_ = l_Lean_Syntax_getArg(v___x_1906_, v___x_1709_);
lean_dec(v___x_1906_);
v___x_1934_ = l_Lean_Syntax_matchesNull(v___x_1933_, v___x_1715_);
if (v___x_1934_ == 0)
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
lean_dec(v___x_1893_);
lean_dec(v___x_1866_);
lean_dec(v___x_1757_);
v___x_1935_ = l_Lean_Syntax_getArg(v___x_1710_, v___x_1709_);
lean_dec(v___x_1710_);
v___x_1936_ = l_Lean_SourceInfo_fromRef(v_a_1703_, v___x_1934_);
v___x_1937_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1938_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1936_, 3);
v___x_1939_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1936_);
lean_ctor_set(v___x_1939_, 1, v___x_1938_);
v___x_1940_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1941_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1936_);
lean_ctor_set(v___x_1941_, 1, v___x_1940_);
v___x_1942_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1943_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1936_);
lean_ctor_set(v___x_1943_, 1, v___x_1942_);
v___x_1944_ = l_Lean_Syntax_node5(v___x_1936_, v___x_1937_, v___x_1939_, v___x_1716_, v___x_1941_, v___x_1935_, v___x_1943_);
v___x_1945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1944_);
lean_ctor_set(v___x_1945_, 1, v_a_1704_);
return v___x_1945_;
}
else
{
lean_object* v___x_1946_; uint8_t v___x_1947_; 
v___x_1946_ = l_Lean_Syntax_getArg(v___x_1893_, v___x_1709_);
lean_dec(v___x_1893_);
lean_inc(v___x_1946_);
v___x_1947_ = l_Lean_Syntax_matchesNull(v___x_1946_, v___x_1827_);
if (v___x_1947_ == 0)
{
lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
lean_dec(v___x_1946_);
lean_dec(v___x_1866_);
lean_dec(v___x_1757_);
v___x_1948_ = l_Lean_Syntax_getArg(v___x_1710_, v___x_1709_);
lean_dec(v___x_1710_);
v___x_1949_ = l_Lean_SourceInfo_fromRef(v_a_1703_, v___x_1947_);
v___x_1950_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1951_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1949_, 3);
v___x_1952_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1949_);
lean_ctor_set(v___x_1952_, 1, v___x_1951_);
v___x_1953_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1954_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1949_);
lean_ctor_set(v___x_1954_, 1, v___x_1953_);
v___x_1955_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1956_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1956_, 0, v___x_1949_);
lean_ctor_set(v___x_1956_, 1, v___x_1955_);
v___x_1957_ = l_Lean_Syntax_node5(v___x_1949_, v___x_1950_, v___x_1952_, v___x_1716_, v___x_1954_, v___x_1948_, v___x_1956_);
v___x_1958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1958_, 0, v___x_1957_);
lean_ctor_set(v___x_1958_, 1, v_a_1704_);
return v___x_1958_;
}
else
{
lean_object* v___x_1959_; uint8_t v___x_1960_; 
v___x_1959_ = l_Lean_Syntax_getArg(v___x_1946_, v___x_1715_);
v___x_1960_ = l_Lean_Syntax_matchesNull(v___x_1959_, v___x_1715_);
if (v___x_1960_ == 0)
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
lean_dec(v___x_1946_);
lean_dec(v___x_1866_);
lean_dec(v___x_1757_);
v___x_1961_ = l_Lean_Syntax_getArg(v___x_1710_, v___x_1709_);
lean_dec(v___x_1710_);
v___x_1962_ = l_Lean_SourceInfo_fromRef(v_a_1703_, v___x_1960_);
v___x_1963_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1964_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1962_, 3);
v___x_1965_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1962_);
lean_ctor_set(v___x_1965_, 1, v___x_1964_);
v___x_1966_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1967_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1962_);
lean_ctor_set(v___x_1967_, 1, v___x_1966_);
v___x_1968_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1969_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1962_);
lean_ctor_set(v___x_1969_, 1, v___x_1968_);
v___x_1970_ = l_Lean_Syntax_node5(v___x_1962_, v___x_1963_, v___x_1965_, v___x_1716_, v___x_1967_, v___x_1961_, v___x_1969_);
v___x_1971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1970_);
lean_ctor_set(v___x_1971_, 1, v_a_1704_);
return v___x_1971_;
}
else
{
lean_object* v___x_1972_; uint8_t v___x_1973_; 
v___x_1972_ = l_Lean_Syntax_getArg(v___x_1946_, v___x_1709_);
v___x_1973_ = l_Lean_Syntax_matchesNull(v___x_1972_, v___x_1715_);
if (v___x_1973_ == 0)
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
lean_dec(v___x_1946_);
lean_dec(v___x_1866_);
lean_dec(v___x_1757_);
v___x_1974_ = l_Lean_Syntax_getArg(v___x_1710_, v___x_1709_);
lean_dec(v___x_1710_);
v___x_1975_ = l_Lean_SourceInfo_fromRef(v_a_1703_, v___x_1973_);
v___x_1976_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1977_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1975_, 3);
v___x_1978_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1975_);
lean_ctor_set(v___x_1978_, 1, v___x_1977_);
v___x_1979_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1980_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1975_);
lean_ctor_set(v___x_1980_, 1, v___x_1979_);
v___x_1981_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1982_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1975_);
lean_ctor_set(v___x_1982_, 1, v___x_1981_);
v___x_1983_ = l_Lean_Syntax_node5(v___x_1975_, v___x_1976_, v___x_1978_, v___x_1716_, v___x_1980_, v___x_1974_, v___x_1982_);
v___x_1984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1983_);
lean_ctor_set(v___x_1984_, 1, v_a_1704_);
return v___x_1984_;
}
else
{
lean_object* v___x_1985_; uint8_t v___x_1986_; 
v___x_1985_ = l_Lean_Syntax_getArg(v___x_1946_, v___x_1711_);
lean_dec(v___x_1946_);
lean_inc(v___x_1985_);
v___x_1986_ = l_Lean_Syntax_isOfKind(v___x_1985_, v___x_1867_);
if (v___x_1986_ == 0)
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; 
lean_dec(v___x_1985_);
lean_dec(v___x_1866_);
lean_dec(v___x_1757_);
v___x_1987_ = l_Lean_Syntax_getArg(v___x_1710_, v___x_1709_);
lean_dec(v___x_1710_);
v___x_1988_ = l_Lean_SourceInfo_fromRef(v_a_1703_, v___x_1986_);
v___x_1989_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1990_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1988_, 3);
v___x_1991_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1988_);
lean_ctor_set(v___x_1991_, 1, v___x_1990_);
v___x_1992_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1993_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1988_);
lean_ctor_set(v___x_1993_, 1, v___x_1992_);
v___x_1994_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1995_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1988_);
lean_ctor_set(v___x_1995_, 1, v___x_1994_);
v___x_1996_ = l_Lean_Syntax_node5(v___x_1988_, v___x_1989_, v___x_1991_, v___x_1716_, v___x_1993_, v___x_1987_, v___x_1995_);
v___x_1997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1996_);
lean_ctor_set(v___x_1997_, 1, v_a_1704_);
return v___x_1997_;
}
else
{
lean_object* v___x_1998_; uint8_t v___x_1999_; 
v___x_1998_ = l_Lean_Syntax_getArg(v___x_1985_, v___x_1709_);
v___x_1999_ = l_Lean_Syntax_matchesNull(v___x_1998_, v___x_1715_);
if (v___x_1999_ == 0)
{
lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
lean_dec(v___x_1985_);
lean_dec(v___x_1866_);
lean_dec(v___x_1757_);
v___x_2000_ = l_Lean_Syntax_getArg(v___x_1710_, v___x_1709_);
lean_dec(v___x_1710_);
v___x_2001_ = l_Lean_SourceInfo_fromRef(v_a_1703_, v___x_1999_);
v___x_2002_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2003_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2001_, 3);
v___x_2004_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2001_);
lean_ctor_set(v___x_2004_, 1, v___x_2003_);
v___x_2005_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2006_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2006_, 0, v___x_2001_);
lean_ctor_set(v___x_2006_, 1, v___x_2005_);
v___x_2007_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2008_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2008_, 0, v___x_2001_);
lean_ctor_set(v___x_2008_, 1, v___x_2007_);
v___x_2009_ = l_Lean_Syntax_node5(v___x_2001_, v___x_2002_, v___x_2004_, v___x_1716_, v___x_2006_, v___x_2000_, v___x_2008_);
v___x_2010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2009_);
lean_ctor_set(v___x_2010_, 1, v_a_1704_);
return v___x_2010_;
}
else
{
lean_object* v___x_2011_; lean_object* v___x_2012_; uint8_t v___x_2013_; 
v___x_2011_ = lean_unsigned_to_nat(4u);
v___x_2012_ = l_Lean_Syntax_getArg(v___x_1757_, v___x_2011_);
lean_dec(v___x_1757_);
lean_inc(v___x_2012_);
v___x_2013_ = l_Lean_Syntax_isOfKind(v___x_2012_, v___x_1772_);
if (v___x_2013_ == 0)
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
lean_dec(v___x_2012_);
lean_dec(v___x_1985_);
lean_dec(v___x_1866_);
v___x_2014_ = l_Lean_Syntax_getArg(v___x_1710_, v___x_1709_);
lean_dec(v___x_1710_);
v___x_2015_ = l_Lean_SourceInfo_fromRef(v_a_1703_, v___x_2013_);
v___x_2016_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2017_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2015_, 3);
v___x_2018_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2018_, 0, v___x_2015_);
lean_ctor_set(v___x_2018_, 1, v___x_2017_);
v___x_2019_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2020_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2020_, 0, v___x_2015_);
lean_ctor_set(v___x_2020_, 1, v___x_2019_);
v___x_2021_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2022_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2015_);
lean_ctor_set(v___x_2022_, 1, v___x_2021_);
v___x_2023_ = l_Lean_Syntax_node5(v___x_2015_, v___x_2016_, v___x_2018_, v___x_1716_, v___x_2020_, v___x_2014_, v___x_2022_);
v___x_2024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2024_, 0, v___x_2023_);
lean_ctor_set(v___x_2024_, 1, v_a_1704_);
return v___x_2024_;
}
else
{
lean_object* v___x_2025_; uint8_t v___x_2026_; 
v___x_2025_ = l_Lean_Syntax_getArg(v___x_2012_, v___x_1715_);
lean_inc(v___x_2025_);
v___x_2026_ = l_Lean_Syntax_isOfKind(v___x_2025_, v___x_1786_);
if (v___x_2026_ == 0)
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
lean_dec(v___x_2025_);
lean_dec(v___x_2012_);
lean_dec(v___x_1985_);
lean_dec(v___x_1866_);
v___x_2027_ = l_Lean_Syntax_getArg(v___x_1710_, v___x_1709_);
lean_dec(v___x_1710_);
v___x_2028_ = l_Lean_SourceInfo_fromRef(v_a_1703_, v___x_2026_);
v___x_2029_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2030_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2028_, 3);
v___x_2031_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2028_);
lean_ctor_set(v___x_2031_, 1, v___x_2030_);
v___x_2032_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2033_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2028_);
lean_ctor_set(v___x_2033_, 1, v___x_2032_);
v___x_2034_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2035_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2028_);
lean_ctor_set(v___x_2035_, 1, v___x_2034_);
v___x_2036_ = l_Lean_Syntax_node5(v___x_2028_, v___x_2029_, v___x_2031_, v___x_1716_, v___x_2033_, v___x_2027_, v___x_2035_);
v___x_2037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2036_);
lean_ctor_set(v___x_2037_, 1, v_a_1704_);
return v___x_2037_;
}
else
{
lean_object* v___x_2038_; lean_object* v___x_2039_; uint8_t v___x_2040_; 
v___x_2038_ = l_Lean_Syntax_getArg(v___x_2025_, v___x_1715_);
v___x_2039_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__16));
v___x_2040_ = l_Lean_Syntax_matchesIdent(v___x_2038_, v___x_2039_);
lean_dec(v___x_2038_);
if (v___x_2040_ == 0)
{
lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
lean_dec(v___x_2025_);
lean_dec(v___x_2012_);
lean_dec(v___x_1985_);
lean_dec(v___x_1866_);
v___x_2041_ = l_Lean_Syntax_getArg(v___x_1710_, v___x_1709_);
lean_dec(v___x_1710_);
v___x_2042_ = l_Lean_SourceInfo_fromRef(v_a_1703_, v___x_2040_);
v___x_2043_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2044_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2042_, 3);
v___x_2045_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2042_);
lean_ctor_set(v___x_2045_, 1, v___x_2044_);
v___x_2046_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2047_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2042_);
lean_ctor_set(v___x_2047_, 1, v___x_2046_);
v___x_2048_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2049_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2042_);
lean_ctor_set(v___x_2049_, 1, v___x_2048_);
v___x_2050_ = l_Lean_Syntax_node5(v___x_2042_, v___x_2043_, v___x_2045_, v___x_1716_, v___x_2047_, v___x_2041_, v___x_2049_);
v___x_2051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2050_);
lean_ctor_set(v___x_2051_, 1, v_a_1704_);
return v___x_2051_;
}
else
{
lean_object* v___x_2052_; uint8_t v___x_2053_; 
v___x_2052_ = l_Lean_Syntax_getArg(v___x_2025_, v___x_1709_);
lean_dec(v___x_2025_);
v___x_2053_ = l_Lean_Syntax_matchesNull(v___x_2052_, v___x_1715_);
if (v___x_2053_ == 0)
{
lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
lean_dec(v___x_2012_);
lean_dec(v___x_1985_);
lean_dec(v___x_1866_);
v___x_2054_ = l_Lean_Syntax_getArg(v___x_1710_, v___x_1709_);
lean_dec(v___x_1710_);
v___x_2055_ = l_Lean_SourceInfo_fromRef(v_a_1703_, v___x_2053_);
v___x_2056_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2057_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2055_, 3);
v___x_2058_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2055_);
lean_ctor_set(v___x_2058_, 1, v___x_2057_);
v___x_2059_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2060_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2055_);
lean_ctor_set(v___x_2060_, 1, v___x_2059_);
v___x_2061_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2062_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2055_);
lean_ctor_set(v___x_2062_, 1, v___x_2061_);
v___x_2063_ = l_Lean_Syntax_node5(v___x_2055_, v___x_2056_, v___x_2058_, v___x_1716_, v___x_2060_, v___x_2054_, v___x_2062_);
v___x_2064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2063_);
lean_ctor_set(v___x_2064_, 1, v_a_1704_);
return v___x_2064_;
}
else
{
lean_object* v___x_2065_; uint8_t v___x_2066_; 
v___x_2065_ = l_Lean_Syntax_getArg(v___x_2012_, v___x_1709_);
lean_dec(v___x_2012_);
lean_inc(v___x_2065_);
v___x_2066_ = l_Lean_Syntax_matchesNull(v___x_2065_, v___x_1827_);
if (v___x_2066_ == 0)
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
lean_dec(v___x_2065_);
lean_dec(v___x_1985_);
lean_dec(v___x_1866_);
v___x_2067_ = l_Lean_Syntax_getArg(v___x_1710_, v___x_1709_);
lean_dec(v___x_1710_);
v___x_2068_ = l_Lean_SourceInfo_fromRef(v_a_1703_, v___x_2066_);
v___x_2069_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2070_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2068_, 3);
v___x_2071_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2068_);
lean_ctor_set(v___x_2071_, 1, v___x_2070_);
v___x_2072_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2073_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2068_);
lean_ctor_set(v___x_2073_, 1, v___x_2072_);
v___x_2074_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2075_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2068_);
lean_ctor_set(v___x_2075_, 1, v___x_2074_);
v___x_2076_ = l_Lean_Syntax_node5(v___x_2068_, v___x_2069_, v___x_2071_, v___x_1716_, v___x_2073_, v___x_2067_, v___x_2075_);
v___x_2077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2076_);
lean_ctor_set(v___x_2077_, 1, v_a_1704_);
return v___x_2077_;
}
else
{
lean_object* v___x_2078_; uint8_t v___x_2079_; 
v___x_2078_ = l_Lean_Syntax_getArg(v___x_2065_, v___x_1715_);
v___x_2079_ = l_Lean_Syntax_matchesNull(v___x_2078_, v___x_1715_);
if (v___x_2079_ == 0)
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
lean_dec(v___x_2065_);
lean_dec(v___x_1985_);
lean_dec(v___x_1866_);
v___x_2080_ = l_Lean_Syntax_getArg(v___x_1710_, v___x_1709_);
lean_dec(v___x_1710_);
v___x_2081_ = l_Lean_SourceInfo_fromRef(v_a_1703_, v___x_2079_);
v___x_2082_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2083_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2081_, 3);
v___x_2084_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2081_);
lean_ctor_set(v___x_2084_, 1, v___x_2083_);
v___x_2085_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2086_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2081_);
lean_ctor_set(v___x_2086_, 1, v___x_2085_);
v___x_2087_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2088_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2081_);
lean_ctor_set(v___x_2088_, 1, v___x_2087_);
v___x_2089_ = l_Lean_Syntax_node5(v___x_2081_, v___x_2082_, v___x_2084_, v___x_1716_, v___x_2086_, v___x_2080_, v___x_2088_);
v___x_2090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2089_);
lean_ctor_set(v___x_2090_, 1, v_a_1704_);
return v___x_2090_;
}
else
{
lean_object* v___x_2091_; uint8_t v___x_2092_; 
v___x_2091_ = l_Lean_Syntax_getArg(v___x_2065_, v___x_1709_);
v___x_2092_ = l_Lean_Syntax_matchesNull(v___x_2091_, v___x_1715_);
if (v___x_2092_ == 0)
{
lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
lean_dec(v___x_2065_);
lean_dec(v___x_1985_);
lean_dec(v___x_1866_);
v___x_2093_ = l_Lean_Syntax_getArg(v___x_1710_, v___x_1709_);
lean_dec(v___x_1710_);
v___x_2094_ = l_Lean_SourceInfo_fromRef(v_a_1703_, v___x_2092_);
v___x_2095_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2096_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2094_, 3);
v___x_2097_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2094_);
lean_ctor_set(v___x_2097_, 1, v___x_2096_);
v___x_2098_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2099_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2094_);
lean_ctor_set(v___x_2099_, 1, v___x_2098_);
v___x_2100_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2101_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2094_);
lean_ctor_set(v___x_2101_, 1, v___x_2100_);
v___x_2102_ = l_Lean_Syntax_node5(v___x_2094_, v___x_2095_, v___x_2097_, v___x_1716_, v___x_2099_, v___x_2093_, v___x_2101_);
v___x_2103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2102_);
lean_ctor_set(v___x_2103_, 1, v_a_1704_);
return v___x_2103_;
}
else
{
lean_object* v___x_2104_; uint8_t v___x_2105_; 
v___x_2104_ = l_Lean_Syntax_getArg(v___x_2065_, v___x_1711_);
lean_dec(v___x_2065_);
lean_inc(v___x_2104_);
v___x_2105_ = l_Lean_Syntax_isOfKind(v___x_2104_, v___x_1867_);
if (v___x_2105_ == 0)
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
lean_dec(v___x_2104_);
lean_dec(v___x_1985_);
lean_dec(v___x_1866_);
v___x_2106_ = l_Lean_Syntax_getArg(v___x_1710_, v___x_1709_);
lean_dec(v___x_1710_);
v___x_2107_ = l_Lean_SourceInfo_fromRef(v_a_1703_, v___x_2105_);
v___x_2108_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2109_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2107_, 3);
v___x_2110_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2107_);
lean_ctor_set(v___x_2110_, 1, v___x_2109_);
v___x_2111_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2112_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2107_);
lean_ctor_set(v___x_2112_, 1, v___x_2111_);
v___x_2113_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2114_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2107_);
lean_ctor_set(v___x_2114_, 1, v___x_2113_);
v___x_2115_ = l_Lean_Syntax_node5(v___x_2107_, v___x_2108_, v___x_2110_, v___x_1716_, v___x_2112_, v___x_2106_, v___x_2114_);
v___x_2116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2115_);
lean_ctor_set(v___x_2116_, 1, v_a_1704_);
return v___x_2116_;
}
else
{
lean_object* v___x_2117_; uint8_t v___x_2118_; 
v___x_2117_ = l_Lean_Syntax_getArg(v___x_2104_, v___x_1709_);
v___x_2118_ = l_Lean_Syntax_matchesNull(v___x_2117_, v___x_1715_);
if (v___x_2118_ == 0)
{
lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
lean_dec(v___x_2104_);
lean_dec(v___x_1985_);
lean_dec(v___x_1866_);
v___x_2119_ = l_Lean_Syntax_getArg(v___x_1710_, v___x_1709_);
lean_dec(v___x_1710_);
v___x_2120_ = l_Lean_SourceInfo_fromRef(v_a_1703_, v___x_2118_);
v___x_2121_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2122_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2120_, 3);
v___x_2123_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2120_);
lean_ctor_set(v___x_2123_, 1, v___x_2122_);
v___x_2124_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2125_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2120_);
lean_ctor_set(v___x_2125_, 1, v___x_2124_);
v___x_2126_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2127_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2120_);
lean_ctor_set(v___x_2127_, 1, v___x_2126_);
v___x_2128_ = l_Lean_Syntax_node5(v___x_2120_, v___x_2121_, v___x_2123_, v___x_1716_, v___x_2125_, v___x_2119_, v___x_2127_);
v___x_2129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2128_);
lean_ctor_set(v___x_2129_, 1, v_a_1704_);
return v___x_2129_;
}
else
{
lean_object* v___x_2130_; lean_object* v___x_2131_; uint8_t v___x_2132_; 
v___x_2130_ = l_Lean_Syntax_getArg(v___x_1716_, v___x_1827_);
v___x_2131_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__18));
lean_inc(v___x_2130_);
v___x_2132_ = l_Lean_Syntax_isOfKind(v___x_2130_, v___x_2131_);
if (v___x_2132_ == 0)
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
lean_dec(v___x_2130_);
lean_dec(v___x_2104_);
lean_dec(v___x_1985_);
lean_dec(v___x_1866_);
v___x_2133_ = l_Lean_Syntax_getArg(v___x_1710_, v___x_1709_);
lean_dec(v___x_1710_);
v___x_2134_ = l_Lean_SourceInfo_fromRef(v_a_1703_, v___x_2132_);
v___x_2135_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2136_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2134_, 3);
v___x_2137_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2137_, 0, v___x_2134_);
lean_ctor_set(v___x_2137_, 1, v___x_2136_);
v___x_2138_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2139_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2134_);
lean_ctor_set(v___x_2139_, 1, v___x_2138_);
v___x_2140_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2141_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2141_, 0, v___x_2134_);
lean_ctor_set(v___x_2141_, 1, v___x_2140_);
v___x_2142_ = l_Lean_Syntax_node5(v___x_2134_, v___x_2135_, v___x_2137_, v___x_1716_, v___x_2139_, v___x_2133_, v___x_2141_);
v___x_2143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2142_);
lean_ctor_set(v___x_2143_, 1, v_a_1704_);
return v___x_2143_;
}
else
{
lean_object* v___x_2144_; uint8_t v___x_2145_; 
v___x_2144_ = l_Lean_Syntax_getArg(v___x_2130_, v___x_1715_);
lean_dec(v___x_2130_);
v___x_2145_ = l_Lean_Syntax_matchesNull(v___x_2144_, v___x_1715_);
if (v___x_2145_ == 0)
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; 
lean_dec(v___x_2104_);
lean_dec(v___x_1985_);
lean_dec(v___x_1866_);
v___x_2146_ = l_Lean_Syntax_getArg(v___x_1710_, v___x_1709_);
lean_dec(v___x_1710_);
v___x_2147_ = l_Lean_SourceInfo_fromRef(v_a_1703_, v___x_2145_);
v___x_2148_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2149_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2147_, 3);
v___x_2150_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2147_);
lean_ctor_set(v___x_2150_, 1, v___x_2149_);
v___x_2151_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2152_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2147_);
lean_ctor_set(v___x_2152_, 1, v___x_2151_);
v___x_2153_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2154_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2147_);
lean_ctor_set(v___x_2154_, 1, v___x_2153_);
v___x_2155_ = l_Lean_Syntax_node5(v___x_2147_, v___x_2148_, v___x_2150_, v___x_1716_, v___x_2152_, v___x_2146_, v___x_2154_);
v___x_2156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2155_);
lean_ctor_set(v___x_2156_, 1, v_a_1704_);
return v___x_2156_;
}
else
{
lean_object* v___x_2157_; uint8_t v___x_2158_; 
v___x_2157_ = l_Lean_Syntax_getArg(v___x_1716_, v___x_2011_);
v___x_2158_ = l_Lean_Syntax_matchesNull(v___x_2157_, v___x_1715_);
if (v___x_2158_ == 0)
{
lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
lean_dec(v___x_2104_);
lean_dec(v___x_1985_);
lean_dec(v___x_1866_);
v___x_2159_ = l_Lean_Syntax_getArg(v___x_1710_, v___x_1709_);
lean_dec(v___x_1710_);
v___x_2160_ = l_Lean_SourceInfo_fromRef(v_a_1703_, v___x_2158_);
v___x_2161_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2162_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2160_, 3);
v___x_2163_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2160_);
lean_ctor_set(v___x_2163_, 1, v___x_2162_);
v___x_2164_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2165_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2160_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
v___x_2166_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2167_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2167_, 0, v___x_2160_);
lean_ctor_set(v___x_2167_, 1, v___x_2166_);
v___x_2168_ = l_Lean_Syntax_node5(v___x_2160_, v___x_2161_, v___x_2163_, v___x_1716_, v___x_2165_, v___x_2159_, v___x_2167_);
v___x_2169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2168_);
lean_ctor_set(v___x_2169_, 1, v_a_1704_);
return v___x_2169_;
}
else
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; uint8_t v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
lean_dec(v___x_1716_);
v___x_2170_ = l_Lean_Syntax_getArg(v___x_1866_, v___x_1711_);
lean_dec(v___x_1866_);
v___x_2171_ = l_Lean_Syntax_getArg(v___x_1985_, v___x_1711_);
lean_dec(v___x_1985_);
v___x_2172_ = l_Lean_Syntax_getArg(v___x_2104_, v___x_1711_);
lean_dec(v___x_2104_);
v___x_2173_ = l_Lean_Syntax_getArg(v___x_1710_, v___x_1709_);
lean_dec(v___x_1710_);
v___x_2174_ = 0;
v___x_2175_ = l_Lean_SourceInfo_fromRef(v_a_1703_, v___x_2174_);
v___x_2176_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__1));
v___x_2177_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2175_, 7);
v___x_2178_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2178_, 0, v___x_2175_);
lean_ctor_set(v___x_2178_, 1, v___x_2177_);
v___x_2179_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2180_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2175_);
lean_ctor_set(v___x_2180_, 1, v___x_2179_);
v___x_2181_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__20));
v___x_2182_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__21));
v___x_2183_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2175_);
lean_ctor_set(v___x_2183_, 1, v___x_2182_);
v___x_2184_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__14));
lean_inc_ref_n(v___x_2180_, 2);
v___x_2185_ = l_Lean_Syntax_node3(v___x_2175_, v___x_2184_, v___x_2171_, v___x_2180_, v___x_2172_);
v___x_2186_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__22));
v___x_2187_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2187_, 0, v___x_2175_);
lean_ctor_set(v___x_2187_, 1, v___x_2186_);
v___x_2188_ = l_Lean_Syntax_node3(v___x_2175_, v___x_2181_, v___x_2183_, v___x_2185_, v___x_2187_);
v___x_2189_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2190_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2175_);
lean_ctor_set(v___x_2190_, 1, v___x_2189_);
v___x_2191_ = l_Lean_Syntax_node7(v___x_2175_, v___x_2176_, v___x_2178_, v___x_2170_, v___x_2180_, v___x_2188_, v___x_2180_, v___x_2173_, v___x_2190_);
v___x_2192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2191_);
lean_ctor_set(v___x_2192_, 1, v_a_1704_);
return v___x_2192_;
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_unexpandDenote___boxed(lean_object* v_x_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_){
_start:
{
lean_object* v_res_2196_; 
v_res_2196_ = l_Std_Sat_AIG_unexpandDenote(v_x_2193_, v_a_2194_, v_a_2195_);
lean_dec(v_a_2194_);
return v_res_2196_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGate___redArg(lean_object* v_aig_2197_, lean_object* v_input_2198_){
_start:
{
lean_object* v_lhs_2199_; lean_object* v_rhs_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2238_; 
v_lhs_2199_ = lean_ctor_get(v_input_2198_, 0);
v_rhs_2200_ = lean_ctor_get(v_input_2198_, 1);
v_isSharedCheck_2238_ = !lean_is_exclusive(v_input_2198_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2202_ = v_input_2198_;
v_isShared_2203_ = v_isSharedCheck_2238_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_rhs_2200_);
lean_inc(v_lhs_2199_);
lean_dec(v_input_2198_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2238_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v_decls_2204_; lean_object* v_cache_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2237_; 
v_decls_2204_ = lean_ctor_get(v_aig_2197_, 0);
v_cache_2205_ = lean_ctor_get(v_aig_2197_, 1);
v_isSharedCheck_2237_ = !lean_is_exclusive(v_aig_2197_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2207_ = v_aig_2197_;
v_isShared_2208_ = v_isSharedCheck_2237_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_cache_2205_);
lean_inc(v_decls_2204_);
lean_dec(v_aig_2197_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2237_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v_gate_2209_; uint8_t v_invert_2210_; lean_object* v_gate_2211_; uint8_t v_invert_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2236_; 
v_gate_2209_ = lean_ctor_get(v_lhs_2199_, 0);
lean_inc(v_gate_2209_);
v_invert_2210_ = lean_ctor_get_uint8(v_lhs_2199_, sizeof(void*)*1);
lean_dec_ref(v_lhs_2199_);
v_gate_2211_ = lean_ctor_get(v_rhs_2200_, 0);
v_invert_2212_ = lean_ctor_get_uint8(v_rhs_2200_, sizeof(void*)*1);
v_isSharedCheck_2236_ = !lean_is_exclusive(v_rhs_2200_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2214_ = v_rhs_2200_;
v_isShared_2215_ = v_isSharedCheck_2236_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_gate_2211_);
lean_dec(v_rhs_2200_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2236_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v_g_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2225_; 
v_g_2216_ = lean_array_get_size(v_decls_2204_);
v___x_2217_ = lean_unsigned_to_nat(2u);
v___x_2218_ = lean_nat_mul(v_gate_2209_, v___x_2217_);
lean_dec(v_gate_2209_);
v___x_2219_ = l_Bool_toNat(v_invert_2210_);
v___x_2220_ = lean_nat_lor(v___x_2218_, v___x_2219_);
lean_dec(v___x_2219_);
lean_dec(v___x_2218_);
v___x_2221_ = lean_nat_mul(v_gate_2211_, v___x_2217_);
lean_dec(v_gate_2211_);
v___x_2222_ = l_Bool_toNat(v_invert_2212_);
v___x_2223_ = lean_nat_lor(v___x_2221_, v___x_2222_);
lean_dec(v___x_2222_);
lean_dec(v___x_2221_);
if (v_isShared_2203_ == 0)
{
lean_ctor_set_tag(v___x_2202_, 2);
lean_ctor_set(v___x_2202_, 1, v___x_2223_);
lean_ctor_set(v___x_2202_, 0, v___x_2220_);
v___x_2225_ = v___x_2202_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_2220_);
lean_ctor_set(v_reuseFailAlloc_2235_, 1, v___x_2223_);
v___x_2225_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
lean_object* v_decls_2226_; lean_object* v___x_2228_; 
v_decls_2226_ = lean_array_push(v_decls_2204_, v___x_2225_);
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 0, v_decls_2226_);
v___x_2228_ = v___x_2207_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_decls_2226_);
lean_ctor_set(v_reuseFailAlloc_2234_, 1, v_cache_2205_);
v___x_2228_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
uint8_t v___x_2229_; lean_object* v___x_2231_; 
v___x_2229_ = 0;
if (v_isShared_2215_ == 0)
{
lean_ctor_set(v___x_2214_, 0, v_g_2216_);
v___x_2231_ = v___x_2214_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_g_2216_);
v___x_2231_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
lean_object* v___x_2232_; 
lean_ctor_set_uint8(v___x_2231_, sizeof(void*)*1, v___x_2229_);
v___x_2232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2228_);
lean_ctor_set(v___x_2232_, 1, v___x_2231_);
return v___x_2232_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGate(lean_object* v_00_u03b1_2239_, lean_object* v_inst_2240_, lean_object* v_inst_2241_, lean_object* v_aig_2242_, lean_object* v_input_2243_){
_start:
{
lean_object* v___x_2244_; 
v___x_2244_ = l_Std_Sat_AIG_mkGate___redArg(v_aig_2242_, v_input_2243_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGate___boxed(lean_object* v_00_u03b1_2245_, lean_object* v_inst_2246_, lean_object* v_inst_2247_, lean_object* v_aig_2248_, lean_object* v_input_2249_){
_start:
{
lean_object* v_res_2250_; 
v_res_2250_ = l_Std_Sat_AIG_mkGate(v_00_u03b1_2245_, v_inst_2246_, v_inst_2247_, v_aig_2248_, v_input_2249_);
lean_dec_ref(v_inst_2247_);
lean_dec_ref(v_inst_2246_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtom___redArg(lean_object* v_aig_2251_, lean_object* v_n_2252_){
_start:
{
lean_object* v_decls_2253_; lean_object* v_cache_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2267_; 
v_decls_2253_ = lean_ctor_get(v_aig_2251_, 0);
v_cache_2254_ = lean_ctor_get(v_aig_2251_, 1);
v_isSharedCheck_2267_ = !lean_is_exclusive(v_aig_2251_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2256_ = v_aig_2251_;
v_isShared_2257_ = v_isSharedCheck_2267_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_cache_2254_);
lean_inc(v_decls_2253_);
lean_dec(v_aig_2251_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2267_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v_g_2258_; lean_object* v___x_2259_; lean_object* v_decls_2260_; lean_object* v___x_2262_; 
v_g_2258_ = lean_array_get_size(v_decls_2253_);
v___x_2259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2259_, 0, v_n_2252_);
v_decls_2260_ = lean_array_push(v_decls_2253_, v___x_2259_);
if (v_isShared_2257_ == 0)
{
lean_ctor_set(v___x_2256_, 0, v_decls_2260_);
v___x_2262_ = v___x_2256_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_decls_2260_);
lean_ctor_set(v_reuseFailAlloc_2266_, 1, v_cache_2254_);
v___x_2262_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
uint8_t v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2263_ = 0;
v___x_2264_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2264_, 0, v_g_2258_);
lean_ctor_set_uint8(v___x_2264_, sizeof(void*)*1, v___x_2263_);
v___x_2265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2262_);
lean_ctor_set(v___x_2265_, 1, v___x_2264_);
return v___x_2265_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtom(lean_object* v_00_u03b1_2268_, lean_object* v_inst_2269_, lean_object* v_inst_2270_, lean_object* v_aig_2271_, lean_object* v_n_2272_){
_start:
{
lean_object* v___x_2273_; 
v___x_2273_ = l_Std_Sat_AIG_mkAtom___redArg(v_aig_2271_, v_n_2272_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtom___boxed(lean_object* v_00_u03b1_2274_, lean_object* v_inst_2275_, lean_object* v_inst_2276_, lean_object* v_aig_2277_, lean_object* v_n_2278_){
_start:
{
lean_object* v_res_2279_; 
v_res_2279_ = l_Std_Sat_AIG_mkAtom(v_00_u03b1_2274_, v_inst_2275_, v_inst_2276_, v_aig_2277_, v_n_2278_);
lean_dec_ref(v_inst_2276_);
lean_dec_ref(v_inst_2275_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConst___redArg(lean_object* v_aig_2280_, uint8_t v_val_2281_){
_start:
{
lean_object* v_decls_2282_; lean_object* v_cache_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2295_; 
v_decls_2282_ = lean_ctor_get(v_aig_2280_, 0);
v_cache_2283_ = lean_ctor_get(v_aig_2280_, 1);
v_isSharedCheck_2295_ = !lean_is_exclusive(v_aig_2280_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2285_ = v_aig_2280_;
v_isShared_2286_ = v_isSharedCheck_2295_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_cache_2283_);
lean_inc(v_decls_2282_);
lean_dec(v_aig_2280_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2295_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v_g_2287_; lean_object* v___x_2288_; lean_object* v_decls_2289_; lean_object* v___x_2291_; 
v_g_2287_ = lean_array_get_size(v_decls_2282_);
v___x_2288_ = lean_box(0);
v_decls_2289_ = lean_array_push(v_decls_2282_, v___x_2288_);
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 0, v_decls_2289_);
v___x_2291_ = v___x_2285_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_decls_2289_);
lean_ctor_set(v_reuseFailAlloc_2294_, 1, v_cache_2283_);
v___x_2291_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2292_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2292_, 0, v_g_2287_);
lean_ctor_set_uint8(v___x_2292_, sizeof(void*)*1, v_val_2281_);
v___x_2293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2291_);
lean_ctor_set(v___x_2293_, 1, v___x_2292_);
return v___x_2293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConst___redArg___boxed(lean_object* v_aig_2296_, lean_object* v_val_2297_){
_start:
{
uint8_t v_val_boxed_2298_; lean_object* v_res_2299_; 
v_val_boxed_2298_ = lean_unbox(v_val_2297_);
v_res_2299_ = l_Std_Sat_AIG_mkConst___redArg(v_aig_2296_, v_val_boxed_2298_);
return v_res_2299_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConst(lean_object* v_00_u03b1_2300_, lean_object* v_inst_2301_, lean_object* v_inst_2302_, lean_object* v_aig_2303_, uint8_t v_val_2304_){
_start:
{
lean_object* v___x_2305_; 
v___x_2305_ = l_Std_Sat_AIG_mkConst___redArg(v_aig_2303_, v_val_2304_);
return v___x_2305_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConst___boxed(lean_object* v_00_u03b1_2306_, lean_object* v_inst_2307_, lean_object* v_inst_2308_, lean_object* v_aig_2309_, lean_object* v_val_2310_){
_start:
{
uint8_t v_val_boxed_2311_; lean_object* v_res_2312_; 
v_val_boxed_2311_ = lean_unbox(v_val_2310_);
v_res_2312_ = l_Std_Sat_AIG_mkConst(v_00_u03b1_2306_, v_inst_2307_, v_inst_2308_, v_aig_2309_, v_val_boxed_2311_);
lean_dec_ref(v_inst_2308_);
lean_dec_ref(v_inst_2307_);
return v_res_2312_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_isConstant___redArg(lean_object* v_aig_2313_, lean_object* v_ref_2314_, uint8_t v_b_2315_){
_start:
{
lean_object* v_gate_2316_; uint8_t v_invert_2317_; lean_object* v_decls_2318_; lean_object* v_decl_2319_; uint8_t v___y_2321_; 
v_gate_2316_ = lean_ctor_get(v_ref_2314_, 0);
v_invert_2317_ = lean_ctor_get_uint8(v_ref_2314_, sizeof(void*)*1);
v_decls_2318_ = lean_ctor_get(v_aig_2313_, 0);
v_decl_2319_ = lean_array_fget_borrowed(v_decls_2318_, v_gate_2316_);
if (v_invert_2317_ == 0)
{
if (v_b_2315_ == 0)
{
uint8_t v___x_2323_; 
v___x_2323_ = 1;
v___y_2321_ = v___x_2323_;
goto v___jp_2320_;
}
else
{
v___y_2321_ = v_invert_2317_;
goto v___jp_2320_;
}
}
else
{
v___y_2321_ = v_b_2315_;
goto v___jp_2320_;
}
v___jp_2320_:
{
if (lean_obj_tag(v_decl_2319_) == 0)
{
return v___y_2321_;
}
else
{
uint8_t v___x_2322_; 
v___x_2322_ = 0;
return v___x_2322_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_isConstant___redArg___boxed(lean_object* v_aig_2324_, lean_object* v_ref_2325_, lean_object* v_b_2326_){
_start:
{
uint8_t v_b_boxed_2327_; uint8_t v_res_2328_; lean_object* v_r_2329_; 
v_b_boxed_2327_ = lean_unbox(v_b_2326_);
v_res_2328_ = l_Std_Sat_AIG_isConstant___redArg(v_aig_2324_, v_ref_2325_, v_b_boxed_2327_);
lean_dec_ref(v_ref_2325_);
lean_dec_ref(v_aig_2324_);
v_r_2329_ = lean_box(v_res_2328_);
return v_r_2329_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_isConstant(lean_object* v_00_u03b1_2330_, lean_object* v_inst_2331_, lean_object* v_inst_2332_, lean_object* v_aig_2333_, lean_object* v_ref_2334_, uint8_t v_b_2335_){
_start:
{
uint8_t v___x_2336_; 
v___x_2336_ = l_Std_Sat_AIG_isConstant___redArg(v_aig_2333_, v_ref_2334_, v_b_2335_);
return v___x_2336_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_isConstant___boxed(lean_object* v_00_u03b1_2337_, lean_object* v_inst_2338_, lean_object* v_inst_2339_, lean_object* v_aig_2340_, lean_object* v_ref_2341_, lean_object* v_b_2342_){
_start:
{
uint8_t v_b_boxed_2343_; uint8_t v_res_2344_; lean_object* v_r_2345_; 
v_b_boxed_2343_ = lean_unbox(v_b_2342_);
v_res_2344_ = l_Std_Sat_AIG_isConstant(v_00_u03b1_2337_, v_inst_2338_, v_inst_2339_, v_aig_2340_, v_ref_2341_, v_b_boxed_2343_);
lean_dec_ref(v_ref_2341_);
lean_dec_ref(v_aig_2340_);
lean_dec_ref(v_inst_2339_);
lean_dec_ref(v_inst_2338_);
v_r_2345_ = lean_box(v_res_2344_);
return v_r_2345_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___redArg(lean_object* v_aig_2346_, lean_object* v_ref_2347_){
_start:
{
lean_object* v_gate_2348_; uint8_t v_invert_2349_; lean_object* v_decls_2350_; lean_object* v_decl_2351_; 
v_gate_2348_ = lean_ctor_get(v_ref_2347_, 0);
v_invert_2349_ = lean_ctor_get_uint8(v_ref_2347_, sizeof(void*)*1);
v_decls_2350_ = lean_ctor_get(v_aig_2346_, 0);
v_decl_2351_ = lean_array_fget_borrowed(v_decls_2350_, v_gate_2348_);
if (lean_obj_tag(v_decl_2351_) == 0)
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2352_ = lean_box(v_invert_2349_);
v___x_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2352_);
return v___x_2353_;
}
else
{
lean_object* v___x_2354_; 
v___x_2354_ = lean_box(0);
return v___x_2354_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___redArg___boxed(lean_object* v_aig_2355_, lean_object* v_ref_2356_){
_start:
{
lean_object* v_res_2357_; 
v_res_2357_ = l_Std_Sat_AIG_getConstant___redArg(v_aig_2355_, v_ref_2356_);
lean_dec_ref(v_ref_2356_);
lean_dec_ref(v_aig_2355_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant(lean_object* v_00_u03b1_2358_, lean_object* v_inst_2359_, lean_object* v_inst_2360_, lean_object* v_aig_2361_, lean_object* v_ref_2362_){
_start:
{
lean_object* v___x_2363_; 
v___x_2363_ = l_Std_Sat_AIG_getConstant___redArg(v_aig_2361_, v_ref_2362_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___boxed(lean_object* v_00_u03b1_2364_, lean_object* v_inst_2365_, lean_object* v_inst_2366_, lean_object* v_aig_2367_, lean_object* v_ref_2368_){
_start:
{
lean_object* v_res_2369_; 
v_res_2369_ = l_Std_Sat_AIG_getConstant(v_00_u03b1_2364_, v_inst_2365_, v_inst_2366_, v_aig_2367_, v_ref_2368_);
lean_dec_ref(v_ref_2368_);
lean_dec_ref(v_aig_2367_);
lean_dec_ref(v_inst_2366_);
lean_dec_ref(v_inst_2365_);
return v_res_2369_;
}
}
lean_object* runtime_initialize_Std_Data_HashSet(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sat_AIG_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
