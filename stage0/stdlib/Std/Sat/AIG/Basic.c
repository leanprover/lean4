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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_UInt64_ofNat___boxed(lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Bool_toNat(uint8_t);
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
lean_dec_ref(v_t_121_);
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
lean_dec_ref(v_t_121_);
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
lean_dec_ref(v_x_170_);
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
lean_dec_ref(v_x_170_);
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
lean_dec_ref(v_x_222_);
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
lean_dec_ref(v_x_295_);
v___x_300_ = 0;
if (lean_obj_tag(v_x_296_) == 1)
{
lean_object* v_idx_301_; lean_object* v___x_302_; uint8_t v___x_303_; 
v_idx_301_ = lean_ctor_get(v_x_296_, 0);
lean_inc(v_idx_301_);
lean_dec_ref(v_x_296_);
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
lean_dec_ref(v_x_295_);
v___x_307_ = 0;
if (lean_obj_tag(v_x_296_) == 2)
{
lean_object* v_l_308_; lean_object* v_r_309_; uint8_t v___x_310_; 
v_l_308_ = lean_ctor_get(v_x_296_, 0);
lean_inc(v_l_308_);
v_r_309_ = lean_ctor_get(v_x_296_, 1);
lean_inc(v_r_309_);
lean_dec_ref(v_x_296_);
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instInhabitedDecl_default(lean_object* v_a_348_){
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
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_352_ = lean_box(0);
v___x_353_ = lean_unsigned_to_nat(16u);
v___x_354_ = lean_mk_array(v___x_353_, v___x_352_);
return v___x_354_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___closed__1(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_355_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___closed__0, &l_Std_Sat_AIG_Cache_empty___closed__0_once, _init_l_Std_Sat_AIG_Cache_empty___closed__0);
v___x_356_ = lean_unsigned_to_nat(0u);
v___x_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
lean_ctor_set(v___x_357_, 1, v___x_355_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_empty(lean_object* v_00_u03b1_358_, lean_object* v_inst_359_, lean_object* v_inst_360_, lean_object* v_decls_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___closed__1, &l_Std_Sat_AIG_Cache_empty___closed__1_once, _init_l_Std_Sat_AIG_Cache_empty___closed__1);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_empty___boxed(lean_object* v_00_u03b1_363_, lean_object* v_inst_364_, lean_object* v_inst_365_, lean_object* v_decls_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Std_Sat_AIG_Cache_empty(v_00_u03b1_363_, v_inst_364_, v_inst_365_, v_decls_366_);
lean_dec_ref(v_decls_366_);
lean_dec_ref(v_inst_365_);
lean_dec_ref(v_inst_364_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_noUpdate___redArg(lean_object* v_cache_368_){
_start:
{
lean_inc_ref(v_cache_368_);
return v_cache_368_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_noUpdate___redArg___boxed(lean_object* v_cache_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Std_Sat_AIG_Cache_noUpdate___redArg(v_cache_369_);
lean_dec_ref(v_cache_369_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_noUpdate(lean_object* v_00_u03b1_371_, lean_object* v_inst_372_, lean_object* v_inst_373_, lean_object* v_decls_374_, lean_object* v_decl_375_, lean_object* v_cache_376_){
_start:
{
lean_inc_ref(v_cache_376_);
return v_cache_376_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_noUpdate___boxed(lean_object* v_00_u03b1_377_, lean_object* v_inst_378_, lean_object* v_inst_379_, lean_object* v_decls_380_, lean_object* v_decl_381_, lean_object* v_cache_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Std_Sat_AIG_Cache_noUpdate(v_00_u03b1_377_, v_inst_378_, v_inst_379_, v_decls_380_, v_decl_381_, v_cache_382_);
lean_dec_ref(v_cache_382_);
lean_dec(v_decl_381_);
lean_dec_ref(v_decls_380_);
lean_dec_ref(v_inst_379_);
lean_dec_ref(v_inst_378_);
return v_res_383_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_Cache_insert___redArg___lam__0(lean_object* v_inst_384_, lean_object* v_a_385_, lean_object* v_b_386_){
_start:
{
uint8_t v___x_387_; 
v___x_387_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v_inst_384_, v_a_385_, v_b_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed(lean_object* v_inst_388_, lean_object* v_a_389_, lean_object* v_b_390_){
_start:
{
uint8_t v_res_391_; lean_object* v_r_392_; 
v_res_391_ = l_Std_Sat_AIG_Cache_insert___redArg___lam__0(v_inst_388_, v_a_389_, v_b_390_);
v_r_392_ = lean_box(v_res_391_);
return v_r_392_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___redArg(lean_object* v_inst_393_, lean_object* v_inst_394_, lean_object* v_decls_395_, lean_object* v_cache_396_, lean_object* v_decl_397_){
_start:
{
lean_object* v___f_398_; lean_object* v___x_399_; lean_object* v___f_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___f_398_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_398_, 0, v_inst_394_);
v___x_399_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_399_, 0, lean_box(0));
lean_closure_set(v___x_399_, 1, v_inst_393_);
v___f_400_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_400_, 0, v___f_398_);
v___x_401_ = lean_array_get_size(v_decls_395_);
v___x_402_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_400_, v___x_399_, v_cache_396_, v_decl_397_, v___x_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___redArg___boxed(lean_object* v_inst_403_, lean_object* v_inst_404_, lean_object* v_decls_405_, lean_object* v_cache_406_, lean_object* v_decl_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Std_Sat_AIG_Cache_insert___redArg(v_inst_403_, v_inst_404_, v_decls_405_, v_cache_406_, v_decl_407_);
lean_dec_ref(v_decls_405_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert(lean_object* v_00_u03b1_409_, lean_object* v_inst_410_, lean_object* v_inst_411_, lean_object* v_decls_412_, lean_object* v_cache_413_, lean_object* v_decl_414_){
_start:
{
lean_object* v___f_415_; lean_object* v___x_416_; lean_object* v___f_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v___f_415_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_415_, 0, v_inst_411_);
v___x_416_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_416_, 0, lean_box(0));
lean_closure_set(v___x_416_, 1, v_inst_410_);
v___f_417_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_417_, 0, v___f_415_);
v___x_418_ = lean_array_get_size(v_decls_412_);
v___x_419_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_417_, v___x_416_, v_cache_413_, v_decl_414_, v___x_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___boxed(lean_object* v_00_u03b1_420_, lean_object* v_inst_421_, lean_object* v_inst_422_, lean_object* v_decls_423_, lean_object* v_cache_424_, lean_object* v_decl_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Std_Sat_AIG_Cache_insert(v_00_u03b1_420_, v_inst_421_, v_inst_422_, v_decls_423_, v_cache_424_, v_decl_425_);
lean_dec_ref(v_decls_423_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f___redArg(lean_object* v_inst_427_, lean_object* v_inst_428_, lean_object* v_cache_429_, lean_object* v_decl_430_){
_start:
{
lean_object* v___f_431_; lean_object* v___x_432_; lean_object* v___f_433_; lean_object* v___x_434_; 
v___f_431_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_431_, 0, v_inst_428_);
v___x_432_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_432_, 0, lean_box(0));
lean_closure_set(v___x_432_, 1, v_inst_427_);
v___f_433_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_433_, 0, v___f_431_);
v___x_434_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_433_, v___x_432_, v_cache_429_, v_decl_430_);
if (lean_obj_tag(v___x_434_) == 0)
{
lean_object* v___x_435_; 
v___x_435_ = lean_box(0);
return v___x_435_;
}
else
{
lean_object* v_val_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_443_; 
v_val_436_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_443_ == 0)
{
v___x_438_ = v___x_434_;
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_val_436_);
lean_dec(v___x_434_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_441_; 
if (v_isShared_439_ == 0)
{
v___x_441_ = v___x_438_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_val_436_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f___redArg___boxed(lean_object* v_inst_444_, lean_object* v_inst_445_, lean_object* v_cache_446_, lean_object* v_decl_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Std_Sat_AIG_Cache_get_x3f___redArg(v_inst_444_, v_inst_445_, v_cache_446_, v_decl_447_);
lean_dec_ref(v_cache_446_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f(lean_object* v_00_u03b1_449_, lean_object* v_inst_450_, lean_object* v_inst_451_, lean_object* v_decls_452_, lean_object* v_cache_453_, lean_object* v_decl_454_){
_start:
{
lean_object* v___f_455_; lean_object* v___x_456_; lean_object* v___f_457_; lean_object* v___x_458_; 
v___f_455_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_455_, 0, v_inst_451_);
v___x_456_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_456_, 0, lean_box(0));
lean_closure_set(v___x_456_, 1, v_inst_450_);
v___f_457_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_457_, 0, v___f_455_);
v___x_458_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_457_, v___x_456_, v_cache_453_, v_decl_454_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v___x_459_; 
v___x_459_ = lean_box(0);
return v___x_459_;
}
else
{
lean_object* v_val_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_467_; 
v_val_460_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_467_ == 0)
{
v___x_462_ = v___x_458_;
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_val_460_);
lean_dec(v___x_458_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_465_; 
if (v_isShared_463_ == 0)
{
v___x_465_ = v___x_462_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_val_460_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f___boxed(lean_object* v_00_u03b1_468_, lean_object* v_inst_469_, lean_object* v_inst_470_, lean_object* v_decls_471_, lean_object* v_cache_472_, lean_object* v_decl_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Std_Sat_AIG_Cache_get_x3f(v_00_u03b1_468_, v_inst_469_, v_inst_470_, v_decls_471_, v_cache_472_, v_decl_473_);
lean_dec_ref(v_cache_472_);
lean_dec_ref(v_decls_471_);
return v_res_474_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___closed__1(void){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_479_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___closed__1, &l_Std_Sat_AIG_Cache_empty___closed__1_once, _init_l_Std_Sat_AIG_Cache_empty___closed__1);
v___x_480_ = ((lean_object*)(l_Std_Sat_AIG_empty___closed__0));
v___x_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
lean_ctor_set(v___x_481_, 1, v___x_479_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_empty(lean_object* v_00_u03b1_482_, lean_object* v_inst_483_, lean_object* v_inst_484_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = lean_obj_once(&l_Std_Sat_AIG_empty___closed__1, &l_Std_Sat_AIG_empty___closed__1_once, _init_l_Std_Sat_AIG_empty___closed__1);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_empty___boxed(lean_object* v_00_u03b1_486_, lean_object* v_inst_487_, lean_object* v_inst_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Std_Sat_AIG_empty(v_00_u03b1_486_, v_inst_487_, v_inst_488_);
lean_dec_ref(v_inst_488_);
lean_dec_ref(v_inst_487_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instMembership(lean_object* v_00_u03b1_490_, lean_object* v_inst_491_, lean_object* v_inst_492_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = lean_box(0);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instMembership___boxed(lean_object* v_00_u03b1_494_, lean_object* v_inst_495_, lean_object* v_inst_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Std_Sat_AIG_instMembership(v_00_u03b1_494_, v_inst_495_, v_inst_496_);
lean_dec_ref(v_inst_496_);
lean_dec_ref(v_inst_495_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_cast___redArg(lean_object* v_ref_498_){
_start:
{
lean_object* v_gate_499_; uint8_t v_invert_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_507_; 
v_gate_499_ = lean_ctor_get(v_ref_498_, 0);
v_invert_500_ = lean_ctor_get_uint8(v_ref_498_, sizeof(void*)*1);
v_isSharedCheck_507_ = !lean_is_exclusive(v_ref_498_);
if (v_isSharedCheck_507_ == 0)
{
v___x_502_ = v_ref_498_;
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_gate_499_);
lean_dec(v_ref_498_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_505_; 
if (v_isShared_503_ == 0)
{
v___x_505_ = v___x_502_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_gate_499_);
lean_ctor_set_uint8(v_reuseFailAlloc_506_, sizeof(void*)*1, v_invert_500_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_cast(lean_object* v_00_u03b1_508_, lean_object* v_inst_509_, lean_object* v_inst_510_, lean_object* v_aig1_511_, lean_object* v_aig2_512_, lean_object* v_ref_513_, lean_object* v_h_514_){
_start:
{
lean_object* v_gate_515_; uint8_t v_invert_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_523_; 
v_gate_515_ = lean_ctor_get(v_ref_513_, 0);
v_invert_516_ = lean_ctor_get_uint8(v_ref_513_, sizeof(void*)*1);
v_isSharedCheck_523_ = !lean_is_exclusive(v_ref_513_);
if (v_isSharedCheck_523_ == 0)
{
v___x_518_ = v_ref_513_;
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_gate_515_);
lean_dec(v_ref_513_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_521_; 
if (v_isShared_519_ == 0)
{
v___x_521_ = v___x_518_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_gate_515_);
lean_ctor_set_uint8(v_reuseFailAlloc_522_, sizeof(void*)*1, v_invert_516_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_cast___boxed(lean_object* v_00_u03b1_524_, lean_object* v_inst_525_, lean_object* v_inst_526_, lean_object* v_aig1_527_, lean_object* v_aig2_528_, lean_object* v_ref_529_, lean_object* v_h_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Std_Sat_AIG_Ref_cast(v_00_u03b1_524_, v_inst_525_, v_inst_526_, v_aig1_527_, v_aig2_528_, v_ref_529_, v_h_530_);
lean_dec_ref(v_aig2_528_);
lean_dec_ref(v_aig1_527_);
lean_dec_ref(v_inst_526_);
lean_dec_ref(v_inst_525_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_flip___redArg(lean_object* v_ref_532_, uint8_t v_inv_533_){
_start:
{
lean_object* v_gate_534_; uint8_t v_invert_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_547_; 
v_gate_534_ = lean_ctor_get(v_ref_532_, 0);
v_invert_535_ = lean_ctor_get_uint8(v_ref_532_, sizeof(void*)*1);
v_isSharedCheck_547_ = !lean_is_exclusive(v_ref_532_);
if (v_isSharedCheck_547_ == 0)
{
v___x_537_ = v_ref_532_;
v_isShared_538_ = v_isSharedCheck_547_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_gate_534_);
lean_dec(v_ref_532_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_547_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
if (v_inv_533_ == 0)
{
if (v_invert_535_ == 0)
{
lean_del_object(v___x_537_);
goto v___jp_544_;
}
else
{
goto v___jp_539_;
}
}
else
{
if (v_invert_535_ == 0)
{
goto v___jp_539_;
}
else
{
lean_del_object(v___x_537_);
goto v___jp_544_;
}
}
v___jp_539_:
{
uint8_t v___x_540_; lean_object* v___x_542_; 
v___x_540_ = 1;
if (v_isShared_538_ == 0)
{
v___x_542_ = v___x_537_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_gate_534_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
lean_ctor_set_uint8(v___x_542_, sizeof(void*)*1, v___x_540_);
return v___x_542_;
}
}
v___jp_544_:
{
uint8_t v___x_545_; lean_object* v___x_546_; 
v___x_545_ = 0;
v___x_546_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_546_, 0, v_gate_534_);
lean_ctor_set_uint8(v___x_546_, sizeof(void*)*1, v___x_545_);
return v___x_546_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_flip___redArg___boxed(lean_object* v_ref_548_, lean_object* v_inv_549_){
_start:
{
uint8_t v_inv_boxed_550_; lean_object* v_res_551_; 
v_inv_boxed_550_ = lean_unbox(v_inv_549_);
v_res_551_ = l_Std_Sat_AIG_Ref_flip___redArg(v_ref_548_, v_inv_boxed_550_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_flip(lean_object* v_00_u03b1_552_, lean_object* v_inst_553_, lean_object* v_inst_554_, lean_object* v_aig_555_, lean_object* v_ref_556_, uint8_t v_inv_557_){
_start:
{
lean_object* v_gate_558_; uint8_t v_invert_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_571_; 
v_gate_558_ = lean_ctor_get(v_ref_556_, 0);
v_invert_559_ = lean_ctor_get_uint8(v_ref_556_, sizeof(void*)*1);
v_isSharedCheck_571_ = !lean_is_exclusive(v_ref_556_);
if (v_isSharedCheck_571_ == 0)
{
v___x_561_ = v_ref_556_;
v_isShared_562_ = v_isSharedCheck_571_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_gate_558_);
lean_dec(v_ref_556_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_571_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
if (v_inv_557_ == 0)
{
if (v_invert_559_ == 0)
{
lean_del_object(v___x_561_);
goto v___jp_568_;
}
else
{
goto v___jp_563_;
}
}
else
{
if (v_invert_559_ == 0)
{
goto v___jp_563_;
}
else
{
lean_del_object(v___x_561_);
goto v___jp_568_;
}
}
v___jp_563_:
{
uint8_t v___x_564_; lean_object* v___x_566_; 
v___x_564_ = 1;
if (v_isShared_562_ == 0)
{
v___x_566_ = v___x_561_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_gate_558_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
lean_ctor_set_uint8(v___x_566_, sizeof(void*)*1, v___x_564_);
return v___x_566_;
}
}
v___jp_568_:
{
uint8_t v___x_569_; lean_object* v___x_570_; 
v___x_569_ = 0;
v___x_570_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_570_, 0, v_gate_558_);
lean_ctor_set_uint8(v___x_570_, sizeof(void*)*1, v___x_569_);
return v___x_570_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_flip___boxed(lean_object* v_00_u03b1_572_, lean_object* v_inst_573_, lean_object* v_inst_574_, lean_object* v_aig_575_, lean_object* v_ref_576_, lean_object* v_inv_577_){
_start:
{
uint8_t v_inv_boxed_578_; lean_object* v_res_579_; 
v_inv_boxed_578_ = lean_unbox(v_inv_577_);
v_res_579_ = l_Std_Sat_AIG_Ref_flip(v_00_u03b1_572_, v_inst_573_, v_inst_574_, v_aig_575_, v_ref_576_, v_inv_boxed_578_);
lean_dec_ref(v_aig_575_);
lean_dec_ref(v_inst_574_);
lean_dec_ref(v_inst_573_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_not___redArg(lean_object* v_ref_580_){
_start:
{
uint8_t v_invert_581_; 
v_invert_581_ = lean_ctor_get_uint8(v_ref_580_, sizeof(void*)*1);
if (v_invert_581_ == 0)
{
lean_object* v_gate_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_590_; 
v_gate_582_ = lean_ctor_get(v_ref_580_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v_ref_580_);
if (v_isSharedCheck_590_ == 0)
{
v___x_584_ = v_ref_580_;
v_isShared_585_ = v_isSharedCheck_590_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_gate_582_);
lean_dec(v_ref_580_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_590_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
uint8_t v___x_586_; lean_object* v___x_588_; 
v___x_586_ = 1;
if (v_isShared_585_ == 0)
{
v___x_588_ = v___x_584_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_gate_582_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
lean_ctor_set_uint8(v___x_588_, sizeof(void*)*1, v___x_586_);
return v___x_588_;
}
}
}
else
{
lean_object* v_gate_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_599_; 
v_gate_591_ = lean_ctor_get(v_ref_580_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v_ref_580_);
if (v_isSharedCheck_599_ == 0)
{
v___x_593_ = v_ref_580_;
v_isShared_594_ = v_isSharedCheck_599_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_gate_591_);
lean_dec(v_ref_580_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_599_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
uint8_t v___x_595_; lean_object* v___x_597_; 
v___x_595_ = 0;
if (v_isShared_594_ == 0)
{
v___x_597_ = v___x_593_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_gate_591_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
lean_ctor_set_uint8(v___x_597_, sizeof(void*)*1, v___x_595_);
return v___x_597_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_not(lean_object* v_00_u03b1_600_, lean_object* v_inst_601_, lean_object* v_inst_602_, lean_object* v_aig_603_, lean_object* v_ref_604_){
_start:
{
uint8_t v_invert_605_; 
v_invert_605_ = lean_ctor_get_uint8(v_ref_604_, sizeof(void*)*1);
if (v_invert_605_ == 0)
{
lean_object* v_gate_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_614_; 
v_gate_606_ = lean_ctor_get(v_ref_604_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v_ref_604_);
if (v_isSharedCheck_614_ == 0)
{
v___x_608_ = v_ref_604_;
v_isShared_609_ = v_isSharedCheck_614_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_gate_606_);
lean_dec(v_ref_604_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_614_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
uint8_t v___x_610_; lean_object* v___x_612_; 
v___x_610_ = 1;
if (v_isShared_609_ == 0)
{
v___x_612_ = v___x_608_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_gate_606_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
lean_ctor_set_uint8(v___x_612_, sizeof(void*)*1, v___x_610_);
return v___x_612_;
}
}
}
else
{
lean_object* v_gate_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_623_; 
v_gate_615_ = lean_ctor_get(v_ref_604_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v_ref_604_);
if (v_isSharedCheck_623_ == 0)
{
v___x_617_ = v_ref_604_;
v_isShared_618_ = v_isSharedCheck_623_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_gate_615_);
lean_dec(v_ref_604_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_623_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
uint8_t v___x_619_; lean_object* v___x_621_; 
v___x_619_ = 0;
if (v_isShared_618_ == 0)
{
v___x_621_ = v___x_617_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_gate_615_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
lean_ctor_set_uint8(v___x_621_, sizeof(void*)*1, v___x_619_);
return v___x_621_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_not___boxed(lean_object* v_00_u03b1_624_, lean_object* v_inst_625_, lean_object* v_inst_626_, lean_object* v_aig_627_, lean_object* v_ref_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Std_Sat_AIG_Ref_not(v_00_u03b1_624_, v_inst_625_, v_inst_626_, v_aig_627_, v_ref_628_);
lean_dec_ref(v_aig_627_);
lean_dec_ref(v_inst_626_);
lean_dec_ref(v_inst_625_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_cast___redArg(lean_object* v_input_630_){
_start:
{
lean_object* v_lhs_631_; lean_object* v_rhs_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_657_; 
v_lhs_631_ = lean_ctor_get(v_input_630_, 0);
v_rhs_632_ = lean_ctor_get(v_input_630_, 1);
v_isSharedCheck_657_ = !lean_is_exclusive(v_input_630_);
if (v_isSharedCheck_657_ == 0)
{
v___x_634_ = v_input_630_;
v_isShared_635_ = v_isSharedCheck_657_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_rhs_632_);
lean_inc(v_lhs_631_);
lean_dec(v_input_630_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_657_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v_gate_636_; uint8_t v_invert_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_656_; 
v_gate_636_ = lean_ctor_get(v_lhs_631_, 0);
v_invert_637_ = lean_ctor_get_uint8(v_lhs_631_, sizeof(void*)*1);
v_isSharedCheck_656_ = !lean_is_exclusive(v_lhs_631_);
if (v_isSharedCheck_656_ == 0)
{
v___x_639_ = v_lhs_631_;
v_isShared_640_ = v_isSharedCheck_656_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_gate_636_);
lean_dec(v_lhs_631_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_656_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v_gate_641_; uint8_t v_invert_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_655_; 
v_gate_641_ = lean_ctor_get(v_rhs_632_, 0);
v_invert_642_ = lean_ctor_get_uint8(v_rhs_632_, sizeof(void*)*1);
v_isSharedCheck_655_ = !lean_is_exclusive(v_rhs_632_);
if (v_isSharedCheck_655_ == 0)
{
v___x_644_ = v_rhs_632_;
v_isShared_645_ = v_isSharedCheck_655_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_gate_641_);
lean_dec(v_rhs_632_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_655_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_647_; 
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 0, v_gate_636_);
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_gate_636_);
v___x_647_ = v_reuseFailAlloc_654_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
lean_object* v___x_649_; 
lean_ctor_set_uint8(v___x_647_, sizeof(void*)*1, v_invert_637_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 0, v_gate_641_);
v___x_649_ = v___x_639_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_gate_641_);
v___x_649_ = v_reuseFailAlloc_653_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_object* v___x_651_; 
lean_ctor_set_uint8(v___x_649_, sizeof(void*)*1, v_invert_642_);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 1, v___x_649_);
lean_ctor_set(v___x_634_, 0, v___x_647_);
v___x_651_ = v___x_634_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_647_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v___x_649_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_cast(lean_object* v_00_u03b1_658_, lean_object* v_inst_659_, lean_object* v_inst_660_, lean_object* v_aig1_661_, lean_object* v_aig2_662_, lean_object* v_input_663_, lean_object* v_h_664_){
_start:
{
lean_object* v_lhs_665_; lean_object* v_rhs_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_691_; 
v_lhs_665_ = lean_ctor_get(v_input_663_, 0);
v_rhs_666_ = lean_ctor_get(v_input_663_, 1);
v_isSharedCheck_691_ = !lean_is_exclusive(v_input_663_);
if (v_isSharedCheck_691_ == 0)
{
v___x_668_ = v_input_663_;
v_isShared_669_ = v_isSharedCheck_691_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_rhs_666_);
lean_inc(v_lhs_665_);
lean_dec(v_input_663_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_691_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v_gate_670_; uint8_t v_invert_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_690_; 
v_gate_670_ = lean_ctor_get(v_lhs_665_, 0);
v_invert_671_ = lean_ctor_get_uint8(v_lhs_665_, sizeof(void*)*1);
v_isSharedCheck_690_ = !lean_is_exclusive(v_lhs_665_);
if (v_isSharedCheck_690_ == 0)
{
v___x_673_ = v_lhs_665_;
v_isShared_674_ = v_isSharedCheck_690_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_gate_670_);
lean_dec(v_lhs_665_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_690_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v_gate_675_; uint8_t v_invert_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_689_; 
v_gate_675_ = lean_ctor_get(v_rhs_666_, 0);
v_invert_676_ = lean_ctor_get_uint8(v_rhs_666_, sizeof(void*)*1);
v_isSharedCheck_689_ = !lean_is_exclusive(v_rhs_666_);
if (v_isSharedCheck_689_ == 0)
{
v___x_678_ = v_rhs_666_;
v_isShared_679_ = v_isSharedCheck_689_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_gate_675_);
lean_dec(v_rhs_666_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_689_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 0, v_gate_670_);
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_gate_670_);
v___x_681_ = v_reuseFailAlloc_688_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
lean_object* v___x_683_; 
lean_ctor_set_uint8(v___x_681_, sizeof(void*)*1, v_invert_671_);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 0, v_gate_675_);
v___x_683_ = v___x_673_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_gate_675_);
v___x_683_ = v_reuseFailAlloc_687_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
lean_object* v___x_685_; 
lean_ctor_set_uint8(v___x_683_, sizeof(void*)*1, v_invert_676_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 1, v___x_683_);
lean_ctor_set(v___x_668_, 0, v___x_681_);
v___x_685_ = v___x_668_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v___x_681_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v___x_683_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_cast___boxed(lean_object* v_00_u03b1_692_, lean_object* v_inst_693_, lean_object* v_inst_694_, lean_object* v_aig1_695_, lean_object* v_aig2_696_, lean_object* v_input_697_, lean_object* v_h_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Std_Sat_AIG_BinaryInput_cast(v_00_u03b1_692_, v_inst_693_, v_inst_694_, v_aig1_695_, v_aig2_696_, v_input_697_, v_h_698_);
lean_dec_ref(v_aig2_696_);
lean_dec_ref(v_aig1_695_);
lean_dec_ref(v_inst_694_);
lean_dec_ref(v_inst_693_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_invert___redArg(lean_object* v_input_700_, uint8_t v_linv_701_, uint8_t v_rinv_702_){
_start:
{
lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v_lhs_715_; lean_object* v_rhs_716_; lean_object* v___y_718_; lean_object* v_gate_725_; uint8_t v_invert_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_738_; 
v_lhs_715_ = lean_ctor_get(v_input_700_, 0);
lean_inc_ref(v_lhs_715_);
v_rhs_716_ = lean_ctor_get(v_input_700_, 1);
lean_inc_ref(v_rhs_716_);
lean_dec_ref(v_input_700_);
v_gate_725_ = lean_ctor_get(v_lhs_715_, 0);
v_invert_726_ = lean_ctor_get_uint8(v_lhs_715_, sizeof(void*)*1);
v_isSharedCheck_738_ = !lean_is_exclusive(v_lhs_715_);
if (v_isSharedCheck_738_ == 0)
{
v___x_728_ = v_lhs_715_;
v_isShared_729_ = v_isSharedCheck_738_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_gate_725_);
lean_dec(v_lhs_715_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_738_;
goto v_resetjp_727_;
}
v___jp_703_:
{
uint8_t v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_706_ = 0;
v___x_707_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_707_, 0, v___y_705_);
lean_ctor_set_uint8(v___x_707_, sizeof(void*)*1, v___x_706_);
v___x_708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_708_, 0, v___y_704_);
lean_ctor_set(v___x_708_, 1, v___x_707_);
return v___x_708_;
}
v___jp_709_:
{
uint8_t v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_712_ = 1;
v___x_713_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_713_, 0, v___y_711_);
lean_ctor_set_uint8(v___x_713_, sizeof(void*)*1, v___x_712_);
v___x_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_714_, 0, v___y_710_);
lean_ctor_set(v___x_714_, 1, v___x_713_);
return v___x_714_;
}
v___jp_717_:
{
if (v_rinv_702_ == 0)
{
uint8_t v_invert_719_; 
v_invert_719_ = lean_ctor_get_uint8(v_rhs_716_, sizeof(void*)*1);
if (v_invert_719_ == 0)
{
lean_object* v_gate_720_; 
v_gate_720_ = lean_ctor_get(v_rhs_716_, 0);
lean_inc(v_gate_720_);
lean_dec_ref(v_rhs_716_);
v___y_704_ = v___y_718_;
v___y_705_ = v_gate_720_;
goto v___jp_703_;
}
else
{
lean_object* v_gate_721_; 
v_gate_721_ = lean_ctor_get(v_rhs_716_, 0);
lean_inc(v_gate_721_);
lean_dec_ref(v_rhs_716_);
v___y_710_ = v___y_718_;
v___y_711_ = v_gate_721_;
goto v___jp_709_;
}
}
else
{
uint8_t v_invert_722_; 
v_invert_722_ = lean_ctor_get_uint8(v_rhs_716_, sizeof(void*)*1);
if (v_invert_722_ == 0)
{
lean_object* v_gate_723_; 
v_gate_723_ = lean_ctor_get(v_rhs_716_, 0);
lean_inc(v_gate_723_);
lean_dec_ref(v_rhs_716_);
v___y_710_ = v___y_718_;
v___y_711_ = v_gate_723_;
goto v___jp_709_;
}
else
{
lean_object* v_gate_724_; 
v_gate_724_ = lean_ctor_get(v_rhs_716_, 0);
lean_inc(v_gate_724_);
lean_dec_ref(v_rhs_716_);
v___y_704_ = v___y_718_;
v___y_705_ = v_gate_724_;
goto v___jp_703_;
}
}
}
v_resetjp_727_:
{
if (v_linv_701_ == 0)
{
if (v_invert_726_ == 0)
{
lean_del_object(v___x_728_);
goto v___jp_735_;
}
else
{
goto v___jp_730_;
}
}
else
{
if (v_invert_726_ == 0)
{
goto v___jp_730_;
}
else
{
lean_del_object(v___x_728_);
goto v___jp_735_;
}
}
v___jp_730_:
{
uint8_t v___x_731_; lean_object* v___x_733_; 
v___x_731_ = 1;
if (v_isShared_729_ == 0)
{
v___x_733_ = v___x_728_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_gate_725_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_ctor_set_uint8(v___x_733_, sizeof(void*)*1, v___x_731_);
v___y_718_ = v___x_733_;
goto v___jp_717_;
}
}
v___jp_735_:
{
uint8_t v___x_736_; lean_object* v___x_737_; 
v___x_736_ = 0;
v___x_737_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_737_, 0, v_gate_725_);
lean_ctor_set_uint8(v___x_737_, sizeof(void*)*1, v___x_736_);
v___y_718_ = v___x_737_;
goto v___jp_717_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_invert___redArg___boxed(lean_object* v_input_739_, lean_object* v_linv_740_, lean_object* v_rinv_741_){
_start:
{
uint8_t v_linv_boxed_742_; uint8_t v_rinv_boxed_743_; lean_object* v_res_744_; 
v_linv_boxed_742_ = lean_unbox(v_linv_740_);
v_rinv_boxed_743_ = lean_unbox(v_rinv_741_);
v_res_744_ = l_Std_Sat_AIG_BinaryInput_invert___redArg(v_input_739_, v_linv_boxed_742_, v_rinv_boxed_743_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_invert(lean_object* v_00_u03b1_745_, lean_object* v_inst_746_, lean_object* v_inst_747_, lean_object* v_aig_748_, lean_object* v_input_749_, uint8_t v_linv_750_, uint8_t v_rinv_751_){
_start:
{
lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v_lhs_764_; lean_object* v_rhs_765_; lean_object* v___y_767_; lean_object* v_gate_774_; uint8_t v_invert_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_787_; 
v_lhs_764_ = lean_ctor_get(v_input_749_, 0);
lean_inc_ref(v_lhs_764_);
v_rhs_765_ = lean_ctor_get(v_input_749_, 1);
lean_inc_ref(v_rhs_765_);
lean_dec_ref(v_input_749_);
v_gate_774_ = lean_ctor_get(v_lhs_764_, 0);
v_invert_775_ = lean_ctor_get_uint8(v_lhs_764_, sizeof(void*)*1);
v_isSharedCheck_787_ = !lean_is_exclusive(v_lhs_764_);
if (v_isSharedCheck_787_ == 0)
{
v___x_777_ = v_lhs_764_;
v_isShared_778_ = v_isSharedCheck_787_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_gate_774_);
lean_dec(v_lhs_764_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_787_;
goto v_resetjp_776_;
}
v___jp_752_:
{
uint8_t v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_755_ = 0;
v___x_756_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_756_, 0, v___y_754_);
lean_ctor_set_uint8(v___x_756_, sizeof(void*)*1, v___x_755_);
v___x_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_757_, 0, v___y_753_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
return v___x_757_;
}
v___jp_758_:
{
uint8_t v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_761_ = 1;
v___x_762_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_762_, 0, v___y_760_);
lean_ctor_set_uint8(v___x_762_, sizeof(void*)*1, v___x_761_);
v___x_763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_763_, 0, v___y_759_);
lean_ctor_set(v___x_763_, 1, v___x_762_);
return v___x_763_;
}
v___jp_766_:
{
if (v_rinv_751_ == 0)
{
uint8_t v_invert_768_; 
v_invert_768_ = lean_ctor_get_uint8(v_rhs_765_, sizeof(void*)*1);
if (v_invert_768_ == 0)
{
lean_object* v_gate_769_; 
v_gate_769_ = lean_ctor_get(v_rhs_765_, 0);
lean_inc(v_gate_769_);
lean_dec_ref(v_rhs_765_);
v___y_753_ = v___y_767_;
v___y_754_ = v_gate_769_;
goto v___jp_752_;
}
else
{
lean_object* v_gate_770_; 
v_gate_770_ = lean_ctor_get(v_rhs_765_, 0);
lean_inc(v_gate_770_);
lean_dec_ref(v_rhs_765_);
v___y_759_ = v___y_767_;
v___y_760_ = v_gate_770_;
goto v___jp_758_;
}
}
else
{
uint8_t v_invert_771_; 
v_invert_771_ = lean_ctor_get_uint8(v_rhs_765_, sizeof(void*)*1);
if (v_invert_771_ == 0)
{
lean_object* v_gate_772_; 
v_gate_772_ = lean_ctor_get(v_rhs_765_, 0);
lean_inc(v_gate_772_);
lean_dec_ref(v_rhs_765_);
v___y_759_ = v___y_767_;
v___y_760_ = v_gate_772_;
goto v___jp_758_;
}
else
{
lean_object* v_gate_773_; 
v_gate_773_ = lean_ctor_get(v_rhs_765_, 0);
lean_inc(v_gate_773_);
lean_dec_ref(v_rhs_765_);
v___y_753_ = v___y_767_;
v___y_754_ = v_gate_773_;
goto v___jp_752_;
}
}
}
v_resetjp_776_:
{
if (v_linv_750_ == 0)
{
if (v_invert_775_ == 0)
{
lean_del_object(v___x_777_);
goto v___jp_784_;
}
else
{
goto v___jp_779_;
}
}
else
{
if (v_invert_775_ == 0)
{
goto v___jp_779_;
}
else
{
lean_del_object(v___x_777_);
goto v___jp_784_;
}
}
v___jp_779_:
{
uint8_t v___x_780_; lean_object* v___x_782_; 
v___x_780_ = 1;
if (v_isShared_778_ == 0)
{
v___x_782_ = v___x_777_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_gate_774_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
lean_ctor_set_uint8(v___x_782_, sizeof(void*)*1, v___x_780_);
v___y_767_ = v___x_782_;
goto v___jp_766_;
}
}
v___jp_784_:
{
uint8_t v___x_785_; lean_object* v___x_786_; 
v___x_785_ = 0;
v___x_786_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_786_, 0, v_gate_774_);
lean_ctor_set_uint8(v___x_786_, sizeof(void*)*1, v___x_785_);
v___y_767_ = v___x_786_;
goto v___jp_766_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_invert___boxed(lean_object* v_00_u03b1_788_, lean_object* v_inst_789_, lean_object* v_inst_790_, lean_object* v_aig_791_, lean_object* v_input_792_, lean_object* v_linv_793_, lean_object* v_rinv_794_){
_start:
{
uint8_t v_linv_boxed_795_; uint8_t v_rinv_boxed_796_; lean_object* v_res_797_; 
v_linv_boxed_795_ = lean_unbox(v_linv_793_);
v_rinv_boxed_796_ = lean_unbox(v_rinv_794_);
v_res_797_ = l_Std_Sat_AIG_BinaryInput_invert(v_00_u03b1_788_, v_inst_789_, v_inst_790_, v_aig_791_, v_input_792_, v_linv_boxed_795_, v_rinv_boxed_796_);
lean_dec_ref(v_aig_791_);
lean_dec_ref(v_inst_790_);
lean_dec_ref(v_inst_789_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_TernaryInput_cast___redArg(lean_object* v_input_798_){
_start:
{
lean_object* v_discr_799_; lean_object* v_lhs_800_; lean_object* v_rhs_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_835_; 
v_discr_799_ = lean_ctor_get(v_input_798_, 0);
v_lhs_800_ = lean_ctor_get(v_input_798_, 1);
v_rhs_801_ = lean_ctor_get(v_input_798_, 2);
v_isSharedCheck_835_ = !lean_is_exclusive(v_input_798_);
if (v_isSharedCheck_835_ == 0)
{
v___x_803_ = v_input_798_;
v_isShared_804_ = v_isSharedCheck_835_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_rhs_801_);
lean_inc(v_lhs_800_);
lean_inc(v_discr_799_);
lean_dec(v_input_798_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_835_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v_gate_805_; uint8_t v_invert_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_834_; 
v_gate_805_ = lean_ctor_get(v_discr_799_, 0);
v_invert_806_ = lean_ctor_get_uint8(v_discr_799_, sizeof(void*)*1);
v_isSharedCheck_834_ = !lean_is_exclusive(v_discr_799_);
if (v_isSharedCheck_834_ == 0)
{
v___x_808_ = v_discr_799_;
v_isShared_809_ = v_isSharedCheck_834_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_gate_805_);
lean_dec(v_discr_799_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_834_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v_gate_810_; uint8_t v_invert_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_833_; 
v_gate_810_ = lean_ctor_get(v_lhs_800_, 0);
v_invert_811_ = lean_ctor_get_uint8(v_lhs_800_, sizeof(void*)*1);
v_isSharedCheck_833_ = !lean_is_exclusive(v_lhs_800_);
if (v_isSharedCheck_833_ == 0)
{
v___x_813_ = v_lhs_800_;
v_isShared_814_ = v_isSharedCheck_833_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_gate_810_);
lean_dec(v_lhs_800_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_833_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v_gate_815_; uint8_t v_invert_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_832_; 
v_gate_815_ = lean_ctor_get(v_rhs_801_, 0);
v_invert_816_ = lean_ctor_get_uint8(v_rhs_801_, sizeof(void*)*1);
v_isSharedCheck_832_ = !lean_is_exclusive(v_rhs_801_);
if (v_isSharedCheck_832_ == 0)
{
v___x_818_ = v_rhs_801_;
v_isShared_819_ = v_isSharedCheck_832_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_gate_815_);
lean_dec(v_rhs_801_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_832_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_821_; 
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 0, v_gate_805_);
v___x_821_ = v___x_818_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_gate_805_);
v___x_821_ = v_reuseFailAlloc_831_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
lean_object* v___x_823_; 
lean_ctor_set_uint8(v___x_821_, sizeof(void*)*1, v_invert_806_);
if (v_isShared_814_ == 0)
{
v___x_823_ = v___x_813_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_gate_810_);
lean_ctor_set_uint8(v_reuseFailAlloc_830_, sizeof(void*)*1, v_invert_811_);
v___x_823_ = v_reuseFailAlloc_830_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
lean_object* v___x_825_; 
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 0, v_gate_815_);
v___x_825_ = v___x_808_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_gate_815_);
v___x_825_ = v_reuseFailAlloc_829_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
lean_object* v___x_827_; 
lean_ctor_set_uint8(v___x_825_, sizeof(void*)*1, v_invert_816_);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 2, v___x_825_);
lean_ctor_set(v___x_803_, 1, v___x_823_);
lean_ctor_set(v___x_803_, 0, v___x_821_);
v___x_827_ = v___x_803_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v___x_821_);
lean_ctor_set(v_reuseFailAlloc_828_, 1, v___x_823_);
lean_ctor_set(v_reuseFailAlloc_828_, 2, v___x_825_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_TernaryInput_cast(lean_object* v_00_u03b1_836_, lean_object* v_inst_837_, lean_object* v_inst_838_, lean_object* v_aig1_839_, lean_object* v_aig2_840_, lean_object* v_input_841_, lean_object* v_h_842_){
_start:
{
lean_object* v_discr_843_; lean_object* v_lhs_844_; lean_object* v_rhs_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_879_; 
v_discr_843_ = lean_ctor_get(v_input_841_, 0);
v_lhs_844_ = lean_ctor_get(v_input_841_, 1);
v_rhs_845_ = lean_ctor_get(v_input_841_, 2);
v_isSharedCheck_879_ = !lean_is_exclusive(v_input_841_);
if (v_isSharedCheck_879_ == 0)
{
v___x_847_ = v_input_841_;
v_isShared_848_ = v_isSharedCheck_879_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_rhs_845_);
lean_inc(v_lhs_844_);
lean_inc(v_discr_843_);
lean_dec(v_input_841_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_879_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v_gate_849_; uint8_t v_invert_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_878_; 
v_gate_849_ = lean_ctor_get(v_discr_843_, 0);
v_invert_850_ = lean_ctor_get_uint8(v_discr_843_, sizeof(void*)*1);
v_isSharedCheck_878_ = !lean_is_exclusive(v_discr_843_);
if (v_isSharedCheck_878_ == 0)
{
v___x_852_ = v_discr_843_;
v_isShared_853_ = v_isSharedCheck_878_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_gate_849_);
lean_dec(v_discr_843_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_878_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v_gate_854_; uint8_t v_invert_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_877_; 
v_gate_854_ = lean_ctor_get(v_lhs_844_, 0);
v_invert_855_ = lean_ctor_get_uint8(v_lhs_844_, sizeof(void*)*1);
v_isSharedCheck_877_ = !lean_is_exclusive(v_lhs_844_);
if (v_isSharedCheck_877_ == 0)
{
v___x_857_ = v_lhs_844_;
v_isShared_858_ = v_isSharedCheck_877_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_gate_854_);
lean_dec(v_lhs_844_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_877_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v_gate_859_; uint8_t v_invert_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_876_; 
v_gate_859_ = lean_ctor_get(v_rhs_845_, 0);
v_invert_860_ = lean_ctor_get_uint8(v_rhs_845_, sizeof(void*)*1);
v_isSharedCheck_876_ = !lean_is_exclusive(v_rhs_845_);
if (v_isSharedCheck_876_ == 0)
{
v___x_862_ = v_rhs_845_;
v_isShared_863_ = v_isSharedCheck_876_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_gate_859_);
lean_dec(v_rhs_845_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_876_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 0, v_gate_849_);
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_gate_849_);
v___x_865_ = v_reuseFailAlloc_875_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
lean_object* v___x_867_; 
lean_ctor_set_uint8(v___x_865_, sizeof(void*)*1, v_invert_850_);
if (v_isShared_858_ == 0)
{
v___x_867_ = v___x_857_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_gate_854_);
lean_ctor_set_uint8(v_reuseFailAlloc_874_, sizeof(void*)*1, v_invert_855_);
v___x_867_ = v_reuseFailAlloc_874_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
lean_object* v___x_869_; 
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 0, v_gate_859_);
v___x_869_ = v___x_852_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_gate_859_);
v___x_869_ = v_reuseFailAlloc_873_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
lean_object* v___x_871_; 
lean_ctor_set_uint8(v___x_869_, sizeof(void*)*1, v_invert_860_);
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 2, v___x_869_);
lean_ctor_set(v___x_847_, 1, v___x_867_);
lean_ctor_set(v___x_847_, 0, v___x_865_);
v___x_871_ = v___x_847_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_865_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v___x_867_);
lean_ctor_set(v_reuseFailAlloc_872_, 2, v___x_869_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_TernaryInput_cast___boxed(lean_object* v_00_u03b1_880_, lean_object* v_inst_881_, lean_object* v_inst_882_, lean_object* v_aig1_883_, lean_object* v_aig2_884_, lean_object* v_input_885_, lean_object* v_h_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Std_Sat_AIG_TernaryInput_cast(v_00_u03b1_880_, v_inst_881_, v_inst_882_, v_aig1_883_, v_aig2_884_, v_input_885_, v_h_886_);
lean_dec_ref(v_aig2_884_);
lean_dec_ref(v_aig1_883_);
lean_dec_ref(v_inst_882_);
lean_dec_ref(v_inst_881_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_invEdgeStyle(uint8_t v_isInv_890_){
_start:
{
if (v_isInv_890_ == 0)
{
lean_object* v___x_891_; 
v___x_891_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_invEdgeStyle___closed__0));
return v___x_891_;
}
else
{
lean_object* v___x_892_; 
v___x_892_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_invEdgeStyle___closed__1));
return v___x_892_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_invEdgeStyle___boxed(lean_object* v_isInv_893_){
_start:
{
uint8_t v_isInv_boxed_894_; lean_object* v_res_895_; 
v_isInv_boxed_894_ = lean_unbox(v_isInv_893_);
v_res_895_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v_isInv_boxed_894_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___redArg(lean_object* v_acc_900_, lean_object* v_decls_901_, lean_object* v_idx_902_, lean_object* v_a_903_){
_start:
{
lean_object* v___x_904_; lean_object* v___f_905_; lean_object* v___x_906_; lean_object* v___f_907_; uint8_t v___x_908_; 
v___x_904_ = lean_array_get_size(v_decls_901_);
v___f_905_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___redArg___closed__0));
v___x_906_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_906_, 0, v___x_904_);
v___f_907_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_907_, 0, v___x_906_);
lean_inc(v_idx_902_);
lean_inc_ref(v___f_907_);
v___x_908_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_907_, v___f_905_, v_a_903_, v_idx_902_);
if (v___x_908_ == 0)
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_909_ = lean_box(0);
lean_inc(v_idx_902_);
v___x_910_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___f_907_, v___f_905_, v_a_903_, v_idx_902_, v___x_909_);
v___x_911_ = lean_array_fget_borrowed(v_decls_901_, v_idx_902_);
if (lean_obj_tag(v___x_911_) == 2)
{
lean_object* v_l_912_; lean_object* v_r_913_; lean_object* v___x_914_; lean_object* v___x_915_; uint8_t v___y_917_; lean_object* v___y_918_; uint8_t v___y_919_; uint8_t v___y_943_; lean_object* v___x_949_; lean_object* v___x_950_; uint8_t v___x_951_; 
v_l_912_ = lean_ctor_get(v___x_911_, 0);
v_r_913_ = lean_ctor_get(v___x_911_, 1);
v___x_914_ = lean_unsigned_to_nat(1u);
v___x_915_ = lean_nat_shiftr(v_l_912_, v___x_914_);
v___x_949_ = lean_nat_land(v___x_914_, v_l_912_);
v___x_950_ = lean_unsigned_to_nat(0u);
v___x_951_ = lean_nat_dec_eq(v___x_949_, v___x_950_);
lean_dec(v___x_949_);
if (v___x_951_ == 0)
{
uint8_t v___x_952_; 
v___x_952_ = 1;
v___y_943_ = v___x_952_;
goto v___jp_942_;
}
else
{
v___y_943_ = v___x_908_;
goto v___jp_942_;
}
v___jp_916_:
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v_fst_939_; lean_object* v_snd_940_; 
v___x_920_ = l_Nat_reprFast(v_idx_902_);
v___x_921_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___redArg___closed__1));
lean_inc_ref(v___x_920_);
v___x_922_ = lean_string_append(v___x_920_, v___x_921_);
lean_inc(v___x_915_);
v___x_923_ = l_Nat_reprFast(v___x_915_);
v___x_924_ = lean_string_append(v___x_922_, v___x_923_);
lean_dec_ref(v___x_923_);
v___x_925_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_917_);
v___x_926_ = lean_string_append(v___x_924_, v___x_925_);
lean_dec_ref(v___x_925_);
v___x_927_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___redArg___closed__2));
v___x_928_ = lean_string_append(v___x_926_, v___x_927_);
v___x_929_ = lean_string_append(v___x_928_, v___x_920_);
lean_dec_ref(v___x_920_);
v___x_930_ = lean_string_append(v___x_929_, v___x_921_);
lean_inc(v___y_918_);
v___x_931_ = l_Nat_reprFast(v___y_918_);
v___x_932_ = lean_string_append(v___x_930_, v___x_931_);
lean_dec_ref(v___x_931_);
v___x_933_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_919_);
v___x_934_ = lean_string_append(v___x_932_, v___x_933_);
lean_dec_ref(v___x_933_);
v___x_935_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___redArg___closed__3));
v___x_936_ = lean_string_append(v___x_934_, v___x_935_);
v___x_937_ = lean_string_append(v_acc_900_, v___x_936_);
lean_dec_ref(v___x_936_);
v___x_938_ = l_Std_Sat_AIG_toGraphviz_go___redArg(v___x_937_, v_decls_901_, v___x_915_, v___x_910_);
v_fst_939_ = lean_ctor_get(v___x_938_, 0);
lean_inc(v_fst_939_);
v_snd_940_ = lean_ctor_get(v___x_938_, 1);
lean_inc(v_snd_940_);
lean_dec_ref(v___x_938_);
v_acc_900_ = v_fst_939_;
v_idx_902_ = v___y_918_;
v_a_903_ = v_snd_940_;
goto _start;
}
v___jp_942_:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; uint8_t v___x_947_; 
v___x_944_ = lean_nat_shiftr(v_r_913_, v___x_914_);
v___x_945_ = lean_nat_land(v___x_914_, v_r_913_);
v___x_946_ = lean_unsigned_to_nat(0u);
v___x_947_ = lean_nat_dec_eq(v___x_945_, v___x_946_);
lean_dec(v___x_945_);
if (v___x_947_ == 0)
{
uint8_t v___x_948_; 
v___x_948_ = 1;
v___y_917_ = v___y_943_;
v___y_918_ = v___x_944_;
v___y_919_ = v___x_948_;
goto v___jp_916_;
}
else
{
v___y_917_ = v___y_943_;
v___y_918_ = v___x_944_;
v___y_919_ = v___x_908_;
goto v___jp_916_;
}
}
}
else
{
lean_object* v___x_953_; 
lean_dec(v_idx_902_);
v___x_953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_953_, 0, v_acc_900_);
lean_ctor_set(v___x_953_, 1, v___x_910_);
return v___x_953_;
}
}
else
{
lean_object* v___x_954_; 
lean_dec_ref(v___f_907_);
lean_dec(v_idx_902_);
v___x_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_954_, 0, v_acc_900_);
lean_ctor_set(v___x_954_, 1, v_a_903_);
return v___x_954_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___redArg___boxed(lean_object* v_acc_955_, lean_object* v_decls_956_, lean_object* v_idx_957_, lean_object* v_a_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Std_Sat_AIG_toGraphviz_go___redArg(v_acc_955_, v_decls_956_, v_idx_957_, v_a_958_);
lean_dec_ref(v_decls_956_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go(lean_object* v_00_u03b1_960_, lean_object* v_inst_961_, lean_object* v_inst_962_, lean_object* v_inst_963_, lean_object* v_acc_964_, lean_object* v_decls_965_, lean_object* v_hinv_966_, lean_object* v_idx_967_, lean_object* v_hidx_968_, lean_object* v_a_969_){
_start:
{
lean_object* v___x_970_; 
v___x_970_ = l_Std_Sat_AIG_toGraphviz_go___redArg(v_acc_964_, v_decls_965_, v_idx_967_, v_a_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___boxed(lean_object* v_00_u03b1_971_, lean_object* v_inst_972_, lean_object* v_inst_973_, lean_object* v_inst_974_, lean_object* v_acc_975_, lean_object* v_decls_976_, lean_object* v_hinv_977_, lean_object* v_idx_978_, lean_object* v_hidx_979_, lean_object* v_a_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Std_Sat_AIG_toGraphviz_go(v_00_u03b1_971_, v_inst_972_, v_inst_973_, v_inst_974_, v_acc_975_, v_decls_976_, v_hinv_977_, v_idx_978_, v_hidx_979_, v_a_980_);
lean_dec_ref(v_decls_976_);
lean_dec_ref(v_inst_974_);
lean_dec_ref(v_inst_973_);
lean_dec_ref(v_inst_972_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter___redArg(lean_object* v_x_982_, lean_object* v_h__1_983_, lean_object* v_h__2_984_, lean_object* v_h__3_985_){
_start:
{
switch(lean_obj_tag(v_x_982_))
{
case 0:
{
lean_object* v___x_986_; 
lean_dec(v_h__3_985_);
lean_dec(v_h__2_984_);
v___x_986_ = lean_apply_1(v_h__1_983_, lean_box(0));
return v___x_986_;
}
case 1:
{
lean_object* v_idx_987_; lean_object* v___x_988_; 
lean_dec(v_h__3_985_);
lean_dec(v_h__1_983_);
v_idx_987_ = lean_ctor_get(v_x_982_, 0);
lean_inc(v_idx_987_);
lean_dec_ref(v_x_982_);
v___x_988_ = lean_apply_2(v_h__2_984_, v_idx_987_, lean_box(0));
return v___x_988_;
}
default: 
{
lean_object* v_l_989_; lean_object* v_r_990_; lean_object* v___x_991_; 
lean_dec(v_h__2_984_);
lean_dec(v_h__1_983_);
v_l_989_ = lean_ctor_get(v_x_982_, 0);
lean_inc(v_l_989_);
v_r_990_ = lean_ctor_get(v_x_982_, 1);
lean_inc(v_r_990_);
lean_dec_ref(v_x_982_);
v___x_991_ = lean_apply_3(v_h__3_985_, v_l_989_, v_r_990_, lean_box(0));
return v___x_991_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter(lean_object* v_00_u03b1_992_, lean_object* v_motive_993_, lean_object* v_x_994_, lean_object* v_h__1_995_, lean_object* v_h__2_996_, lean_object* v_h__3_997_){
_start:
{
switch(lean_obj_tag(v_x_994_))
{
case 0:
{
lean_object* v___x_998_; 
lean_dec(v_h__3_997_);
lean_dec(v_h__2_996_);
v___x_998_ = lean_apply_1(v_h__1_995_, lean_box(0));
return v___x_998_;
}
case 1:
{
lean_object* v_idx_999_; lean_object* v___x_1000_; 
lean_dec(v_h__3_997_);
lean_dec(v_h__1_995_);
v_idx_999_ = lean_ctor_get(v_x_994_, 0);
lean_inc(v_idx_999_);
lean_dec_ref(v_x_994_);
v___x_1000_ = lean_apply_2(v_h__2_996_, v_idx_999_, lean_box(0));
return v___x_1000_;
}
default: 
{
lean_object* v_l_1001_; lean_object* v_r_1002_; lean_object* v___x_1003_; 
lean_dec(v_h__2_996_);
lean_dec(v_h__1_995_);
v_l_1001_ = lean_ctor_get(v_x_994_, 0);
lean_inc(v_l_1001_);
v_r_1002_ = lean_ctor_get(v_x_994_, 1);
lean_inc(v_r_1002_);
lean_dec_ref(v_x_994_);
v___x_1003_ = lean_apply_3(v_h__3_997_, v_l_1001_, v_r_1002_, lean_box(0));
return v___x_1003_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg(lean_object* v_inst_1009_, lean_object* v_decls_1010_, lean_object* v_idx_1011_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = lean_array_fget_borrowed(v_decls_1010_, v_idx_1011_);
switch(lean_obj_tag(v___x_1012_))
{
case 0:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
lean_dec_ref(v_inst_1009_);
v___x_1013_ = l_Nat_reprFast(v_idx_1011_);
v___x_1014_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__0));
v___x_1015_ = lean_string_append(v___x_1013_, v___x_1014_);
v___x_1016_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__1));
v___x_1017_ = lean_string_append(v___x_1015_, v___x_1016_);
v___x_1018_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__2));
v___x_1019_ = lean_string_append(v___x_1017_, v___x_1018_);
return v___x_1019_;
}
case 1:
{
lean_object* v_idx_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v_idx_1020_ = lean_ctor_get(v___x_1012_, 0);
v___x_1021_ = l_Nat_reprFast(v_idx_1011_);
v___x_1022_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__0));
v___x_1023_ = lean_string_append(v___x_1021_, v___x_1022_);
lean_inc(v_idx_1020_);
v___x_1024_ = lean_apply_1(v_inst_1009_, v_idx_1020_);
v___x_1025_ = lean_string_append(v___x_1023_, v___x_1024_);
lean_dec_ref(v___x_1024_);
v___x_1026_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__3));
v___x_1027_ = lean_string_append(v___x_1025_, v___x_1026_);
return v___x_1027_;
}
default: 
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
lean_dec_ref(v_inst_1009_);
v___x_1028_ = l_Nat_reprFast(v_idx_1011_);
v___x_1029_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__0));
lean_inc_ref(v___x_1028_);
v___x_1030_ = lean_string_append(v___x_1028_, v___x_1029_);
v___x_1031_ = lean_string_append(v___x_1030_, v___x_1028_);
lean_dec_ref(v___x_1028_);
v___x_1032_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__4));
v___x_1033_ = lean_string_append(v___x_1031_, v___x_1032_);
return v___x_1033_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___boxed(lean_object* v_inst_1034_, lean_object* v_decls_1035_, lean_object* v_idx_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg(v_inst_1034_, v_decls_1035_, v_idx_1036_);
lean_dec_ref(v_decls_1035_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString(lean_object* v_00_u03b1_1038_, lean_object* v_inst_1039_, lean_object* v_inst_1040_, lean_object* v_inst_1041_, lean_object* v_decls_1042_, lean_object* v_idx_1043_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg(v_inst_1040_, v_decls_1042_, v_idx_1043_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___boxed(lean_object* v_00_u03b1_1045_, lean_object* v_inst_1046_, lean_object* v_inst_1047_, lean_object* v_inst_1048_, lean_object* v_decls_1049_, lean_object* v_idx_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString(v_00_u03b1_1045_, v_inst_1046_, v_inst_1047_, v_inst_1048_, v_decls_1049_, v_idx_1050_);
lean_dec_ref(v_decls_1049_);
lean_dec_ref(v_inst_1048_);
lean_dec_ref(v_inst_1046_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___redArg___lam__0(lean_object* v_inst_1052_, lean_object* v_decls_1053_, lean_object* v_x1_1054_, lean_object* v_x2_1055_, lean_object* v_x3_1056_){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg(v_inst_1052_, v_decls_1053_, v_x2_1055_);
v___x_1058_ = lean_string_append(v_x1_1054_, v___x_1057_);
lean_dec_ref(v___x_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___redArg___lam__0___boxed(lean_object* v_inst_1059_, lean_object* v_decls_1060_, lean_object* v_x1_1061_, lean_object* v_x2_1062_, lean_object* v_x3_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Std_Sat_AIG_toGraphviz___redArg___lam__0(v_inst_1059_, v_decls_1060_, v_x1_1061_, v_x2_1062_, v_x3_1063_);
lean_dec_ref(v_decls_1060_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___redArg___lam__1(lean_object* v___x_1065_, lean_object* v___f_1066_, lean_object* v_acc_1067_, lean_object* v_l_1068_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1065_, v___f_1066_, v_acc_1067_, v_l_1068_);
return v___x_1069_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___redArg___closed__1(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1071_ = lean_box(0);
v___x_1072_ = lean_unsigned_to_nat(16u);
v___x_1073_ = lean_mk_array(v___x_1072_, v___x_1071_);
return v___x_1073_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___redArg___closed__2(void){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1074_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___redArg___closed__1, &l_Std_Sat_AIG_toGraphviz___redArg___closed__1_once, _init_l_Std_Sat_AIG_toGraphviz___redArg___closed__1);
v___x_1075_ = lean_unsigned_to_nat(0u);
v___x_1076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
lean_ctor_set(v___x_1076_, 1, v___x_1074_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___redArg(lean_object* v_inst_1098_, lean_object* v_entry_1099_){
_start:
{
lean_object* v_aig_1100_; lean_object* v_ref_1101_; lean_object* v_decls_1102_; lean_object* v_gate_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v_fst_1108_; lean_object* v_snd_1109_; lean_object* v___y_1111_; lean_object* v___x_1117_; lean_object* v_buckets_1118_; lean_object* v___x_1119_; uint8_t v___x_1120_; 
v_aig_1100_ = lean_ctor_get(v_entry_1099_, 0);
lean_inc_ref(v_aig_1100_);
v_ref_1101_ = lean_ctor_get(v_entry_1099_, 1);
lean_inc_ref(v_ref_1101_);
lean_dec_ref(v_entry_1099_);
v_decls_1102_ = lean_ctor_get(v_aig_1100_, 0);
lean_inc_ref(v_decls_1102_);
lean_dec_ref(v_aig_1100_);
v_gate_1103_ = lean_ctor_get(v_ref_1101_, 0);
lean_inc(v_gate_1103_);
lean_dec_ref(v_ref_1101_);
v___x_1104_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___redArg___closed__0));
v___x_1105_ = lean_unsigned_to_nat(0u);
v___x_1106_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___redArg___closed__2, &l_Std_Sat_AIG_toGraphviz___redArg___closed__2_once, _init_l_Std_Sat_AIG_toGraphviz___redArg___closed__2);
v___x_1107_ = l_Std_Sat_AIG_toGraphviz_go___redArg(v___x_1104_, v_decls_1102_, v_gate_1103_, v___x_1106_);
v_fst_1108_ = lean_ctor_get(v___x_1107_, 0);
lean_inc(v_fst_1108_);
v_snd_1109_ = lean_ctor_get(v___x_1107_, 1);
lean_inc(v_snd_1109_);
lean_dec_ref(v___x_1107_);
v___x_1117_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___redArg___closed__14));
v_buckets_1118_ = lean_ctor_get(v_snd_1109_, 1);
lean_inc_ref(v_buckets_1118_);
lean_dec(v_snd_1109_);
v___x_1119_ = lean_array_get_size(v_buckets_1118_);
v___x_1120_ = lean_nat_dec_lt(v___x_1105_, v___x_1119_);
if (v___x_1120_ == 0)
{
lean_dec_ref(v_buckets_1118_);
lean_dec_ref(v_decls_1102_);
lean_dec_ref(v_inst_1098_);
v___y_1111_ = v___x_1104_;
goto v___jp_1110_;
}
else
{
lean_object* v___f_1121_; lean_object* v___f_1122_; uint8_t v___x_1123_; 
v___f_1121_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_toGraphviz___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1121_, 0, v_inst_1098_);
lean_closure_set(v___f_1121_, 1, v_decls_1102_);
v___f_1122_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_toGraphviz___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1122_, 0, v___x_1117_);
lean_closure_set(v___f_1122_, 1, v___f_1121_);
v___x_1123_ = lean_nat_dec_le(v___x_1119_, v___x_1119_);
if (v___x_1123_ == 0)
{
if (v___x_1120_ == 0)
{
lean_dec_ref(v___f_1122_);
lean_dec_ref(v_buckets_1118_);
v___y_1111_ = v___x_1104_;
goto v___jp_1110_;
}
else
{
size_t v___x_1124_; size_t v___x_1125_; lean_object* v___x_1126_; 
v___x_1124_ = ((size_t)0ULL);
v___x_1125_ = lean_usize_of_nat(v___x_1119_);
v___x_1126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1117_, v___f_1122_, v_buckets_1118_, v___x_1124_, v___x_1125_, v___x_1104_);
v___y_1111_ = v___x_1126_;
goto v___jp_1110_;
}
}
else
{
size_t v___x_1127_; size_t v___x_1128_; lean_object* v___x_1129_; 
v___x_1127_ = ((size_t)0ULL);
v___x_1128_ = lean_usize_of_nat(v___x_1119_);
v___x_1129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1117_, v___f_1122_, v_buckets_1118_, v___x_1127_, v___x_1128_, v___x_1104_);
v___y_1111_ = v___x_1129_;
goto v___jp_1110_;
}
}
v___jp_1110_:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1112_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___redArg___closed__3));
v___x_1113_ = lean_string_append(v___x_1112_, v___y_1111_);
lean_dec_ref(v___y_1111_);
v___x_1114_ = lean_string_append(v___x_1113_, v_fst_1108_);
lean_dec(v_fst_1108_);
v___x_1115_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___redArg___closed__4));
v___x_1116_ = lean_string_append(v___x_1114_, v___x_1115_);
return v___x_1116_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz(lean_object* v_00_u03b1_1130_, lean_object* v_inst_1131_, lean_object* v_inst_1132_, lean_object* v_inst_1133_, lean_object* v_entry_1134_){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = l_Std_Sat_AIG_toGraphviz___redArg(v_inst_1132_, v_entry_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___boxed(lean_object* v_00_u03b1_1136_, lean_object* v_inst_1137_, lean_object* v_inst_1138_, lean_object* v_inst_1139_, lean_object* v_entry_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Std_Sat_AIG_toGraphviz(v_00_u03b1_1136_, v_inst_1137_, v_inst_1138_, v_inst_1139_, v_entry_1140_);
lean_dec_ref(v_inst_1139_);
lean_dec_ref(v_inst_1137_);
return v_res_1141_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote_go___redArg(lean_object* v_x_1142_, lean_object* v_decls_1143_, lean_object* v_assign_1144_){
_start:
{
uint8_t v___y_1146_; uint8_t v___y_1147_; lean_object* v___x_1149_; 
v___x_1149_ = lean_array_fget_borrowed(v_decls_1143_, v_x_1142_);
switch(lean_obj_tag(v___x_1149_))
{
case 0:
{
uint8_t v___x_1150_; 
lean_dec_ref(v_assign_1144_);
v___x_1150_ = 0;
return v___x_1150_;
}
case 1:
{
lean_object* v_idx_1151_; lean_object* v___x_1152_; uint8_t v___x_1153_; 
v_idx_1151_ = lean_ctor_get(v___x_1149_, 0);
lean_inc(v_idx_1151_);
v___x_1152_ = lean_apply_1(v_assign_1144_, v_idx_1151_);
v___x_1153_ = lean_unbox(v___x_1152_);
return v___x_1153_;
}
default: 
{
lean_object* v_l_1154_; lean_object* v_r_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; uint8_t v_lval_1158_; lean_object* v___x_1159_; uint8_t v_rval_1160_; uint8_t v___y_1162_; uint8_t v___y_1163_; uint8_t v___y_1165_; uint8_t v___y_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; uint8_t v___x_1175_; 
v_l_1154_ = lean_ctor_get(v___x_1149_, 0);
v_r_1155_ = lean_ctor_get(v___x_1149_, 1);
v___x_1156_ = lean_unsigned_to_nat(1u);
v___x_1157_ = lean_nat_shiftr(v_l_1154_, v___x_1156_);
lean_inc_ref(v_assign_1144_);
v_lval_1158_ = l_Std_Sat_AIG_denote_go___redArg(v___x_1157_, v_decls_1143_, v_assign_1144_);
lean_dec(v___x_1157_);
v___x_1159_ = lean_nat_shiftr(v_r_1155_, v___x_1156_);
v_rval_1160_ = l_Std_Sat_AIG_denote_go___redArg(v___x_1159_, v_decls_1143_, v_assign_1144_);
lean_dec(v___x_1159_);
v___x_1173_ = lean_nat_land(v___x_1156_, v_l_1154_);
v___x_1174_ = lean_unsigned_to_nat(0u);
v___x_1175_ = lean_nat_dec_eq(v___x_1173_, v___x_1174_);
lean_dec(v___x_1173_);
if (v___x_1175_ == 0)
{
uint8_t v___x_1176_; 
v___x_1176_ = 1;
v___y_1172_ = v___x_1176_;
goto v___jp_1171_;
}
else
{
uint8_t v___x_1177_; 
v___x_1177_ = 0;
v___y_1172_ = v___x_1177_;
goto v___jp_1171_;
}
v___jp_1161_:
{
if (v_rval_1160_ == 0)
{
if (v___y_1163_ == 0)
{
return v___y_1162_;
}
else
{
v___y_1146_ = v___y_1162_;
v___y_1147_ = v_rval_1160_;
goto v___jp_1145_;
}
}
else
{
v___y_1146_ = v___y_1162_;
v___y_1147_ = v___y_1163_;
goto v___jp_1145_;
}
}
v___jp_1164_:
{
if (v___y_1165_ == 0)
{
lean_object* v___x_1166_; lean_object* v___x_1167_; uint8_t v___x_1168_; 
v___x_1166_ = lean_nat_land(v___x_1156_, v_r_1155_);
v___x_1167_ = lean_unsigned_to_nat(0u);
v___x_1168_ = lean_nat_dec_eq(v___x_1166_, v___x_1167_);
lean_dec(v___x_1166_);
if (v___x_1168_ == 0)
{
uint8_t v___x_1169_; 
v___x_1169_ = 1;
v___y_1162_ = v___y_1165_;
v___y_1163_ = v___x_1169_;
goto v___jp_1161_;
}
else
{
v___y_1162_ = v___y_1165_;
v___y_1163_ = v___y_1165_;
goto v___jp_1161_;
}
}
else
{
uint8_t v___x_1170_; 
v___x_1170_ = 0;
return v___x_1170_;
}
}
v___jp_1171_:
{
if (v_lval_1158_ == 0)
{
if (v___y_1172_ == 0)
{
return v___y_1172_;
}
else
{
v___y_1165_ = v_lval_1158_;
goto v___jp_1164_;
}
}
else
{
v___y_1165_ = v___y_1172_;
goto v___jp_1164_;
}
}
}
}
v___jp_1145_:
{
if (v___y_1147_ == 0)
{
uint8_t v___x_1148_; 
v___x_1148_ = 1;
return v___x_1148_;
}
else
{
return v___y_1146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote_go___redArg___boxed(lean_object* v_x_1178_, lean_object* v_decls_1179_, lean_object* v_assign_1180_){
_start:
{
uint8_t v_res_1181_; lean_object* v_r_1182_; 
v_res_1181_ = l_Std_Sat_AIG_denote_go___redArg(v_x_1178_, v_decls_1179_, v_assign_1180_);
lean_dec_ref(v_decls_1179_);
lean_dec(v_x_1178_);
v_r_1182_ = lean_box(v_res_1181_);
return v_r_1182_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote_go(lean_object* v_00_u03b1_1183_, lean_object* v_x_1184_, lean_object* v_decls_1185_, lean_object* v_assign_1186_, lean_object* v_h1_1187_, lean_object* v_h2_1188_){
_start:
{
uint8_t v___x_1189_; 
v___x_1189_ = l_Std_Sat_AIG_denote_go___redArg(v_x_1184_, v_decls_1185_, v_assign_1186_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote_go___boxed(lean_object* v_00_u03b1_1190_, lean_object* v_x_1191_, lean_object* v_decls_1192_, lean_object* v_assign_1193_, lean_object* v_h1_1194_, lean_object* v_h2_1195_){
_start:
{
uint8_t v_res_1196_; lean_object* v_r_1197_; 
v_res_1196_ = l_Std_Sat_AIG_denote_go(v_00_u03b1_1190_, v_x_1191_, v_decls_1192_, v_assign_1193_, v_h1_1194_, v_h2_1195_);
lean_dec_ref(v_decls_1192_);
lean_dec(v_x_1191_);
v_r_1197_ = lean_box(v_res_1196_);
return v_r_1197_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote___redArg(lean_object* v_assign_1198_, lean_object* v_entry_1199_){
_start:
{
uint8_t v___y_1201_; lean_object* v_ref_1204_; lean_object* v_aig_1205_; lean_object* v_gate_1206_; uint8_t v_invert_1207_; lean_object* v_decls_1208_; uint8_t v___x_1209_; 
v_ref_1204_ = lean_ctor_get(v_entry_1199_, 1);
v_aig_1205_ = lean_ctor_get(v_entry_1199_, 0);
v_gate_1206_ = lean_ctor_get(v_ref_1204_, 0);
v_invert_1207_ = lean_ctor_get_uint8(v_ref_1204_, sizeof(void*)*1);
v_decls_1208_ = lean_ctor_get(v_aig_1205_, 0);
v___x_1209_ = l_Std_Sat_AIG_denote_go___redArg(v_gate_1206_, v_decls_1208_, v_assign_1198_);
if (v___x_1209_ == 0)
{
if (v_invert_1207_ == 0)
{
return v_invert_1207_;
}
else
{
v___y_1201_ = v___x_1209_;
goto v___jp_1200_;
}
}
else
{
v___y_1201_ = v_invert_1207_;
goto v___jp_1200_;
}
v___jp_1200_:
{
if (v___y_1201_ == 0)
{
uint8_t v___x_1202_; 
v___x_1202_ = 1;
return v___x_1202_;
}
else
{
uint8_t v___x_1203_; 
v___x_1203_ = 0;
return v___x_1203_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote___redArg___boxed(lean_object* v_assign_1210_, lean_object* v_entry_1211_){
_start:
{
uint8_t v_res_1212_; lean_object* v_r_1213_; 
v_res_1212_ = l_Std_Sat_AIG_denote___redArg(v_assign_1210_, v_entry_1211_);
lean_dec_ref(v_entry_1211_);
v_r_1213_ = lean_box(v_res_1212_);
return v_r_1213_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote(lean_object* v_00_u03b1_1214_, lean_object* v_inst_1215_, lean_object* v_inst_1216_, lean_object* v_assign_1217_, lean_object* v_entry_1218_){
_start:
{
uint8_t v___x_1219_; 
v___x_1219_ = l_Std_Sat_AIG_denote___redArg(v_assign_1217_, v_entry_1218_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote___boxed(lean_object* v_00_u03b1_1220_, lean_object* v_inst_1221_, lean_object* v_inst_1222_, lean_object* v_assign_1223_, lean_object* v_entry_1224_){
_start:
{
uint8_t v_res_1225_; lean_object* v_r_1226_; 
v_res_1225_ = l_Std_Sat_AIG_denote(v_00_u03b1_1220_, v_inst_1221_, v_inst_1222_, v_assign_1223_, v_entry_1224_);
lean_dec_ref(v_entry_1224_);
lean_dec_ref(v_inst_1222_);
lean_dec_ref(v_inst_1221_);
v_r_1226_ = lean_box(v_res_1225_);
return v_r_1226_;
}
}
static lean_object* _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6(void){
_start:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__5));
v___x_1309_ = l_String_toRawSubstring_x27(v___x_1308_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1(lean_object* v_x_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_){
_start:
{
lean_object* v___x_1334_; uint8_t v___x_1335_; 
v___x_1334_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
lean_inc(v_x_1331_);
v___x_1335_ = l_Lean_Syntax_isOfKind(v_x_1331_, v___x_1334_);
if (v___x_1335_ == 0)
{
lean_object* v___x_1336_; lean_object* v___x_1337_; 
lean_dec_ref(v_a_1332_);
lean_dec(v_x_1331_);
v___x_1336_ = lean_box(1);
v___x_1337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1336_);
lean_ctor_set(v___x_1337_, 1, v_a_1333_);
return v___x_1337_;
}
else
{
lean_object* v_quotContext_1338_; lean_object* v_currMacroScope_1339_; lean_object* v_ref_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; uint8_t v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v_quotContext_1338_ = lean_ctor_get(v_a_1332_, 1);
lean_inc(v_quotContext_1338_);
v_currMacroScope_1339_ = lean_ctor_get(v_a_1332_, 2);
lean_inc(v_currMacroScope_1339_);
v_ref_1340_ = lean_ctor_get(v_a_1332_, 5);
lean_inc(v_ref_1340_);
lean_dec_ref(v_a_1332_);
v___x_1341_ = lean_unsigned_to_nat(1u);
v___x_1342_ = l_Lean_Syntax_getArg(v_x_1331_, v___x_1341_);
v___x_1343_ = lean_unsigned_to_nat(3u);
v___x_1344_ = l_Lean_Syntax_getArg(v_x_1331_, v___x_1343_);
lean_dec(v_x_1331_);
v___x_1345_ = 0;
v___x_1346_ = l_Lean_SourceInfo_fromRef(v_ref_1340_, v___x_1345_);
lean_dec(v_ref_1340_);
v___x_1347_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4));
v___x_1348_ = lean_obj_once(&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6, &l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6_once, _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6);
v___x_1349_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__7));
v___x_1350_ = l_Lean_addMacroScope(v_quotContext_1338_, v___x_1349_, v_currMacroScope_1339_);
v___x_1351_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__12));
lean_inc(v___x_1346_);
v___x_1352_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1346_);
lean_ctor_set(v___x_1352_, 1, v___x_1348_);
lean_ctor_set(v___x_1352_, 2, v___x_1350_);
lean_ctor_set(v___x_1352_, 3, v___x_1351_);
v___x_1353_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__14));
lean_inc(v___x_1346_);
v___x_1354_ = l_Lean_Syntax_node2(v___x_1346_, v___x_1353_, v___x_1344_, v___x_1342_);
v___x_1355_ = l_Lean_Syntax_node2(v___x_1346_, v___x_1347_, v___x_1352_, v___x_1354_);
v___x_1356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1355_);
lean_ctor_set(v___x_1356_, 1, v_a_1333_);
return v___x_1356_;
}
}
}
static lean_object* _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__7(void){
_start:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1373_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___redArg___closed__0));
v___x_1374_ = l_String_toRawSubstring_x27(v___x_1373_);
return v___x_1374_;
}
}
static lean_object* _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__12(void){
_start:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1385_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__11));
v___x_1386_ = l_String_toRawSubstring_x27(v___x_1385_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1(lean_object* v_x_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_){
_start:
{
lean_object* v___x_1413_; uint8_t v___x_1414_; 
v___x_1413_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__1));
lean_inc(v_x_1410_);
v___x_1414_ = l_Lean_Syntax_isOfKind(v_x_1410_, v___x_1413_);
if (v___x_1414_ == 0)
{
lean_object* v___x_1415_; lean_object* v___x_1416_; 
lean_dec_ref(v_a_1411_);
lean_dec(v_x_1410_);
v___x_1415_ = lean_box(1);
v___x_1416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1415_);
lean_ctor_set(v___x_1416_, 1, v_a_1412_);
return v___x_1416_;
}
else
{
lean_object* v_quotContext_1417_; lean_object* v_currMacroScope_1418_; lean_object* v_ref_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; uint8_t v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v_quotContext_1417_ = lean_ctor_get(v_a_1411_, 1);
lean_inc(v_quotContext_1417_);
v_currMacroScope_1418_ = lean_ctor_get(v_a_1411_, 2);
lean_inc(v_currMacroScope_1418_);
v_ref_1419_ = lean_ctor_get(v_a_1411_, 5);
lean_inc(v_ref_1419_);
lean_dec_ref(v_a_1411_);
v___x_1420_ = lean_unsigned_to_nat(1u);
v___x_1421_ = l_Lean_Syntax_getArg(v_x_1410_, v___x_1420_);
v___x_1422_ = lean_unsigned_to_nat(3u);
v___x_1423_ = l_Lean_Syntax_getArg(v_x_1410_, v___x_1422_);
v___x_1424_ = lean_unsigned_to_nat(5u);
v___x_1425_ = l_Lean_Syntax_getArg(v_x_1410_, v___x_1424_);
lean_dec(v_x_1410_);
v___x_1426_ = 0;
v___x_1427_ = l_Lean_SourceInfo_fromRef(v_ref_1419_, v___x_1426_);
lean_dec(v_ref_1419_);
v___x_1428_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4));
v___x_1429_ = lean_obj_once(&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6, &l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6_once, _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6);
v___x_1430_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__7));
lean_inc(v_currMacroScope_1418_);
lean_inc(v_quotContext_1417_);
v___x_1431_ = l_Lean_addMacroScope(v_quotContext_1417_, v___x_1430_, v_currMacroScope_1418_);
v___x_1432_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__12));
lean_inc(v___x_1427_);
v___x_1433_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1427_);
lean_ctor_set(v___x_1433_, 1, v___x_1429_);
lean_ctor_set(v___x_1433_, 2, v___x_1431_);
lean_ctor_set(v___x_1433_, 3, v___x_1432_);
v___x_1434_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__14));
v___x_1435_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__1));
v___x_1436_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__3));
v___x_1437_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__4));
lean_inc(v___x_1427_);
v___x_1438_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1427_);
lean_ctor_set(v___x_1438_, 1, v___x_1437_);
v___x_1439_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__6));
v___x_1440_ = lean_obj_once(&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__7, &l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__7_once, _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__7);
v___x_1441_ = lean_box(0);
lean_inc(v_currMacroScope_1418_);
lean_inc(v_quotContext_1417_);
v___x_1442_ = l_Lean_addMacroScope(v_quotContext_1417_, v___x_1441_, v_currMacroScope_1418_);
v___x_1443_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__10));
lean_inc(v___x_1427_);
v___x_1444_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1427_);
lean_ctor_set(v___x_1444_, 1, v___x_1440_);
lean_ctor_set(v___x_1444_, 2, v___x_1442_);
lean_ctor_set(v___x_1444_, 3, v___x_1443_);
lean_inc(v___x_1427_);
v___x_1445_ = l_Lean_Syntax_node1(v___x_1427_, v___x_1439_, v___x_1444_);
lean_inc(v___x_1427_);
v___x_1446_ = l_Lean_Syntax_node2(v___x_1427_, v___x_1436_, v___x_1438_, v___x_1445_);
v___x_1447_ = lean_obj_once(&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__12, &l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__12_once, _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__12);
v___x_1448_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__15));
v___x_1449_ = l_Lean_addMacroScope(v_quotContext_1417_, v___x_1448_, v_currMacroScope_1418_);
v___x_1450_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__20));
lean_inc(v___x_1427_);
v___x_1451_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1427_);
lean_ctor_set(v___x_1451_, 1, v___x_1447_);
lean_ctor_set(v___x_1451_, 2, v___x_1449_);
lean_ctor_set(v___x_1451_, 3, v___x_1450_);
lean_inc(v___x_1427_);
v___x_1452_ = l_Lean_Syntax_node2(v___x_1427_, v___x_1434_, v___x_1421_, v___x_1423_);
lean_inc(v___x_1427_);
v___x_1453_ = l_Lean_Syntax_node2(v___x_1427_, v___x_1428_, v___x_1451_, v___x_1452_);
v___x_1454_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__21));
lean_inc(v___x_1427_);
v___x_1455_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1427_);
lean_ctor_set(v___x_1455_, 1, v___x_1454_);
lean_inc(v___x_1427_);
v___x_1456_ = l_Lean_Syntax_node3(v___x_1427_, v___x_1435_, v___x_1446_, v___x_1453_, v___x_1455_);
lean_inc(v___x_1427_);
v___x_1457_ = l_Lean_Syntax_node2(v___x_1427_, v___x_1434_, v___x_1425_, v___x_1456_);
v___x_1458_ = l_Lean_Syntax_node2(v___x_1427_, v___x_1428_, v___x_1433_, v___x_1457_);
v___x_1459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1458_);
lean_ctor_set(v___x_1459_, 1, v_a_1412_);
return v___x_1459_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_unexpandDenote(lean_object* v_x_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_){
_start:
{
lean_object* v___x_1517_; uint8_t v___x_1518_; 
v___x_1517_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4));
lean_inc(v_x_1514_);
v___x_1518_ = l_Lean_Syntax_isOfKind(v_x_1514_, v___x_1517_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1519_; lean_object* v___x_1520_; 
lean_dec(v_x_1514_);
v___x_1519_ = lean_box(0);
v___x_1520_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1519_);
lean_ctor_set(v___x_1520_, 1, v_a_1516_);
return v___x_1520_;
}
else
{
lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; uint8_t v___x_1524_; 
v___x_1521_ = lean_unsigned_to_nat(1u);
v___x_1522_ = l_Lean_Syntax_getArg(v_x_1514_, v___x_1521_);
lean_dec(v_x_1514_);
v___x_1523_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1522_);
v___x_1524_ = l_Lean_Syntax_matchesNull(v___x_1522_, v___x_1523_);
if (v___x_1524_ == 0)
{
lean_object* v___x_1525_; lean_object* v___x_1526_; 
lean_dec(v___x_1522_);
v___x_1525_ = lean_box(0);
v___x_1526_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
lean_ctor_set(v___x_1526_, 1, v_a_1516_);
return v___x_1526_;
}
else
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; uint8_t v___x_1530_; 
v___x_1527_ = lean_unsigned_to_nat(0u);
v___x_1528_ = l_Lean_Syntax_getArg(v___x_1522_, v___x_1527_);
v___x_1529_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__1));
lean_inc(v___x_1528_);
v___x_1530_ = l_Lean_Syntax_isOfKind(v___x_1528_, v___x_1529_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1531_ = l_Lean_Syntax_getArg(v___x_1522_, v___x_1521_);
lean_dec(v___x_1522_);
v___x_1532_ = l_Lean_SourceInfo_fromRef(v_a_1515_, v___x_1530_);
v___x_1533_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1534_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc(v___x_1532_);
v___x_1535_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1532_);
lean_ctor_set(v___x_1535_, 1, v___x_1534_);
v___x_1536_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
lean_inc(v___x_1532_);
v___x_1537_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1532_);
lean_ctor_set(v___x_1537_, 1, v___x_1536_);
v___x_1538_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
lean_inc(v___x_1532_);
v___x_1539_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1532_);
lean_ctor_set(v___x_1539_, 1, v___x_1538_);
v___x_1540_ = l_Lean_Syntax_node5(v___x_1532_, v___x_1533_, v___x_1535_, v___x_1528_, v___x_1537_, v___x_1531_, v___x_1539_);
v___x_1541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1540_);
lean_ctor_set(v___x_1541_, 1, v_a_1516_);
return v___x_1541_;
}
else
{
lean_object* v___x_1542_; uint8_t v___x_1543_; 
v___x_1542_ = l_Lean_Syntax_getArg(v___x_1528_, v___x_1521_);
v___x_1543_ = l_Lean_Syntax_matchesNull(v___x_1542_, v___x_1527_);
if (v___x_1543_ == 0)
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1544_ = l_Lean_Syntax_getArg(v___x_1522_, v___x_1521_);
lean_dec(v___x_1522_);
v___x_1545_ = l_Lean_SourceInfo_fromRef(v_a_1515_, v___x_1543_);
v___x_1546_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1547_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc(v___x_1545_);
v___x_1548_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1545_);
lean_ctor_set(v___x_1548_, 1, v___x_1547_);
v___x_1549_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
lean_inc(v___x_1545_);
v___x_1550_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1545_);
lean_ctor_set(v___x_1550_, 1, v___x_1549_);
v___x_1551_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
lean_inc(v___x_1545_);
v___x_1552_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1545_);
lean_ctor_set(v___x_1552_, 1, v___x_1551_);
v___x_1553_ = l_Lean_Syntax_node5(v___x_1545_, v___x_1546_, v___x_1548_, v___x_1528_, v___x_1550_, v___x_1544_, v___x_1552_);
v___x_1554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1553_);
lean_ctor_set(v___x_1554_, 1, v_a_1516_);
return v___x_1554_;
}
else
{
lean_object* v___x_1555_; lean_object* v___x_1556_; uint8_t v___x_1557_; 
v___x_1555_ = l_Lean_Syntax_getArg(v___x_1528_, v___x_1523_);
v___x_1556_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__4));
lean_inc(v___x_1555_);
v___x_1557_ = l_Lean_Syntax_isOfKind(v___x_1555_, v___x_1556_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
lean_dec(v___x_1555_);
v___x_1558_ = l_Lean_Syntax_getArg(v___x_1522_, v___x_1521_);
lean_dec(v___x_1522_);
v___x_1559_ = l_Lean_SourceInfo_fromRef(v_a_1515_, v___x_1557_);
v___x_1560_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1561_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc(v___x_1559_);
v___x_1562_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1559_);
lean_ctor_set(v___x_1562_, 1, v___x_1561_);
v___x_1563_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
lean_inc(v___x_1559_);
v___x_1564_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1559_);
lean_ctor_set(v___x_1564_, 1, v___x_1563_);
v___x_1565_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
lean_inc(v___x_1559_);
v___x_1566_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1559_);
lean_ctor_set(v___x_1566_, 1, v___x_1565_);
v___x_1567_ = l_Lean_Syntax_node5(v___x_1559_, v___x_1560_, v___x_1562_, v___x_1528_, v___x_1564_, v___x_1558_, v___x_1566_);
v___x_1568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1567_);
lean_ctor_set(v___x_1568_, 1, v_a_1516_);
return v___x_1568_;
}
else
{
lean_object* v___x_1569_; lean_object* v___x_1570_; uint8_t v___x_1571_; 
v___x_1569_ = l_Lean_Syntax_getArg(v___x_1555_, v___x_1527_);
lean_dec(v___x_1555_);
v___x_1570_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_1569_);
v___x_1571_ = l_Lean_Syntax_matchesNull(v___x_1569_, v___x_1570_);
if (v___x_1571_ == 0)
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
lean_dec(v___x_1569_);
v___x_1572_ = l_Lean_Syntax_getArg(v___x_1522_, v___x_1521_);
lean_dec(v___x_1522_);
v___x_1573_ = l_Lean_SourceInfo_fromRef(v_a_1515_, v___x_1571_);
v___x_1574_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1575_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc(v___x_1573_);
v___x_1576_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1573_);
lean_ctor_set(v___x_1576_, 1, v___x_1575_);
v___x_1577_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
lean_inc(v___x_1573_);
v___x_1578_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1573_);
lean_ctor_set(v___x_1578_, 1, v___x_1577_);
v___x_1579_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
lean_inc(v___x_1573_);
v___x_1580_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1573_);
lean_ctor_set(v___x_1580_, 1, v___x_1579_);
v___x_1581_ = l_Lean_Syntax_node5(v___x_1573_, v___x_1574_, v___x_1576_, v___x_1528_, v___x_1578_, v___x_1572_, v___x_1580_);
v___x_1582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1581_);
lean_ctor_set(v___x_1582_, 1, v_a_1516_);
return v___x_1582_;
}
else
{
lean_object* v___x_1583_; lean_object* v___x_1584_; uint8_t v___x_1585_; 
v___x_1583_ = l_Lean_Syntax_getArg(v___x_1569_, v___x_1527_);
v___x_1584_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__6));
lean_inc(v___x_1583_);
v___x_1585_ = l_Lean_Syntax_isOfKind(v___x_1583_, v___x_1584_);
if (v___x_1585_ == 0)
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
lean_dec(v___x_1583_);
lean_dec(v___x_1569_);
v___x_1586_ = l_Lean_Syntax_getArg(v___x_1522_, v___x_1521_);
lean_dec(v___x_1522_);
v___x_1587_ = l_Lean_SourceInfo_fromRef(v_a_1515_, v___x_1585_);
v___x_1588_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1589_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc(v___x_1587_);
v___x_1590_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1587_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
v___x_1591_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
lean_inc(v___x_1587_);
v___x_1592_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1587_);
lean_ctor_set(v___x_1592_, 1, v___x_1591_);
v___x_1593_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
lean_inc(v___x_1587_);
v___x_1594_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1587_);
lean_ctor_set(v___x_1594_, 1, v___x_1593_);
v___x_1595_ = l_Lean_Syntax_node5(v___x_1587_, v___x_1588_, v___x_1590_, v___x_1528_, v___x_1592_, v___x_1586_, v___x_1594_);
v___x_1596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1595_);
lean_ctor_set(v___x_1596_, 1, v_a_1516_);
return v___x_1596_;
}
else
{
lean_object* v___x_1597_; lean_object* v___x_1598_; uint8_t v___x_1599_; 
v___x_1597_ = l_Lean_Syntax_getArg(v___x_1583_, v___x_1527_);
v___x_1598_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__8));
lean_inc(v___x_1597_);
v___x_1599_ = l_Lean_Syntax_isOfKind(v___x_1597_, v___x_1598_);
if (v___x_1599_ == 0)
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
lean_dec(v___x_1597_);
lean_dec(v___x_1583_);
lean_dec(v___x_1569_);
v___x_1600_ = l_Lean_Syntax_getArg(v___x_1522_, v___x_1521_);
lean_dec(v___x_1522_);
v___x_1601_ = l_Lean_SourceInfo_fromRef(v_a_1515_, v___x_1599_);
v___x_1602_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1603_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc(v___x_1601_);
v___x_1604_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1601_);
lean_ctor_set(v___x_1604_, 1, v___x_1603_);
v___x_1605_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
lean_inc(v___x_1601_);
v___x_1606_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1601_);
lean_ctor_set(v___x_1606_, 1, v___x_1605_);
v___x_1607_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
lean_inc(v___x_1601_);
v___x_1608_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1601_);
lean_ctor_set(v___x_1608_, 1, v___x_1607_);
v___x_1609_ = l_Lean_Syntax_node5(v___x_1601_, v___x_1602_, v___x_1604_, v___x_1528_, v___x_1606_, v___x_1600_, v___x_1608_);
v___x_1610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1609_);
lean_ctor_set(v___x_1610_, 1, v_a_1516_);
return v___x_1610_;
}
else
{
lean_object* v___x_1611_; lean_object* v___x_1612_; uint8_t v___x_1613_; 
v___x_1611_ = l_Lean_Syntax_getArg(v___x_1597_, v___x_1527_);
v___x_1612_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__10));
v___x_1613_ = l_Lean_Syntax_matchesIdent(v___x_1611_, v___x_1612_);
lean_dec(v___x_1611_);
if (v___x_1613_ == 0)
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
lean_dec(v___x_1597_);
lean_dec(v___x_1583_);
lean_dec(v___x_1569_);
v___x_1614_ = l_Lean_Syntax_getArg(v___x_1522_, v___x_1521_);
lean_dec(v___x_1522_);
v___x_1615_ = l_Lean_SourceInfo_fromRef(v_a_1515_, v___x_1613_);
v___x_1616_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1617_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc(v___x_1615_);
v___x_1618_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1615_);
lean_ctor_set(v___x_1618_, 1, v___x_1617_);
v___x_1619_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
lean_inc(v___x_1615_);
v___x_1620_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1615_);
lean_ctor_set(v___x_1620_, 1, v___x_1619_);
v___x_1621_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
lean_inc(v___x_1615_);
v___x_1622_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1615_);
lean_ctor_set(v___x_1622_, 1, v___x_1621_);
v___x_1623_ = l_Lean_Syntax_node5(v___x_1615_, v___x_1616_, v___x_1618_, v___x_1528_, v___x_1620_, v___x_1614_, v___x_1622_);
v___x_1624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1623_);
lean_ctor_set(v___x_1624_, 1, v_a_1516_);
return v___x_1624_;
}
else
{
lean_object* v___x_1625_; uint8_t v___x_1626_; 
v___x_1625_ = l_Lean_Syntax_getArg(v___x_1597_, v___x_1521_);
lean_dec(v___x_1597_);
v___x_1626_ = l_Lean_Syntax_matchesNull(v___x_1625_, v___x_1527_);
if (v___x_1626_ == 0)
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
lean_dec(v___x_1583_);
lean_dec(v___x_1569_);
v___x_1627_ = l_Lean_Syntax_getArg(v___x_1522_, v___x_1521_);
lean_dec(v___x_1522_);
v___x_1628_ = l_Lean_SourceInfo_fromRef(v_a_1515_, v___x_1626_);
v___x_1629_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1630_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc(v___x_1628_);
v___x_1631_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1628_);
lean_ctor_set(v___x_1631_, 1, v___x_1630_);
v___x_1632_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
lean_inc(v___x_1628_);
v___x_1633_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1628_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
v___x_1634_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
lean_inc(v___x_1628_);
v___x_1635_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1628_);
lean_ctor_set(v___x_1635_, 1, v___x_1634_);
v___x_1636_ = l_Lean_Syntax_node5(v___x_1628_, v___x_1629_, v___x_1631_, v___x_1528_, v___x_1633_, v___x_1627_, v___x_1635_);
v___x_1637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1636_);
lean_ctor_set(v___x_1637_, 1, v_a_1516_);
return v___x_1637_;
}
else
{
lean_object* v___x_1638_; lean_object* v___x_1639_; uint8_t v___x_1640_; 
v___x_1638_ = l_Lean_Syntax_getArg(v___x_1583_, v___x_1521_);
lean_dec(v___x_1583_);
v___x_1639_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_1638_);
v___x_1640_ = l_Lean_Syntax_matchesNull(v___x_1638_, v___x_1639_);
if (v___x_1640_ == 0)
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
lean_dec(v___x_1638_);
lean_dec(v___x_1569_);
v___x_1641_ = l_Lean_Syntax_getArg(v___x_1522_, v___x_1521_);
lean_dec(v___x_1522_);
v___x_1642_ = l_Lean_SourceInfo_fromRef(v_a_1515_, v___x_1640_);
v___x_1643_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1644_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc(v___x_1642_);
v___x_1645_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1642_);
lean_ctor_set(v___x_1645_, 1, v___x_1644_);
v___x_1646_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
lean_inc(v___x_1642_);
v___x_1647_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1642_);
lean_ctor_set(v___x_1647_, 1, v___x_1646_);
v___x_1648_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
lean_inc(v___x_1642_);
v___x_1649_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1642_);
lean_ctor_set(v___x_1649_, 1, v___x_1648_);
v___x_1650_ = l_Lean_Syntax_node5(v___x_1642_, v___x_1643_, v___x_1645_, v___x_1528_, v___x_1647_, v___x_1641_, v___x_1649_);
v___x_1651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1650_);
lean_ctor_set(v___x_1651_, 1, v_a_1516_);
return v___x_1651_;
}
else
{
lean_object* v___x_1652_; uint8_t v___x_1653_; 
v___x_1652_ = l_Lean_Syntax_getArg(v___x_1638_, v___x_1527_);
v___x_1653_ = l_Lean_Syntax_matchesNull(v___x_1652_, v___x_1527_);
if (v___x_1653_ == 0)
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
lean_dec(v___x_1638_);
lean_dec(v___x_1569_);
v___x_1654_ = l_Lean_Syntax_getArg(v___x_1522_, v___x_1521_);
lean_dec(v___x_1522_);
v___x_1655_ = l_Lean_SourceInfo_fromRef(v_a_1515_, v___x_1653_);
v___x_1656_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1657_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc(v___x_1655_);
v___x_1658_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1655_);
lean_ctor_set(v___x_1658_, 1, v___x_1657_);
v___x_1659_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
lean_inc(v___x_1655_);
v___x_1660_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1655_);
lean_ctor_set(v___x_1660_, 1, v___x_1659_);
v___x_1661_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
lean_inc(v___x_1655_);
v___x_1662_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1655_);
lean_ctor_set(v___x_1662_, 1, v___x_1661_);
v___x_1663_ = l_Lean_Syntax_node5(v___x_1655_, v___x_1656_, v___x_1658_, v___x_1528_, v___x_1660_, v___x_1654_, v___x_1662_);
v___x_1664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1663_);
lean_ctor_set(v___x_1664_, 1, v_a_1516_);
return v___x_1664_;
}
else
{
lean_object* v___x_1665_; uint8_t v___x_1666_; 
v___x_1665_ = l_Lean_Syntax_getArg(v___x_1638_, v___x_1521_);
v___x_1666_ = l_Lean_Syntax_matchesNull(v___x_1665_, v___x_1527_);
if (v___x_1666_ == 0)
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
lean_dec(v___x_1638_);
lean_dec(v___x_1569_);
v___x_1667_ = l_Lean_Syntax_getArg(v___x_1522_, v___x_1521_);
lean_dec(v___x_1522_);
v___x_1668_ = l_Lean_SourceInfo_fromRef(v_a_1515_, v___x_1666_);
v___x_1669_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1670_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc(v___x_1668_);
v___x_1671_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1668_);
lean_ctor_set(v___x_1671_, 1, v___x_1670_);
v___x_1672_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
lean_inc(v___x_1668_);
v___x_1673_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1668_);
lean_ctor_set(v___x_1673_, 1, v___x_1672_);
v___x_1674_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
lean_inc(v___x_1668_);
v___x_1675_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1668_);
lean_ctor_set(v___x_1675_, 1, v___x_1674_);
v___x_1676_ = l_Lean_Syntax_node5(v___x_1668_, v___x_1669_, v___x_1671_, v___x_1528_, v___x_1673_, v___x_1667_, v___x_1675_);
v___x_1677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1676_);
lean_ctor_set(v___x_1677_, 1, v_a_1516_);
return v___x_1677_;
}
else
{
lean_object* v___x_1678_; lean_object* v___x_1679_; uint8_t v___x_1680_; 
v___x_1678_ = l_Lean_Syntax_getArg(v___x_1638_, v___x_1523_);
lean_dec(v___x_1638_);
v___x_1679_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__12));
lean_inc(v___x_1678_);
v___x_1680_ = l_Lean_Syntax_isOfKind(v___x_1678_, v___x_1679_);
if (v___x_1680_ == 0)
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
lean_dec(v___x_1678_);
lean_dec(v___x_1569_);
v___x_1681_ = l_Lean_Syntax_getArg(v___x_1522_, v___x_1521_);
lean_dec(v___x_1522_);
v___x_1682_ = l_Lean_SourceInfo_fromRef(v_a_1515_, v___x_1680_);
v___x_1683_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1684_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc(v___x_1682_);
v___x_1685_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1682_);
lean_ctor_set(v___x_1685_, 1, v___x_1684_);
v___x_1686_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
lean_inc(v___x_1682_);
v___x_1687_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1682_);
lean_ctor_set(v___x_1687_, 1, v___x_1686_);
v___x_1688_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
lean_inc(v___x_1682_);
v___x_1689_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1682_);
lean_ctor_set(v___x_1689_, 1, v___x_1688_);
v___x_1690_ = l_Lean_Syntax_node5(v___x_1682_, v___x_1683_, v___x_1685_, v___x_1528_, v___x_1687_, v___x_1681_, v___x_1689_);
v___x_1691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1690_);
lean_ctor_set(v___x_1691_, 1, v_a_1516_);
return v___x_1691_;
}
else
{
lean_object* v___x_1692_; uint8_t v___x_1693_; 
v___x_1692_ = l_Lean_Syntax_getArg(v___x_1678_, v___x_1521_);
v___x_1693_ = l_Lean_Syntax_matchesNull(v___x_1692_, v___x_1527_);
if (v___x_1693_ == 0)
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
lean_dec(v___x_1678_);
lean_dec(v___x_1569_);
v___x_1694_ = l_Lean_Syntax_getArg(v___x_1522_, v___x_1521_);
lean_dec(v___x_1522_);
v___x_1695_ = l_Lean_SourceInfo_fromRef(v_a_1515_, v___x_1693_);
v___x_1696_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1697_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc(v___x_1695_);
v___x_1698_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1695_);
lean_ctor_set(v___x_1698_, 1, v___x_1697_);
v___x_1699_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
lean_inc(v___x_1695_);
v___x_1700_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1695_);
lean_ctor_set(v___x_1700_, 1, v___x_1699_);
v___x_1701_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
lean_inc(v___x_1695_);
v___x_1702_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1695_);
lean_ctor_set(v___x_1702_, 1, v___x_1701_);
v___x_1703_ = l_Lean_Syntax_node5(v___x_1695_, v___x_1696_, v___x_1698_, v___x_1528_, v___x_1700_, v___x_1694_, v___x_1702_);
v___x_1704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1703_);
lean_ctor_set(v___x_1704_, 1, v_a_1516_);
return v___x_1704_;
}
else
{
lean_object* v___x_1705_; uint8_t v___x_1706_; 
v___x_1705_ = l_Lean_Syntax_getArg(v___x_1569_, v___x_1523_);
lean_inc(v___x_1705_);
v___x_1706_ = l_Lean_Syntax_isOfKind(v___x_1705_, v___x_1584_);
if (v___x_1706_ == 0)
{
lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
lean_dec(v___x_1705_);
lean_dec(v___x_1678_);
lean_dec(v___x_1569_);
v___x_1707_ = l_Lean_Syntax_getArg(v___x_1522_, v___x_1521_);
lean_dec(v___x_1522_);
v___x_1708_ = l_Lean_SourceInfo_fromRef(v_a_1515_, v___x_1706_);
v___x_1709_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1710_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc(v___x_1708_);
v___x_1711_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1708_);
lean_ctor_set(v___x_1711_, 1, v___x_1710_);
v___x_1712_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
lean_inc(v___x_1708_);
v___x_1713_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1708_);
lean_ctor_set(v___x_1713_, 1, v___x_1712_);
v___x_1714_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
lean_inc(v___x_1708_);
v___x_1715_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1708_);
lean_ctor_set(v___x_1715_, 1, v___x_1714_);
v___x_1716_ = l_Lean_Syntax_node5(v___x_1708_, v___x_1709_, v___x_1711_, v___x_1528_, v___x_1713_, v___x_1707_, v___x_1715_);
v___x_1717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1716_);
lean_ctor_set(v___x_1717_, 1, v_a_1516_);
return v___x_1717_;
}
else
{
lean_object* v___x_1718_; uint8_t v___x_1719_; 
v___x_1718_ = l_Lean_Syntax_getArg(v___x_1705_, v___x_1527_);
lean_inc(v___x_1718_);
v___x_1719_ = l_Lean_Syntax_isOfKind(v___x_1718_, v___x_1598_);
if (v___x_1719_ == 0)
{
lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
lean_dec(v___x_1718_);
lean_dec(v___x_1705_);
lean_dec(v___x_1678_);
lean_dec(v___x_1569_);
v___x_1720_ = l_Lean_Syntax_getArg(v___x_1522_, v___x_1521_);
lean_dec(v___x_1522_);
v___x_1721_ = l_Lean_SourceInfo_fromRef(v_a_1515_, v___x_1719_);
v___x_1722_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1723_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc(v___x_1721_);
v___x_1724_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1721_);
lean_ctor_set(v___x_1724_, 1, v___x_1723_);
v___x_1725_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
lean_inc(v___x_1721_);
v___x_1726_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1721_);
lean_ctor_set(v___x_1726_, 1, v___x_1725_);
v___x_1727_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
lean_inc(v___x_1721_);
v___x_1728_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1721_);
lean_ctor_set(v___x_1728_, 1, v___x_1727_);
v___x_1729_ = l_Lean_Syntax_node5(v___x_1721_, v___x_1722_, v___x_1724_, v___x_1528_, v___x_1726_, v___x_1720_, v___x_1728_);
v___x_1730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1729_);
lean_ctor_set(v___x_1730_, 1, v_a_1516_);
return v___x_1730_;
}
else
{
lean_object* v___x_1731_; lean_object* v___x_1732_; uint8_t v___x_1733_; 
v___x_1731_ = l_Lean_Syntax_getArg(v___x_1718_, v___x_1527_);
v___x_1732_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__14));
v___x_1733_ = l_Lean_Syntax_matchesIdent(v___x_1731_, v___x_1732_);
lean_dec(v___x_1731_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
lean_dec(v___x_1718_);
lean_dec(v___x_1705_);
lean_dec(v___x_1678_);
lean_dec(v___x_1569_);
v___x_1734_ = l_Lean_Syntax_getArg(v___x_1522_, v___x_1521_);
lean_dec(v___x_1522_);
v___x_1735_ = l_Lean_SourceInfo_fromRef(v_a_1515_, v___x_1733_);
v___x_1736_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1737_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc(v___x_1735_);
v___x_1738_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1735_);
lean_ctor_set(v___x_1738_, 1, v___x_1737_);
v___x_1739_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
lean_inc(v___x_1735_);
v___x_1740_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1735_);
lean_ctor_set(v___x_1740_, 1, v___x_1739_);
v___x_1741_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
lean_inc(v___x_1735_);
v___x_1742_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1735_);
lean_ctor_set(v___x_1742_, 1, v___x_1741_);
v___x_1743_ = l_Lean_Syntax_node5(v___x_1735_, v___x_1736_, v___x_1738_, v___x_1528_, v___x_1740_, v___x_1734_, v___x_1742_);
v___x_1744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1743_);
lean_ctor_set(v___x_1744_, 1, v_a_1516_);
return v___x_1744_;
}
else
{
lean_object* v___x_1745_; uint8_t v___x_1746_; 
v___x_1745_ = l_Lean_Syntax_getArg(v___x_1718_, v___x_1521_);
lean_dec(v___x_1718_);
v___x_1746_ = l_Lean_Syntax_matchesNull(v___x_1745_, v___x_1527_);
if (v___x_1746_ == 0)
{
lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
lean_dec(v___x_1705_);
lean_dec(v___x_1678_);
lean_dec(v___x_1569_);
v___x_1747_ = l_Lean_Syntax_getArg(v___x_1522_, v___x_1521_);
lean_dec(v___x_1522_);
v___x_1748_ = l_Lean_SourceInfo_fromRef(v_a_1515_, v___x_1746_);
v___x_1749_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1750_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc(v___x_1748_);
v___x_1751_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1748_);
lean_ctor_set(v___x_1751_, 1, v___x_1750_);
v___x_1752_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
lean_inc(v___x_1748_);
v___x_1753_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1748_);
lean_ctor_set(v___x_1753_, 1, v___x_1752_);
v___x_1754_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
lean_inc(v___x_1748_);
v___x_1755_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1748_);
lean_ctor_set(v___x_1755_, 1, v___x_1754_);
v___x_1756_ = l_Lean_Syntax_node5(v___x_1748_, v___x_1749_, v___x_1751_, v___x_1528_, v___x_1753_, v___x_1747_, v___x_1755_);
v___x_1757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1756_);
lean_ctor_set(v___x_1757_, 1, v_a_1516_);
return v___x_1757_;
}
else
{
lean_object* v___x_1758_; uint8_t v___x_1759_; 
v___x_1758_ = l_Lean_Syntax_getArg(v___x_1705_, v___x_1521_);
lean_dec(v___x_1705_);
lean_inc(v___x_1758_);
v___x_1759_ = l_Lean_Syntax_matchesNull(v___x_1758_, v___x_1639_);
if (v___x_1759_ == 0)
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
lean_dec(v___x_1758_);
lean_dec(v___x_1678_);
lean_dec(v___x_1569_);
v___x_1760_ = l_Lean_Syntax_getArg(v___x_1522_, v___x_1521_);
lean_dec(v___x_1522_);
v___x_1761_ = l_Lean_SourceInfo_fromRef(v_a_1515_, v___x_1759_);
v___x_1762_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1763_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc(v___x_1761_);
v___x_1764_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1764_, 0, v___x_1761_);
lean_ctor_set(v___x_1764_, 1, v___x_1763_);
v___x_1765_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
lean_inc(v___x_1761_);
v___x_1766_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1766_, 0, v___x_1761_);
lean_ctor_set(v___x_1766_, 1, v___x_1765_);
v___x_1767_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
lean_inc(v___x_1761_);
v___x_1768_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1761_);
lean_ctor_set(v___x_1768_, 1, v___x_1767_);
v___x_1769_ = l_Lean_Syntax_node5(v___x_1761_, v___x_1762_, v___x_1764_, v___x_1528_, v___x_1766_, v___x_1760_, v___x_1768_);
v___x_1770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1769_);
lean_ctor_set(v___x_1770_, 1, v_a_1516_);
return v___x_1770_;
}
else
{
lean_object* v___x_1771_; uint8_t v___x_1772_; 
v___x_1771_ = l_Lean_Syntax_getArg(v___x_1758_, v___x_1527_);
v___x_1772_ = l_Lean_Syntax_matchesNull(v___x_1771_, v___x_1527_);
if (v___x_1772_ == 0)
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
lean_dec(v___x_1758_);
lean_dec(v___x_1678_);
lean_dec(v___x_1569_);
v___x_1773_ = l_Lean_Syntax_getArg(v___x_1522_, v___x_1521_);
lean_dec(v___x_1522_);
v___x_1774_ = l_Lean_SourceInfo_fromRef(v_a_1515_, v___x_1772_);
v___x_1775_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1776_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc(v___x_1774_);
v___x_1777_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1774_);
lean_ctor_set(v___x_1777_, 1, v___x_1776_);
v___x_1778_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
lean_inc(v___x_1774_);
v___x_1779_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1774_);
lean_ctor_set(v___x_1779_, 1, v___x_1778_);
v___x_1780_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
lean_inc(v___x_1774_);
v___x_1781_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1774_);
lean_ctor_set(v___x_1781_, 1, v___x_1780_);
v___x_1782_ = l_Lean_Syntax_node5(v___x_1774_, v___x_1775_, v___x_1777_, v___x_1528_, v___x_1779_, v___x_1773_, v___x_1781_);
v___x_1783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1782_);
lean_ctor_set(v___x_1783_, 1, v_a_1516_);
return v___x_1783_;
}
else
{
lean_object* v___x_1784_; uint8_t v___x_1785_; 
v___x_1784_ = l_Lean_Syntax_getArg(v___x_1758_, v___x_1521_);
v___x_1785_ = l_Lean_Syntax_matchesNull(v___x_1784_, v___x_1527_);
if (v___x_1785_ == 0)
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
lean_dec(v___x_1758_);
lean_dec(v___x_1678_);
lean_dec(v___x_1569_);
v___x_1786_ = l_Lean_Syntax_getArg(v___x_1522_, v___x_1521_);
lean_dec(v___x_1522_);
v___x_1787_ = l_Lean_SourceInfo_fromRef(v_a_1515_, v___x_1785_);
v___x_1788_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1789_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc(v___x_1787_);
v___x_1790_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1787_);
lean_ctor_set(v___x_1790_, 1, v___x_1789_);
v___x_1791_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
lean_inc(v___x_1787_);
v___x_1792_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1787_);
lean_ctor_set(v___x_1792_, 1, v___x_1791_);
v___x_1793_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
lean_inc(v___x_1787_);
v___x_1794_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1787_);
lean_ctor_set(v___x_1794_, 1, v___x_1793_);
v___x_1795_ = l_Lean_Syntax_node5(v___x_1787_, v___x_1788_, v___x_1790_, v___x_1528_, v___x_1792_, v___x_1786_, v___x_1794_);
v___x_1796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1795_);
lean_ctor_set(v___x_1796_, 1, v_a_1516_);
return v___x_1796_;
}
else
{
lean_object* v___x_1797_; uint8_t v___x_1798_; 
v___x_1797_ = l_Lean_Syntax_getArg(v___x_1758_, v___x_1523_);
lean_dec(v___x_1758_);
lean_inc(v___x_1797_);
v___x_1798_ = l_Lean_Syntax_isOfKind(v___x_1797_, v___x_1679_);
if (v___x_1798_ == 0)
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
lean_dec(v___x_1797_);
lean_dec(v___x_1678_);
lean_dec(v___x_1569_);
v___x_1799_ = l_Lean_Syntax_getArg(v___x_1522_, v___x_1521_);
lean_dec(v___x_1522_);
v___x_1800_ = l_Lean_SourceInfo_fromRef(v_a_1515_, v___x_1798_);
v___x_1801_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1802_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc(v___x_1800_);
v___x_1803_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1800_);
lean_ctor_set(v___x_1803_, 1, v___x_1802_);
v___x_1804_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
lean_inc(v___x_1800_);
v___x_1805_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1800_);
lean_ctor_set(v___x_1805_, 1, v___x_1804_);
v___x_1806_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
lean_inc(v___x_1800_);
v___x_1807_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1800_);
lean_ctor_set(v___x_1807_, 1, v___x_1806_);
v___x_1808_ = l_Lean_Syntax_node5(v___x_1800_, v___x_1801_, v___x_1803_, v___x_1528_, v___x_1805_, v___x_1799_, v___x_1807_);
v___x_1809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1808_);
lean_ctor_set(v___x_1809_, 1, v_a_1516_);
return v___x_1809_;
}
else
{
lean_object* v___x_1810_; uint8_t v___x_1811_; 
v___x_1810_ = l_Lean_Syntax_getArg(v___x_1797_, v___x_1521_);
v___x_1811_ = l_Lean_Syntax_matchesNull(v___x_1810_, v___x_1527_);
if (v___x_1811_ == 0)
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
lean_dec(v___x_1797_);
lean_dec(v___x_1678_);
lean_dec(v___x_1569_);
v___x_1812_ = l_Lean_Syntax_getArg(v___x_1522_, v___x_1521_);
lean_dec(v___x_1522_);
v___x_1813_ = l_Lean_SourceInfo_fromRef(v_a_1515_, v___x_1811_);
v___x_1814_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1815_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc(v___x_1813_);
v___x_1816_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1813_);
lean_ctor_set(v___x_1816_, 1, v___x_1815_);
v___x_1817_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
lean_inc(v___x_1813_);
v___x_1818_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1813_);
lean_ctor_set(v___x_1818_, 1, v___x_1817_);
v___x_1819_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
lean_inc(v___x_1813_);
v___x_1820_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1813_);
lean_ctor_set(v___x_1820_, 1, v___x_1819_);
v___x_1821_ = l_Lean_Syntax_node5(v___x_1813_, v___x_1814_, v___x_1816_, v___x_1528_, v___x_1818_, v___x_1812_, v___x_1820_);
v___x_1822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1821_);
lean_ctor_set(v___x_1822_, 1, v_a_1516_);
return v___x_1822_;
}
else
{
lean_object* v___x_1823_; lean_object* v___x_1824_; uint8_t v___x_1825_; 
v___x_1823_ = lean_unsigned_to_nat(4u);
v___x_1824_ = l_Lean_Syntax_getArg(v___x_1569_, v___x_1823_);
lean_dec(v___x_1569_);
lean_inc(v___x_1824_);
v___x_1825_ = l_Lean_Syntax_isOfKind(v___x_1824_, v___x_1584_);
if (v___x_1825_ == 0)
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
lean_dec(v___x_1824_);
lean_dec(v___x_1797_);
lean_dec(v___x_1678_);
v___x_1826_ = l_Lean_Syntax_getArg(v___x_1522_, v___x_1521_);
lean_dec(v___x_1522_);
v___x_1827_ = l_Lean_SourceInfo_fromRef(v_a_1515_, v___x_1825_);
v___x_1828_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1829_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc(v___x_1827_);
v___x_1830_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1827_);
lean_ctor_set(v___x_1830_, 1, v___x_1829_);
v___x_1831_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
lean_inc(v___x_1827_);
v___x_1832_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1827_);
lean_ctor_set(v___x_1832_, 1, v___x_1831_);
v___x_1833_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
lean_inc(v___x_1827_);
v___x_1834_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1827_);
lean_ctor_set(v___x_1834_, 1, v___x_1833_);
v___x_1835_ = l_Lean_Syntax_node5(v___x_1827_, v___x_1828_, v___x_1830_, v___x_1528_, v___x_1832_, v___x_1826_, v___x_1834_);
v___x_1836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1835_);
lean_ctor_set(v___x_1836_, 1, v_a_1516_);
return v___x_1836_;
}
else
{
lean_object* v___x_1837_; uint8_t v___x_1838_; 
v___x_1837_ = l_Lean_Syntax_getArg(v___x_1824_, v___x_1527_);
lean_inc(v___x_1837_);
v___x_1838_ = l_Lean_Syntax_isOfKind(v___x_1837_, v___x_1598_);
if (v___x_1838_ == 0)
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
lean_dec(v___x_1837_);
lean_dec(v___x_1824_);
lean_dec(v___x_1797_);
lean_dec(v___x_1678_);
v___x_1839_ = l_Lean_Syntax_getArg(v___x_1522_, v___x_1521_);
lean_dec(v___x_1522_);
v___x_1840_ = l_Lean_SourceInfo_fromRef(v_a_1515_, v___x_1838_);
v___x_1841_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1842_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc(v___x_1840_);
v___x_1843_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1840_);
lean_ctor_set(v___x_1843_, 1, v___x_1842_);
v___x_1844_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
lean_inc(v___x_1840_);
v___x_1845_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1840_);
lean_ctor_set(v___x_1845_, 1, v___x_1844_);
v___x_1846_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
lean_inc(v___x_1840_);
v___x_1847_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1840_);
lean_ctor_set(v___x_1847_, 1, v___x_1846_);
v___x_1848_ = l_Lean_Syntax_node5(v___x_1840_, v___x_1841_, v___x_1843_, v___x_1528_, v___x_1845_, v___x_1839_, v___x_1847_);
v___x_1849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1848_);
lean_ctor_set(v___x_1849_, 1, v_a_1516_);
return v___x_1849_;
}
else
{
lean_object* v___x_1850_; lean_object* v___x_1851_; uint8_t v___x_1852_; 
v___x_1850_ = l_Lean_Syntax_getArg(v___x_1837_, v___x_1527_);
v___x_1851_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__16));
v___x_1852_ = l_Lean_Syntax_matchesIdent(v___x_1850_, v___x_1851_);
lean_dec(v___x_1850_);
if (v___x_1852_ == 0)
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
lean_dec(v___x_1837_);
lean_dec(v___x_1824_);
lean_dec(v___x_1797_);
lean_dec(v___x_1678_);
v___x_1853_ = l_Lean_Syntax_getArg(v___x_1522_, v___x_1521_);
lean_dec(v___x_1522_);
v___x_1854_ = l_Lean_SourceInfo_fromRef(v_a_1515_, v___x_1852_);
v___x_1855_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1856_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc(v___x_1854_);
v___x_1857_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1854_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
v___x_1858_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
lean_inc(v___x_1854_);
v___x_1859_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1854_);
lean_ctor_set(v___x_1859_, 1, v___x_1858_);
v___x_1860_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
lean_inc(v___x_1854_);
v___x_1861_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1854_);
lean_ctor_set(v___x_1861_, 1, v___x_1860_);
v___x_1862_ = l_Lean_Syntax_node5(v___x_1854_, v___x_1855_, v___x_1857_, v___x_1528_, v___x_1859_, v___x_1853_, v___x_1861_);
v___x_1863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1862_);
lean_ctor_set(v___x_1863_, 1, v_a_1516_);
return v___x_1863_;
}
else
{
lean_object* v___x_1864_; uint8_t v___x_1865_; 
v___x_1864_ = l_Lean_Syntax_getArg(v___x_1837_, v___x_1521_);
lean_dec(v___x_1837_);
v___x_1865_ = l_Lean_Syntax_matchesNull(v___x_1864_, v___x_1527_);
if (v___x_1865_ == 0)
{
lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
lean_dec(v___x_1824_);
lean_dec(v___x_1797_);
lean_dec(v___x_1678_);
v___x_1866_ = l_Lean_Syntax_getArg(v___x_1522_, v___x_1521_);
lean_dec(v___x_1522_);
v___x_1867_ = l_Lean_SourceInfo_fromRef(v_a_1515_, v___x_1865_);
v___x_1868_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1869_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc(v___x_1867_);
v___x_1870_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1867_);
lean_ctor_set(v___x_1870_, 1, v___x_1869_);
v___x_1871_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
lean_inc(v___x_1867_);
v___x_1872_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1867_);
lean_ctor_set(v___x_1872_, 1, v___x_1871_);
v___x_1873_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
lean_inc(v___x_1867_);
v___x_1874_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1867_);
lean_ctor_set(v___x_1874_, 1, v___x_1873_);
v___x_1875_ = l_Lean_Syntax_node5(v___x_1867_, v___x_1868_, v___x_1870_, v___x_1528_, v___x_1872_, v___x_1866_, v___x_1874_);
v___x_1876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1875_);
lean_ctor_set(v___x_1876_, 1, v_a_1516_);
return v___x_1876_;
}
else
{
lean_object* v___x_1877_; uint8_t v___x_1878_; 
v___x_1877_ = l_Lean_Syntax_getArg(v___x_1824_, v___x_1521_);
lean_dec(v___x_1824_);
lean_inc(v___x_1877_);
v___x_1878_ = l_Lean_Syntax_matchesNull(v___x_1877_, v___x_1639_);
if (v___x_1878_ == 0)
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
lean_dec(v___x_1877_);
lean_dec(v___x_1797_);
lean_dec(v___x_1678_);
v___x_1879_ = l_Lean_Syntax_getArg(v___x_1522_, v___x_1521_);
lean_dec(v___x_1522_);
v___x_1880_ = l_Lean_SourceInfo_fromRef(v_a_1515_, v___x_1878_);
v___x_1881_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1882_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc(v___x_1880_);
v___x_1883_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1880_);
lean_ctor_set(v___x_1883_, 1, v___x_1882_);
v___x_1884_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
lean_inc(v___x_1880_);
v___x_1885_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1880_);
lean_ctor_set(v___x_1885_, 1, v___x_1884_);
v___x_1886_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
lean_inc(v___x_1880_);
v___x_1887_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1887_, 0, v___x_1880_);
lean_ctor_set(v___x_1887_, 1, v___x_1886_);
v___x_1888_ = l_Lean_Syntax_node5(v___x_1880_, v___x_1881_, v___x_1883_, v___x_1528_, v___x_1885_, v___x_1879_, v___x_1887_);
v___x_1889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1888_);
lean_ctor_set(v___x_1889_, 1, v_a_1516_);
return v___x_1889_;
}
else
{
lean_object* v___x_1890_; uint8_t v___x_1891_; 
v___x_1890_ = l_Lean_Syntax_getArg(v___x_1877_, v___x_1527_);
v___x_1891_ = l_Lean_Syntax_matchesNull(v___x_1890_, v___x_1527_);
if (v___x_1891_ == 0)
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
lean_dec(v___x_1877_);
lean_dec(v___x_1797_);
lean_dec(v___x_1678_);
v___x_1892_ = l_Lean_Syntax_getArg(v___x_1522_, v___x_1521_);
lean_dec(v___x_1522_);
v___x_1893_ = l_Lean_SourceInfo_fromRef(v_a_1515_, v___x_1891_);
v___x_1894_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1895_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc(v___x_1893_);
v___x_1896_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1893_);
lean_ctor_set(v___x_1896_, 1, v___x_1895_);
v___x_1897_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
lean_inc(v___x_1893_);
v___x_1898_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1893_);
lean_ctor_set(v___x_1898_, 1, v___x_1897_);
v___x_1899_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
lean_inc(v___x_1893_);
v___x_1900_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1893_);
lean_ctor_set(v___x_1900_, 1, v___x_1899_);
v___x_1901_ = l_Lean_Syntax_node5(v___x_1893_, v___x_1894_, v___x_1896_, v___x_1528_, v___x_1898_, v___x_1892_, v___x_1900_);
v___x_1902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1901_);
lean_ctor_set(v___x_1902_, 1, v_a_1516_);
return v___x_1902_;
}
else
{
lean_object* v___x_1903_; uint8_t v___x_1904_; 
v___x_1903_ = l_Lean_Syntax_getArg(v___x_1877_, v___x_1521_);
v___x_1904_ = l_Lean_Syntax_matchesNull(v___x_1903_, v___x_1527_);
if (v___x_1904_ == 0)
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
lean_dec(v___x_1877_);
lean_dec(v___x_1797_);
lean_dec(v___x_1678_);
v___x_1905_ = l_Lean_Syntax_getArg(v___x_1522_, v___x_1521_);
lean_dec(v___x_1522_);
v___x_1906_ = l_Lean_SourceInfo_fromRef(v_a_1515_, v___x_1904_);
v___x_1907_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1908_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc(v___x_1906_);
v___x_1909_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1906_);
lean_ctor_set(v___x_1909_, 1, v___x_1908_);
v___x_1910_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
lean_inc(v___x_1906_);
v___x_1911_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1906_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
v___x_1912_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
lean_inc(v___x_1906_);
v___x_1913_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1906_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
v___x_1914_ = l_Lean_Syntax_node5(v___x_1906_, v___x_1907_, v___x_1909_, v___x_1528_, v___x_1911_, v___x_1905_, v___x_1913_);
v___x_1915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1914_);
lean_ctor_set(v___x_1915_, 1, v_a_1516_);
return v___x_1915_;
}
else
{
lean_object* v___x_1916_; uint8_t v___x_1917_; 
v___x_1916_ = l_Lean_Syntax_getArg(v___x_1877_, v___x_1523_);
lean_dec(v___x_1877_);
lean_inc(v___x_1916_);
v___x_1917_ = l_Lean_Syntax_isOfKind(v___x_1916_, v___x_1679_);
if (v___x_1917_ == 0)
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
lean_dec(v___x_1916_);
lean_dec(v___x_1797_);
lean_dec(v___x_1678_);
v___x_1918_ = l_Lean_Syntax_getArg(v___x_1522_, v___x_1521_);
lean_dec(v___x_1522_);
v___x_1919_ = l_Lean_SourceInfo_fromRef(v_a_1515_, v___x_1917_);
v___x_1920_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1921_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc(v___x_1919_);
v___x_1922_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1919_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
v___x_1923_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
lean_inc(v___x_1919_);
v___x_1924_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1919_);
lean_ctor_set(v___x_1924_, 1, v___x_1923_);
v___x_1925_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
lean_inc(v___x_1919_);
v___x_1926_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1919_);
lean_ctor_set(v___x_1926_, 1, v___x_1925_);
v___x_1927_ = l_Lean_Syntax_node5(v___x_1919_, v___x_1920_, v___x_1922_, v___x_1528_, v___x_1924_, v___x_1918_, v___x_1926_);
v___x_1928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1927_);
lean_ctor_set(v___x_1928_, 1, v_a_1516_);
return v___x_1928_;
}
else
{
lean_object* v___x_1929_; uint8_t v___x_1930_; 
v___x_1929_ = l_Lean_Syntax_getArg(v___x_1916_, v___x_1521_);
v___x_1930_ = l_Lean_Syntax_matchesNull(v___x_1929_, v___x_1527_);
if (v___x_1930_ == 0)
{
lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
lean_dec(v___x_1916_);
lean_dec(v___x_1797_);
lean_dec(v___x_1678_);
v___x_1931_ = l_Lean_Syntax_getArg(v___x_1522_, v___x_1521_);
lean_dec(v___x_1522_);
v___x_1932_ = l_Lean_SourceInfo_fromRef(v_a_1515_, v___x_1930_);
v___x_1933_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1934_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc(v___x_1932_);
v___x_1935_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1932_);
lean_ctor_set(v___x_1935_, 1, v___x_1934_);
v___x_1936_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
lean_inc(v___x_1932_);
v___x_1937_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1932_);
lean_ctor_set(v___x_1937_, 1, v___x_1936_);
v___x_1938_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
lean_inc(v___x_1932_);
v___x_1939_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1932_);
lean_ctor_set(v___x_1939_, 1, v___x_1938_);
v___x_1940_ = l_Lean_Syntax_node5(v___x_1932_, v___x_1933_, v___x_1935_, v___x_1528_, v___x_1937_, v___x_1931_, v___x_1939_);
v___x_1941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1940_);
lean_ctor_set(v___x_1941_, 1, v_a_1516_);
return v___x_1941_;
}
else
{
lean_object* v___x_1942_; lean_object* v___x_1943_; uint8_t v___x_1944_; 
v___x_1942_ = l_Lean_Syntax_getArg(v___x_1528_, v___x_1639_);
v___x_1943_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__18));
lean_inc(v___x_1942_);
v___x_1944_ = l_Lean_Syntax_isOfKind(v___x_1942_, v___x_1943_);
if (v___x_1944_ == 0)
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
lean_dec(v___x_1942_);
lean_dec(v___x_1916_);
lean_dec(v___x_1797_);
lean_dec(v___x_1678_);
v___x_1945_ = l_Lean_Syntax_getArg(v___x_1522_, v___x_1521_);
lean_dec(v___x_1522_);
v___x_1946_ = l_Lean_SourceInfo_fromRef(v_a_1515_, v___x_1944_);
v___x_1947_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1948_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc(v___x_1946_);
v___x_1949_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1946_);
lean_ctor_set(v___x_1949_, 1, v___x_1948_);
v___x_1950_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
lean_inc(v___x_1946_);
v___x_1951_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1946_);
lean_ctor_set(v___x_1951_, 1, v___x_1950_);
v___x_1952_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
lean_inc(v___x_1946_);
v___x_1953_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1946_);
lean_ctor_set(v___x_1953_, 1, v___x_1952_);
v___x_1954_ = l_Lean_Syntax_node5(v___x_1946_, v___x_1947_, v___x_1949_, v___x_1528_, v___x_1951_, v___x_1945_, v___x_1953_);
v___x_1955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1954_);
lean_ctor_set(v___x_1955_, 1, v_a_1516_);
return v___x_1955_;
}
else
{
lean_object* v___x_1956_; uint8_t v___x_1957_; 
v___x_1956_ = l_Lean_Syntax_getArg(v___x_1942_, v___x_1527_);
lean_dec(v___x_1942_);
v___x_1957_ = l_Lean_Syntax_matchesNull(v___x_1956_, v___x_1527_);
if (v___x_1957_ == 0)
{
lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
lean_dec(v___x_1916_);
lean_dec(v___x_1797_);
lean_dec(v___x_1678_);
v___x_1958_ = l_Lean_Syntax_getArg(v___x_1522_, v___x_1521_);
lean_dec(v___x_1522_);
v___x_1959_ = l_Lean_SourceInfo_fromRef(v_a_1515_, v___x_1957_);
v___x_1960_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1961_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc(v___x_1959_);
v___x_1962_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1959_);
lean_ctor_set(v___x_1962_, 1, v___x_1961_);
v___x_1963_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
lean_inc(v___x_1959_);
v___x_1964_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1959_);
lean_ctor_set(v___x_1964_, 1, v___x_1963_);
v___x_1965_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
lean_inc(v___x_1959_);
v___x_1966_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1959_);
lean_ctor_set(v___x_1966_, 1, v___x_1965_);
v___x_1967_ = l_Lean_Syntax_node5(v___x_1959_, v___x_1960_, v___x_1962_, v___x_1528_, v___x_1964_, v___x_1958_, v___x_1966_);
v___x_1968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1967_);
lean_ctor_set(v___x_1968_, 1, v_a_1516_);
return v___x_1968_;
}
else
{
lean_object* v___x_1969_; uint8_t v___x_1970_; 
v___x_1969_ = l_Lean_Syntax_getArg(v___x_1528_, v___x_1823_);
v___x_1970_ = l_Lean_Syntax_matchesNull(v___x_1969_, v___x_1527_);
if (v___x_1970_ == 0)
{
lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
lean_dec(v___x_1916_);
lean_dec(v___x_1797_);
lean_dec(v___x_1678_);
v___x_1971_ = l_Lean_Syntax_getArg(v___x_1522_, v___x_1521_);
lean_dec(v___x_1522_);
v___x_1972_ = l_Lean_SourceInfo_fromRef(v_a_1515_, v___x_1970_);
v___x_1973_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1974_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc(v___x_1972_);
v___x_1975_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1972_);
lean_ctor_set(v___x_1975_, 1, v___x_1974_);
v___x_1976_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
lean_inc(v___x_1972_);
v___x_1977_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1972_);
lean_ctor_set(v___x_1977_, 1, v___x_1976_);
v___x_1978_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
lean_inc(v___x_1972_);
v___x_1979_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1972_);
lean_ctor_set(v___x_1979_, 1, v___x_1978_);
v___x_1980_ = l_Lean_Syntax_node5(v___x_1972_, v___x_1973_, v___x_1975_, v___x_1528_, v___x_1977_, v___x_1971_, v___x_1979_);
v___x_1981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1980_);
lean_ctor_set(v___x_1981_, 1, v_a_1516_);
return v___x_1981_;
}
else
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; uint8_t v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
lean_dec(v___x_1528_);
v___x_1982_ = l_Lean_Syntax_getArg(v___x_1678_, v___x_1523_);
lean_dec(v___x_1678_);
v___x_1983_ = l_Lean_Syntax_getArg(v___x_1797_, v___x_1523_);
lean_dec(v___x_1797_);
v___x_1984_ = l_Lean_Syntax_getArg(v___x_1916_, v___x_1523_);
lean_dec(v___x_1916_);
v___x_1985_ = l_Lean_Syntax_getArg(v___x_1522_, v___x_1521_);
lean_dec(v___x_1522_);
v___x_1986_ = 0;
v___x_1987_ = l_Lean_SourceInfo_fromRef(v_a_1515_, v___x_1986_);
v___x_1988_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__1));
v___x_1989_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc(v___x_1987_);
v___x_1990_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1987_);
lean_ctor_set(v___x_1990_, 1, v___x_1989_);
v___x_1991_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
lean_inc(v___x_1987_);
v___x_1992_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1987_);
lean_ctor_set(v___x_1992_, 1, v___x_1991_);
v___x_1993_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__20));
v___x_1994_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__21));
lean_inc(v___x_1987_);
v___x_1995_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1987_);
lean_ctor_set(v___x_1995_, 1, v___x_1994_);
v___x_1996_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__14));
lean_inc_ref(v___x_1992_);
lean_inc(v___x_1987_);
v___x_1997_ = l_Lean_Syntax_node3(v___x_1987_, v___x_1996_, v___x_1983_, v___x_1992_, v___x_1984_);
v___x_1998_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__22));
lean_inc(v___x_1987_);
v___x_1999_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1987_);
lean_ctor_set(v___x_1999_, 1, v___x_1998_);
lean_inc(v___x_1987_);
v___x_2000_ = l_Lean_Syntax_node3(v___x_1987_, v___x_1993_, v___x_1995_, v___x_1997_, v___x_1999_);
v___x_2001_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
lean_inc(v___x_1987_);
v___x_2002_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2002_, 0, v___x_1987_);
lean_ctor_set(v___x_2002_, 1, v___x_2001_);
lean_inc_ref(v___x_1992_);
v___x_2003_ = l_Lean_Syntax_node7(v___x_1987_, v___x_1988_, v___x_1990_, v___x_1982_, v___x_1992_, v___x_2000_, v___x_1992_, v___x_1985_, v___x_2002_);
v___x_2004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2003_);
lean_ctor_set(v___x_2004_, 1, v_a_1516_);
return v___x_2004_;
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_unexpandDenote___boxed(lean_object* v_x_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l_Std_Sat_AIG_unexpandDenote(v_x_2005_, v_a_2006_, v_a_2007_);
lean_dec(v_a_2006_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGate___redArg(lean_object* v_aig_2009_, lean_object* v_input_2010_){
_start:
{
lean_object* v_lhs_2011_; lean_object* v_rhs_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2050_; 
v_lhs_2011_ = lean_ctor_get(v_input_2010_, 0);
v_rhs_2012_ = lean_ctor_get(v_input_2010_, 1);
v_isSharedCheck_2050_ = !lean_is_exclusive(v_input_2010_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2014_ = v_input_2010_;
v_isShared_2015_ = v_isSharedCheck_2050_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_rhs_2012_);
lean_inc(v_lhs_2011_);
lean_dec(v_input_2010_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2050_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v_decls_2016_; lean_object* v_cache_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2049_; 
v_decls_2016_ = lean_ctor_get(v_aig_2009_, 0);
v_cache_2017_ = lean_ctor_get(v_aig_2009_, 1);
v_isSharedCheck_2049_ = !lean_is_exclusive(v_aig_2009_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2019_ = v_aig_2009_;
v_isShared_2020_ = v_isSharedCheck_2049_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_cache_2017_);
lean_inc(v_decls_2016_);
lean_dec(v_aig_2009_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2049_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v_gate_2021_; uint8_t v_invert_2022_; lean_object* v_gate_2023_; uint8_t v_invert_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2048_; 
v_gate_2021_ = lean_ctor_get(v_lhs_2011_, 0);
lean_inc(v_gate_2021_);
v_invert_2022_ = lean_ctor_get_uint8(v_lhs_2011_, sizeof(void*)*1);
lean_dec_ref(v_lhs_2011_);
v_gate_2023_ = lean_ctor_get(v_rhs_2012_, 0);
v_invert_2024_ = lean_ctor_get_uint8(v_rhs_2012_, sizeof(void*)*1);
v_isSharedCheck_2048_ = !lean_is_exclusive(v_rhs_2012_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2026_ = v_rhs_2012_;
v_isShared_2027_ = v_isSharedCheck_2048_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_gate_2023_);
lean_dec(v_rhs_2012_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2048_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v_g_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2037_; 
v_g_2028_ = lean_array_get_size(v_decls_2016_);
v___x_2029_ = lean_unsigned_to_nat(2u);
v___x_2030_ = lean_nat_mul(v_gate_2021_, v___x_2029_);
lean_dec(v_gate_2021_);
v___x_2031_ = l_Bool_toNat(v_invert_2022_);
v___x_2032_ = lean_nat_lor(v___x_2030_, v___x_2031_);
lean_dec(v___x_2031_);
lean_dec(v___x_2030_);
v___x_2033_ = lean_nat_mul(v_gate_2023_, v___x_2029_);
lean_dec(v_gate_2023_);
v___x_2034_ = l_Bool_toNat(v_invert_2024_);
v___x_2035_ = lean_nat_lor(v___x_2033_, v___x_2034_);
lean_dec(v___x_2034_);
lean_dec(v___x_2033_);
if (v_isShared_2015_ == 0)
{
lean_ctor_set_tag(v___x_2014_, 2);
lean_ctor_set(v___x_2014_, 1, v___x_2035_);
lean_ctor_set(v___x_2014_, 0, v___x_2032_);
v___x_2037_ = v___x_2014_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_2032_);
lean_ctor_set(v_reuseFailAlloc_2047_, 1, v___x_2035_);
v___x_2037_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
lean_object* v_decls_2038_; lean_object* v___x_2040_; 
v_decls_2038_ = lean_array_push(v_decls_2016_, v___x_2037_);
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 0, v_decls_2038_);
v___x_2040_ = v___x_2019_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_decls_2038_);
lean_ctor_set(v_reuseFailAlloc_2046_, 1, v_cache_2017_);
v___x_2040_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
uint8_t v___x_2041_; lean_object* v___x_2043_; 
v___x_2041_ = 0;
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 0, v_g_2028_);
v___x_2043_ = v___x_2026_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_g_2028_);
v___x_2043_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
lean_object* v___x_2044_; 
lean_ctor_set_uint8(v___x_2043_, sizeof(void*)*1, v___x_2041_);
v___x_2044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2040_);
lean_ctor_set(v___x_2044_, 1, v___x_2043_);
return v___x_2044_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGate(lean_object* v_00_u03b1_2051_, lean_object* v_inst_2052_, lean_object* v_inst_2053_, lean_object* v_aig_2054_, lean_object* v_input_2055_){
_start:
{
lean_object* v___x_2056_; 
v___x_2056_ = l_Std_Sat_AIG_mkGate___redArg(v_aig_2054_, v_input_2055_);
return v___x_2056_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGate___boxed(lean_object* v_00_u03b1_2057_, lean_object* v_inst_2058_, lean_object* v_inst_2059_, lean_object* v_aig_2060_, lean_object* v_input_2061_){
_start:
{
lean_object* v_res_2062_; 
v_res_2062_ = l_Std_Sat_AIG_mkGate(v_00_u03b1_2057_, v_inst_2058_, v_inst_2059_, v_aig_2060_, v_input_2061_);
lean_dec_ref(v_inst_2059_);
lean_dec_ref(v_inst_2058_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtom___redArg(lean_object* v_aig_2063_, lean_object* v_n_2064_){
_start:
{
lean_object* v_decls_2065_; lean_object* v_cache_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2079_; 
v_decls_2065_ = lean_ctor_get(v_aig_2063_, 0);
v_cache_2066_ = lean_ctor_get(v_aig_2063_, 1);
v_isSharedCheck_2079_ = !lean_is_exclusive(v_aig_2063_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2068_ = v_aig_2063_;
v_isShared_2069_ = v_isSharedCheck_2079_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_cache_2066_);
lean_inc(v_decls_2065_);
lean_dec(v_aig_2063_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2079_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v_g_2070_; lean_object* v___x_2071_; lean_object* v_decls_2072_; lean_object* v___x_2074_; 
v_g_2070_ = lean_array_get_size(v_decls_2065_);
v___x_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2071_, 0, v_n_2064_);
v_decls_2072_ = lean_array_push(v_decls_2065_, v___x_2071_);
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 0, v_decls_2072_);
v___x_2074_ = v___x_2068_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_decls_2072_);
lean_ctor_set(v_reuseFailAlloc_2078_, 1, v_cache_2066_);
v___x_2074_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
uint8_t v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2075_ = 0;
v___x_2076_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2076_, 0, v_g_2070_);
lean_ctor_set_uint8(v___x_2076_, sizeof(void*)*1, v___x_2075_);
v___x_2077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2074_);
lean_ctor_set(v___x_2077_, 1, v___x_2076_);
return v___x_2077_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtom(lean_object* v_00_u03b1_2080_, lean_object* v_inst_2081_, lean_object* v_inst_2082_, lean_object* v_aig_2083_, lean_object* v_n_2084_){
_start:
{
lean_object* v___x_2085_; 
v___x_2085_ = l_Std_Sat_AIG_mkAtom___redArg(v_aig_2083_, v_n_2084_);
return v___x_2085_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtom___boxed(lean_object* v_00_u03b1_2086_, lean_object* v_inst_2087_, lean_object* v_inst_2088_, lean_object* v_aig_2089_, lean_object* v_n_2090_){
_start:
{
lean_object* v_res_2091_; 
v_res_2091_ = l_Std_Sat_AIG_mkAtom(v_00_u03b1_2086_, v_inst_2087_, v_inst_2088_, v_aig_2089_, v_n_2090_);
lean_dec_ref(v_inst_2088_);
lean_dec_ref(v_inst_2087_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConst___redArg(lean_object* v_aig_2092_, uint8_t v_val_2093_){
_start:
{
lean_object* v_decls_2094_; lean_object* v_cache_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2107_; 
v_decls_2094_ = lean_ctor_get(v_aig_2092_, 0);
v_cache_2095_ = lean_ctor_get(v_aig_2092_, 1);
v_isSharedCheck_2107_ = !lean_is_exclusive(v_aig_2092_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2097_ = v_aig_2092_;
v_isShared_2098_ = v_isSharedCheck_2107_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_cache_2095_);
lean_inc(v_decls_2094_);
lean_dec(v_aig_2092_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2107_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v_g_2099_; lean_object* v___x_2100_; lean_object* v_decls_2101_; lean_object* v___x_2103_; 
v_g_2099_ = lean_array_get_size(v_decls_2094_);
v___x_2100_ = lean_box(0);
v_decls_2101_ = lean_array_push(v_decls_2094_, v___x_2100_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 0, v_decls_2101_);
v___x_2103_ = v___x_2097_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_decls_2101_);
lean_ctor_set(v_reuseFailAlloc_2106_, 1, v_cache_2095_);
v___x_2103_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2104_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2104_, 0, v_g_2099_);
lean_ctor_set_uint8(v___x_2104_, sizeof(void*)*1, v_val_2093_);
v___x_2105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2103_);
lean_ctor_set(v___x_2105_, 1, v___x_2104_);
return v___x_2105_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConst___redArg___boxed(lean_object* v_aig_2108_, lean_object* v_val_2109_){
_start:
{
uint8_t v_val_boxed_2110_; lean_object* v_res_2111_; 
v_val_boxed_2110_ = lean_unbox(v_val_2109_);
v_res_2111_ = l_Std_Sat_AIG_mkConst___redArg(v_aig_2108_, v_val_boxed_2110_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConst(lean_object* v_00_u03b1_2112_, lean_object* v_inst_2113_, lean_object* v_inst_2114_, lean_object* v_aig_2115_, uint8_t v_val_2116_){
_start:
{
lean_object* v___x_2117_; 
v___x_2117_ = l_Std_Sat_AIG_mkConst___redArg(v_aig_2115_, v_val_2116_);
return v___x_2117_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConst___boxed(lean_object* v_00_u03b1_2118_, lean_object* v_inst_2119_, lean_object* v_inst_2120_, lean_object* v_aig_2121_, lean_object* v_val_2122_){
_start:
{
uint8_t v_val_boxed_2123_; lean_object* v_res_2124_; 
v_val_boxed_2123_ = lean_unbox(v_val_2122_);
v_res_2124_ = l_Std_Sat_AIG_mkConst(v_00_u03b1_2118_, v_inst_2119_, v_inst_2120_, v_aig_2121_, v_val_boxed_2123_);
lean_dec_ref(v_inst_2120_);
lean_dec_ref(v_inst_2119_);
return v_res_2124_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_isConstant___redArg(lean_object* v_aig_2125_, lean_object* v_ref_2126_, uint8_t v_b_2127_){
_start:
{
lean_object* v_gate_2128_; uint8_t v_invert_2129_; lean_object* v_decls_2130_; lean_object* v_decl_2131_; uint8_t v___y_2133_; 
v_gate_2128_ = lean_ctor_get(v_ref_2126_, 0);
v_invert_2129_ = lean_ctor_get_uint8(v_ref_2126_, sizeof(void*)*1);
v_decls_2130_ = lean_ctor_get(v_aig_2125_, 0);
v_decl_2131_ = lean_array_fget_borrowed(v_decls_2130_, v_gate_2128_);
if (v_invert_2129_ == 0)
{
if (v_b_2127_ == 0)
{
uint8_t v___x_2135_; 
v___x_2135_ = 1;
v___y_2133_ = v___x_2135_;
goto v___jp_2132_;
}
else
{
v___y_2133_ = v_invert_2129_;
goto v___jp_2132_;
}
}
else
{
v___y_2133_ = v_b_2127_;
goto v___jp_2132_;
}
v___jp_2132_:
{
if (lean_obj_tag(v_decl_2131_) == 0)
{
return v___y_2133_;
}
else
{
uint8_t v___x_2134_; 
v___x_2134_ = 0;
return v___x_2134_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_isConstant___redArg___boxed(lean_object* v_aig_2136_, lean_object* v_ref_2137_, lean_object* v_b_2138_){
_start:
{
uint8_t v_b_boxed_2139_; uint8_t v_res_2140_; lean_object* v_r_2141_; 
v_b_boxed_2139_ = lean_unbox(v_b_2138_);
v_res_2140_ = l_Std_Sat_AIG_isConstant___redArg(v_aig_2136_, v_ref_2137_, v_b_boxed_2139_);
lean_dec_ref(v_ref_2137_);
lean_dec_ref(v_aig_2136_);
v_r_2141_ = lean_box(v_res_2140_);
return v_r_2141_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_isConstant(lean_object* v_00_u03b1_2142_, lean_object* v_inst_2143_, lean_object* v_inst_2144_, lean_object* v_aig_2145_, lean_object* v_ref_2146_, uint8_t v_b_2147_){
_start:
{
uint8_t v___x_2148_; 
v___x_2148_ = l_Std_Sat_AIG_isConstant___redArg(v_aig_2145_, v_ref_2146_, v_b_2147_);
return v___x_2148_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_isConstant___boxed(lean_object* v_00_u03b1_2149_, lean_object* v_inst_2150_, lean_object* v_inst_2151_, lean_object* v_aig_2152_, lean_object* v_ref_2153_, lean_object* v_b_2154_){
_start:
{
uint8_t v_b_boxed_2155_; uint8_t v_res_2156_; lean_object* v_r_2157_; 
v_b_boxed_2155_ = lean_unbox(v_b_2154_);
v_res_2156_ = l_Std_Sat_AIG_isConstant(v_00_u03b1_2149_, v_inst_2150_, v_inst_2151_, v_aig_2152_, v_ref_2153_, v_b_boxed_2155_);
lean_dec_ref(v_ref_2153_);
lean_dec_ref(v_aig_2152_);
lean_dec_ref(v_inst_2151_);
lean_dec_ref(v_inst_2150_);
v_r_2157_ = lean_box(v_res_2156_);
return v_r_2157_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___redArg(lean_object* v_aig_2158_, lean_object* v_ref_2159_){
_start:
{
lean_object* v_gate_2160_; uint8_t v_invert_2161_; lean_object* v_decls_2162_; lean_object* v_decl_2163_; 
v_gate_2160_ = lean_ctor_get(v_ref_2159_, 0);
v_invert_2161_ = lean_ctor_get_uint8(v_ref_2159_, sizeof(void*)*1);
v_decls_2162_ = lean_ctor_get(v_aig_2158_, 0);
v_decl_2163_ = lean_array_fget_borrowed(v_decls_2162_, v_gate_2160_);
if (lean_obj_tag(v_decl_2163_) == 0)
{
lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2164_ = lean_box(v_invert_2161_);
v___x_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2164_);
return v___x_2165_;
}
else
{
lean_object* v___x_2166_; 
v___x_2166_ = lean_box(0);
return v___x_2166_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___redArg___boxed(lean_object* v_aig_2167_, lean_object* v_ref_2168_){
_start:
{
lean_object* v_res_2169_; 
v_res_2169_ = l_Std_Sat_AIG_getConstant___redArg(v_aig_2167_, v_ref_2168_);
lean_dec_ref(v_ref_2168_);
lean_dec_ref(v_aig_2167_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant(lean_object* v_00_u03b1_2170_, lean_object* v_inst_2171_, lean_object* v_inst_2172_, lean_object* v_aig_2173_, lean_object* v_ref_2174_){
_start:
{
lean_object* v___x_2175_; 
v___x_2175_ = l_Std_Sat_AIG_getConstant___redArg(v_aig_2173_, v_ref_2174_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___boxed(lean_object* v_00_u03b1_2176_, lean_object* v_inst_2177_, lean_object* v_inst_2178_, lean_object* v_aig_2179_, lean_object* v_ref_2180_){
_start:
{
lean_object* v_res_2181_; 
v_res_2181_ = l_Std_Sat_AIG_getConstant(v_00_u03b1_2176_, v_inst_2177_, v_inst_2178_, v_aig_2179_, v_ref_2180_);
lean_dec_ref(v_ref_2180_);
lean_dec_ref(v_aig_2179_);
lean_dec_ref(v_inst_2178_);
lean_dec_ref(v_inst_2177_);
return v_res_2181_;
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
