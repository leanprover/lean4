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
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_UInt64_ofNat___boxed(lean_object*);
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
if (lean_obj_tag(v_x_296_) == 1)
{
lean_object* v_idx_299_; lean_object* v_idx_300_; lean_object* v___x_301_; uint8_t v___x_302_; 
v_idx_299_ = lean_ctor_get(v_x_295_, 0);
lean_inc(v_idx_299_);
lean_dec_ref_known(v_x_295_, 1);
v_idx_300_ = lean_ctor_get(v_x_296_, 0);
lean_inc(v_idx_300_);
lean_dec_ref_known(v_x_296_, 1);
v___x_301_ = lean_apply_2(v_inst_294_, v_idx_299_, v_idx_300_);
v___x_302_ = lean_unbox(v___x_301_);
return v___x_302_;
}
else
{
uint8_t v___x_303_; 
lean_dec_ref_known(v_x_295_, 1);
lean_dec(v_x_296_);
lean_dec_ref(v_inst_294_);
v___x_303_ = 0;
return v___x_303_;
}
}
default: 
{
lean_dec_ref(v_inst_294_);
if (lean_obj_tag(v_x_296_) == 2)
{
lean_object* v_l_304_; lean_object* v_r_305_; lean_object* v_l_306_; lean_object* v_r_307_; uint8_t v___x_308_; 
v_l_304_ = lean_ctor_get(v_x_295_, 0);
lean_inc(v_l_304_);
v_r_305_ = lean_ctor_get(v_x_295_, 1);
lean_inc(v_r_305_);
lean_dec_ref_known(v_x_295_, 2);
v_l_306_ = lean_ctor_get(v_x_296_, 0);
lean_inc(v_l_306_);
v_r_307_ = lean_ctor_get(v_x_296_, 1);
lean_inc(v_r_307_);
lean_dec_ref_known(v_x_296_, 2);
v___x_308_ = lean_nat_dec_eq(v_l_304_, v_l_306_);
lean_dec(v_l_306_);
lean_dec(v_l_304_);
if (v___x_308_ == 0)
{
lean_dec(v_r_307_);
lean_dec(v_r_305_);
return v___x_308_;
}
else
{
uint8_t v___x_309_; 
v___x_309_ = lean_nat_dec_eq(v_r_305_, v_r_307_);
lean_dec(v_r_307_);
lean_dec(v_r_305_);
return v___x_309_;
}
}
else
{
uint8_t v___x_310_; 
lean_dec_ref_known(v_x_295_, 2);
lean_dec(v_x_296_);
v___x_310_ = 0;
return v___x_310_;
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
lean_object* v_gate_533_; uint8_t v_invert_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_546_; 
v_gate_533_ = lean_ctor_get(v_ref_531_, 0);
v_invert_534_ = lean_ctor_get_uint8(v_ref_531_, sizeof(void*)*1);
v_isSharedCheck_546_ = !lean_is_exclusive(v_ref_531_);
if (v_isSharedCheck_546_ == 0)
{
v___x_536_ = v_ref_531_;
v_isShared_537_ = v_isSharedCheck_546_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_gate_533_);
lean_dec(v_ref_531_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_546_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
if (v_invert_534_ == 0)
{
if (v_inv_532_ == 0)
{
lean_del_object(v___x_536_);
goto v___jp_543_;
}
else
{
goto v___jp_538_;
}
}
else
{
if (v_inv_532_ == 0)
{
goto v___jp_538_;
}
else
{
lean_del_object(v___x_536_);
goto v___jp_543_;
}
}
v___jp_538_:
{
uint8_t v___x_539_; lean_object* v___x_541_; 
v___x_539_ = 1;
if (v_isShared_537_ == 0)
{
v___x_541_ = v___x_536_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_gate_533_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_ctor_set_uint8(v___x_541_, sizeof(void*)*1, v___x_539_);
return v___x_541_;
}
}
v___jp_543_:
{
uint8_t v___x_544_; lean_object* v___x_545_; 
v___x_544_ = 0;
v___x_545_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_545_, 0, v_gate_533_);
lean_ctor_set_uint8(v___x_545_, sizeof(void*)*1, v___x_544_);
return v___x_545_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_flip___redArg___boxed(lean_object* v_ref_547_, lean_object* v_inv_548_){
_start:
{
uint8_t v_inv_boxed_549_; lean_object* v_res_550_; 
v_inv_boxed_549_ = lean_unbox(v_inv_548_);
v_res_550_ = l_Std_Sat_AIG_Ref_flip___redArg(v_ref_547_, v_inv_boxed_549_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_flip(lean_object* v_00_u03b1_551_, lean_object* v_inst_552_, lean_object* v_inst_553_, lean_object* v_aig_554_, lean_object* v_ref_555_, uint8_t v_inv_556_){
_start:
{
lean_object* v_gate_557_; uint8_t v_invert_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_570_; 
v_gate_557_ = lean_ctor_get(v_ref_555_, 0);
v_invert_558_ = lean_ctor_get_uint8(v_ref_555_, sizeof(void*)*1);
v_isSharedCheck_570_ = !lean_is_exclusive(v_ref_555_);
if (v_isSharedCheck_570_ == 0)
{
v___x_560_ = v_ref_555_;
v_isShared_561_ = v_isSharedCheck_570_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_gate_557_);
lean_dec(v_ref_555_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_570_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
if (v_invert_558_ == 0)
{
if (v_inv_556_ == 0)
{
lean_del_object(v___x_560_);
goto v___jp_567_;
}
else
{
goto v___jp_562_;
}
}
else
{
if (v_inv_556_ == 0)
{
goto v___jp_562_;
}
else
{
lean_del_object(v___x_560_);
goto v___jp_567_;
}
}
v___jp_562_:
{
uint8_t v___x_563_; lean_object* v___x_565_; 
v___x_563_ = 1;
if (v_isShared_561_ == 0)
{
v___x_565_ = v___x_560_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_gate_557_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
lean_ctor_set_uint8(v___x_565_, sizeof(void*)*1, v___x_563_);
return v___x_565_;
}
}
v___jp_567_:
{
uint8_t v___x_568_; lean_object* v___x_569_; 
v___x_568_ = 0;
v___x_569_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_569_, 0, v_gate_557_);
lean_ctor_set_uint8(v___x_569_, sizeof(void*)*1, v___x_568_);
return v___x_569_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_flip___boxed(lean_object* v_00_u03b1_571_, lean_object* v_inst_572_, lean_object* v_inst_573_, lean_object* v_aig_574_, lean_object* v_ref_575_, lean_object* v_inv_576_){
_start:
{
uint8_t v_inv_boxed_577_; lean_object* v_res_578_; 
v_inv_boxed_577_ = lean_unbox(v_inv_576_);
v_res_578_ = l_Std_Sat_AIG_Ref_flip(v_00_u03b1_571_, v_inst_572_, v_inst_573_, v_aig_574_, v_ref_575_, v_inv_boxed_577_);
lean_dec_ref(v_aig_574_);
lean_dec_ref(v_inst_573_);
lean_dec_ref(v_inst_572_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_not___redArg(lean_object* v_ref_579_){
_start:
{
uint8_t v_invert_580_; 
v_invert_580_ = lean_ctor_get_uint8(v_ref_579_, sizeof(void*)*1);
if (v_invert_580_ == 0)
{
lean_object* v_gate_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_589_; 
v_gate_581_ = lean_ctor_get(v_ref_579_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v_ref_579_);
if (v_isSharedCheck_589_ == 0)
{
v___x_583_ = v_ref_579_;
v_isShared_584_ = v_isSharedCheck_589_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_gate_581_);
lean_dec(v_ref_579_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_589_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
uint8_t v___x_585_; lean_object* v___x_587_; 
v___x_585_ = 1;
if (v_isShared_584_ == 0)
{
v___x_587_ = v___x_583_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_gate_581_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
lean_ctor_set_uint8(v___x_587_, sizeof(void*)*1, v___x_585_);
return v___x_587_;
}
}
}
else
{
lean_object* v_gate_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_598_; 
v_gate_590_ = lean_ctor_get(v_ref_579_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v_ref_579_);
if (v_isSharedCheck_598_ == 0)
{
v___x_592_ = v_ref_579_;
v_isShared_593_ = v_isSharedCheck_598_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_gate_590_);
lean_dec(v_ref_579_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_598_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
uint8_t v___x_594_; lean_object* v___x_596_; 
v___x_594_ = 0;
if (v_isShared_593_ == 0)
{
v___x_596_ = v___x_592_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_gate_590_);
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
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_not(lean_object* v_00_u03b1_599_, lean_object* v_inst_600_, lean_object* v_inst_601_, lean_object* v_aig_602_, lean_object* v_ref_603_){
_start:
{
uint8_t v_invert_604_; 
v_invert_604_ = lean_ctor_get_uint8(v_ref_603_, sizeof(void*)*1);
if (v_invert_604_ == 0)
{
lean_object* v_gate_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_613_; 
v_gate_605_ = lean_ctor_get(v_ref_603_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v_ref_603_);
if (v_isSharedCheck_613_ == 0)
{
v___x_607_ = v_ref_603_;
v_isShared_608_ = v_isSharedCheck_613_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_gate_605_);
lean_dec(v_ref_603_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_613_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
uint8_t v___x_609_; lean_object* v___x_611_; 
v___x_609_ = 1;
if (v_isShared_608_ == 0)
{
v___x_611_ = v___x_607_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_gate_605_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_ctor_set_uint8(v___x_611_, sizeof(void*)*1, v___x_609_);
return v___x_611_;
}
}
}
else
{
lean_object* v_gate_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_622_; 
v_gate_614_ = lean_ctor_get(v_ref_603_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v_ref_603_);
if (v_isSharedCheck_622_ == 0)
{
v___x_616_ = v_ref_603_;
v_isShared_617_ = v_isSharedCheck_622_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_gate_614_);
lean_dec(v_ref_603_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_622_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
uint8_t v___x_618_; lean_object* v___x_620_; 
v___x_618_ = 0;
if (v_isShared_617_ == 0)
{
v___x_620_ = v___x_616_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_gate_614_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
lean_ctor_set_uint8(v___x_620_, sizeof(void*)*1, v___x_618_);
return v___x_620_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_not___boxed(lean_object* v_00_u03b1_623_, lean_object* v_inst_624_, lean_object* v_inst_625_, lean_object* v_aig_626_, lean_object* v_ref_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Std_Sat_AIG_Ref_not(v_00_u03b1_623_, v_inst_624_, v_inst_625_, v_aig_626_, v_ref_627_);
lean_dec_ref(v_aig_626_);
lean_dec_ref(v_inst_625_);
lean_dec_ref(v_inst_624_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_cast___redArg(lean_object* v_input_629_){
_start:
{
lean_object* v_lhs_630_; lean_object* v_rhs_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_656_; 
v_lhs_630_ = lean_ctor_get(v_input_629_, 0);
v_rhs_631_ = lean_ctor_get(v_input_629_, 1);
v_isSharedCheck_656_ = !lean_is_exclusive(v_input_629_);
if (v_isSharedCheck_656_ == 0)
{
v___x_633_ = v_input_629_;
v_isShared_634_ = v_isSharedCheck_656_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_rhs_631_);
lean_inc(v_lhs_630_);
lean_dec(v_input_629_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_656_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v_gate_635_; uint8_t v_invert_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_655_; 
v_gate_635_ = lean_ctor_get(v_lhs_630_, 0);
v_invert_636_ = lean_ctor_get_uint8(v_lhs_630_, sizeof(void*)*1);
v_isSharedCheck_655_ = !lean_is_exclusive(v_lhs_630_);
if (v_isSharedCheck_655_ == 0)
{
v___x_638_ = v_lhs_630_;
v_isShared_639_ = v_isSharedCheck_655_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_gate_635_);
lean_dec(v_lhs_630_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_655_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v_gate_640_; uint8_t v_invert_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_654_; 
v_gate_640_ = lean_ctor_get(v_rhs_631_, 0);
v_invert_641_ = lean_ctor_get_uint8(v_rhs_631_, sizeof(void*)*1);
v_isSharedCheck_654_ = !lean_is_exclusive(v_rhs_631_);
if (v_isSharedCheck_654_ == 0)
{
v___x_643_ = v_rhs_631_;
v_isShared_644_ = v_isSharedCheck_654_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_gate_640_);
lean_dec(v_rhs_631_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_654_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_646_; 
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 0, v_gate_635_);
v___x_646_ = v___x_643_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_gate_635_);
v___x_646_ = v_reuseFailAlloc_653_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
lean_object* v___x_648_; 
lean_ctor_set_uint8(v___x_646_, sizeof(void*)*1, v_invert_636_);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 0, v_gate_640_);
v___x_648_ = v___x_638_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_gate_640_);
v___x_648_ = v_reuseFailAlloc_652_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
lean_object* v___x_650_; 
lean_ctor_set_uint8(v___x_648_, sizeof(void*)*1, v_invert_641_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 1, v___x_648_);
lean_ctor_set(v___x_633_, 0, v___x_646_);
v___x_650_ = v___x_633_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_646_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v___x_648_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_cast(lean_object* v_00_u03b1_657_, lean_object* v_inst_658_, lean_object* v_inst_659_, lean_object* v_aig1_660_, lean_object* v_aig2_661_, lean_object* v_input_662_, lean_object* v_h_663_){
_start:
{
lean_object* v_lhs_664_; lean_object* v_rhs_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_690_; 
v_lhs_664_ = lean_ctor_get(v_input_662_, 0);
v_rhs_665_ = lean_ctor_get(v_input_662_, 1);
v_isSharedCheck_690_ = !lean_is_exclusive(v_input_662_);
if (v_isSharedCheck_690_ == 0)
{
v___x_667_ = v_input_662_;
v_isShared_668_ = v_isSharedCheck_690_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_rhs_665_);
lean_inc(v_lhs_664_);
lean_dec(v_input_662_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_690_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v_gate_669_; uint8_t v_invert_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_689_; 
v_gate_669_ = lean_ctor_get(v_lhs_664_, 0);
v_invert_670_ = lean_ctor_get_uint8(v_lhs_664_, sizeof(void*)*1);
v_isSharedCheck_689_ = !lean_is_exclusive(v_lhs_664_);
if (v_isSharedCheck_689_ == 0)
{
v___x_672_ = v_lhs_664_;
v_isShared_673_ = v_isSharedCheck_689_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_gate_669_);
lean_dec(v_lhs_664_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_689_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v_gate_674_; uint8_t v_invert_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_688_; 
v_gate_674_ = lean_ctor_get(v_rhs_665_, 0);
v_invert_675_ = lean_ctor_get_uint8(v_rhs_665_, sizeof(void*)*1);
v_isSharedCheck_688_ = !lean_is_exclusive(v_rhs_665_);
if (v_isSharedCheck_688_ == 0)
{
v___x_677_ = v_rhs_665_;
v_isShared_678_ = v_isSharedCheck_688_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_gate_674_);
lean_dec(v_rhs_665_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_688_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_680_; 
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 0, v_gate_669_);
v___x_680_ = v___x_677_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_gate_669_);
v___x_680_ = v_reuseFailAlloc_687_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
lean_object* v___x_682_; 
lean_ctor_set_uint8(v___x_680_, sizeof(void*)*1, v_invert_670_);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 0, v_gate_674_);
v___x_682_ = v___x_672_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_gate_674_);
v___x_682_ = v_reuseFailAlloc_686_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
lean_object* v___x_684_; 
lean_ctor_set_uint8(v___x_682_, sizeof(void*)*1, v_invert_675_);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 1, v___x_682_);
lean_ctor_set(v___x_667_, 0, v___x_680_);
v___x_684_ = v___x_667_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_680_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v___x_682_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_cast___boxed(lean_object* v_00_u03b1_691_, lean_object* v_inst_692_, lean_object* v_inst_693_, lean_object* v_aig1_694_, lean_object* v_aig2_695_, lean_object* v_input_696_, lean_object* v_h_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Std_Sat_AIG_BinaryInput_cast(v_00_u03b1_691_, v_inst_692_, v_inst_693_, v_aig1_694_, v_aig2_695_, v_input_696_, v_h_697_);
lean_dec_ref(v_aig2_695_);
lean_dec_ref(v_aig1_694_);
lean_dec_ref(v_inst_693_);
lean_dec_ref(v_inst_692_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_invert___redArg(lean_object* v_input_699_, uint8_t v_linv_700_, uint8_t v_rinv_701_){
_start:
{
lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v_lhs_714_; lean_object* v_rhs_715_; lean_object* v___y_717_; lean_object* v_gate_723_; uint8_t v_invert_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_736_; 
v_lhs_714_ = lean_ctor_get(v_input_699_, 0);
lean_inc_ref(v_lhs_714_);
v_rhs_715_ = lean_ctor_get(v_input_699_, 1);
lean_inc_ref(v_rhs_715_);
lean_dec_ref(v_input_699_);
v_gate_723_ = lean_ctor_get(v_lhs_714_, 0);
v_invert_724_ = lean_ctor_get_uint8(v_lhs_714_, sizeof(void*)*1);
v_isSharedCheck_736_ = !lean_is_exclusive(v_lhs_714_);
if (v_isSharedCheck_736_ == 0)
{
v___x_726_ = v_lhs_714_;
v_isShared_727_ = v_isSharedCheck_736_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_gate_723_);
lean_dec(v_lhs_714_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_736_;
goto v_resetjp_725_;
}
v___jp_702_:
{
uint8_t v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_705_ = 0;
v___x_706_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_706_, 0, v___y_703_);
lean_ctor_set_uint8(v___x_706_, sizeof(void*)*1, v___x_705_);
v___x_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_707_, 0, v___y_704_);
lean_ctor_set(v___x_707_, 1, v___x_706_);
return v___x_707_;
}
v___jp_708_:
{
uint8_t v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_711_ = 1;
v___x_712_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_712_, 0, v___y_709_);
lean_ctor_set_uint8(v___x_712_, sizeof(void*)*1, v___x_711_);
v___x_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_713_, 0, v___y_710_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
return v___x_713_;
}
v___jp_716_:
{
uint8_t v_invert_718_; 
v_invert_718_ = lean_ctor_get_uint8(v_rhs_715_, sizeof(void*)*1);
if (v_invert_718_ == 0)
{
if (v_rinv_701_ == 0)
{
lean_object* v_gate_719_; 
v_gate_719_ = lean_ctor_get(v_rhs_715_, 0);
lean_inc(v_gate_719_);
lean_dec_ref(v_rhs_715_);
v___y_703_ = v_gate_719_;
v___y_704_ = v___y_717_;
goto v___jp_702_;
}
else
{
lean_object* v_gate_720_; 
v_gate_720_ = lean_ctor_get(v_rhs_715_, 0);
lean_inc(v_gate_720_);
lean_dec_ref(v_rhs_715_);
v___y_709_ = v_gate_720_;
v___y_710_ = v___y_717_;
goto v___jp_708_;
}
}
else
{
if (v_rinv_701_ == 0)
{
lean_object* v_gate_721_; 
v_gate_721_ = lean_ctor_get(v_rhs_715_, 0);
lean_inc(v_gate_721_);
lean_dec_ref(v_rhs_715_);
v___y_709_ = v_gate_721_;
v___y_710_ = v___y_717_;
goto v___jp_708_;
}
else
{
lean_object* v_gate_722_; 
v_gate_722_ = lean_ctor_get(v_rhs_715_, 0);
lean_inc(v_gate_722_);
lean_dec_ref(v_rhs_715_);
v___y_703_ = v_gate_722_;
v___y_704_ = v___y_717_;
goto v___jp_702_;
}
}
}
v_resetjp_725_:
{
if (v_invert_724_ == 0)
{
if (v_linv_700_ == 0)
{
lean_del_object(v___x_726_);
goto v___jp_733_;
}
else
{
goto v___jp_728_;
}
}
else
{
if (v_linv_700_ == 0)
{
goto v___jp_728_;
}
else
{
lean_del_object(v___x_726_);
goto v___jp_733_;
}
}
v___jp_728_:
{
uint8_t v___x_729_; lean_object* v___x_731_; 
v___x_729_ = 1;
if (v_isShared_727_ == 0)
{
v___x_731_ = v___x_726_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_gate_723_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
lean_ctor_set_uint8(v___x_731_, sizeof(void*)*1, v___x_729_);
v___y_717_ = v___x_731_;
goto v___jp_716_;
}
}
v___jp_733_:
{
uint8_t v___x_734_; lean_object* v___x_735_; 
v___x_734_ = 0;
v___x_735_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_735_, 0, v_gate_723_);
lean_ctor_set_uint8(v___x_735_, sizeof(void*)*1, v___x_734_);
v___y_717_ = v___x_735_;
goto v___jp_716_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_invert___redArg___boxed(lean_object* v_input_737_, lean_object* v_linv_738_, lean_object* v_rinv_739_){
_start:
{
uint8_t v_linv_boxed_740_; uint8_t v_rinv_boxed_741_; lean_object* v_res_742_; 
v_linv_boxed_740_ = lean_unbox(v_linv_738_);
v_rinv_boxed_741_ = lean_unbox(v_rinv_739_);
v_res_742_ = l_Std_Sat_AIG_BinaryInput_invert___redArg(v_input_737_, v_linv_boxed_740_, v_rinv_boxed_741_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_invert(lean_object* v_00_u03b1_743_, lean_object* v_inst_744_, lean_object* v_inst_745_, lean_object* v_aig_746_, lean_object* v_input_747_, uint8_t v_linv_748_, uint8_t v_rinv_749_){
_start:
{
lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v_lhs_762_; lean_object* v_rhs_763_; lean_object* v___y_765_; lean_object* v_gate_771_; uint8_t v_invert_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_784_; 
v_lhs_762_ = lean_ctor_get(v_input_747_, 0);
lean_inc_ref(v_lhs_762_);
v_rhs_763_ = lean_ctor_get(v_input_747_, 1);
lean_inc_ref(v_rhs_763_);
lean_dec_ref(v_input_747_);
v_gate_771_ = lean_ctor_get(v_lhs_762_, 0);
v_invert_772_ = lean_ctor_get_uint8(v_lhs_762_, sizeof(void*)*1);
v_isSharedCheck_784_ = !lean_is_exclusive(v_lhs_762_);
if (v_isSharedCheck_784_ == 0)
{
v___x_774_ = v_lhs_762_;
v_isShared_775_ = v_isSharedCheck_784_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_gate_771_);
lean_dec(v_lhs_762_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_784_;
goto v_resetjp_773_;
}
v___jp_750_:
{
uint8_t v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_753_ = 0;
v___x_754_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_754_, 0, v___y_751_);
lean_ctor_set_uint8(v___x_754_, sizeof(void*)*1, v___x_753_);
v___x_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_755_, 0, v___y_752_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
return v___x_755_;
}
v___jp_756_:
{
uint8_t v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_759_ = 1;
v___x_760_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_760_, 0, v___y_757_);
lean_ctor_set_uint8(v___x_760_, sizeof(void*)*1, v___x_759_);
v___x_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_761_, 0, v___y_758_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
return v___x_761_;
}
v___jp_764_:
{
uint8_t v_invert_766_; 
v_invert_766_ = lean_ctor_get_uint8(v_rhs_763_, sizeof(void*)*1);
if (v_invert_766_ == 0)
{
if (v_rinv_749_ == 0)
{
lean_object* v_gate_767_; 
v_gate_767_ = lean_ctor_get(v_rhs_763_, 0);
lean_inc(v_gate_767_);
lean_dec_ref(v_rhs_763_);
v___y_751_ = v_gate_767_;
v___y_752_ = v___y_765_;
goto v___jp_750_;
}
else
{
lean_object* v_gate_768_; 
v_gate_768_ = lean_ctor_get(v_rhs_763_, 0);
lean_inc(v_gate_768_);
lean_dec_ref(v_rhs_763_);
v___y_757_ = v_gate_768_;
v___y_758_ = v___y_765_;
goto v___jp_756_;
}
}
else
{
if (v_rinv_749_ == 0)
{
lean_object* v_gate_769_; 
v_gate_769_ = lean_ctor_get(v_rhs_763_, 0);
lean_inc(v_gate_769_);
lean_dec_ref(v_rhs_763_);
v___y_757_ = v_gate_769_;
v___y_758_ = v___y_765_;
goto v___jp_756_;
}
else
{
lean_object* v_gate_770_; 
v_gate_770_ = lean_ctor_get(v_rhs_763_, 0);
lean_inc(v_gate_770_);
lean_dec_ref(v_rhs_763_);
v___y_751_ = v_gate_770_;
v___y_752_ = v___y_765_;
goto v___jp_750_;
}
}
}
v_resetjp_773_:
{
if (v_invert_772_ == 0)
{
if (v_linv_748_ == 0)
{
lean_del_object(v___x_774_);
goto v___jp_781_;
}
else
{
goto v___jp_776_;
}
}
else
{
if (v_linv_748_ == 0)
{
goto v___jp_776_;
}
else
{
lean_del_object(v___x_774_);
goto v___jp_781_;
}
}
v___jp_776_:
{
uint8_t v___x_777_; lean_object* v___x_779_; 
v___x_777_ = 1;
if (v_isShared_775_ == 0)
{
v___x_779_ = v___x_774_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_gate_771_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
lean_ctor_set_uint8(v___x_779_, sizeof(void*)*1, v___x_777_);
v___y_765_ = v___x_779_;
goto v___jp_764_;
}
}
v___jp_781_:
{
uint8_t v___x_782_; lean_object* v___x_783_; 
v___x_782_ = 0;
v___x_783_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_783_, 0, v_gate_771_);
lean_ctor_set_uint8(v___x_783_, sizeof(void*)*1, v___x_782_);
v___y_765_ = v___x_783_;
goto v___jp_764_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_invert___boxed(lean_object* v_00_u03b1_785_, lean_object* v_inst_786_, lean_object* v_inst_787_, lean_object* v_aig_788_, lean_object* v_input_789_, lean_object* v_linv_790_, lean_object* v_rinv_791_){
_start:
{
uint8_t v_linv_boxed_792_; uint8_t v_rinv_boxed_793_; lean_object* v_res_794_; 
v_linv_boxed_792_ = lean_unbox(v_linv_790_);
v_rinv_boxed_793_ = lean_unbox(v_rinv_791_);
v_res_794_ = l_Std_Sat_AIG_BinaryInput_invert(v_00_u03b1_785_, v_inst_786_, v_inst_787_, v_aig_788_, v_input_789_, v_linv_boxed_792_, v_rinv_boxed_793_);
lean_dec_ref(v_aig_788_);
lean_dec_ref(v_inst_787_);
lean_dec_ref(v_inst_786_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_TernaryInput_cast___redArg(lean_object* v_input_795_){
_start:
{
lean_object* v_discr_796_; lean_object* v_lhs_797_; lean_object* v_rhs_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_832_; 
v_discr_796_ = lean_ctor_get(v_input_795_, 0);
v_lhs_797_ = lean_ctor_get(v_input_795_, 1);
v_rhs_798_ = lean_ctor_get(v_input_795_, 2);
v_isSharedCheck_832_ = !lean_is_exclusive(v_input_795_);
if (v_isSharedCheck_832_ == 0)
{
v___x_800_ = v_input_795_;
v_isShared_801_ = v_isSharedCheck_832_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_rhs_798_);
lean_inc(v_lhs_797_);
lean_inc(v_discr_796_);
lean_dec(v_input_795_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_832_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v_gate_802_; uint8_t v_invert_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_831_; 
v_gate_802_ = lean_ctor_get(v_discr_796_, 0);
v_invert_803_ = lean_ctor_get_uint8(v_discr_796_, sizeof(void*)*1);
v_isSharedCheck_831_ = !lean_is_exclusive(v_discr_796_);
if (v_isSharedCheck_831_ == 0)
{
v___x_805_ = v_discr_796_;
v_isShared_806_ = v_isSharedCheck_831_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_gate_802_);
lean_dec(v_discr_796_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_831_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v_gate_807_; uint8_t v_invert_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_830_; 
v_gate_807_ = lean_ctor_get(v_lhs_797_, 0);
v_invert_808_ = lean_ctor_get_uint8(v_lhs_797_, sizeof(void*)*1);
v_isSharedCheck_830_ = !lean_is_exclusive(v_lhs_797_);
if (v_isSharedCheck_830_ == 0)
{
v___x_810_ = v_lhs_797_;
v_isShared_811_ = v_isSharedCheck_830_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_gate_807_);
lean_dec(v_lhs_797_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_830_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v_gate_812_; uint8_t v_invert_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_829_; 
v_gate_812_ = lean_ctor_get(v_rhs_798_, 0);
v_invert_813_ = lean_ctor_get_uint8(v_rhs_798_, sizeof(void*)*1);
v_isSharedCheck_829_ = !lean_is_exclusive(v_rhs_798_);
if (v_isSharedCheck_829_ == 0)
{
v___x_815_ = v_rhs_798_;
v_isShared_816_ = v_isSharedCheck_829_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_gate_812_);
lean_dec(v_rhs_798_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_829_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v_gate_802_);
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_gate_802_);
v___x_818_ = v_reuseFailAlloc_828_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
lean_object* v___x_820_; 
lean_ctor_set_uint8(v___x_818_, sizeof(void*)*1, v_invert_803_);
if (v_isShared_811_ == 0)
{
v___x_820_ = v___x_810_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_gate_807_);
lean_ctor_set_uint8(v_reuseFailAlloc_827_, sizeof(void*)*1, v_invert_808_);
v___x_820_ = v_reuseFailAlloc_827_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
lean_object* v___x_822_; 
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v_gate_812_);
v___x_822_ = v___x_805_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_gate_812_);
v___x_822_ = v_reuseFailAlloc_826_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
lean_object* v___x_824_; 
lean_ctor_set_uint8(v___x_822_, sizeof(void*)*1, v_invert_813_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 2, v___x_822_);
lean_ctor_set(v___x_800_, 1, v___x_820_);
lean_ctor_set(v___x_800_, 0, v___x_818_);
v___x_824_ = v___x_800_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_818_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v___x_820_);
lean_ctor_set(v_reuseFailAlloc_825_, 2, v___x_822_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_TernaryInput_cast(lean_object* v_00_u03b1_833_, lean_object* v_inst_834_, lean_object* v_inst_835_, lean_object* v_aig1_836_, lean_object* v_aig2_837_, lean_object* v_input_838_, lean_object* v_h_839_){
_start:
{
lean_object* v_discr_840_; lean_object* v_lhs_841_; lean_object* v_rhs_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_876_; 
v_discr_840_ = lean_ctor_get(v_input_838_, 0);
v_lhs_841_ = lean_ctor_get(v_input_838_, 1);
v_rhs_842_ = lean_ctor_get(v_input_838_, 2);
v_isSharedCheck_876_ = !lean_is_exclusive(v_input_838_);
if (v_isSharedCheck_876_ == 0)
{
v___x_844_ = v_input_838_;
v_isShared_845_ = v_isSharedCheck_876_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_rhs_842_);
lean_inc(v_lhs_841_);
lean_inc(v_discr_840_);
lean_dec(v_input_838_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_876_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v_gate_846_; uint8_t v_invert_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_875_; 
v_gate_846_ = lean_ctor_get(v_discr_840_, 0);
v_invert_847_ = lean_ctor_get_uint8(v_discr_840_, sizeof(void*)*1);
v_isSharedCheck_875_ = !lean_is_exclusive(v_discr_840_);
if (v_isSharedCheck_875_ == 0)
{
v___x_849_ = v_discr_840_;
v_isShared_850_ = v_isSharedCheck_875_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_gate_846_);
lean_dec(v_discr_840_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_875_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v_gate_851_; uint8_t v_invert_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_874_; 
v_gate_851_ = lean_ctor_get(v_lhs_841_, 0);
v_invert_852_ = lean_ctor_get_uint8(v_lhs_841_, sizeof(void*)*1);
v_isSharedCheck_874_ = !lean_is_exclusive(v_lhs_841_);
if (v_isSharedCheck_874_ == 0)
{
v___x_854_ = v_lhs_841_;
v_isShared_855_ = v_isSharedCheck_874_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_gate_851_);
lean_dec(v_lhs_841_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_874_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v_gate_856_; uint8_t v_invert_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_873_; 
v_gate_856_ = lean_ctor_get(v_rhs_842_, 0);
v_invert_857_ = lean_ctor_get_uint8(v_rhs_842_, sizeof(void*)*1);
v_isSharedCheck_873_ = !lean_is_exclusive(v_rhs_842_);
if (v_isSharedCheck_873_ == 0)
{
v___x_859_ = v_rhs_842_;
v_isShared_860_ = v_isSharedCheck_873_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_gate_856_);
lean_dec(v_rhs_842_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_873_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_862_; 
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 0, v_gate_846_);
v___x_862_ = v___x_859_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_gate_846_);
v___x_862_ = v_reuseFailAlloc_872_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
lean_object* v___x_864_; 
lean_ctor_set_uint8(v___x_862_, sizeof(void*)*1, v_invert_847_);
if (v_isShared_855_ == 0)
{
v___x_864_ = v___x_854_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_gate_851_);
lean_ctor_set_uint8(v_reuseFailAlloc_871_, sizeof(void*)*1, v_invert_852_);
v___x_864_ = v_reuseFailAlloc_871_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
lean_object* v___x_866_; 
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 0, v_gate_856_);
v___x_866_ = v___x_849_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_gate_856_);
v___x_866_ = v_reuseFailAlloc_870_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
lean_object* v___x_868_; 
lean_ctor_set_uint8(v___x_866_, sizeof(void*)*1, v_invert_857_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 2, v___x_866_);
lean_ctor_set(v___x_844_, 1, v___x_864_);
lean_ctor_set(v___x_844_, 0, v___x_862_);
v___x_868_ = v___x_844_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_862_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v___x_864_);
lean_ctor_set(v_reuseFailAlloc_869_, 2, v___x_866_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_TernaryInput_cast___boxed(lean_object* v_00_u03b1_877_, lean_object* v_inst_878_, lean_object* v_inst_879_, lean_object* v_aig1_880_, lean_object* v_aig2_881_, lean_object* v_input_882_, lean_object* v_h_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Std_Sat_AIG_TernaryInput_cast(v_00_u03b1_877_, v_inst_878_, v_inst_879_, v_aig1_880_, v_aig2_881_, v_input_882_, v_h_883_);
lean_dec_ref(v_aig2_881_);
lean_dec_ref(v_aig1_880_);
lean_dec_ref(v_inst_879_);
lean_dec_ref(v_inst_878_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_invEdgeStyle(uint8_t v_isInv_887_){
_start:
{
if (v_isInv_887_ == 0)
{
lean_object* v___x_888_; 
v___x_888_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_invEdgeStyle___closed__0));
return v___x_888_;
}
else
{
lean_object* v___x_889_; 
v___x_889_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_invEdgeStyle___closed__1));
return v___x_889_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_invEdgeStyle___boxed(lean_object* v_isInv_890_){
_start:
{
uint8_t v_isInv_boxed_891_; lean_object* v_res_892_; 
v_isInv_boxed_891_ = lean_unbox(v_isInv_890_);
v_res_892_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v_isInv_boxed_891_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___redArg(lean_object* v_acc_897_, lean_object* v_decls_898_, lean_object* v_idx_899_, lean_object* v_a_900_){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___f_903_; lean_object* v___f_904_; uint8_t v___x_905_; 
v___x_901_ = lean_array_get_size(v_decls_898_);
v___x_902_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_902_, 0, v___x_901_);
v___f_903_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_903_, 0, v___x_902_);
v___f_904_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___redArg___closed__0));
lean_inc(v_idx_899_);
lean_inc_ref(v___f_903_);
v___x_905_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_903_, v___f_904_, v_a_900_, v_idx_899_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_906_ = lean_box(0);
lean_inc(v_idx_899_);
v___x_907_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___f_903_, v___f_904_, v_a_900_, v_idx_899_, v___x_906_);
v___x_908_ = lean_array_fget_borrowed(v_decls_898_, v_idx_899_);
if (lean_obj_tag(v___x_908_) == 2)
{
lean_object* v_l_909_; lean_object* v_r_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___y_914_; uint8_t v___y_915_; uint8_t v___y_916_; uint8_t v___y_940_; lean_object* v___x_946_; lean_object* v___x_947_; uint8_t v___x_948_; 
v_l_909_ = lean_ctor_get(v___x_908_, 0);
v_r_910_ = lean_ctor_get(v___x_908_, 1);
v___x_911_ = lean_unsigned_to_nat(1u);
v___x_912_ = lean_nat_shiftr(v_l_909_, v___x_911_);
v___x_946_ = lean_nat_land(v___x_911_, v_l_909_);
v___x_947_ = lean_unsigned_to_nat(0u);
v___x_948_ = lean_nat_dec_eq(v___x_946_, v___x_947_);
lean_dec(v___x_946_);
if (v___x_948_ == 0)
{
uint8_t v___x_949_; 
v___x_949_ = 1;
v___y_940_ = v___x_949_;
goto v___jp_939_;
}
else
{
v___y_940_ = v___x_905_;
goto v___jp_939_;
}
v___jp_913_:
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v_fst_936_; lean_object* v_snd_937_; 
v___x_917_ = l_Nat_reprFast(v_idx_899_);
v___x_918_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___redArg___closed__1));
lean_inc_ref(v___x_917_);
v___x_919_ = lean_string_append(v___x_917_, v___x_918_);
lean_inc(v___x_912_);
v___x_920_ = l_Nat_reprFast(v___x_912_);
v___x_921_ = lean_string_append(v___x_919_, v___x_920_);
lean_dec_ref(v___x_920_);
v___x_922_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_915_);
v___x_923_ = lean_string_append(v___x_921_, v___x_922_);
lean_dec_ref(v___x_922_);
v___x_924_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___redArg___closed__2));
v___x_925_ = lean_string_append(v___x_923_, v___x_924_);
v___x_926_ = lean_string_append(v___x_925_, v___x_917_);
lean_dec_ref(v___x_917_);
v___x_927_ = lean_string_append(v___x_926_, v___x_918_);
lean_inc(v___y_914_);
v___x_928_ = l_Nat_reprFast(v___y_914_);
v___x_929_ = lean_string_append(v___x_927_, v___x_928_);
lean_dec_ref(v___x_928_);
v___x_930_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_916_);
v___x_931_ = lean_string_append(v___x_929_, v___x_930_);
lean_dec_ref(v___x_930_);
v___x_932_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___redArg___closed__3));
v___x_933_ = lean_string_append(v___x_931_, v___x_932_);
v___x_934_ = lean_string_append(v_acc_897_, v___x_933_);
lean_dec_ref(v___x_933_);
v___x_935_ = l_Std_Sat_AIG_toGraphviz_go___redArg(v___x_934_, v_decls_898_, v___x_912_, v___x_907_);
v_fst_936_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_fst_936_);
v_snd_937_ = lean_ctor_get(v___x_935_, 1);
lean_inc(v_snd_937_);
lean_dec_ref(v___x_935_);
v_acc_897_ = v_fst_936_;
v_idx_899_ = v___y_914_;
v_a_900_ = v_snd_937_;
goto _start;
}
v___jp_939_:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; uint8_t v___x_944_; 
v___x_941_ = lean_nat_shiftr(v_r_910_, v___x_911_);
v___x_942_ = lean_nat_land(v___x_911_, v_r_910_);
v___x_943_ = lean_unsigned_to_nat(0u);
v___x_944_ = lean_nat_dec_eq(v___x_942_, v___x_943_);
lean_dec(v___x_942_);
if (v___x_944_ == 0)
{
uint8_t v___x_945_; 
v___x_945_ = 1;
v___y_914_ = v___x_941_;
v___y_915_ = v___y_940_;
v___y_916_ = v___x_945_;
goto v___jp_913_;
}
else
{
v___y_914_ = v___x_941_;
v___y_915_ = v___y_940_;
v___y_916_ = v___x_905_;
goto v___jp_913_;
}
}
}
else
{
lean_object* v___x_950_; 
lean_dec(v_idx_899_);
v___x_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_950_, 0, v_acc_897_);
lean_ctor_set(v___x_950_, 1, v___x_907_);
return v___x_950_;
}
}
else
{
lean_object* v___x_951_; 
lean_dec_ref(v___f_903_);
lean_dec(v_idx_899_);
v___x_951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_951_, 0, v_acc_897_);
lean_ctor_set(v___x_951_, 1, v_a_900_);
return v___x_951_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___redArg___boxed(lean_object* v_acc_952_, lean_object* v_decls_953_, lean_object* v_idx_954_, lean_object* v_a_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Std_Sat_AIG_toGraphviz_go___redArg(v_acc_952_, v_decls_953_, v_idx_954_, v_a_955_);
lean_dec_ref(v_decls_953_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go(lean_object* v_00_u03b1_957_, lean_object* v_inst_958_, lean_object* v_inst_959_, lean_object* v_inst_960_, lean_object* v_acc_961_, lean_object* v_decls_962_, lean_object* v_hinv_963_, lean_object* v_idx_964_, lean_object* v_hidx_965_, lean_object* v_a_966_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_Std_Sat_AIG_toGraphviz_go___redArg(v_acc_961_, v_decls_962_, v_idx_964_, v_a_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___boxed(lean_object* v_00_u03b1_968_, lean_object* v_inst_969_, lean_object* v_inst_970_, lean_object* v_inst_971_, lean_object* v_acc_972_, lean_object* v_decls_973_, lean_object* v_hinv_974_, lean_object* v_idx_975_, lean_object* v_hidx_976_, lean_object* v_a_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Std_Sat_AIG_toGraphviz_go(v_00_u03b1_968_, v_inst_969_, v_inst_970_, v_inst_971_, v_acc_972_, v_decls_973_, v_hinv_974_, v_idx_975_, v_hidx_976_, v_a_977_);
lean_dec_ref(v_decls_973_);
lean_dec_ref(v_inst_971_);
lean_dec_ref(v_inst_970_);
lean_dec_ref(v_inst_969_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter___redArg(lean_object* v_x_979_, lean_object* v_h__1_980_, lean_object* v_h__2_981_, lean_object* v_h__3_982_){
_start:
{
switch(lean_obj_tag(v_x_979_))
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
v_idx_984_ = lean_ctor_get(v_x_979_, 0);
lean_inc(v_idx_984_);
lean_dec_ref_known(v_x_979_, 1);
v___x_985_ = lean_apply_2(v_h__2_981_, v_idx_984_, lean_box(0));
return v___x_985_;
}
default: 
{
lean_object* v_l_986_; lean_object* v_r_987_; lean_object* v___x_988_; 
lean_dec(v_h__2_981_);
lean_dec(v_h__1_980_);
v_l_986_ = lean_ctor_get(v_x_979_, 0);
lean_inc(v_l_986_);
v_r_987_ = lean_ctor_get(v_x_979_, 1);
lean_inc(v_r_987_);
lean_dec_ref_known(v_x_979_, 2);
v___x_988_ = lean_apply_3(v_h__3_982_, v_l_986_, v_r_987_, lean_box(0));
return v___x_988_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter(lean_object* v_00_u03b1_989_, lean_object* v_motive_990_, lean_object* v_x_991_, lean_object* v_h__1_992_, lean_object* v_h__2_993_, lean_object* v_h__3_994_){
_start:
{
switch(lean_obj_tag(v_x_991_))
{
case 0:
{
lean_object* v___x_995_; 
lean_dec(v_h__3_994_);
lean_dec(v_h__2_993_);
v___x_995_ = lean_apply_1(v_h__1_992_, lean_box(0));
return v___x_995_;
}
case 1:
{
lean_object* v_idx_996_; lean_object* v___x_997_; 
lean_dec(v_h__3_994_);
lean_dec(v_h__1_992_);
v_idx_996_ = lean_ctor_get(v_x_991_, 0);
lean_inc(v_idx_996_);
lean_dec_ref_known(v_x_991_, 1);
v___x_997_ = lean_apply_2(v_h__2_993_, v_idx_996_, lean_box(0));
return v___x_997_;
}
default: 
{
lean_object* v_l_998_; lean_object* v_r_999_; lean_object* v___x_1000_; 
lean_dec(v_h__2_993_);
lean_dec(v_h__1_992_);
v_l_998_ = lean_ctor_get(v_x_991_, 0);
lean_inc(v_l_998_);
v_r_999_ = lean_ctor_get(v_x_991_, 1);
lean_inc(v_r_999_);
lean_dec_ref_known(v_x_991_, 2);
v___x_1000_ = lean_apply_3(v_h__3_994_, v_l_998_, v_r_999_, lean_box(0));
return v___x_1000_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg(lean_object* v_inst_1006_, lean_object* v_decls_1007_, lean_object* v_idx_1008_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = lean_array_fget_borrowed(v_decls_1007_, v_idx_1008_);
switch(lean_obj_tag(v___x_1009_))
{
case 0:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
lean_dec_ref(v_inst_1006_);
v___x_1010_ = l_Nat_reprFast(v_idx_1008_);
v___x_1011_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__0));
v___x_1012_ = lean_string_append(v___x_1010_, v___x_1011_);
v___x_1013_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__1));
v___x_1014_ = lean_string_append(v___x_1012_, v___x_1013_);
v___x_1015_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__2));
v___x_1016_ = lean_string_append(v___x_1014_, v___x_1015_);
return v___x_1016_;
}
case 1:
{
lean_object* v_idx_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v_idx_1017_ = lean_ctor_get(v___x_1009_, 0);
v___x_1018_ = l_Nat_reprFast(v_idx_1008_);
v___x_1019_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__0));
v___x_1020_ = lean_string_append(v___x_1018_, v___x_1019_);
lean_inc(v_idx_1017_);
v___x_1021_ = lean_apply_1(v_inst_1006_, v_idx_1017_);
v___x_1022_ = lean_string_append(v___x_1020_, v___x_1021_);
lean_dec_ref(v___x_1021_);
v___x_1023_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__3));
v___x_1024_ = lean_string_append(v___x_1022_, v___x_1023_);
return v___x_1024_;
}
default: 
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
lean_dec_ref(v_inst_1006_);
v___x_1025_ = l_Nat_reprFast(v_idx_1008_);
v___x_1026_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__0));
lean_inc_ref(v___x_1025_);
v___x_1027_ = lean_string_append(v___x_1025_, v___x_1026_);
v___x_1028_ = lean_string_append(v___x_1027_, v___x_1025_);
lean_dec_ref(v___x_1025_);
v___x_1029_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__4));
v___x_1030_ = lean_string_append(v___x_1028_, v___x_1029_);
return v___x_1030_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___boxed(lean_object* v_inst_1031_, lean_object* v_decls_1032_, lean_object* v_idx_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg(v_inst_1031_, v_decls_1032_, v_idx_1033_);
lean_dec_ref(v_decls_1032_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString(lean_object* v_00_u03b1_1035_, lean_object* v_inst_1036_, lean_object* v_inst_1037_, lean_object* v_inst_1038_, lean_object* v_decls_1039_, lean_object* v_idx_1040_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg(v_inst_1037_, v_decls_1039_, v_idx_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___boxed(lean_object* v_00_u03b1_1042_, lean_object* v_inst_1043_, lean_object* v_inst_1044_, lean_object* v_inst_1045_, lean_object* v_decls_1046_, lean_object* v_idx_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString(v_00_u03b1_1042_, v_inst_1043_, v_inst_1044_, v_inst_1045_, v_decls_1046_, v_idx_1047_);
lean_dec_ref(v_decls_1046_);
lean_dec_ref(v_inst_1045_);
lean_dec_ref(v_inst_1043_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___redArg___lam__0(lean_object* v_inst_1049_, lean_object* v_decls_1050_, lean_object* v_x1_1051_, lean_object* v_x2_1052_, lean_object* v_x3_1053_){
_start:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1054_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg(v_inst_1049_, v_decls_1050_, v_x2_1052_);
v___x_1055_ = lean_string_append(v_x1_1051_, v___x_1054_);
lean_dec_ref(v___x_1054_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___redArg___lam__0___boxed(lean_object* v_inst_1056_, lean_object* v_decls_1057_, lean_object* v_x1_1058_, lean_object* v_x2_1059_, lean_object* v_x3_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Std_Sat_AIG_toGraphviz___redArg___lam__0(v_inst_1056_, v_decls_1057_, v_x1_1058_, v_x2_1059_, v_x3_1060_);
lean_dec_ref(v_decls_1057_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___redArg___lam__1(lean_object* v___x_1062_, lean_object* v___f_1063_, lean_object* v_acc_1064_, lean_object* v_l_1065_){
_start:
{
lean_object* v___x_1066_; 
v___x_1066_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1062_, v___f_1063_, v_acc_1064_, v_l_1065_);
return v___x_1066_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___redArg___closed__1(void){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1068_ = lean_box(0);
v___x_1069_ = lean_unsigned_to_nat(16u);
v___x_1070_ = lean_mk_array(v___x_1069_, v___x_1068_);
return v___x_1070_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___redArg___closed__2(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1071_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___redArg___closed__1, &l_Std_Sat_AIG_toGraphviz___redArg___closed__1_once, _init_l_Std_Sat_AIG_toGraphviz___redArg___closed__1);
v___x_1072_ = lean_unsigned_to_nat(0u);
v___x_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
lean_ctor_set(v___x_1073_, 1, v___x_1071_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___redArg(lean_object* v_inst_1095_, lean_object* v_entry_1096_){
_start:
{
lean_object* v_aig_1097_; lean_object* v_ref_1098_; lean_object* v_decls_1099_; lean_object* v_gate_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v_fst_1105_; lean_object* v_snd_1106_; lean_object* v___y_1108_; lean_object* v___x_1114_; lean_object* v_buckets_1115_; lean_object* v___x_1116_; uint8_t v___x_1117_; 
v_aig_1097_ = lean_ctor_get(v_entry_1096_, 0);
lean_inc_ref(v_aig_1097_);
v_ref_1098_ = lean_ctor_get(v_entry_1096_, 1);
lean_inc_ref(v_ref_1098_);
lean_dec_ref(v_entry_1096_);
v_decls_1099_ = lean_ctor_get(v_aig_1097_, 0);
lean_inc_ref(v_decls_1099_);
lean_dec_ref(v_aig_1097_);
v_gate_1100_ = lean_ctor_get(v_ref_1098_, 0);
lean_inc(v_gate_1100_);
lean_dec_ref(v_ref_1098_);
v___x_1101_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___redArg___closed__0));
v___x_1102_ = lean_unsigned_to_nat(0u);
v___x_1103_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___redArg___closed__2, &l_Std_Sat_AIG_toGraphviz___redArg___closed__2_once, _init_l_Std_Sat_AIG_toGraphviz___redArg___closed__2);
v___x_1104_ = l_Std_Sat_AIG_toGraphviz_go___redArg(v___x_1101_, v_decls_1099_, v_gate_1100_, v___x_1103_);
v_fst_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_fst_1105_);
v_snd_1106_ = lean_ctor_get(v___x_1104_, 1);
lean_inc(v_snd_1106_);
lean_dec_ref(v___x_1104_);
v___x_1114_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___redArg___closed__14));
v_buckets_1115_ = lean_ctor_get(v_snd_1106_, 1);
lean_inc_ref(v_buckets_1115_);
lean_dec(v_snd_1106_);
v___x_1116_ = lean_array_get_size(v_buckets_1115_);
v___x_1117_ = lean_nat_dec_lt(v___x_1102_, v___x_1116_);
if (v___x_1117_ == 0)
{
lean_dec_ref(v_buckets_1115_);
lean_dec_ref(v_decls_1099_);
lean_dec_ref(v_inst_1095_);
v___y_1108_ = v___x_1101_;
goto v___jp_1107_;
}
else
{
lean_object* v___f_1118_; lean_object* v___f_1119_; size_t v___x_1120_; size_t v___x_1121_; lean_object* v___x_1122_; 
v___f_1118_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_toGraphviz___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1118_, 0, v_inst_1095_);
lean_closure_set(v___f_1118_, 1, v_decls_1099_);
v___f_1119_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_toGraphviz___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1119_, 0, v___x_1114_);
lean_closure_set(v___f_1119_, 1, v___f_1118_);
v___x_1120_ = ((size_t)0ULL);
v___x_1121_ = lean_usize_of_nat(v___x_1116_);
v___x_1122_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1114_, v___f_1119_, v_buckets_1115_, v___x_1120_, v___x_1121_, v___x_1101_);
v___y_1108_ = v___x_1122_;
goto v___jp_1107_;
}
v___jp_1107_:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1109_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___redArg___closed__3));
v___x_1110_ = lean_string_append(v___x_1109_, v___y_1108_);
lean_dec_ref(v___y_1108_);
v___x_1111_ = lean_string_append(v___x_1110_, v_fst_1105_);
lean_dec(v_fst_1105_);
v___x_1112_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___redArg___closed__4));
v___x_1113_ = lean_string_append(v___x_1111_, v___x_1112_);
return v___x_1113_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz(lean_object* v_00_u03b1_1123_, lean_object* v_inst_1124_, lean_object* v_inst_1125_, lean_object* v_inst_1126_, lean_object* v_entry_1127_){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = l_Std_Sat_AIG_toGraphviz___redArg(v_inst_1125_, v_entry_1127_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___boxed(lean_object* v_00_u03b1_1129_, lean_object* v_inst_1130_, lean_object* v_inst_1131_, lean_object* v_inst_1132_, lean_object* v_entry_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_Std_Sat_AIG_toGraphviz(v_00_u03b1_1129_, v_inst_1130_, v_inst_1131_, v_inst_1132_, v_entry_1133_);
lean_dec_ref(v_inst_1132_);
lean_dec_ref(v_inst_1130_);
return v_res_1134_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote_go___redArg(lean_object* v_x_1135_, lean_object* v_decls_1136_, lean_object* v_assign_1137_){
_start:
{
uint8_t v___y_1139_; uint8_t v___y_1140_; lean_object* v___x_1142_; 
v___x_1142_ = lean_array_fget_borrowed(v_decls_1136_, v_x_1135_);
switch(lean_obj_tag(v___x_1142_))
{
case 0:
{
uint8_t v___x_1143_; 
lean_dec_ref(v_assign_1137_);
v___x_1143_ = 0;
return v___x_1143_;
}
case 1:
{
lean_object* v_idx_1144_; lean_object* v___x_1145_; uint8_t v___x_1146_; 
v_idx_1144_ = lean_ctor_get(v___x_1142_, 0);
lean_inc(v_idx_1144_);
v___x_1145_ = lean_apply_1(v_assign_1137_, v_idx_1144_);
v___x_1146_ = lean_unbox(v___x_1145_);
return v___x_1146_;
}
default: 
{
lean_object* v_l_1147_; lean_object* v_r_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; uint8_t v_lval_1151_; lean_object* v___x_1152_; uint8_t v_rval_1153_; uint8_t v___y_1155_; uint8_t v___y_1160_; lean_object* v___x_1162_; lean_object* v___x_1163_; uint8_t v___x_1164_; 
v_l_1147_ = lean_ctor_get(v___x_1142_, 0);
v_r_1148_ = lean_ctor_get(v___x_1142_, 1);
v___x_1149_ = lean_unsigned_to_nat(1u);
v___x_1150_ = lean_nat_shiftr(v_l_1147_, v___x_1149_);
lean_inc_ref(v_assign_1137_);
v_lval_1151_ = l_Std_Sat_AIG_denote_go___redArg(v___x_1150_, v_decls_1136_, v_assign_1137_);
lean_dec(v___x_1150_);
v___x_1152_ = lean_nat_shiftr(v_r_1148_, v___x_1149_);
v_rval_1153_ = l_Std_Sat_AIG_denote_go___redArg(v___x_1152_, v_decls_1136_, v_assign_1137_);
lean_dec(v___x_1152_);
v___x_1162_ = lean_nat_land(v___x_1149_, v_l_1147_);
v___x_1163_ = lean_unsigned_to_nat(0u);
v___x_1164_ = lean_nat_dec_eq(v___x_1162_, v___x_1163_);
lean_dec(v___x_1162_);
if (v___x_1164_ == 0)
{
v___y_1160_ = v_lval_1151_;
goto v___jp_1159_;
}
else
{
if (v_lval_1151_ == 0)
{
v___y_1160_ = v___x_1164_;
goto v___jp_1159_;
}
else
{
uint8_t v___x_1165_; 
v___x_1165_ = 0;
v___y_1155_ = v___x_1165_;
goto v___jp_1154_;
}
}
v___jp_1154_:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; uint8_t v___x_1158_; 
v___x_1156_ = lean_nat_land(v___x_1149_, v_r_1148_);
v___x_1157_ = lean_unsigned_to_nat(0u);
v___x_1158_ = lean_nat_dec_eq(v___x_1156_, v___x_1157_);
lean_dec(v___x_1156_);
if (v___x_1158_ == 0)
{
v___y_1139_ = v___y_1155_;
v___y_1140_ = v_rval_1153_;
goto v___jp_1138_;
}
else
{
if (v_rval_1153_ == 0)
{
v___y_1139_ = v___y_1155_;
v___y_1140_ = v___x_1158_;
goto v___jp_1138_;
}
else
{
return v_rval_1153_;
}
}
}
v___jp_1159_:
{
if (v___y_1160_ == 0)
{
v___y_1155_ = v___y_1160_;
goto v___jp_1154_;
}
else
{
uint8_t v___x_1161_; 
v___x_1161_ = 0;
return v___x_1161_;
}
}
}
}
v___jp_1138_:
{
if (v___y_1140_ == 0)
{
uint8_t v___x_1141_; 
v___x_1141_ = 1;
return v___x_1141_;
}
else
{
return v___y_1139_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote_go___redArg___boxed(lean_object* v_x_1166_, lean_object* v_decls_1167_, lean_object* v_assign_1168_){
_start:
{
uint8_t v_res_1169_; lean_object* v_r_1170_; 
v_res_1169_ = l_Std_Sat_AIG_denote_go___redArg(v_x_1166_, v_decls_1167_, v_assign_1168_);
lean_dec_ref(v_decls_1167_);
lean_dec(v_x_1166_);
v_r_1170_ = lean_box(v_res_1169_);
return v_r_1170_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote_go(lean_object* v_00_u03b1_1171_, lean_object* v_x_1172_, lean_object* v_decls_1173_, lean_object* v_assign_1174_, lean_object* v_h1_1175_, lean_object* v_h2_1176_){
_start:
{
uint8_t v___x_1177_; 
v___x_1177_ = l_Std_Sat_AIG_denote_go___redArg(v_x_1172_, v_decls_1173_, v_assign_1174_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote_go___boxed(lean_object* v_00_u03b1_1178_, lean_object* v_x_1179_, lean_object* v_decls_1180_, lean_object* v_assign_1181_, lean_object* v_h1_1182_, lean_object* v_h2_1183_){
_start:
{
uint8_t v_res_1184_; lean_object* v_r_1185_; 
v_res_1184_ = l_Std_Sat_AIG_denote_go(v_00_u03b1_1178_, v_x_1179_, v_decls_1180_, v_assign_1181_, v_h1_1182_, v_h2_1183_);
lean_dec_ref(v_decls_1180_);
lean_dec(v_x_1179_);
v_r_1185_ = lean_box(v_res_1184_);
return v_r_1185_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote___redArg(lean_object* v_assign_1186_, lean_object* v_entry_1187_){
_start:
{
lean_object* v_ref_1188_; lean_object* v_aig_1189_; lean_object* v_gate_1190_; uint8_t v_invert_1191_; lean_object* v_decls_1192_; uint8_t v___x_1193_; 
v_ref_1188_ = lean_ctor_get(v_entry_1187_, 1);
v_aig_1189_ = lean_ctor_get(v_entry_1187_, 0);
v_gate_1190_ = lean_ctor_get(v_ref_1188_, 0);
v_invert_1191_ = lean_ctor_get_uint8(v_ref_1188_, sizeof(void*)*1);
v_decls_1192_ = lean_ctor_get(v_aig_1189_, 0);
v___x_1193_ = l_Std_Sat_AIG_denote_go___redArg(v_gate_1190_, v_decls_1192_, v_assign_1186_);
if (v_invert_1191_ == 0)
{
return v___x_1193_;
}
else
{
if (v___x_1193_ == 0)
{
return v_invert_1191_;
}
else
{
uint8_t v___x_1194_; 
v___x_1194_ = 0;
return v___x_1194_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote___redArg___boxed(lean_object* v_assign_1195_, lean_object* v_entry_1196_){
_start:
{
uint8_t v_res_1197_; lean_object* v_r_1198_; 
v_res_1197_ = l_Std_Sat_AIG_denote___redArg(v_assign_1195_, v_entry_1196_);
lean_dec_ref(v_entry_1196_);
v_r_1198_ = lean_box(v_res_1197_);
return v_r_1198_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote(lean_object* v_00_u03b1_1199_, lean_object* v_inst_1200_, lean_object* v_inst_1201_, lean_object* v_assign_1202_, lean_object* v_entry_1203_){
_start:
{
uint8_t v___x_1204_; 
v___x_1204_ = l_Std_Sat_AIG_denote___redArg(v_assign_1202_, v_entry_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote___boxed(lean_object* v_00_u03b1_1205_, lean_object* v_inst_1206_, lean_object* v_inst_1207_, lean_object* v_assign_1208_, lean_object* v_entry_1209_){
_start:
{
uint8_t v_res_1210_; lean_object* v_r_1211_; 
v_res_1210_ = l_Std_Sat_AIG_denote(v_00_u03b1_1205_, v_inst_1206_, v_inst_1207_, v_assign_1208_, v_entry_1209_);
lean_dec_ref(v_entry_1209_);
lean_dec_ref(v_inst_1207_);
lean_dec_ref(v_inst_1206_);
v_r_1211_ = lean_box(v_res_1210_);
return v_r_1211_;
}
}
static lean_object* _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6(void){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__5));
v___x_1294_ = l_String_toRawSubstring_x27(v___x_1293_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1(lean_object* v_x_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_){
_start:
{
lean_object* v___x_1319_; uint8_t v___x_1320_; 
v___x_1319_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
lean_inc(v_x_1316_);
v___x_1320_ = l_Lean_Syntax_isOfKind(v_x_1316_, v___x_1319_);
if (v___x_1320_ == 0)
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
lean_dec(v_x_1316_);
v___x_1321_ = lean_box(1);
v___x_1322_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1321_);
lean_ctor_set(v___x_1322_, 1, v_a_1318_);
return v___x_1322_;
}
else
{
lean_object* v_quotContext_1323_; lean_object* v_currMacroScope_1324_; lean_object* v_ref_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; uint8_t v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v_quotContext_1323_ = lean_ctor_get(v_a_1317_, 1);
v_currMacroScope_1324_ = lean_ctor_get(v_a_1317_, 2);
v_ref_1325_ = lean_ctor_get(v_a_1317_, 5);
v___x_1326_ = lean_unsigned_to_nat(1u);
v___x_1327_ = l_Lean_Syntax_getArg(v_x_1316_, v___x_1326_);
v___x_1328_ = lean_unsigned_to_nat(3u);
v___x_1329_ = l_Lean_Syntax_getArg(v_x_1316_, v___x_1328_);
lean_dec(v_x_1316_);
v___x_1330_ = 0;
v___x_1331_ = l_Lean_SourceInfo_fromRef(v_ref_1325_, v___x_1330_);
v___x_1332_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4));
v___x_1333_ = lean_obj_once(&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6, &l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6_once, _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6);
v___x_1334_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__7));
lean_inc(v_currMacroScope_1324_);
lean_inc(v_quotContext_1323_);
v___x_1335_ = l_Lean_addMacroScope(v_quotContext_1323_, v___x_1334_, v_currMacroScope_1324_);
v___x_1336_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__12));
lean_inc_n(v___x_1331_, 2);
v___x_1337_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1331_);
lean_ctor_set(v___x_1337_, 1, v___x_1333_);
lean_ctor_set(v___x_1337_, 2, v___x_1335_);
lean_ctor_set(v___x_1337_, 3, v___x_1336_);
v___x_1338_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__14));
v___x_1339_ = l_Lean_Syntax_node2(v___x_1331_, v___x_1338_, v___x_1329_, v___x_1327_);
v___x_1340_ = l_Lean_Syntax_node2(v___x_1331_, v___x_1332_, v___x_1337_, v___x_1339_);
v___x_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1340_);
lean_ctor_set(v___x_1341_, 1, v_a_1318_);
return v___x_1341_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___boxed(lean_object* v_x_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1(v_x_1342_, v_a_1343_, v_a_1344_);
lean_dec_ref(v_a_1343_);
return v_res_1345_;
}
}
static lean_object* _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__7(void){
_start:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1362_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___redArg___closed__0));
v___x_1363_ = l_String_toRawSubstring_x27(v___x_1362_);
return v___x_1363_;
}
}
static lean_object* _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__12(void){
_start:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1374_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__11));
v___x_1375_ = l_String_toRawSubstring_x27(v___x_1374_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1(lean_object* v_x_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_){
_start:
{
lean_object* v___x_1402_; uint8_t v___x_1403_; 
v___x_1402_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__1));
lean_inc(v_x_1399_);
v___x_1403_ = l_Lean_Syntax_isOfKind(v_x_1399_, v___x_1402_);
if (v___x_1403_ == 0)
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
lean_dec(v_x_1399_);
v___x_1404_ = lean_box(1);
v___x_1405_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1404_);
lean_ctor_set(v___x_1405_, 1, v_a_1401_);
return v___x_1405_;
}
else
{
lean_object* v_quotContext_1406_; lean_object* v_currMacroScope_1407_; lean_object* v_ref_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; uint8_t v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v_quotContext_1406_ = lean_ctor_get(v_a_1400_, 1);
v_currMacroScope_1407_ = lean_ctor_get(v_a_1400_, 2);
v_ref_1408_ = lean_ctor_get(v_a_1400_, 5);
v___x_1409_ = lean_unsigned_to_nat(1u);
v___x_1410_ = l_Lean_Syntax_getArg(v_x_1399_, v___x_1409_);
v___x_1411_ = lean_unsigned_to_nat(3u);
v___x_1412_ = l_Lean_Syntax_getArg(v_x_1399_, v___x_1411_);
v___x_1413_ = lean_unsigned_to_nat(5u);
v___x_1414_ = l_Lean_Syntax_getArg(v_x_1399_, v___x_1413_);
lean_dec(v_x_1399_);
v___x_1415_ = 0;
v___x_1416_ = l_Lean_SourceInfo_fromRef(v_ref_1408_, v___x_1415_);
v___x_1417_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4));
v___x_1418_ = lean_obj_once(&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6, &l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6_once, _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6);
v___x_1419_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__7));
lean_inc_n(v_currMacroScope_1407_, 3);
lean_inc_n(v_quotContext_1406_, 3);
v___x_1420_ = l_Lean_addMacroScope(v_quotContext_1406_, v___x_1419_, v_currMacroScope_1407_);
v___x_1421_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__12));
lean_inc_n(v___x_1416_, 11);
v___x_1422_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1416_);
lean_ctor_set(v___x_1422_, 1, v___x_1418_);
lean_ctor_set(v___x_1422_, 2, v___x_1420_);
lean_ctor_set(v___x_1422_, 3, v___x_1421_);
v___x_1423_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__14));
v___x_1424_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__1));
v___x_1425_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__3));
v___x_1426_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__4));
v___x_1427_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1416_);
lean_ctor_set(v___x_1427_, 1, v___x_1426_);
v___x_1428_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__6));
v___x_1429_ = lean_obj_once(&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__7, &l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__7_once, _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__7);
v___x_1430_ = lean_box(0);
v___x_1431_ = l_Lean_addMacroScope(v_quotContext_1406_, v___x_1430_, v_currMacroScope_1407_);
v___x_1432_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__10));
v___x_1433_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1416_);
lean_ctor_set(v___x_1433_, 1, v___x_1429_);
lean_ctor_set(v___x_1433_, 2, v___x_1431_);
lean_ctor_set(v___x_1433_, 3, v___x_1432_);
v___x_1434_ = l_Lean_Syntax_node1(v___x_1416_, v___x_1428_, v___x_1433_);
v___x_1435_ = l_Lean_Syntax_node2(v___x_1416_, v___x_1425_, v___x_1427_, v___x_1434_);
v___x_1436_ = lean_obj_once(&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__12, &l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__12_once, _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__12);
v___x_1437_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__15));
v___x_1438_ = l_Lean_addMacroScope(v_quotContext_1406_, v___x_1437_, v_currMacroScope_1407_);
v___x_1439_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__20));
v___x_1440_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1416_);
lean_ctor_set(v___x_1440_, 1, v___x_1436_);
lean_ctor_set(v___x_1440_, 2, v___x_1438_);
lean_ctor_set(v___x_1440_, 3, v___x_1439_);
v___x_1441_ = l_Lean_Syntax_node2(v___x_1416_, v___x_1423_, v___x_1410_, v___x_1412_);
v___x_1442_ = l_Lean_Syntax_node2(v___x_1416_, v___x_1417_, v___x_1440_, v___x_1441_);
v___x_1443_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__21));
v___x_1444_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1416_);
lean_ctor_set(v___x_1444_, 1, v___x_1443_);
v___x_1445_ = l_Lean_Syntax_node3(v___x_1416_, v___x_1424_, v___x_1435_, v___x_1442_, v___x_1444_);
v___x_1446_ = l_Lean_Syntax_node2(v___x_1416_, v___x_1423_, v___x_1414_, v___x_1445_);
v___x_1447_ = l_Lean_Syntax_node2(v___x_1416_, v___x_1417_, v___x_1422_, v___x_1446_);
v___x_1448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1447_);
lean_ctor_set(v___x_1448_, 1, v_a_1401_);
return v___x_1448_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___boxed(lean_object* v_x_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1(v_x_1449_, v_a_1450_, v_a_1451_);
lean_dec_ref(v_a_1450_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_unexpandDenote(lean_object* v_x_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_){
_start:
{
lean_object* v___x_1510_; uint8_t v___x_1511_; 
v___x_1510_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4));
lean_inc(v_x_1507_);
v___x_1511_ = l_Lean_Syntax_isOfKind(v_x_1507_, v___x_1510_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
lean_dec(v_x_1507_);
v___x_1512_ = lean_box(0);
v___x_1513_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1512_);
lean_ctor_set(v___x_1513_, 1, v_a_1509_);
return v___x_1513_;
}
else
{
lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; uint8_t v___x_1517_; 
v___x_1514_ = lean_unsigned_to_nat(1u);
v___x_1515_ = l_Lean_Syntax_getArg(v_x_1507_, v___x_1514_);
lean_dec(v_x_1507_);
v___x_1516_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1515_);
v___x_1517_ = l_Lean_Syntax_matchesNull(v___x_1515_, v___x_1516_);
if (v___x_1517_ == 0)
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
lean_dec(v___x_1515_);
v___x_1518_ = lean_box(0);
v___x_1519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1518_);
lean_ctor_set(v___x_1519_, 1, v_a_1509_);
return v___x_1519_;
}
else
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; uint8_t v___x_1523_; 
v___x_1520_ = lean_unsigned_to_nat(0u);
v___x_1521_ = l_Lean_Syntax_getArg(v___x_1515_, v___x_1520_);
v___x_1522_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__1));
lean_inc(v___x_1521_);
v___x_1523_ = l_Lean_Syntax_isOfKind(v___x_1521_, v___x_1522_);
if (v___x_1523_ == 0)
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1524_ = l_Lean_Syntax_getArg(v___x_1515_, v___x_1514_);
lean_dec(v___x_1515_);
v___x_1525_ = l_Lean_SourceInfo_fromRef(v_a_1508_, v___x_1523_);
v___x_1526_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1527_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1525_, 3);
v___x_1528_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1525_);
lean_ctor_set(v___x_1528_, 1, v___x_1527_);
v___x_1529_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1530_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1525_);
lean_ctor_set(v___x_1530_, 1, v___x_1529_);
v___x_1531_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1532_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1525_);
lean_ctor_set(v___x_1532_, 1, v___x_1531_);
v___x_1533_ = l_Lean_Syntax_node5(v___x_1525_, v___x_1526_, v___x_1528_, v___x_1521_, v___x_1530_, v___x_1524_, v___x_1532_);
v___x_1534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1533_);
lean_ctor_set(v___x_1534_, 1, v_a_1509_);
return v___x_1534_;
}
else
{
lean_object* v___x_1535_; uint8_t v___x_1536_; 
v___x_1535_ = l_Lean_Syntax_getArg(v___x_1521_, v___x_1514_);
v___x_1536_ = l_Lean_Syntax_matchesNull(v___x_1535_, v___x_1520_);
if (v___x_1536_ == 0)
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1537_ = l_Lean_Syntax_getArg(v___x_1515_, v___x_1514_);
lean_dec(v___x_1515_);
v___x_1538_ = l_Lean_SourceInfo_fromRef(v_a_1508_, v___x_1536_);
v___x_1539_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1540_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1538_, 3);
v___x_1541_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1538_);
lean_ctor_set(v___x_1541_, 1, v___x_1540_);
v___x_1542_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1543_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1538_);
lean_ctor_set(v___x_1543_, 1, v___x_1542_);
v___x_1544_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1545_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1538_);
lean_ctor_set(v___x_1545_, 1, v___x_1544_);
v___x_1546_ = l_Lean_Syntax_node5(v___x_1538_, v___x_1539_, v___x_1541_, v___x_1521_, v___x_1543_, v___x_1537_, v___x_1545_);
v___x_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1546_);
lean_ctor_set(v___x_1547_, 1, v_a_1509_);
return v___x_1547_;
}
else
{
lean_object* v___x_1548_; lean_object* v___x_1549_; uint8_t v___x_1550_; 
v___x_1548_ = l_Lean_Syntax_getArg(v___x_1521_, v___x_1516_);
v___x_1549_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__4));
lean_inc(v___x_1548_);
v___x_1550_ = l_Lean_Syntax_isOfKind(v___x_1548_, v___x_1549_);
if (v___x_1550_ == 0)
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
lean_dec(v___x_1548_);
v___x_1551_ = l_Lean_Syntax_getArg(v___x_1515_, v___x_1514_);
lean_dec(v___x_1515_);
v___x_1552_ = l_Lean_SourceInfo_fromRef(v_a_1508_, v___x_1550_);
v___x_1553_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1554_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1552_, 3);
v___x_1555_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1552_);
lean_ctor_set(v___x_1555_, 1, v___x_1554_);
v___x_1556_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1557_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1552_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
v___x_1558_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1559_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1552_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
v___x_1560_ = l_Lean_Syntax_node5(v___x_1552_, v___x_1553_, v___x_1555_, v___x_1521_, v___x_1557_, v___x_1551_, v___x_1559_);
v___x_1561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1560_);
lean_ctor_set(v___x_1561_, 1, v_a_1509_);
return v___x_1561_;
}
else
{
lean_object* v___x_1562_; lean_object* v___x_1563_; uint8_t v___x_1564_; 
v___x_1562_ = l_Lean_Syntax_getArg(v___x_1548_, v___x_1520_);
lean_dec(v___x_1548_);
v___x_1563_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_1562_);
v___x_1564_ = l_Lean_Syntax_matchesNull(v___x_1562_, v___x_1563_);
if (v___x_1564_ == 0)
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
lean_dec(v___x_1562_);
v___x_1565_ = l_Lean_Syntax_getArg(v___x_1515_, v___x_1514_);
lean_dec(v___x_1515_);
v___x_1566_ = l_Lean_SourceInfo_fromRef(v_a_1508_, v___x_1564_);
v___x_1567_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1568_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1566_, 3);
v___x_1569_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1566_);
lean_ctor_set(v___x_1569_, 1, v___x_1568_);
v___x_1570_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1571_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1566_);
lean_ctor_set(v___x_1571_, 1, v___x_1570_);
v___x_1572_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1573_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1566_);
lean_ctor_set(v___x_1573_, 1, v___x_1572_);
v___x_1574_ = l_Lean_Syntax_node5(v___x_1566_, v___x_1567_, v___x_1569_, v___x_1521_, v___x_1571_, v___x_1565_, v___x_1573_);
v___x_1575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1574_);
lean_ctor_set(v___x_1575_, 1, v_a_1509_);
return v___x_1575_;
}
else
{
lean_object* v___x_1576_; lean_object* v___x_1577_; uint8_t v___x_1578_; 
v___x_1576_ = l_Lean_Syntax_getArg(v___x_1562_, v___x_1520_);
v___x_1577_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__6));
lean_inc(v___x_1576_);
v___x_1578_ = l_Lean_Syntax_isOfKind(v___x_1576_, v___x_1577_);
if (v___x_1578_ == 0)
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
lean_dec(v___x_1576_);
lean_dec(v___x_1562_);
v___x_1579_ = l_Lean_Syntax_getArg(v___x_1515_, v___x_1514_);
lean_dec(v___x_1515_);
v___x_1580_ = l_Lean_SourceInfo_fromRef(v_a_1508_, v___x_1578_);
v___x_1581_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1582_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1580_, 3);
v___x_1583_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1580_);
lean_ctor_set(v___x_1583_, 1, v___x_1582_);
v___x_1584_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1585_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1580_);
lean_ctor_set(v___x_1585_, 1, v___x_1584_);
v___x_1586_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1587_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1580_);
lean_ctor_set(v___x_1587_, 1, v___x_1586_);
v___x_1588_ = l_Lean_Syntax_node5(v___x_1580_, v___x_1581_, v___x_1583_, v___x_1521_, v___x_1585_, v___x_1579_, v___x_1587_);
v___x_1589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1588_);
lean_ctor_set(v___x_1589_, 1, v_a_1509_);
return v___x_1589_;
}
else
{
lean_object* v___x_1590_; lean_object* v___x_1591_; uint8_t v___x_1592_; 
v___x_1590_ = l_Lean_Syntax_getArg(v___x_1576_, v___x_1520_);
v___x_1591_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__8));
lean_inc(v___x_1590_);
v___x_1592_ = l_Lean_Syntax_isOfKind(v___x_1590_, v___x_1591_);
if (v___x_1592_ == 0)
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
lean_dec(v___x_1590_);
lean_dec(v___x_1576_);
lean_dec(v___x_1562_);
v___x_1593_ = l_Lean_Syntax_getArg(v___x_1515_, v___x_1514_);
lean_dec(v___x_1515_);
v___x_1594_ = l_Lean_SourceInfo_fromRef(v_a_1508_, v___x_1592_);
v___x_1595_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1596_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1594_, 3);
v___x_1597_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1594_);
lean_ctor_set(v___x_1597_, 1, v___x_1596_);
v___x_1598_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1599_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1594_);
lean_ctor_set(v___x_1599_, 1, v___x_1598_);
v___x_1600_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1601_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1594_);
lean_ctor_set(v___x_1601_, 1, v___x_1600_);
v___x_1602_ = l_Lean_Syntax_node5(v___x_1594_, v___x_1595_, v___x_1597_, v___x_1521_, v___x_1599_, v___x_1593_, v___x_1601_);
v___x_1603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1602_);
lean_ctor_set(v___x_1603_, 1, v_a_1509_);
return v___x_1603_;
}
else
{
lean_object* v___x_1604_; lean_object* v___x_1605_; uint8_t v___x_1606_; 
v___x_1604_ = l_Lean_Syntax_getArg(v___x_1590_, v___x_1520_);
v___x_1605_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__10));
v___x_1606_ = l_Lean_Syntax_matchesIdent(v___x_1604_, v___x_1605_);
lean_dec(v___x_1604_);
if (v___x_1606_ == 0)
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
lean_dec(v___x_1590_);
lean_dec(v___x_1576_);
lean_dec(v___x_1562_);
v___x_1607_ = l_Lean_Syntax_getArg(v___x_1515_, v___x_1514_);
lean_dec(v___x_1515_);
v___x_1608_ = l_Lean_SourceInfo_fromRef(v_a_1508_, v___x_1606_);
v___x_1609_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1610_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1608_, 3);
v___x_1611_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1608_);
lean_ctor_set(v___x_1611_, 1, v___x_1610_);
v___x_1612_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1613_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1608_);
lean_ctor_set(v___x_1613_, 1, v___x_1612_);
v___x_1614_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1615_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1608_);
lean_ctor_set(v___x_1615_, 1, v___x_1614_);
v___x_1616_ = l_Lean_Syntax_node5(v___x_1608_, v___x_1609_, v___x_1611_, v___x_1521_, v___x_1613_, v___x_1607_, v___x_1615_);
v___x_1617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1616_);
lean_ctor_set(v___x_1617_, 1, v_a_1509_);
return v___x_1617_;
}
else
{
lean_object* v___x_1618_; uint8_t v___x_1619_; 
v___x_1618_ = l_Lean_Syntax_getArg(v___x_1590_, v___x_1514_);
lean_dec(v___x_1590_);
v___x_1619_ = l_Lean_Syntax_matchesNull(v___x_1618_, v___x_1520_);
if (v___x_1619_ == 0)
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
lean_dec(v___x_1576_);
lean_dec(v___x_1562_);
v___x_1620_ = l_Lean_Syntax_getArg(v___x_1515_, v___x_1514_);
lean_dec(v___x_1515_);
v___x_1621_ = l_Lean_SourceInfo_fromRef(v_a_1508_, v___x_1619_);
v___x_1622_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1623_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1621_, 3);
v___x_1624_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1621_);
lean_ctor_set(v___x_1624_, 1, v___x_1623_);
v___x_1625_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1626_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1621_);
lean_ctor_set(v___x_1626_, 1, v___x_1625_);
v___x_1627_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1628_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1621_);
lean_ctor_set(v___x_1628_, 1, v___x_1627_);
v___x_1629_ = l_Lean_Syntax_node5(v___x_1621_, v___x_1622_, v___x_1624_, v___x_1521_, v___x_1626_, v___x_1620_, v___x_1628_);
v___x_1630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1629_);
lean_ctor_set(v___x_1630_, 1, v_a_1509_);
return v___x_1630_;
}
else
{
lean_object* v___x_1631_; lean_object* v___x_1632_; uint8_t v___x_1633_; 
v___x_1631_ = l_Lean_Syntax_getArg(v___x_1576_, v___x_1514_);
lean_dec(v___x_1576_);
v___x_1632_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_1631_);
v___x_1633_ = l_Lean_Syntax_matchesNull(v___x_1631_, v___x_1632_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
lean_dec(v___x_1631_);
lean_dec(v___x_1562_);
v___x_1634_ = l_Lean_Syntax_getArg(v___x_1515_, v___x_1514_);
lean_dec(v___x_1515_);
v___x_1635_ = l_Lean_SourceInfo_fromRef(v_a_1508_, v___x_1633_);
v___x_1636_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1637_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1635_, 3);
v___x_1638_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1635_);
lean_ctor_set(v___x_1638_, 1, v___x_1637_);
v___x_1639_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1640_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1635_);
lean_ctor_set(v___x_1640_, 1, v___x_1639_);
v___x_1641_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1642_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1635_);
lean_ctor_set(v___x_1642_, 1, v___x_1641_);
v___x_1643_ = l_Lean_Syntax_node5(v___x_1635_, v___x_1636_, v___x_1638_, v___x_1521_, v___x_1640_, v___x_1634_, v___x_1642_);
v___x_1644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1643_);
lean_ctor_set(v___x_1644_, 1, v_a_1509_);
return v___x_1644_;
}
else
{
lean_object* v___x_1645_; uint8_t v___x_1646_; 
v___x_1645_ = l_Lean_Syntax_getArg(v___x_1631_, v___x_1520_);
v___x_1646_ = l_Lean_Syntax_matchesNull(v___x_1645_, v___x_1520_);
if (v___x_1646_ == 0)
{
lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
lean_dec(v___x_1631_);
lean_dec(v___x_1562_);
v___x_1647_ = l_Lean_Syntax_getArg(v___x_1515_, v___x_1514_);
lean_dec(v___x_1515_);
v___x_1648_ = l_Lean_SourceInfo_fromRef(v_a_1508_, v___x_1646_);
v___x_1649_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1650_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1648_, 3);
v___x_1651_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1648_);
lean_ctor_set(v___x_1651_, 1, v___x_1650_);
v___x_1652_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1653_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1648_);
lean_ctor_set(v___x_1653_, 1, v___x_1652_);
v___x_1654_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1655_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1648_);
lean_ctor_set(v___x_1655_, 1, v___x_1654_);
v___x_1656_ = l_Lean_Syntax_node5(v___x_1648_, v___x_1649_, v___x_1651_, v___x_1521_, v___x_1653_, v___x_1647_, v___x_1655_);
v___x_1657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1656_);
lean_ctor_set(v___x_1657_, 1, v_a_1509_);
return v___x_1657_;
}
else
{
lean_object* v___x_1658_; uint8_t v___x_1659_; 
v___x_1658_ = l_Lean_Syntax_getArg(v___x_1631_, v___x_1514_);
v___x_1659_ = l_Lean_Syntax_matchesNull(v___x_1658_, v___x_1520_);
if (v___x_1659_ == 0)
{
lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
lean_dec(v___x_1631_);
lean_dec(v___x_1562_);
v___x_1660_ = l_Lean_Syntax_getArg(v___x_1515_, v___x_1514_);
lean_dec(v___x_1515_);
v___x_1661_ = l_Lean_SourceInfo_fromRef(v_a_1508_, v___x_1659_);
v___x_1662_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1663_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1661_, 3);
v___x_1664_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1661_);
lean_ctor_set(v___x_1664_, 1, v___x_1663_);
v___x_1665_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1666_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1661_);
lean_ctor_set(v___x_1666_, 1, v___x_1665_);
v___x_1667_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1668_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1661_);
lean_ctor_set(v___x_1668_, 1, v___x_1667_);
v___x_1669_ = l_Lean_Syntax_node5(v___x_1661_, v___x_1662_, v___x_1664_, v___x_1521_, v___x_1666_, v___x_1660_, v___x_1668_);
v___x_1670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1669_);
lean_ctor_set(v___x_1670_, 1, v_a_1509_);
return v___x_1670_;
}
else
{
lean_object* v___x_1671_; lean_object* v___x_1672_; uint8_t v___x_1673_; 
v___x_1671_ = l_Lean_Syntax_getArg(v___x_1631_, v___x_1516_);
lean_dec(v___x_1631_);
v___x_1672_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__12));
lean_inc(v___x_1671_);
v___x_1673_ = l_Lean_Syntax_isOfKind(v___x_1671_, v___x_1672_);
if (v___x_1673_ == 0)
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
lean_dec(v___x_1671_);
lean_dec(v___x_1562_);
v___x_1674_ = l_Lean_Syntax_getArg(v___x_1515_, v___x_1514_);
lean_dec(v___x_1515_);
v___x_1675_ = l_Lean_SourceInfo_fromRef(v_a_1508_, v___x_1673_);
v___x_1676_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1677_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1675_, 3);
v___x_1678_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1675_);
lean_ctor_set(v___x_1678_, 1, v___x_1677_);
v___x_1679_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1680_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1675_);
lean_ctor_set(v___x_1680_, 1, v___x_1679_);
v___x_1681_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1682_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1682_, 0, v___x_1675_);
lean_ctor_set(v___x_1682_, 1, v___x_1681_);
v___x_1683_ = l_Lean_Syntax_node5(v___x_1675_, v___x_1676_, v___x_1678_, v___x_1521_, v___x_1680_, v___x_1674_, v___x_1682_);
v___x_1684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1683_);
lean_ctor_set(v___x_1684_, 1, v_a_1509_);
return v___x_1684_;
}
else
{
lean_object* v___x_1685_; uint8_t v___x_1686_; 
v___x_1685_ = l_Lean_Syntax_getArg(v___x_1671_, v___x_1514_);
v___x_1686_ = l_Lean_Syntax_matchesNull(v___x_1685_, v___x_1520_);
if (v___x_1686_ == 0)
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
lean_dec(v___x_1671_);
lean_dec(v___x_1562_);
v___x_1687_ = l_Lean_Syntax_getArg(v___x_1515_, v___x_1514_);
lean_dec(v___x_1515_);
v___x_1688_ = l_Lean_SourceInfo_fromRef(v_a_1508_, v___x_1686_);
v___x_1689_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1690_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1688_, 3);
v___x_1691_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1688_);
lean_ctor_set(v___x_1691_, 1, v___x_1690_);
v___x_1692_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1693_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1688_);
lean_ctor_set(v___x_1693_, 1, v___x_1692_);
v___x_1694_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1695_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1688_);
lean_ctor_set(v___x_1695_, 1, v___x_1694_);
v___x_1696_ = l_Lean_Syntax_node5(v___x_1688_, v___x_1689_, v___x_1691_, v___x_1521_, v___x_1693_, v___x_1687_, v___x_1695_);
v___x_1697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1696_);
lean_ctor_set(v___x_1697_, 1, v_a_1509_);
return v___x_1697_;
}
else
{
lean_object* v___x_1698_; uint8_t v___x_1699_; 
v___x_1698_ = l_Lean_Syntax_getArg(v___x_1562_, v___x_1516_);
lean_inc(v___x_1698_);
v___x_1699_ = l_Lean_Syntax_isOfKind(v___x_1698_, v___x_1577_);
if (v___x_1699_ == 0)
{
lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
lean_dec(v___x_1698_);
lean_dec(v___x_1671_);
lean_dec(v___x_1562_);
v___x_1700_ = l_Lean_Syntax_getArg(v___x_1515_, v___x_1514_);
lean_dec(v___x_1515_);
v___x_1701_ = l_Lean_SourceInfo_fromRef(v_a_1508_, v___x_1699_);
v___x_1702_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1703_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1701_, 3);
v___x_1704_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1701_);
lean_ctor_set(v___x_1704_, 1, v___x_1703_);
v___x_1705_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1706_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1706_, 0, v___x_1701_);
lean_ctor_set(v___x_1706_, 1, v___x_1705_);
v___x_1707_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1708_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1701_);
lean_ctor_set(v___x_1708_, 1, v___x_1707_);
v___x_1709_ = l_Lean_Syntax_node5(v___x_1701_, v___x_1702_, v___x_1704_, v___x_1521_, v___x_1706_, v___x_1700_, v___x_1708_);
v___x_1710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1709_);
lean_ctor_set(v___x_1710_, 1, v_a_1509_);
return v___x_1710_;
}
else
{
lean_object* v___x_1711_; uint8_t v___x_1712_; 
v___x_1711_ = l_Lean_Syntax_getArg(v___x_1698_, v___x_1520_);
lean_inc(v___x_1711_);
v___x_1712_ = l_Lean_Syntax_isOfKind(v___x_1711_, v___x_1591_);
if (v___x_1712_ == 0)
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
lean_dec(v___x_1711_);
lean_dec(v___x_1698_);
lean_dec(v___x_1671_);
lean_dec(v___x_1562_);
v___x_1713_ = l_Lean_Syntax_getArg(v___x_1515_, v___x_1514_);
lean_dec(v___x_1515_);
v___x_1714_ = l_Lean_SourceInfo_fromRef(v_a_1508_, v___x_1712_);
v___x_1715_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1716_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1714_, 3);
v___x_1717_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1714_);
lean_ctor_set(v___x_1717_, 1, v___x_1716_);
v___x_1718_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1719_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1714_);
lean_ctor_set(v___x_1719_, 1, v___x_1718_);
v___x_1720_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1721_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1714_);
lean_ctor_set(v___x_1721_, 1, v___x_1720_);
v___x_1722_ = l_Lean_Syntax_node5(v___x_1714_, v___x_1715_, v___x_1717_, v___x_1521_, v___x_1719_, v___x_1713_, v___x_1721_);
v___x_1723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1722_);
lean_ctor_set(v___x_1723_, 1, v_a_1509_);
return v___x_1723_;
}
else
{
lean_object* v___x_1724_; lean_object* v___x_1725_; uint8_t v___x_1726_; 
v___x_1724_ = l_Lean_Syntax_getArg(v___x_1711_, v___x_1520_);
v___x_1725_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__14));
v___x_1726_ = l_Lean_Syntax_matchesIdent(v___x_1724_, v___x_1725_);
lean_dec(v___x_1724_);
if (v___x_1726_ == 0)
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
lean_dec(v___x_1711_);
lean_dec(v___x_1698_);
lean_dec(v___x_1671_);
lean_dec(v___x_1562_);
v___x_1727_ = l_Lean_Syntax_getArg(v___x_1515_, v___x_1514_);
lean_dec(v___x_1515_);
v___x_1728_ = l_Lean_SourceInfo_fromRef(v_a_1508_, v___x_1726_);
v___x_1729_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1730_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1728_, 3);
v___x_1731_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1728_);
lean_ctor_set(v___x_1731_, 1, v___x_1730_);
v___x_1732_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1733_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1728_);
lean_ctor_set(v___x_1733_, 1, v___x_1732_);
v___x_1734_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1735_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1728_);
lean_ctor_set(v___x_1735_, 1, v___x_1734_);
v___x_1736_ = l_Lean_Syntax_node5(v___x_1728_, v___x_1729_, v___x_1731_, v___x_1521_, v___x_1733_, v___x_1727_, v___x_1735_);
v___x_1737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1736_);
lean_ctor_set(v___x_1737_, 1, v_a_1509_);
return v___x_1737_;
}
else
{
lean_object* v___x_1738_; uint8_t v___x_1739_; 
v___x_1738_ = l_Lean_Syntax_getArg(v___x_1711_, v___x_1514_);
lean_dec(v___x_1711_);
v___x_1739_ = l_Lean_Syntax_matchesNull(v___x_1738_, v___x_1520_);
if (v___x_1739_ == 0)
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
lean_dec(v___x_1698_);
lean_dec(v___x_1671_);
lean_dec(v___x_1562_);
v___x_1740_ = l_Lean_Syntax_getArg(v___x_1515_, v___x_1514_);
lean_dec(v___x_1515_);
v___x_1741_ = l_Lean_SourceInfo_fromRef(v_a_1508_, v___x_1739_);
v___x_1742_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1743_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1741_, 3);
v___x_1744_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1741_);
lean_ctor_set(v___x_1744_, 1, v___x_1743_);
v___x_1745_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1746_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1741_);
lean_ctor_set(v___x_1746_, 1, v___x_1745_);
v___x_1747_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1748_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1741_);
lean_ctor_set(v___x_1748_, 1, v___x_1747_);
v___x_1749_ = l_Lean_Syntax_node5(v___x_1741_, v___x_1742_, v___x_1744_, v___x_1521_, v___x_1746_, v___x_1740_, v___x_1748_);
v___x_1750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1749_);
lean_ctor_set(v___x_1750_, 1, v_a_1509_);
return v___x_1750_;
}
else
{
lean_object* v___x_1751_; uint8_t v___x_1752_; 
v___x_1751_ = l_Lean_Syntax_getArg(v___x_1698_, v___x_1514_);
lean_dec(v___x_1698_);
lean_inc(v___x_1751_);
v___x_1752_ = l_Lean_Syntax_matchesNull(v___x_1751_, v___x_1632_);
if (v___x_1752_ == 0)
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
lean_dec(v___x_1751_);
lean_dec(v___x_1671_);
lean_dec(v___x_1562_);
v___x_1753_ = l_Lean_Syntax_getArg(v___x_1515_, v___x_1514_);
lean_dec(v___x_1515_);
v___x_1754_ = l_Lean_SourceInfo_fromRef(v_a_1508_, v___x_1752_);
v___x_1755_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1756_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1754_, 3);
v___x_1757_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1754_);
lean_ctor_set(v___x_1757_, 1, v___x_1756_);
v___x_1758_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1759_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1754_);
lean_ctor_set(v___x_1759_, 1, v___x_1758_);
v___x_1760_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1761_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1754_);
lean_ctor_set(v___x_1761_, 1, v___x_1760_);
v___x_1762_ = l_Lean_Syntax_node5(v___x_1754_, v___x_1755_, v___x_1757_, v___x_1521_, v___x_1759_, v___x_1753_, v___x_1761_);
v___x_1763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
lean_ctor_set(v___x_1763_, 1, v_a_1509_);
return v___x_1763_;
}
else
{
lean_object* v___x_1764_; uint8_t v___x_1765_; 
v___x_1764_ = l_Lean_Syntax_getArg(v___x_1751_, v___x_1520_);
v___x_1765_ = l_Lean_Syntax_matchesNull(v___x_1764_, v___x_1520_);
if (v___x_1765_ == 0)
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
lean_dec(v___x_1751_);
lean_dec(v___x_1671_);
lean_dec(v___x_1562_);
v___x_1766_ = l_Lean_Syntax_getArg(v___x_1515_, v___x_1514_);
lean_dec(v___x_1515_);
v___x_1767_ = l_Lean_SourceInfo_fromRef(v_a_1508_, v___x_1765_);
v___x_1768_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1769_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1767_, 3);
v___x_1770_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1767_);
lean_ctor_set(v___x_1770_, 1, v___x_1769_);
v___x_1771_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1772_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1767_);
lean_ctor_set(v___x_1772_, 1, v___x_1771_);
v___x_1773_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1774_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1767_);
lean_ctor_set(v___x_1774_, 1, v___x_1773_);
v___x_1775_ = l_Lean_Syntax_node5(v___x_1767_, v___x_1768_, v___x_1770_, v___x_1521_, v___x_1772_, v___x_1766_, v___x_1774_);
v___x_1776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1775_);
lean_ctor_set(v___x_1776_, 1, v_a_1509_);
return v___x_1776_;
}
else
{
lean_object* v___x_1777_; uint8_t v___x_1778_; 
v___x_1777_ = l_Lean_Syntax_getArg(v___x_1751_, v___x_1514_);
v___x_1778_ = l_Lean_Syntax_matchesNull(v___x_1777_, v___x_1520_);
if (v___x_1778_ == 0)
{
lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
lean_dec(v___x_1751_);
lean_dec(v___x_1671_);
lean_dec(v___x_1562_);
v___x_1779_ = l_Lean_Syntax_getArg(v___x_1515_, v___x_1514_);
lean_dec(v___x_1515_);
v___x_1780_ = l_Lean_SourceInfo_fromRef(v_a_1508_, v___x_1778_);
v___x_1781_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1782_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1780_, 3);
v___x_1783_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1780_);
lean_ctor_set(v___x_1783_, 1, v___x_1782_);
v___x_1784_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1785_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1780_);
lean_ctor_set(v___x_1785_, 1, v___x_1784_);
v___x_1786_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1787_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1780_);
lean_ctor_set(v___x_1787_, 1, v___x_1786_);
v___x_1788_ = l_Lean_Syntax_node5(v___x_1780_, v___x_1781_, v___x_1783_, v___x_1521_, v___x_1785_, v___x_1779_, v___x_1787_);
v___x_1789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1788_);
lean_ctor_set(v___x_1789_, 1, v_a_1509_);
return v___x_1789_;
}
else
{
lean_object* v___x_1790_; uint8_t v___x_1791_; 
v___x_1790_ = l_Lean_Syntax_getArg(v___x_1751_, v___x_1516_);
lean_dec(v___x_1751_);
lean_inc(v___x_1790_);
v___x_1791_ = l_Lean_Syntax_isOfKind(v___x_1790_, v___x_1672_);
if (v___x_1791_ == 0)
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
lean_dec(v___x_1790_);
lean_dec(v___x_1671_);
lean_dec(v___x_1562_);
v___x_1792_ = l_Lean_Syntax_getArg(v___x_1515_, v___x_1514_);
lean_dec(v___x_1515_);
v___x_1793_ = l_Lean_SourceInfo_fromRef(v_a_1508_, v___x_1791_);
v___x_1794_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1795_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1793_, 3);
v___x_1796_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1793_);
lean_ctor_set(v___x_1796_, 1, v___x_1795_);
v___x_1797_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1798_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1793_);
lean_ctor_set(v___x_1798_, 1, v___x_1797_);
v___x_1799_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1800_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1793_);
lean_ctor_set(v___x_1800_, 1, v___x_1799_);
v___x_1801_ = l_Lean_Syntax_node5(v___x_1793_, v___x_1794_, v___x_1796_, v___x_1521_, v___x_1798_, v___x_1792_, v___x_1800_);
v___x_1802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1801_);
lean_ctor_set(v___x_1802_, 1, v_a_1509_);
return v___x_1802_;
}
else
{
lean_object* v___x_1803_; uint8_t v___x_1804_; 
v___x_1803_ = l_Lean_Syntax_getArg(v___x_1790_, v___x_1514_);
v___x_1804_ = l_Lean_Syntax_matchesNull(v___x_1803_, v___x_1520_);
if (v___x_1804_ == 0)
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
lean_dec(v___x_1790_);
lean_dec(v___x_1671_);
lean_dec(v___x_1562_);
v___x_1805_ = l_Lean_Syntax_getArg(v___x_1515_, v___x_1514_);
lean_dec(v___x_1515_);
v___x_1806_ = l_Lean_SourceInfo_fromRef(v_a_1508_, v___x_1804_);
v___x_1807_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1808_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1806_, 3);
v___x_1809_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1806_);
lean_ctor_set(v___x_1809_, 1, v___x_1808_);
v___x_1810_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1811_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1806_);
lean_ctor_set(v___x_1811_, 1, v___x_1810_);
v___x_1812_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1813_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1806_);
lean_ctor_set(v___x_1813_, 1, v___x_1812_);
v___x_1814_ = l_Lean_Syntax_node5(v___x_1806_, v___x_1807_, v___x_1809_, v___x_1521_, v___x_1811_, v___x_1805_, v___x_1813_);
v___x_1815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1814_);
lean_ctor_set(v___x_1815_, 1, v_a_1509_);
return v___x_1815_;
}
else
{
lean_object* v___x_1816_; lean_object* v___x_1817_; uint8_t v___x_1818_; 
v___x_1816_ = lean_unsigned_to_nat(4u);
v___x_1817_ = l_Lean_Syntax_getArg(v___x_1562_, v___x_1816_);
lean_dec(v___x_1562_);
lean_inc(v___x_1817_);
v___x_1818_ = l_Lean_Syntax_isOfKind(v___x_1817_, v___x_1577_);
if (v___x_1818_ == 0)
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
lean_dec(v___x_1817_);
lean_dec(v___x_1790_);
lean_dec(v___x_1671_);
v___x_1819_ = l_Lean_Syntax_getArg(v___x_1515_, v___x_1514_);
lean_dec(v___x_1515_);
v___x_1820_ = l_Lean_SourceInfo_fromRef(v_a_1508_, v___x_1818_);
v___x_1821_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1822_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1820_, 3);
v___x_1823_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1820_);
lean_ctor_set(v___x_1823_, 1, v___x_1822_);
v___x_1824_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1825_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1820_);
lean_ctor_set(v___x_1825_, 1, v___x_1824_);
v___x_1826_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1827_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1820_);
lean_ctor_set(v___x_1827_, 1, v___x_1826_);
v___x_1828_ = l_Lean_Syntax_node5(v___x_1820_, v___x_1821_, v___x_1823_, v___x_1521_, v___x_1825_, v___x_1819_, v___x_1827_);
v___x_1829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1828_);
lean_ctor_set(v___x_1829_, 1, v_a_1509_);
return v___x_1829_;
}
else
{
lean_object* v___x_1830_; uint8_t v___x_1831_; 
v___x_1830_ = l_Lean_Syntax_getArg(v___x_1817_, v___x_1520_);
lean_inc(v___x_1830_);
v___x_1831_ = l_Lean_Syntax_isOfKind(v___x_1830_, v___x_1591_);
if (v___x_1831_ == 0)
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
lean_dec(v___x_1830_);
lean_dec(v___x_1817_);
lean_dec(v___x_1790_);
lean_dec(v___x_1671_);
v___x_1832_ = l_Lean_Syntax_getArg(v___x_1515_, v___x_1514_);
lean_dec(v___x_1515_);
v___x_1833_ = l_Lean_SourceInfo_fromRef(v_a_1508_, v___x_1831_);
v___x_1834_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1835_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1833_, 3);
v___x_1836_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1833_);
lean_ctor_set(v___x_1836_, 1, v___x_1835_);
v___x_1837_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1838_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1833_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
v___x_1839_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1840_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1833_);
lean_ctor_set(v___x_1840_, 1, v___x_1839_);
v___x_1841_ = l_Lean_Syntax_node5(v___x_1833_, v___x_1834_, v___x_1836_, v___x_1521_, v___x_1838_, v___x_1832_, v___x_1840_);
v___x_1842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
lean_ctor_set(v___x_1842_, 1, v_a_1509_);
return v___x_1842_;
}
else
{
lean_object* v___x_1843_; lean_object* v___x_1844_; uint8_t v___x_1845_; 
v___x_1843_ = l_Lean_Syntax_getArg(v___x_1830_, v___x_1520_);
v___x_1844_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__16));
v___x_1845_ = l_Lean_Syntax_matchesIdent(v___x_1843_, v___x_1844_);
lean_dec(v___x_1843_);
if (v___x_1845_ == 0)
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
lean_dec(v___x_1830_);
lean_dec(v___x_1817_);
lean_dec(v___x_1790_);
lean_dec(v___x_1671_);
v___x_1846_ = l_Lean_Syntax_getArg(v___x_1515_, v___x_1514_);
lean_dec(v___x_1515_);
v___x_1847_ = l_Lean_SourceInfo_fromRef(v_a_1508_, v___x_1845_);
v___x_1848_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1849_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1847_, 3);
v___x_1850_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1847_);
lean_ctor_set(v___x_1850_, 1, v___x_1849_);
v___x_1851_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1852_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1847_);
lean_ctor_set(v___x_1852_, 1, v___x_1851_);
v___x_1853_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1854_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1847_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
v___x_1855_ = l_Lean_Syntax_node5(v___x_1847_, v___x_1848_, v___x_1850_, v___x_1521_, v___x_1852_, v___x_1846_, v___x_1854_);
v___x_1856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
lean_ctor_set(v___x_1856_, 1, v_a_1509_);
return v___x_1856_;
}
else
{
lean_object* v___x_1857_; uint8_t v___x_1858_; 
v___x_1857_ = l_Lean_Syntax_getArg(v___x_1830_, v___x_1514_);
lean_dec(v___x_1830_);
v___x_1858_ = l_Lean_Syntax_matchesNull(v___x_1857_, v___x_1520_);
if (v___x_1858_ == 0)
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
lean_dec(v___x_1817_);
lean_dec(v___x_1790_);
lean_dec(v___x_1671_);
v___x_1859_ = l_Lean_Syntax_getArg(v___x_1515_, v___x_1514_);
lean_dec(v___x_1515_);
v___x_1860_ = l_Lean_SourceInfo_fromRef(v_a_1508_, v___x_1858_);
v___x_1861_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1862_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1860_, 3);
v___x_1863_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1860_);
lean_ctor_set(v___x_1863_, 1, v___x_1862_);
v___x_1864_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1865_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1860_);
lean_ctor_set(v___x_1865_, 1, v___x_1864_);
v___x_1866_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1867_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1860_);
lean_ctor_set(v___x_1867_, 1, v___x_1866_);
v___x_1868_ = l_Lean_Syntax_node5(v___x_1860_, v___x_1861_, v___x_1863_, v___x_1521_, v___x_1865_, v___x_1859_, v___x_1867_);
v___x_1869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1868_);
lean_ctor_set(v___x_1869_, 1, v_a_1509_);
return v___x_1869_;
}
else
{
lean_object* v___x_1870_; uint8_t v___x_1871_; 
v___x_1870_ = l_Lean_Syntax_getArg(v___x_1817_, v___x_1514_);
lean_dec(v___x_1817_);
lean_inc(v___x_1870_);
v___x_1871_ = l_Lean_Syntax_matchesNull(v___x_1870_, v___x_1632_);
if (v___x_1871_ == 0)
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
lean_dec(v___x_1870_);
lean_dec(v___x_1790_);
lean_dec(v___x_1671_);
v___x_1872_ = l_Lean_Syntax_getArg(v___x_1515_, v___x_1514_);
lean_dec(v___x_1515_);
v___x_1873_ = l_Lean_SourceInfo_fromRef(v_a_1508_, v___x_1871_);
v___x_1874_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1875_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1873_, 3);
v___x_1876_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1873_);
lean_ctor_set(v___x_1876_, 1, v___x_1875_);
v___x_1877_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1878_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1873_);
lean_ctor_set(v___x_1878_, 1, v___x_1877_);
v___x_1879_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1880_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1873_);
lean_ctor_set(v___x_1880_, 1, v___x_1879_);
v___x_1881_ = l_Lean_Syntax_node5(v___x_1873_, v___x_1874_, v___x_1876_, v___x_1521_, v___x_1878_, v___x_1872_, v___x_1880_);
v___x_1882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1881_);
lean_ctor_set(v___x_1882_, 1, v_a_1509_);
return v___x_1882_;
}
else
{
lean_object* v___x_1883_; uint8_t v___x_1884_; 
v___x_1883_ = l_Lean_Syntax_getArg(v___x_1870_, v___x_1520_);
v___x_1884_ = l_Lean_Syntax_matchesNull(v___x_1883_, v___x_1520_);
if (v___x_1884_ == 0)
{
lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
lean_dec(v___x_1870_);
lean_dec(v___x_1790_);
lean_dec(v___x_1671_);
v___x_1885_ = l_Lean_Syntax_getArg(v___x_1515_, v___x_1514_);
lean_dec(v___x_1515_);
v___x_1886_ = l_Lean_SourceInfo_fromRef(v_a_1508_, v___x_1884_);
v___x_1887_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1888_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1886_, 3);
v___x_1889_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1886_);
lean_ctor_set(v___x_1889_, 1, v___x_1888_);
v___x_1890_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1891_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1886_);
lean_ctor_set(v___x_1891_, 1, v___x_1890_);
v___x_1892_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1893_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1886_);
lean_ctor_set(v___x_1893_, 1, v___x_1892_);
v___x_1894_ = l_Lean_Syntax_node5(v___x_1886_, v___x_1887_, v___x_1889_, v___x_1521_, v___x_1891_, v___x_1885_, v___x_1893_);
v___x_1895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1894_);
lean_ctor_set(v___x_1895_, 1, v_a_1509_);
return v___x_1895_;
}
else
{
lean_object* v___x_1896_; uint8_t v___x_1897_; 
v___x_1896_ = l_Lean_Syntax_getArg(v___x_1870_, v___x_1514_);
v___x_1897_ = l_Lean_Syntax_matchesNull(v___x_1896_, v___x_1520_);
if (v___x_1897_ == 0)
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
lean_dec(v___x_1870_);
lean_dec(v___x_1790_);
lean_dec(v___x_1671_);
v___x_1898_ = l_Lean_Syntax_getArg(v___x_1515_, v___x_1514_);
lean_dec(v___x_1515_);
v___x_1899_ = l_Lean_SourceInfo_fromRef(v_a_1508_, v___x_1897_);
v___x_1900_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1901_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1899_, 3);
v___x_1902_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1899_);
lean_ctor_set(v___x_1902_, 1, v___x_1901_);
v___x_1903_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1904_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1899_);
lean_ctor_set(v___x_1904_, 1, v___x_1903_);
v___x_1905_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1906_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1899_);
lean_ctor_set(v___x_1906_, 1, v___x_1905_);
v___x_1907_ = l_Lean_Syntax_node5(v___x_1899_, v___x_1900_, v___x_1902_, v___x_1521_, v___x_1904_, v___x_1898_, v___x_1906_);
v___x_1908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1907_);
lean_ctor_set(v___x_1908_, 1, v_a_1509_);
return v___x_1908_;
}
else
{
lean_object* v___x_1909_; uint8_t v___x_1910_; 
v___x_1909_ = l_Lean_Syntax_getArg(v___x_1870_, v___x_1516_);
lean_dec(v___x_1870_);
lean_inc(v___x_1909_);
v___x_1910_ = l_Lean_Syntax_isOfKind(v___x_1909_, v___x_1672_);
if (v___x_1910_ == 0)
{
lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
lean_dec(v___x_1909_);
lean_dec(v___x_1790_);
lean_dec(v___x_1671_);
v___x_1911_ = l_Lean_Syntax_getArg(v___x_1515_, v___x_1514_);
lean_dec(v___x_1515_);
v___x_1912_ = l_Lean_SourceInfo_fromRef(v_a_1508_, v___x_1910_);
v___x_1913_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1914_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1912_, 3);
v___x_1915_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1912_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
v___x_1916_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1917_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1912_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
v___x_1918_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1919_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1912_);
lean_ctor_set(v___x_1919_, 1, v___x_1918_);
v___x_1920_ = l_Lean_Syntax_node5(v___x_1912_, v___x_1913_, v___x_1915_, v___x_1521_, v___x_1917_, v___x_1911_, v___x_1919_);
v___x_1921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1920_);
lean_ctor_set(v___x_1921_, 1, v_a_1509_);
return v___x_1921_;
}
else
{
lean_object* v___x_1922_; uint8_t v___x_1923_; 
v___x_1922_ = l_Lean_Syntax_getArg(v___x_1909_, v___x_1514_);
v___x_1923_ = l_Lean_Syntax_matchesNull(v___x_1922_, v___x_1520_);
if (v___x_1923_ == 0)
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
lean_dec(v___x_1909_);
lean_dec(v___x_1790_);
lean_dec(v___x_1671_);
v___x_1924_ = l_Lean_Syntax_getArg(v___x_1515_, v___x_1514_);
lean_dec(v___x_1515_);
v___x_1925_ = l_Lean_SourceInfo_fromRef(v_a_1508_, v___x_1923_);
v___x_1926_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1927_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1925_, 3);
v___x_1928_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1925_);
lean_ctor_set(v___x_1928_, 1, v___x_1927_);
v___x_1929_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1930_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1925_);
lean_ctor_set(v___x_1930_, 1, v___x_1929_);
v___x_1931_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1932_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1925_);
lean_ctor_set(v___x_1932_, 1, v___x_1931_);
v___x_1933_ = l_Lean_Syntax_node5(v___x_1925_, v___x_1926_, v___x_1928_, v___x_1521_, v___x_1930_, v___x_1924_, v___x_1932_);
v___x_1934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1933_);
lean_ctor_set(v___x_1934_, 1, v_a_1509_);
return v___x_1934_;
}
else
{
lean_object* v___x_1935_; lean_object* v___x_1936_; uint8_t v___x_1937_; 
v___x_1935_ = l_Lean_Syntax_getArg(v___x_1521_, v___x_1632_);
v___x_1936_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__18));
lean_inc(v___x_1935_);
v___x_1937_ = l_Lean_Syntax_isOfKind(v___x_1935_, v___x_1936_);
if (v___x_1937_ == 0)
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
lean_dec(v___x_1935_);
lean_dec(v___x_1909_);
lean_dec(v___x_1790_);
lean_dec(v___x_1671_);
v___x_1938_ = l_Lean_Syntax_getArg(v___x_1515_, v___x_1514_);
lean_dec(v___x_1515_);
v___x_1939_ = l_Lean_SourceInfo_fromRef(v_a_1508_, v___x_1937_);
v___x_1940_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1941_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1939_, 3);
v___x_1942_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1939_);
lean_ctor_set(v___x_1942_, 1, v___x_1941_);
v___x_1943_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1944_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1939_);
lean_ctor_set(v___x_1944_, 1, v___x_1943_);
v___x_1945_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1946_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1946_, 0, v___x_1939_);
lean_ctor_set(v___x_1946_, 1, v___x_1945_);
v___x_1947_ = l_Lean_Syntax_node5(v___x_1939_, v___x_1940_, v___x_1942_, v___x_1521_, v___x_1944_, v___x_1938_, v___x_1946_);
v___x_1948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1947_);
lean_ctor_set(v___x_1948_, 1, v_a_1509_);
return v___x_1948_;
}
else
{
lean_object* v___x_1949_; uint8_t v___x_1950_; 
v___x_1949_ = l_Lean_Syntax_getArg(v___x_1935_, v___x_1520_);
lean_dec(v___x_1935_);
v___x_1950_ = l_Lean_Syntax_matchesNull(v___x_1949_, v___x_1520_);
if (v___x_1950_ == 0)
{
lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
lean_dec(v___x_1909_);
lean_dec(v___x_1790_);
lean_dec(v___x_1671_);
v___x_1951_ = l_Lean_Syntax_getArg(v___x_1515_, v___x_1514_);
lean_dec(v___x_1515_);
v___x_1952_ = l_Lean_SourceInfo_fromRef(v_a_1508_, v___x_1950_);
v___x_1953_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1954_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1952_, 3);
v___x_1955_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1952_);
lean_ctor_set(v___x_1955_, 1, v___x_1954_);
v___x_1956_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1957_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1952_);
lean_ctor_set(v___x_1957_, 1, v___x_1956_);
v___x_1958_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1959_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1959_, 0, v___x_1952_);
lean_ctor_set(v___x_1959_, 1, v___x_1958_);
v___x_1960_ = l_Lean_Syntax_node5(v___x_1952_, v___x_1953_, v___x_1955_, v___x_1521_, v___x_1957_, v___x_1951_, v___x_1959_);
v___x_1961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1960_);
lean_ctor_set(v___x_1961_, 1, v_a_1509_);
return v___x_1961_;
}
else
{
lean_object* v___x_1962_; uint8_t v___x_1963_; 
v___x_1962_ = l_Lean_Syntax_getArg(v___x_1521_, v___x_1816_);
v___x_1963_ = l_Lean_Syntax_matchesNull(v___x_1962_, v___x_1520_);
if (v___x_1963_ == 0)
{
lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
lean_dec(v___x_1909_);
lean_dec(v___x_1790_);
lean_dec(v___x_1671_);
v___x_1964_ = l_Lean_Syntax_getArg(v___x_1515_, v___x_1514_);
lean_dec(v___x_1515_);
v___x_1965_ = l_Lean_SourceInfo_fromRef(v_a_1508_, v___x_1963_);
v___x_1966_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1967_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1965_, 3);
v___x_1968_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1965_);
lean_ctor_set(v___x_1968_, 1, v___x_1967_);
v___x_1969_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1970_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1965_);
lean_ctor_set(v___x_1970_, 1, v___x_1969_);
v___x_1971_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1972_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1972_, 0, v___x_1965_);
lean_ctor_set(v___x_1972_, 1, v___x_1971_);
v___x_1973_ = l_Lean_Syntax_node5(v___x_1965_, v___x_1966_, v___x_1968_, v___x_1521_, v___x_1970_, v___x_1964_, v___x_1972_);
v___x_1974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1973_);
lean_ctor_set(v___x_1974_, 1, v_a_1509_);
return v___x_1974_;
}
else
{
lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; uint8_t v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; 
lean_dec(v___x_1521_);
v___x_1975_ = l_Lean_Syntax_getArg(v___x_1671_, v___x_1516_);
lean_dec(v___x_1671_);
v___x_1976_ = l_Lean_Syntax_getArg(v___x_1790_, v___x_1516_);
lean_dec(v___x_1790_);
v___x_1977_ = l_Lean_Syntax_getArg(v___x_1909_, v___x_1516_);
lean_dec(v___x_1909_);
v___x_1978_ = l_Lean_Syntax_getArg(v___x_1515_, v___x_1514_);
lean_dec(v___x_1515_);
v___x_1979_ = 0;
v___x_1980_ = l_Lean_SourceInfo_fromRef(v_a_1508_, v___x_1979_);
v___x_1981_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__1));
v___x_1982_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1980_, 7);
v___x_1983_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1980_);
lean_ctor_set(v___x_1983_, 1, v___x_1982_);
v___x_1984_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1985_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1980_);
lean_ctor_set(v___x_1985_, 1, v___x_1984_);
v___x_1986_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__20));
v___x_1987_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__21));
v___x_1988_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1980_);
lean_ctor_set(v___x_1988_, 1, v___x_1987_);
v___x_1989_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__14));
lean_inc_ref_n(v___x_1985_, 2);
v___x_1990_ = l_Lean_Syntax_node3(v___x_1980_, v___x_1989_, v___x_1976_, v___x_1985_, v___x_1977_);
v___x_1991_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__22));
v___x_1992_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1980_);
lean_ctor_set(v___x_1992_, 1, v___x_1991_);
v___x_1993_ = l_Lean_Syntax_node3(v___x_1980_, v___x_1986_, v___x_1988_, v___x_1990_, v___x_1992_);
v___x_1994_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1995_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1980_);
lean_ctor_set(v___x_1995_, 1, v___x_1994_);
v___x_1996_ = l_Lean_Syntax_node7(v___x_1980_, v___x_1981_, v___x_1983_, v___x_1975_, v___x_1985_, v___x_1993_, v___x_1985_, v___x_1978_, v___x_1995_);
v___x_1997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1996_);
lean_ctor_set(v___x_1997_, 1, v_a_1509_);
return v___x_1997_;
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_unexpandDenote___boxed(lean_object* v_x_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l_Std_Sat_AIG_unexpandDenote(v_x_1998_, v_a_1999_, v_a_2000_);
lean_dec(v_a_1999_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGate___redArg(lean_object* v_aig_2002_, lean_object* v_input_2003_){
_start:
{
lean_object* v_lhs_2004_; lean_object* v_rhs_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2043_; 
v_lhs_2004_ = lean_ctor_get(v_input_2003_, 0);
v_rhs_2005_ = lean_ctor_get(v_input_2003_, 1);
v_isSharedCheck_2043_ = !lean_is_exclusive(v_input_2003_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2007_ = v_input_2003_;
v_isShared_2008_ = v_isSharedCheck_2043_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_rhs_2005_);
lean_inc(v_lhs_2004_);
lean_dec(v_input_2003_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2043_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v_decls_2009_; lean_object* v_cache_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2042_; 
v_decls_2009_ = lean_ctor_get(v_aig_2002_, 0);
v_cache_2010_ = lean_ctor_get(v_aig_2002_, 1);
v_isSharedCheck_2042_ = !lean_is_exclusive(v_aig_2002_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2012_ = v_aig_2002_;
v_isShared_2013_ = v_isSharedCheck_2042_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_cache_2010_);
lean_inc(v_decls_2009_);
lean_dec(v_aig_2002_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2042_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v_gate_2014_; uint8_t v_invert_2015_; lean_object* v_gate_2016_; uint8_t v_invert_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2041_; 
v_gate_2014_ = lean_ctor_get(v_lhs_2004_, 0);
lean_inc(v_gate_2014_);
v_invert_2015_ = lean_ctor_get_uint8(v_lhs_2004_, sizeof(void*)*1);
lean_dec_ref(v_lhs_2004_);
v_gate_2016_ = lean_ctor_get(v_rhs_2005_, 0);
v_invert_2017_ = lean_ctor_get_uint8(v_rhs_2005_, sizeof(void*)*1);
v_isSharedCheck_2041_ = !lean_is_exclusive(v_rhs_2005_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2019_ = v_rhs_2005_;
v_isShared_2020_ = v_isSharedCheck_2041_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_gate_2016_);
lean_dec(v_rhs_2005_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2041_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v_g_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2030_; 
v_g_2021_ = lean_array_get_size(v_decls_2009_);
v___x_2022_ = lean_unsigned_to_nat(2u);
v___x_2023_ = lean_nat_mul(v_gate_2014_, v___x_2022_);
lean_dec(v_gate_2014_);
v___x_2024_ = l_Bool_toNat(v_invert_2015_);
v___x_2025_ = lean_nat_lor(v___x_2023_, v___x_2024_);
lean_dec(v___x_2024_);
lean_dec(v___x_2023_);
v___x_2026_ = lean_nat_mul(v_gate_2016_, v___x_2022_);
lean_dec(v_gate_2016_);
v___x_2027_ = l_Bool_toNat(v_invert_2017_);
v___x_2028_ = lean_nat_lor(v___x_2026_, v___x_2027_);
lean_dec(v___x_2027_);
lean_dec(v___x_2026_);
if (v_isShared_2008_ == 0)
{
lean_ctor_set_tag(v___x_2007_, 2);
lean_ctor_set(v___x_2007_, 1, v___x_2028_);
lean_ctor_set(v___x_2007_, 0, v___x_2025_);
v___x_2030_ = v___x_2007_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2025_);
lean_ctor_set(v_reuseFailAlloc_2040_, 1, v___x_2028_);
v___x_2030_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
lean_object* v_decls_2031_; lean_object* v___x_2033_; 
v_decls_2031_ = lean_array_push(v_decls_2009_, v___x_2030_);
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 0, v_decls_2031_);
v___x_2033_ = v___x_2012_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_decls_2031_);
lean_ctor_set(v_reuseFailAlloc_2039_, 1, v_cache_2010_);
v___x_2033_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
uint8_t v___x_2034_; lean_object* v___x_2036_; 
v___x_2034_ = 0;
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 0, v_g_2021_);
v___x_2036_ = v___x_2019_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_g_2021_);
v___x_2036_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
lean_object* v___x_2037_; 
lean_ctor_set_uint8(v___x_2036_, sizeof(void*)*1, v___x_2034_);
v___x_2037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2033_);
lean_ctor_set(v___x_2037_, 1, v___x_2036_);
return v___x_2037_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGate(lean_object* v_00_u03b1_2044_, lean_object* v_inst_2045_, lean_object* v_inst_2046_, lean_object* v_aig_2047_, lean_object* v_input_2048_){
_start:
{
lean_object* v___x_2049_; 
v___x_2049_ = l_Std_Sat_AIG_mkGate___redArg(v_aig_2047_, v_input_2048_);
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGate___boxed(lean_object* v_00_u03b1_2050_, lean_object* v_inst_2051_, lean_object* v_inst_2052_, lean_object* v_aig_2053_, lean_object* v_input_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l_Std_Sat_AIG_mkGate(v_00_u03b1_2050_, v_inst_2051_, v_inst_2052_, v_aig_2053_, v_input_2054_);
lean_dec_ref(v_inst_2052_);
lean_dec_ref(v_inst_2051_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtom___redArg(lean_object* v_aig_2056_, lean_object* v_n_2057_){
_start:
{
lean_object* v_decls_2058_; lean_object* v_cache_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2072_; 
v_decls_2058_ = lean_ctor_get(v_aig_2056_, 0);
v_cache_2059_ = lean_ctor_get(v_aig_2056_, 1);
v_isSharedCheck_2072_ = !lean_is_exclusive(v_aig_2056_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2061_ = v_aig_2056_;
v_isShared_2062_ = v_isSharedCheck_2072_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_cache_2059_);
lean_inc(v_decls_2058_);
lean_dec(v_aig_2056_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2072_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v_g_2063_; lean_object* v___x_2064_; lean_object* v_decls_2065_; lean_object* v___x_2067_; 
v_g_2063_ = lean_array_get_size(v_decls_2058_);
v___x_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2064_, 0, v_n_2057_);
v_decls_2065_ = lean_array_push(v_decls_2058_, v___x_2064_);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 0, v_decls_2065_);
v___x_2067_ = v___x_2061_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_decls_2065_);
lean_ctor_set(v_reuseFailAlloc_2071_, 1, v_cache_2059_);
v___x_2067_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
uint8_t v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2068_ = 0;
v___x_2069_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2069_, 0, v_g_2063_);
lean_ctor_set_uint8(v___x_2069_, sizeof(void*)*1, v___x_2068_);
v___x_2070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2067_);
lean_ctor_set(v___x_2070_, 1, v___x_2069_);
return v___x_2070_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtom(lean_object* v_00_u03b1_2073_, lean_object* v_inst_2074_, lean_object* v_inst_2075_, lean_object* v_aig_2076_, lean_object* v_n_2077_){
_start:
{
lean_object* v___x_2078_; 
v___x_2078_ = l_Std_Sat_AIG_mkAtom___redArg(v_aig_2076_, v_n_2077_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtom___boxed(lean_object* v_00_u03b1_2079_, lean_object* v_inst_2080_, lean_object* v_inst_2081_, lean_object* v_aig_2082_, lean_object* v_n_2083_){
_start:
{
lean_object* v_res_2084_; 
v_res_2084_ = l_Std_Sat_AIG_mkAtom(v_00_u03b1_2079_, v_inst_2080_, v_inst_2081_, v_aig_2082_, v_n_2083_);
lean_dec_ref(v_inst_2081_);
lean_dec_ref(v_inst_2080_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConst___redArg(lean_object* v_aig_2085_, uint8_t v_val_2086_){
_start:
{
lean_object* v_decls_2087_; lean_object* v_cache_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2100_; 
v_decls_2087_ = lean_ctor_get(v_aig_2085_, 0);
v_cache_2088_ = lean_ctor_get(v_aig_2085_, 1);
v_isSharedCheck_2100_ = !lean_is_exclusive(v_aig_2085_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2090_ = v_aig_2085_;
v_isShared_2091_ = v_isSharedCheck_2100_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_cache_2088_);
lean_inc(v_decls_2087_);
lean_dec(v_aig_2085_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2100_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v_g_2092_; lean_object* v___x_2093_; lean_object* v_decls_2094_; lean_object* v___x_2096_; 
v_g_2092_ = lean_array_get_size(v_decls_2087_);
v___x_2093_ = lean_box(0);
v_decls_2094_ = lean_array_push(v_decls_2087_, v___x_2093_);
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 0, v_decls_2094_);
v___x_2096_ = v___x_2090_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_decls_2094_);
lean_ctor_set(v_reuseFailAlloc_2099_, 1, v_cache_2088_);
v___x_2096_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2097_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2097_, 0, v_g_2092_);
lean_ctor_set_uint8(v___x_2097_, sizeof(void*)*1, v_val_2086_);
v___x_2098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2096_);
lean_ctor_set(v___x_2098_, 1, v___x_2097_);
return v___x_2098_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConst___redArg___boxed(lean_object* v_aig_2101_, lean_object* v_val_2102_){
_start:
{
uint8_t v_val_boxed_2103_; lean_object* v_res_2104_; 
v_val_boxed_2103_ = lean_unbox(v_val_2102_);
v_res_2104_ = l_Std_Sat_AIG_mkConst___redArg(v_aig_2101_, v_val_boxed_2103_);
return v_res_2104_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConst(lean_object* v_00_u03b1_2105_, lean_object* v_inst_2106_, lean_object* v_inst_2107_, lean_object* v_aig_2108_, uint8_t v_val_2109_){
_start:
{
lean_object* v___x_2110_; 
v___x_2110_ = l_Std_Sat_AIG_mkConst___redArg(v_aig_2108_, v_val_2109_);
return v___x_2110_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConst___boxed(lean_object* v_00_u03b1_2111_, lean_object* v_inst_2112_, lean_object* v_inst_2113_, lean_object* v_aig_2114_, lean_object* v_val_2115_){
_start:
{
uint8_t v_val_boxed_2116_; lean_object* v_res_2117_; 
v_val_boxed_2116_ = lean_unbox(v_val_2115_);
v_res_2117_ = l_Std_Sat_AIG_mkConst(v_00_u03b1_2111_, v_inst_2112_, v_inst_2113_, v_aig_2114_, v_val_boxed_2116_);
lean_dec_ref(v_inst_2113_);
lean_dec_ref(v_inst_2112_);
return v_res_2117_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_isConstant___redArg(lean_object* v_aig_2118_, lean_object* v_ref_2119_, uint8_t v_b_2120_){
_start:
{
lean_object* v_gate_2121_; uint8_t v_invert_2122_; lean_object* v_decls_2123_; lean_object* v_decl_2124_; uint8_t v___y_2126_; 
v_gate_2121_ = lean_ctor_get(v_ref_2119_, 0);
v_invert_2122_ = lean_ctor_get_uint8(v_ref_2119_, sizeof(void*)*1);
v_decls_2123_ = lean_ctor_get(v_aig_2118_, 0);
v_decl_2124_ = lean_array_fget_borrowed(v_decls_2123_, v_gate_2121_);
if (v_b_2120_ == 0)
{
if (v_invert_2122_ == 0)
{
uint8_t v___x_2128_; 
v___x_2128_ = 1;
v___y_2126_ = v___x_2128_;
goto v___jp_2125_;
}
else
{
v___y_2126_ = v_b_2120_;
goto v___jp_2125_;
}
}
else
{
v___y_2126_ = v_invert_2122_;
goto v___jp_2125_;
}
v___jp_2125_:
{
if (lean_obj_tag(v_decl_2124_) == 0)
{
return v___y_2126_;
}
else
{
uint8_t v___x_2127_; 
v___x_2127_ = 0;
return v___x_2127_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_isConstant___redArg___boxed(lean_object* v_aig_2129_, lean_object* v_ref_2130_, lean_object* v_b_2131_){
_start:
{
uint8_t v_b_boxed_2132_; uint8_t v_res_2133_; lean_object* v_r_2134_; 
v_b_boxed_2132_ = lean_unbox(v_b_2131_);
v_res_2133_ = l_Std_Sat_AIG_isConstant___redArg(v_aig_2129_, v_ref_2130_, v_b_boxed_2132_);
lean_dec_ref(v_ref_2130_);
lean_dec_ref(v_aig_2129_);
v_r_2134_ = lean_box(v_res_2133_);
return v_r_2134_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_isConstant(lean_object* v_00_u03b1_2135_, lean_object* v_inst_2136_, lean_object* v_inst_2137_, lean_object* v_aig_2138_, lean_object* v_ref_2139_, uint8_t v_b_2140_){
_start:
{
uint8_t v___x_2141_; 
v___x_2141_ = l_Std_Sat_AIG_isConstant___redArg(v_aig_2138_, v_ref_2139_, v_b_2140_);
return v___x_2141_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_isConstant___boxed(lean_object* v_00_u03b1_2142_, lean_object* v_inst_2143_, lean_object* v_inst_2144_, lean_object* v_aig_2145_, lean_object* v_ref_2146_, lean_object* v_b_2147_){
_start:
{
uint8_t v_b_boxed_2148_; uint8_t v_res_2149_; lean_object* v_r_2150_; 
v_b_boxed_2148_ = lean_unbox(v_b_2147_);
v_res_2149_ = l_Std_Sat_AIG_isConstant(v_00_u03b1_2142_, v_inst_2143_, v_inst_2144_, v_aig_2145_, v_ref_2146_, v_b_boxed_2148_);
lean_dec_ref(v_ref_2146_);
lean_dec_ref(v_aig_2145_);
lean_dec_ref(v_inst_2144_);
lean_dec_ref(v_inst_2143_);
v_r_2150_ = lean_box(v_res_2149_);
return v_r_2150_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___redArg(lean_object* v_aig_2151_, lean_object* v_ref_2152_){
_start:
{
lean_object* v_gate_2153_; uint8_t v_invert_2154_; lean_object* v_decls_2155_; lean_object* v_decl_2156_; 
v_gate_2153_ = lean_ctor_get(v_ref_2152_, 0);
v_invert_2154_ = lean_ctor_get_uint8(v_ref_2152_, sizeof(void*)*1);
v_decls_2155_ = lean_ctor_get(v_aig_2151_, 0);
v_decl_2156_ = lean_array_fget_borrowed(v_decls_2155_, v_gate_2153_);
if (lean_obj_tag(v_decl_2156_) == 0)
{
lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2157_ = lean_box(v_invert_2154_);
v___x_2158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2157_);
return v___x_2158_;
}
else
{
lean_object* v___x_2159_; 
v___x_2159_ = lean_box(0);
return v___x_2159_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___redArg___boxed(lean_object* v_aig_2160_, lean_object* v_ref_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l_Std_Sat_AIG_getConstant___redArg(v_aig_2160_, v_ref_2161_);
lean_dec_ref(v_ref_2161_);
lean_dec_ref(v_aig_2160_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant(lean_object* v_00_u03b1_2163_, lean_object* v_inst_2164_, lean_object* v_inst_2165_, lean_object* v_aig_2166_, lean_object* v_ref_2167_){
_start:
{
lean_object* v___x_2168_; 
v___x_2168_ = l_Std_Sat_AIG_getConstant___redArg(v_aig_2166_, v_ref_2167_);
return v___x_2168_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___boxed(lean_object* v_00_u03b1_2169_, lean_object* v_inst_2170_, lean_object* v_inst_2171_, lean_object* v_aig_2172_, lean_object* v_ref_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l_Std_Sat_AIG_getConstant(v_00_u03b1_2169_, v_inst_2170_, v_inst_2171_, v_aig_2172_, v_ref_2173_);
lean_dec_ref(v_ref_2173_);
lean_dec_ref(v_aig_2172_);
lean_dec_ref(v_inst_2171_);
lean_dec_ref(v_inst_2170_);
return v_res_2174_;
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
