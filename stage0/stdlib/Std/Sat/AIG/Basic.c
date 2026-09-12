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
lean_object* lean_mk_array(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instInhabitedDecl_default___redArg();
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instInhabitedDecl_default___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instInhabitedDecl_default(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instInhabitedDecl___redArg();
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instInhabitedDecl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instInhabitedDecl(lean_object*);
static lean_once_cell_t l_Std_Sat_AIG_Cache_empty___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_Cache_empty___redArg___closed__0;
static lean_once_cell_t l_Std_Sat_AIG_Cache_empty___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_Cache_empty___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_empty___redArg();
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_empty___redArg___boxed(lean_object*);
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
static const lean_array_object l_Std_Sat_AIG_empty___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Sat_AIG_empty___redArg___closed__0 = (const lean_object*)&l_Std_Sat_AIG_empty___redArg___closed__0_value;
static lean_once_cell_t l_Std_Sat_AIG_empty___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_empty___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_empty___redArg();
LEAN_EXPORT lean_object* l_Std_Sat_AIG_empty___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_Sat_AIG_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_empty___closed__0;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_empty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_empty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instMembership___redArg();
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instMembership___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instInhabitedDecl_default___redArg(){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = lean_box(0);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instInhabitedDecl_default___redArg___boxed(lean_object* v___dummy_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Std_Sat_AIG_instInhabitedDecl_default___redArg();
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instInhabitedDecl_default(lean_object* v_00_u03b1_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = lean_box(0);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instInhabitedDecl___redArg(){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = lean_box(0);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instInhabitedDecl___redArg___boxed(lean_object* v___dummy_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Std_Sat_AIG_instInhabitedDecl___redArg();
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instInhabitedDecl(lean_object* v_a_357_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = lean_box(0);
return v___x_358_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___redArg___closed__0(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_359_ = lean_box(0);
v___x_360_ = lean_unsigned_to_nat(16u);
v___x_361_ = lean_mk_array(v___x_360_, v___x_359_);
return v___x_361_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___redArg___closed__1(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_362_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___redArg___closed__0, &l_Std_Sat_AIG_Cache_empty___redArg___closed__0_once, _init_l_Std_Sat_AIG_Cache_empty___redArg___closed__0);
v___x_363_ = lean_unsigned_to_nat(0u);
v___x_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
lean_ctor_set(v___x_364_, 1, v___x_362_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_empty___redArg(){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___redArg___closed__1, &l_Std_Sat_AIG_Cache_empty___redArg___closed__1_once, _init_l_Std_Sat_AIG_Cache_empty___redArg___closed__1);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_empty___redArg___boxed(lean_object* v___dummy_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Std_Sat_AIG_Cache_empty___redArg();
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_empty(lean_object* v_00_u03b1_369_, lean_object* v_inst_370_, lean_object* v_inst_371_, lean_object* v_decls_372_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___redArg___closed__1, &l_Std_Sat_AIG_Cache_empty___redArg___closed__1_once, _init_l_Std_Sat_AIG_Cache_empty___redArg___closed__1);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_empty___boxed(lean_object* v_00_u03b1_374_, lean_object* v_inst_375_, lean_object* v_inst_376_, lean_object* v_decls_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Std_Sat_AIG_Cache_empty(v_00_u03b1_374_, v_inst_375_, v_inst_376_, v_decls_377_);
lean_dec_ref(v_decls_377_);
lean_dec_ref(v_inst_376_);
lean_dec_ref(v_inst_375_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_noUpdate___redArg(lean_object* v_cache_379_){
_start:
{
lean_inc_ref(v_cache_379_);
return v_cache_379_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_noUpdate___redArg___boxed(lean_object* v_cache_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Std_Sat_AIG_Cache_noUpdate___redArg(v_cache_380_);
lean_dec_ref(v_cache_380_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_noUpdate(lean_object* v_00_u03b1_382_, lean_object* v_inst_383_, lean_object* v_inst_384_, lean_object* v_decls_385_, lean_object* v_decl_386_, lean_object* v_cache_387_){
_start:
{
lean_inc_ref(v_cache_387_);
return v_cache_387_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_noUpdate___boxed(lean_object* v_00_u03b1_388_, lean_object* v_inst_389_, lean_object* v_inst_390_, lean_object* v_decls_391_, lean_object* v_decl_392_, lean_object* v_cache_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Std_Sat_AIG_Cache_noUpdate(v_00_u03b1_388_, v_inst_389_, v_inst_390_, v_decls_391_, v_decl_392_, v_cache_393_);
lean_dec_ref(v_cache_393_);
lean_dec(v_decl_392_);
lean_dec_ref(v_decls_391_);
lean_dec_ref(v_inst_390_);
lean_dec_ref(v_inst_389_);
return v_res_394_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_Cache_insert___redArg___lam__0(lean_object* v_inst_395_, lean_object* v_a_396_, lean_object* v_b_397_){
_start:
{
uint8_t v___x_398_; 
v___x_398_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v_inst_395_, v_a_396_, v_b_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed(lean_object* v_inst_399_, lean_object* v_a_400_, lean_object* v_b_401_){
_start:
{
uint8_t v_res_402_; lean_object* v_r_403_; 
v_res_402_ = l_Std_Sat_AIG_Cache_insert___redArg___lam__0(v_inst_399_, v_a_400_, v_b_401_);
v_r_403_ = lean_box(v_res_402_);
return v_r_403_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___redArg(lean_object* v_inst_404_, lean_object* v_inst_405_, lean_object* v_decls_406_, lean_object* v_cache_407_, lean_object* v_decl_408_){
_start:
{
lean_object* v___f_409_; lean_object* v___x_410_; lean_object* v___f_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___f_409_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_409_, 0, v_inst_405_);
v___x_410_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_410_, 0, lean_box(0));
lean_closure_set(v___x_410_, 1, v_inst_404_);
v___f_411_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_411_, 0, v___f_409_);
v___x_412_ = lean_array_get_size(v_decls_406_);
v___x_413_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_411_, v___x_410_, v_cache_407_, v_decl_408_, v___x_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___redArg___boxed(lean_object* v_inst_414_, lean_object* v_inst_415_, lean_object* v_decls_416_, lean_object* v_cache_417_, lean_object* v_decl_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Std_Sat_AIG_Cache_insert___redArg(v_inst_414_, v_inst_415_, v_decls_416_, v_cache_417_, v_decl_418_);
lean_dec_ref(v_decls_416_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert(lean_object* v_00_u03b1_420_, lean_object* v_inst_421_, lean_object* v_inst_422_, lean_object* v_decls_423_, lean_object* v_cache_424_, lean_object* v_decl_425_){
_start:
{
lean_object* v___f_426_; lean_object* v___x_427_; lean_object* v___f_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___f_426_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_426_, 0, v_inst_422_);
v___x_427_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_427_, 0, lean_box(0));
lean_closure_set(v___x_427_, 1, v_inst_421_);
v___f_428_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_428_, 0, v___f_426_);
v___x_429_ = lean_array_get_size(v_decls_423_);
v___x_430_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_428_, v___x_427_, v_cache_424_, v_decl_425_, v___x_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___boxed(lean_object* v_00_u03b1_431_, lean_object* v_inst_432_, lean_object* v_inst_433_, lean_object* v_decls_434_, lean_object* v_cache_435_, lean_object* v_decl_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Std_Sat_AIG_Cache_insert(v_00_u03b1_431_, v_inst_432_, v_inst_433_, v_decls_434_, v_cache_435_, v_decl_436_);
lean_dec_ref(v_decls_434_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f___redArg(lean_object* v_inst_438_, lean_object* v_inst_439_, lean_object* v_cache_440_, lean_object* v_decl_441_){
_start:
{
lean_object* v___f_442_; lean_object* v___x_443_; lean_object* v___f_444_; lean_object* v___x_445_; 
v___f_442_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_442_, 0, v_inst_439_);
v___x_443_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_443_, 0, lean_box(0));
lean_closure_set(v___x_443_, 1, v_inst_438_);
v___f_444_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_444_, 0, v___f_442_);
v___x_445_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_444_, v___x_443_, v_cache_440_, v_decl_441_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v___x_446_; 
v___x_446_ = lean_box(0);
return v___x_446_;
}
else
{
lean_object* v_val_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
v_val_447_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v___x_445_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_val_447_);
lean_dec(v___x_445_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_val_447_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f___redArg___boxed(lean_object* v_inst_455_, lean_object* v_inst_456_, lean_object* v_cache_457_, lean_object* v_decl_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Std_Sat_AIG_Cache_get_x3f___redArg(v_inst_455_, v_inst_456_, v_cache_457_, v_decl_458_);
lean_dec_ref(v_cache_457_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f(lean_object* v_00_u03b1_460_, lean_object* v_inst_461_, lean_object* v_inst_462_, lean_object* v_decls_463_, lean_object* v_cache_464_, lean_object* v_decl_465_){
_start:
{
lean_object* v___f_466_; lean_object* v___x_467_; lean_object* v___f_468_; lean_object* v___x_469_; 
v___f_466_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_466_, 0, v_inst_462_);
v___x_467_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_467_, 0, lean_box(0));
lean_closure_set(v___x_467_, 1, v_inst_461_);
v___f_468_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_468_, 0, v___f_466_);
v___x_469_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_468_, v___x_467_, v_cache_464_, v_decl_465_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v___x_470_; 
v___x_470_ = lean_box(0);
return v___x_470_;
}
else
{
lean_object* v_val_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
v_val_471_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_478_ == 0)
{
v___x_473_ = v___x_469_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_val_471_);
lean_dec(v___x_469_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_val_471_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f___boxed(lean_object* v_00_u03b1_479_, lean_object* v_inst_480_, lean_object* v_inst_481_, lean_object* v_decls_482_, lean_object* v_cache_483_, lean_object* v_decl_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Std_Sat_AIG_Cache_get_x3f(v_00_u03b1_479_, v_inst_480_, v_inst_481_, v_decls_482_, v_cache_483_, v_decl_484_);
lean_dec_ref(v_cache_483_);
lean_dec_ref(v_decls_482_);
return v_res_485_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___redArg___closed__1(void){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_490_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___redArg___closed__1, &l_Std_Sat_AIG_Cache_empty___redArg___closed__1_once, _init_l_Std_Sat_AIG_Cache_empty___redArg___closed__1);
v___x_491_ = ((lean_object*)(l_Std_Sat_AIG_empty___redArg___closed__0));
v___x_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
lean_ctor_set(v___x_492_, 1, v___x_490_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_empty___redArg(){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = lean_obj_once(&l_Std_Sat_AIG_empty___redArg___closed__1, &l_Std_Sat_AIG_empty___redArg___closed__1_once, _init_l_Std_Sat_AIG_empty___redArg___closed__1);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_empty___redArg___boxed(lean_object* v___dummy_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Std_Sat_AIG_empty___redArg();
return v_res_496_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___closed__0(void){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l_Std_Sat_AIG_empty___redArg();
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_empty(lean_object* v_00_u03b1_498_, lean_object* v_inst_499_, lean_object* v_inst_500_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = lean_obj_once(&l_Std_Sat_AIG_empty___closed__0, &l_Std_Sat_AIG_empty___closed__0_once, _init_l_Std_Sat_AIG_empty___closed__0);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_empty___boxed(lean_object* v_00_u03b1_502_, lean_object* v_inst_503_, lean_object* v_inst_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Std_Sat_AIG_empty(v_00_u03b1_502_, v_inst_503_, v_inst_504_);
lean_dec_ref(v_inst_504_);
lean_dec_ref(v_inst_503_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instMembership___redArg(){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = lean_box(0);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instMembership___redArg___boxed(lean_object* v___dummy_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Std_Sat_AIG_instMembership___redArg();
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instMembership(lean_object* v_00_u03b1_510_, lean_object* v_inst_511_, lean_object* v_inst_512_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = lean_box(0);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instMembership___boxed(lean_object* v_00_u03b1_514_, lean_object* v_inst_515_, lean_object* v_inst_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Std_Sat_AIG_instMembership(v_00_u03b1_514_, v_inst_515_, v_inst_516_);
lean_dec_ref(v_inst_516_);
lean_dec_ref(v_inst_515_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_cast___redArg(lean_object* v_ref_518_){
_start:
{
lean_object* v_gate_519_; uint8_t v_invert_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_527_; 
v_gate_519_ = lean_ctor_get(v_ref_518_, 0);
v_invert_520_ = lean_ctor_get_uint8(v_ref_518_, sizeof(void*)*1);
v_isSharedCheck_527_ = !lean_is_exclusive(v_ref_518_);
if (v_isSharedCheck_527_ == 0)
{
v___x_522_ = v_ref_518_;
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_gate_519_);
lean_dec(v_ref_518_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_525_; 
if (v_isShared_523_ == 0)
{
v___x_525_ = v___x_522_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_gate_519_);
lean_ctor_set_uint8(v_reuseFailAlloc_526_, sizeof(void*)*1, v_invert_520_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_cast(lean_object* v_00_u03b1_528_, lean_object* v_inst_529_, lean_object* v_inst_530_, lean_object* v_aig1_531_, lean_object* v_aig2_532_, lean_object* v_ref_533_, lean_object* v_h_534_){
_start:
{
lean_object* v_gate_535_; uint8_t v_invert_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_543_; 
v_gate_535_ = lean_ctor_get(v_ref_533_, 0);
v_invert_536_ = lean_ctor_get_uint8(v_ref_533_, sizeof(void*)*1);
v_isSharedCheck_543_ = !lean_is_exclusive(v_ref_533_);
if (v_isSharedCheck_543_ == 0)
{
v___x_538_ = v_ref_533_;
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_gate_535_);
lean_dec(v_ref_533_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
if (v_isShared_539_ == 0)
{
v___x_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_gate_535_);
lean_ctor_set_uint8(v_reuseFailAlloc_542_, sizeof(void*)*1, v_invert_536_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_cast___boxed(lean_object* v_00_u03b1_544_, lean_object* v_inst_545_, lean_object* v_inst_546_, lean_object* v_aig1_547_, lean_object* v_aig2_548_, lean_object* v_ref_549_, lean_object* v_h_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Std_Sat_AIG_Ref_cast(v_00_u03b1_544_, v_inst_545_, v_inst_546_, v_aig1_547_, v_aig2_548_, v_ref_549_, v_h_550_);
lean_dec_ref(v_aig2_548_);
lean_dec_ref(v_aig1_547_);
lean_dec_ref(v_inst_546_);
lean_dec_ref(v_inst_545_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_flip___redArg(lean_object* v_ref_552_, uint8_t v_inv_553_){
_start:
{
lean_object* v_gate_554_; uint8_t v_invert_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_567_; 
v_gate_554_ = lean_ctor_get(v_ref_552_, 0);
v_invert_555_ = lean_ctor_get_uint8(v_ref_552_, sizeof(void*)*1);
v_isSharedCheck_567_ = !lean_is_exclusive(v_ref_552_);
if (v_isSharedCheck_567_ == 0)
{
v___x_557_ = v_ref_552_;
v_isShared_558_ = v_isSharedCheck_567_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_gate_554_);
lean_dec(v_ref_552_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_567_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
if (v_invert_555_ == 0)
{
if (v_inv_553_ == 0)
{
lean_del_object(v___x_557_);
goto v___jp_564_;
}
else
{
goto v___jp_559_;
}
}
else
{
if (v_inv_553_ == 0)
{
goto v___jp_559_;
}
else
{
lean_del_object(v___x_557_);
goto v___jp_564_;
}
}
v___jp_559_:
{
uint8_t v___x_560_; lean_object* v___x_562_; 
v___x_560_ = 1;
if (v_isShared_558_ == 0)
{
v___x_562_ = v___x_557_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_gate_554_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
lean_ctor_set_uint8(v___x_562_, sizeof(void*)*1, v___x_560_);
return v___x_562_;
}
}
v___jp_564_:
{
uint8_t v___x_565_; lean_object* v___x_566_; 
v___x_565_ = 0;
v___x_566_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_566_, 0, v_gate_554_);
lean_ctor_set_uint8(v___x_566_, sizeof(void*)*1, v___x_565_);
return v___x_566_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_flip___redArg___boxed(lean_object* v_ref_568_, lean_object* v_inv_569_){
_start:
{
uint8_t v_inv_boxed_570_; lean_object* v_res_571_; 
v_inv_boxed_570_ = lean_unbox(v_inv_569_);
v_res_571_ = l_Std_Sat_AIG_Ref_flip___redArg(v_ref_568_, v_inv_boxed_570_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_flip(lean_object* v_00_u03b1_572_, lean_object* v_inst_573_, lean_object* v_inst_574_, lean_object* v_aig_575_, lean_object* v_ref_576_, uint8_t v_inv_577_){
_start:
{
lean_object* v_gate_578_; uint8_t v_invert_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_591_; 
v_gate_578_ = lean_ctor_get(v_ref_576_, 0);
v_invert_579_ = lean_ctor_get_uint8(v_ref_576_, sizeof(void*)*1);
v_isSharedCheck_591_ = !lean_is_exclusive(v_ref_576_);
if (v_isSharedCheck_591_ == 0)
{
v___x_581_ = v_ref_576_;
v_isShared_582_ = v_isSharedCheck_591_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_gate_578_);
lean_dec(v_ref_576_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_591_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
if (v_invert_579_ == 0)
{
if (v_inv_577_ == 0)
{
lean_del_object(v___x_581_);
goto v___jp_588_;
}
else
{
goto v___jp_583_;
}
}
else
{
if (v_inv_577_ == 0)
{
goto v___jp_583_;
}
else
{
lean_del_object(v___x_581_);
goto v___jp_588_;
}
}
v___jp_583_:
{
uint8_t v___x_584_; lean_object* v___x_586_; 
v___x_584_ = 1;
if (v_isShared_582_ == 0)
{
v___x_586_ = v___x_581_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_gate_578_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
lean_ctor_set_uint8(v___x_586_, sizeof(void*)*1, v___x_584_);
return v___x_586_;
}
}
v___jp_588_:
{
uint8_t v___x_589_; lean_object* v___x_590_; 
v___x_589_ = 0;
v___x_590_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_590_, 0, v_gate_578_);
lean_ctor_set_uint8(v___x_590_, sizeof(void*)*1, v___x_589_);
return v___x_590_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_flip___boxed(lean_object* v_00_u03b1_592_, lean_object* v_inst_593_, lean_object* v_inst_594_, lean_object* v_aig_595_, lean_object* v_ref_596_, lean_object* v_inv_597_){
_start:
{
uint8_t v_inv_boxed_598_; lean_object* v_res_599_; 
v_inv_boxed_598_ = lean_unbox(v_inv_597_);
v_res_599_ = l_Std_Sat_AIG_Ref_flip(v_00_u03b1_592_, v_inst_593_, v_inst_594_, v_aig_595_, v_ref_596_, v_inv_boxed_598_);
lean_dec_ref(v_aig_595_);
lean_dec_ref(v_inst_594_);
lean_dec_ref(v_inst_593_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_not___redArg(lean_object* v_ref_600_){
_start:
{
uint8_t v_invert_601_; 
v_invert_601_ = lean_ctor_get_uint8(v_ref_600_, sizeof(void*)*1);
if (v_invert_601_ == 0)
{
lean_object* v_gate_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_610_; 
v_gate_602_ = lean_ctor_get(v_ref_600_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v_ref_600_);
if (v_isSharedCheck_610_ == 0)
{
v___x_604_ = v_ref_600_;
v_isShared_605_ = v_isSharedCheck_610_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_gate_602_);
lean_dec(v_ref_600_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_610_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
uint8_t v___x_606_; lean_object* v___x_608_; 
v___x_606_ = 1;
if (v_isShared_605_ == 0)
{
v___x_608_ = v___x_604_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_gate_602_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
lean_ctor_set_uint8(v___x_608_, sizeof(void*)*1, v___x_606_);
return v___x_608_;
}
}
}
else
{
lean_object* v_gate_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_619_; 
v_gate_611_ = lean_ctor_get(v_ref_600_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v_ref_600_);
if (v_isSharedCheck_619_ == 0)
{
v___x_613_ = v_ref_600_;
v_isShared_614_ = v_isSharedCheck_619_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_gate_611_);
lean_dec(v_ref_600_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_619_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
uint8_t v___x_615_; lean_object* v___x_617_; 
v___x_615_ = 0;
if (v_isShared_614_ == 0)
{
v___x_617_ = v___x_613_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_gate_611_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
lean_ctor_set_uint8(v___x_617_, sizeof(void*)*1, v___x_615_);
return v___x_617_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_not(lean_object* v_00_u03b1_620_, lean_object* v_inst_621_, lean_object* v_inst_622_, lean_object* v_aig_623_, lean_object* v_ref_624_){
_start:
{
uint8_t v_invert_625_; 
v_invert_625_ = lean_ctor_get_uint8(v_ref_624_, sizeof(void*)*1);
if (v_invert_625_ == 0)
{
lean_object* v_gate_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_634_; 
v_gate_626_ = lean_ctor_get(v_ref_624_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v_ref_624_);
if (v_isSharedCheck_634_ == 0)
{
v___x_628_ = v_ref_624_;
v_isShared_629_ = v_isSharedCheck_634_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_gate_626_);
lean_dec(v_ref_624_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_634_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
uint8_t v___x_630_; lean_object* v___x_632_; 
v___x_630_ = 1;
if (v_isShared_629_ == 0)
{
v___x_632_ = v___x_628_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_gate_626_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
lean_ctor_set_uint8(v___x_632_, sizeof(void*)*1, v___x_630_);
return v___x_632_;
}
}
}
else
{
lean_object* v_gate_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_643_; 
v_gate_635_ = lean_ctor_get(v_ref_624_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v_ref_624_);
if (v_isSharedCheck_643_ == 0)
{
v___x_637_ = v_ref_624_;
v_isShared_638_ = v_isSharedCheck_643_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_gate_635_);
lean_dec(v_ref_624_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_643_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
uint8_t v___x_639_; lean_object* v___x_641_; 
v___x_639_ = 0;
if (v_isShared_638_ == 0)
{
v___x_641_ = v___x_637_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_gate_635_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
lean_ctor_set_uint8(v___x_641_, sizeof(void*)*1, v___x_639_);
return v___x_641_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_not___boxed(lean_object* v_00_u03b1_644_, lean_object* v_inst_645_, lean_object* v_inst_646_, lean_object* v_aig_647_, lean_object* v_ref_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_Std_Sat_AIG_Ref_not(v_00_u03b1_644_, v_inst_645_, v_inst_646_, v_aig_647_, v_ref_648_);
lean_dec_ref(v_aig_647_);
lean_dec_ref(v_inst_646_);
lean_dec_ref(v_inst_645_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_cast___redArg(lean_object* v_input_650_){
_start:
{
lean_object* v_lhs_651_; lean_object* v_rhs_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_677_; 
v_lhs_651_ = lean_ctor_get(v_input_650_, 0);
v_rhs_652_ = lean_ctor_get(v_input_650_, 1);
v_isSharedCheck_677_ = !lean_is_exclusive(v_input_650_);
if (v_isSharedCheck_677_ == 0)
{
v___x_654_ = v_input_650_;
v_isShared_655_ = v_isSharedCheck_677_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_rhs_652_);
lean_inc(v_lhs_651_);
lean_dec(v_input_650_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_677_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v_gate_656_; uint8_t v_invert_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_676_; 
v_gate_656_ = lean_ctor_get(v_lhs_651_, 0);
v_invert_657_ = lean_ctor_get_uint8(v_lhs_651_, sizeof(void*)*1);
v_isSharedCheck_676_ = !lean_is_exclusive(v_lhs_651_);
if (v_isSharedCheck_676_ == 0)
{
v___x_659_ = v_lhs_651_;
v_isShared_660_ = v_isSharedCheck_676_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_gate_656_);
lean_dec(v_lhs_651_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_676_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v_gate_661_; uint8_t v_invert_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_675_; 
v_gate_661_ = lean_ctor_get(v_rhs_652_, 0);
v_invert_662_ = lean_ctor_get_uint8(v_rhs_652_, sizeof(void*)*1);
v_isSharedCheck_675_ = !lean_is_exclusive(v_rhs_652_);
if (v_isSharedCheck_675_ == 0)
{
v___x_664_ = v_rhs_652_;
v_isShared_665_ = v_isSharedCheck_675_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_gate_661_);
lean_dec(v_rhs_652_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_675_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 0, v_gate_656_);
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_gate_656_);
v___x_667_ = v_reuseFailAlloc_674_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
lean_object* v___x_669_; 
lean_ctor_set_uint8(v___x_667_, sizeof(void*)*1, v_invert_657_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 0, v_gate_661_);
v___x_669_ = v___x_659_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_gate_661_);
v___x_669_ = v_reuseFailAlloc_673_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
lean_object* v___x_671_; 
lean_ctor_set_uint8(v___x_669_, sizeof(void*)*1, v_invert_662_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 1, v___x_669_);
lean_ctor_set(v___x_654_, 0, v___x_667_);
v___x_671_ = v___x_654_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v___x_667_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v___x_669_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_cast(lean_object* v_00_u03b1_678_, lean_object* v_inst_679_, lean_object* v_inst_680_, lean_object* v_aig1_681_, lean_object* v_aig2_682_, lean_object* v_input_683_, lean_object* v_h_684_){
_start:
{
lean_object* v_lhs_685_; lean_object* v_rhs_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_711_; 
v_lhs_685_ = lean_ctor_get(v_input_683_, 0);
v_rhs_686_ = lean_ctor_get(v_input_683_, 1);
v_isSharedCheck_711_ = !lean_is_exclusive(v_input_683_);
if (v_isSharedCheck_711_ == 0)
{
v___x_688_ = v_input_683_;
v_isShared_689_ = v_isSharedCheck_711_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_rhs_686_);
lean_inc(v_lhs_685_);
lean_dec(v_input_683_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_711_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v_gate_690_; uint8_t v_invert_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_710_; 
v_gate_690_ = lean_ctor_get(v_lhs_685_, 0);
v_invert_691_ = lean_ctor_get_uint8(v_lhs_685_, sizeof(void*)*1);
v_isSharedCheck_710_ = !lean_is_exclusive(v_lhs_685_);
if (v_isSharedCheck_710_ == 0)
{
v___x_693_ = v_lhs_685_;
v_isShared_694_ = v_isSharedCheck_710_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_gate_690_);
lean_dec(v_lhs_685_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_710_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v_gate_695_; uint8_t v_invert_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_709_; 
v_gate_695_ = lean_ctor_get(v_rhs_686_, 0);
v_invert_696_ = lean_ctor_get_uint8(v_rhs_686_, sizeof(void*)*1);
v_isSharedCheck_709_ = !lean_is_exclusive(v_rhs_686_);
if (v_isSharedCheck_709_ == 0)
{
v___x_698_ = v_rhs_686_;
v_isShared_699_ = v_isSharedCheck_709_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_gate_695_);
lean_dec(v_rhs_686_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_709_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v_gate_690_);
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_gate_690_);
v___x_701_ = v_reuseFailAlloc_708_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
lean_object* v___x_703_; 
lean_ctor_set_uint8(v___x_701_, sizeof(void*)*1, v_invert_691_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 0, v_gate_695_);
v___x_703_ = v___x_693_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_gate_695_);
v___x_703_ = v_reuseFailAlloc_707_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
lean_object* v___x_705_; 
lean_ctor_set_uint8(v___x_703_, sizeof(void*)*1, v_invert_696_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 1, v___x_703_);
lean_ctor_set(v___x_688_, 0, v___x_701_);
v___x_705_ = v___x_688_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_701_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v___x_703_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_cast___boxed(lean_object* v_00_u03b1_712_, lean_object* v_inst_713_, lean_object* v_inst_714_, lean_object* v_aig1_715_, lean_object* v_aig2_716_, lean_object* v_input_717_, lean_object* v_h_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Std_Sat_AIG_BinaryInput_cast(v_00_u03b1_712_, v_inst_713_, v_inst_714_, v_aig1_715_, v_aig2_716_, v_input_717_, v_h_718_);
lean_dec_ref(v_aig2_716_);
lean_dec_ref(v_aig1_715_);
lean_dec_ref(v_inst_714_);
lean_dec_ref(v_inst_713_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_invert___redArg(lean_object* v_input_720_, uint8_t v_linv_721_, uint8_t v_rinv_722_){
_start:
{
lean_object* v___y_724_; lean_object* v___y_725_; lean_object* v___y_730_; lean_object* v___y_731_; lean_object* v_lhs_735_; lean_object* v_rhs_736_; lean_object* v___y_738_; lean_object* v_gate_744_; uint8_t v_invert_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_757_; 
v_lhs_735_ = lean_ctor_get(v_input_720_, 0);
lean_inc_ref(v_lhs_735_);
v_rhs_736_ = lean_ctor_get(v_input_720_, 1);
lean_inc_ref(v_rhs_736_);
lean_dec_ref(v_input_720_);
v_gate_744_ = lean_ctor_get(v_lhs_735_, 0);
v_invert_745_ = lean_ctor_get_uint8(v_lhs_735_, sizeof(void*)*1);
v_isSharedCheck_757_ = !lean_is_exclusive(v_lhs_735_);
if (v_isSharedCheck_757_ == 0)
{
v___x_747_ = v_lhs_735_;
v_isShared_748_ = v_isSharedCheck_757_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_gate_744_);
lean_dec(v_lhs_735_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_757_;
goto v_resetjp_746_;
}
v___jp_723_:
{
uint8_t v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_726_ = 0;
v___x_727_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_727_, 0, v___y_724_);
lean_ctor_set_uint8(v___x_727_, sizeof(void*)*1, v___x_726_);
v___x_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_728_, 0, v___y_725_);
lean_ctor_set(v___x_728_, 1, v___x_727_);
return v___x_728_;
}
v___jp_729_:
{
uint8_t v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_732_ = 1;
v___x_733_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_733_, 0, v___y_730_);
lean_ctor_set_uint8(v___x_733_, sizeof(void*)*1, v___x_732_);
v___x_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_734_, 0, v___y_731_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
return v___x_734_;
}
v___jp_737_:
{
uint8_t v_invert_739_; 
v_invert_739_ = lean_ctor_get_uint8(v_rhs_736_, sizeof(void*)*1);
if (v_invert_739_ == 0)
{
if (v_rinv_722_ == 0)
{
lean_object* v_gate_740_; 
v_gate_740_ = lean_ctor_get(v_rhs_736_, 0);
lean_inc(v_gate_740_);
lean_dec_ref(v_rhs_736_);
v___y_724_ = v_gate_740_;
v___y_725_ = v___y_738_;
goto v___jp_723_;
}
else
{
lean_object* v_gate_741_; 
v_gate_741_ = lean_ctor_get(v_rhs_736_, 0);
lean_inc(v_gate_741_);
lean_dec_ref(v_rhs_736_);
v___y_730_ = v_gate_741_;
v___y_731_ = v___y_738_;
goto v___jp_729_;
}
}
else
{
if (v_rinv_722_ == 0)
{
lean_object* v_gate_742_; 
v_gate_742_ = lean_ctor_get(v_rhs_736_, 0);
lean_inc(v_gate_742_);
lean_dec_ref(v_rhs_736_);
v___y_730_ = v_gate_742_;
v___y_731_ = v___y_738_;
goto v___jp_729_;
}
else
{
lean_object* v_gate_743_; 
v_gate_743_ = lean_ctor_get(v_rhs_736_, 0);
lean_inc(v_gate_743_);
lean_dec_ref(v_rhs_736_);
v___y_724_ = v_gate_743_;
v___y_725_ = v___y_738_;
goto v___jp_723_;
}
}
}
v_resetjp_746_:
{
if (v_invert_745_ == 0)
{
if (v_linv_721_ == 0)
{
lean_del_object(v___x_747_);
goto v___jp_754_;
}
else
{
goto v___jp_749_;
}
}
else
{
if (v_linv_721_ == 0)
{
goto v___jp_749_;
}
else
{
lean_del_object(v___x_747_);
goto v___jp_754_;
}
}
v___jp_749_:
{
uint8_t v___x_750_; lean_object* v___x_752_; 
v___x_750_ = 1;
if (v_isShared_748_ == 0)
{
v___x_752_ = v___x_747_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_gate_744_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
lean_ctor_set_uint8(v___x_752_, sizeof(void*)*1, v___x_750_);
v___y_738_ = v___x_752_;
goto v___jp_737_;
}
}
v___jp_754_:
{
uint8_t v___x_755_; lean_object* v___x_756_; 
v___x_755_ = 0;
v___x_756_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_756_, 0, v_gate_744_);
lean_ctor_set_uint8(v___x_756_, sizeof(void*)*1, v___x_755_);
v___y_738_ = v___x_756_;
goto v___jp_737_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_invert___redArg___boxed(lean_object* v_input_758_, lean_object* v_linv_759_, lean_object* v_rinv_760_){
_start:
{
uint8_t v_linv_boxed_761_; uint8_t v_rinv_boxed_762_; lean_object* v_res_763_; 
v_linv_boxed_761_ = lean_unbox(v_linv_759_);
v_rinv_boxed_762_ = lean_unbox(v_rinv_760_);
v_res_763_ = l_Std_Sat_AIG_BinaryInput_invert___redArg(v_input_758_, v_linv_boxed_761_, v_rinv_boxed_762_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_invert(lean_object* v_00_u03b1_764_, lean_object* v_inst_765_, lean_object* v_inst_766_, lean_object* v_aig_767_, lean_object* v_input_768_, uint8_t v_linv_769_, uint8_t v_rinv_770_){
_start:
{
lean_object* v___y_772_; lean_object* v___y_773_; lean_object* v___y_778_; lean_object* v___y_779_; lean_object* v_lhs_783_; lean_object* v_rhs_784_; lean_object* v___y_786_; lean_object* v_gate_792_; uint8_t v_invert_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_805_; 
v_lhs_783_ = lean_ctor_get(v_input_768_, 0);
lean_inc_ref(v_lhs_783_);
v_rhs_784_ = lean_ctor_get(v_input_768_, 1);
lean_inc_ref(v_rhs_784_);
lean_dec_ref(v_input_768_);
v_gate_792_ = lean_ctor_get(v_lhs_783_, 0);
v_invert_793_ = lean_ctor_get_uint8(v_lhs_783_, sizeof(void*)*1);
v_isSharedCheck_805_ = !lean_is_exclusive(v_lhs_783_);
if (v_isSharedCheck_805_ == 0)
{
v___x_795_ = v_lhs_783_;
v_isShared_796_ = v_isSharedCheck_805_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_gate_792_);
lean_dec(v_lhs_783_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_805_;
goto v_resetjp_794_;
}
v___jp_771_:
{
uint8_t v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_774_ = 0;
v___x_775_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_775_, 0, v___y_772_);
lean_ctor_set_uint8(v___x_775_, sizeof(void*)*1, v___x_774_);
v___x_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_776_, 0, v___y_773_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
return v___x_776_;
}
v___jp_777_:
{
uint8_t v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_780_ = 1;
v___x_781_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_781_, 0, v___y_778_);
lean_ctor_set_uint8(v___x_781_, sizeof(void*)*1, v___x_780_);
v___x_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_782_, 0, v___y_779_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
return v___x_782_;
}
v___jp_785_:
{
uint8_t v_invert_787_; 
v_invert_787_ = lean_ctor_get_uint8(v_rhs_784_, sizeof(void*)*1);
if (v_invert_787_ == 0)
{
if (v_rinv_770_ == 0)
{
lean_object* v_gate_788_; 
v_gate_788_ = lean_ctor_get(v_rhs_784_, 0);
lean_inc(v_gate_788_);
lean_dec_ref(v_rhs_784_);
v___y_772_ = v_gate_788_;
v___y_773_ = v___y_786_;
goto v___jp_771_;
}
else
{
lean_object* v_gate_789_; 
v_gate_789_ = lean_ctor_get(v_rhs_784_, 0);
lean_inc(v_gate_789_);
lean_dec_ref(v_rhs_784_);
v___y_778_ = v_gate_789_;
v___y_779_ = v___y_786_;
goto v___jp_777_;
}
}
else
{
if (v_rinv_770_ == 0)
{
lean_object* v_gate_790_; 
v_gate_790_ = lean_ctor_get(v_rhs_784_, 0);
lean_inc(v_gate_790_);
lean_dec_ref(v_rhs_784_);
v___y_778_ = v_gate_790_;
v___y_779_ = v___y_786_;
goto v___jp_777_;
}
else
{
lean_object* v_gate_791_; 
v_gate_791_ = lean_ctor_get(v_rhs_784_, 0);
lean_inc(v_gate_791_);
lean_dec_ref(v_rhs_784_);
v___y_772_ = v_gate_791_;
v___y_773_ = v___y_786_;
goto v___jp_771_;
}
}
}
v_resetjp_794_:
{
if (v_invert_793_ == 0)
{
if (v_linv_769_ == 0)
{
lean_del_object(v___x_795_);
goto v___jp_802_;
}
else
{
goto v___jp_797_;
}
}
else
{
if (v_linv_769_ == 0)
{
goto v___jp_797_;
}
else
{
lean_del_object(v___x_795_);
goto v___jp_802_;
}
}
v___jp_797_:
{
uint8_t v___x_798_; lean_object* v___x_800_; 
v___x_798_ = 1;
if (v_isShared_796_ == 0)
{
v___x_800_ = v___x_795_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_gate_792_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_ctor_set_uint8(v___x_800_, sizeof(void*)*1, v___x_798_);
v___y_786_ = v___x_800_;
goto v___jp_785_;
}
}
v___jp_802_:
{
uint8_t v___x_803_; lean_object* v___x_804_; 
v___x_803_ = 0;
v___x_804_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_804_, 0, v_gate_792_);
lean_ctor_set_uint8(v___x_804_, sizeof(void*)*1, v___x_803_);
v___y_786_ = v___x_804_;
goto v___jp_785_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_invert___boxed(lean_object* v_00_u03b1_806_, lean_object* v_inst_807_, lean_object* v_inst_808_, lean_object* v_aig_809_, lean_object* v_input_810_, lean_object* v_linv_811_, lean_object* v_rinv_812_){
_start:
{
uint8_t v_linv_boxed_813_; uint8_t v_rinv_boxed_814_; lean_object* v_res_815_; 
v_linv_boxed_813_ = lean_unbox(v_linv_811_);
v_rinv_boxed_814_ = lean_unbox(v_rinv_812_);
v_res_815_ = l_Std_Sat_AIG_BinaryInput_invert(v_00_u03b1_806_, v_inst_807_, v_inst_808_, v_aig_809_, v_input_810_, v_linv_boxed_813_, v_rinv_boxed_814_);
lean_dec_ref(v_aig_809_);
lean_dec_ref(v_inst_808_);
lean_dec_ref(v_inst_807_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_TernaryInput_cast___redArg(lean_object* v_input_816_){
_start:
{
lean_object* v_discr_817_; lean_object* v_lhs_818_; lean_object* v_rhs_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_853_; 
v_discr_817_ = lean_ctor_get(v_input_816_, 0);
v_lhs_818_ = lean_ctor_get(v_input_816_, 1);
v_rhs_819_ = lean_ctor_get(v_input_816_, 2);
v_isSharedCheck_853_ = !lean_is_exclusive(v_input_816_);
if (v_isSharedCheck_853_ == 0)
{
v___x_821_ = v_input_816_;
v_isShared_822_ = v_isSharedCheck_853_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_rhs_819_);
lean_inc(v_lhs_818_);
lean_inc(v_discr_817_);
lean_dec(v_input_816_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_853_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v_gate_823_; uint8_t v_invert_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_852_; 
v_gate_823_ = lean_ctor_get(v_discr_817_, 0);
v_invert_824_ = lean_ctor_get_uint8(v_discr_817_, sizeof(void*)*1);
v_isSharedCheck_852_ = !lean_is_exclusive(v_discr_817_);
if (v_isSharedCheck_852_ == 0)
{
v___x_826_ = v_discr_817_;
v_isShared_827_ = v_isSharedCheck_852_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_gate_823_);
lean_dec(v_discr_817_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_852_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v_gate_828_; uint8_t v_invert_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_851_; 
v_gate_828_ = lean_ctor_get(v_lhs_818_, 0);
v_invert_829_ = lean_ctor_get_uint8(v_lhs_818_, sizeof(void*)*1);
v_isSharedCheck_851_ = !lean_is_exclusive(v_lhs_818_);
if (v_isSharedCheck_851_ == 0)
{
v___x_831_ = v_lhs_818_;
v_isShared_832_ = v_isSharedCheck_851_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_gate_828_);
lean_dec(v_lhs_818_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_851_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v_gate_833_; uint8_t v_invert_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_850_; 
v_gate_833_ = lean_ctor_get(v_rhs_819_, 0);
v_invert_834_ = lean_ctor_get_uint8(v_rhs_819_, sizeof(void*)*1);
v_isSharedCheck_850_ = !lean_is_exclusive(v_rhs_819_);
if (v_isSharedCheck_850_ == 0)
{
v___x_836_ = v_rhs_819_;
v_isShared_837_ = v_isSharedCheck_850_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_gate_833_);
lean_dec(v_rhs_819_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_850_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_839_; 
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 0, v_gate_823_);
v___x_839_ = v___x_836_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_gate_823_);
v___x_839_ = v_reuseFailAlloc_849_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
lean_object* v___x_841_; 
lean_ctor_set_uint8(v___x_839_, sizeof(void*)*1, v_invert_824_);
if (v_isShared_832_ == 0)
{
v___x_841_ = v___x_831_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_gate_828_);
lean_ctor_set_uint8(v_reuseFailAlloc_848_, sizeof(void*)*1, v_invert_829_);
v___x_841_ = v_reuseFailAlloc_848_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
lean_object* v___x_843_; 
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v_gate_833_);
v___x_843_ = v___x_826_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_gate_833_);
v___x_843_ = v_reuseFailAlloc_847_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
lean_object* v___x_845_; 
lean_ctor_set_uint8(v___x_843_, sizeof(void*)*1, v_invert_834_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 2, v___x_843_);
lean_ctor_set(v___x_821_, 1, v___x_841_);
lean_ctor_set(v___x_821_, 0, v___x_839_);
v___x_845_ = v___x_821_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_839_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v___x_841_);
lean_ctor_set(v_reuseFailAlloc_846_, 2, v___x_843_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_TernaryInput_cast(lean_object* v_00_u03b1_854_, lean_object* v_inst_855_, lean_object* v_inst_856_, lean_object* v_aig1_857_, lean_object* v_aig2_858_, lean_object* v_input_859_, lean_object* v_h_860_){
_start:
{
lean_object* v_discr_861_; lean_object* v_lhs_862_; lean_object* v_rhs_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_897_; 
v_discr_861_ = lean_ctor_get(v_input_859_, 0);
v_lhs_862_ = lean_ctor_get(v_input_859_, 1);
v_rhs_863_ = lean_ctor_get(v_input_859_, 2);
v_isSharedCheck_897_ = !lean_is_exclusive(v_input_859_);
if (v_isSharedCheck_897_ == 0)
{
v___x_865_ = v_input_859_;
v_isShared_866_ = v_isSharedCheck_897_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_rhs_863_);
lean_inc(v_lhs_862_);
lean_inc(v_discr_861_);
lean_dec(v_input_859_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_897_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v_gate_867_; uint8_t v_invert_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_896_; 
v_gate_867_ = lean_ctor_get(v_discr_861_, 0);
v_invert_868_ = lean_ctor_get_uint8(v_discr_861_, sizeof(void*)*1);
v_isSharedCheck_896_ = !lean_is_exclusive(v_discr_861_);
if (v_isSharedCheck_896_ == 0)
{
v___x_870_ = v_discr_861_;
v_isShared_871_ = v_isSharedCheck_896_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_gate_867_);
lean_dec(v_discr_861_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_896_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v_gate_872_; uint8_t v_invert_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_895_; 
v_gate_872_ = lean_ctor_get(v_lhs_862_, 0);
v_invert_873_ = lean_ctor_get_uint8(v_lhs_862_, sizeof(void*)*1);
v_isSharedCheck_895_ = !lean_is_exclusive(v_lhs_862_);
if (v_isSharedCheck_895_ == 0)
{
v___x_875_ = v_lhs_862_;
v_isShared_876_ = v_isSharedCheck_895_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_gate_872_);
lean_dec(v_lhs_862_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_895_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v_gate_877_; uint8_t v_invert_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_894_; 
v_gate_877_ = lean_ctor_get(v_rhs_863_, 0);
v_invert_878_ = lean_ctor_get_uint8(v_rhs_863_, sizeof(void*)*1);
v_isSharedCheck_894_ = !lean_is_exclusive(v_rhs_863_);
if (v_isSharedCheck_894_ == 0)
{
v___x_880_ = v_rhs_863_;
v_isShared_881_ = v_isSharedCheck_894_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_gate_877_);
lean_dec(v_rhs_863_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_894_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 0, v_gate_867_);
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_gate_867_);
v___x_883_ = v_reuseFailAlloc_893_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
lean_object* v___x_885_; 
lean_ctor_set_uint8(v___x_883_, sizeof(void*)*1, v_invert_868_);
if (v_isShared_876_ == 0)
{
v___x_885_ = v___x_875_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_gate_872_);
lean_ctor_set_uint8(v_reuseFailAlloc_892_, sizeof(void*)*1, v_invert_873_);
v___x_885_ = v_reuseFailAlloc_892_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
lean_object* v___x_887_; 
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 0, v_gate_877_);
v___x_887_ = v___x_870_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_gate_877_);
v___x_887_ = v_reuseFailAlloc_891_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
lean_object* v___x_889_; 
lean_ctor_set_uint8(v___x_887_, sizeof(void*)*1, v_invert_878_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 2, v___x_887_);
lean_ctor_set(v___x_865_, 1, v___x_885_);
lean_ctor_set(v___x_865_, 0, v___x_883_);
v___x_889_ = v___x_865_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_883_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v___x_885_);
lean_ctor_set(v_reuseFailAlloc_890_, 2, v___x_887_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_TernaryInput_cast___boxed(lean_object* v_00_u03b1_898_, lean_object* v_inst_899_, lean_object* v_inst_900_, lean_object* v_aig1_901_, lean_object* v_aig2_902_, lean_object* v_input_903_, lean_object* v_h_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Std_Sat_AIG_TernaryInput_cast(v_00_u03b1_898_, v_inst_899_, v_inst_900_, v_aig1_901_, v_aig2_902_, v_input_903_, v_h_904_);
lean_dec_ref(v_aig2_902_);
lean_dec_ref(v_aig1_901_);
lean_dec_ref(v_inst_900_);
lean_dec_ref(v_inst_899_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_invEdgeStyle(uint8_t v_isInv_908_){
_start:
{
if (v_isInv_908_ == 0)
{
lean_object* v___x_909_; 
v___x_909_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_invEdgeStyle___closed__0));
return v___x_909_;
}
else
{
lean_object* v___x_910_; 
v___x_910_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_invEdgeStyle___closed__1));
return v___x_910_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_invEdgeStyle___boxed(lean_object* v_isInv_911_){
_start:
{
uint8_t v_isInv_boxed_912_; lean_object* v_res_913_; 
v_isInv_boxed_912_ = lean_unbox(v_isInv_911_);
v_res_913_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v_isInv_boxed_912_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___redArg(lean_object* v_acc_918_, lean_object* v_decls_919_, lean_object* v_idx_920_, lean_object* v_a_921_){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___f_924_; lean_object* v___f_925_; uint8_t v___x_926_; 
v___x_922_ = lean_array_get_size(v_decls_919_);
v___x_923_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_923_, 0, v___x_922_);
v___f_924_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_924_, 0, v___x_923_);
v___f_925_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___redArg___closed__0));
lean_inc(v_idx_920_);
lean_inc_ref(v___f_924_);
v___x_926_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_924_, v___f_925_, v_a_921_, v_idx_920_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_927_ = lean_box(0);
lean_inc(v_idx_920_);
v___x_928_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___f_924_, v___f_925_, v_a_921_, v_idx_920_, v___x_927_);
v___x_929_ = lean_array_fget_borrowed(v_decls_919_, v_idx_920_);
if (lean_obj_tag(v___x_929_) == 2)
{
lean_object* v_l_930_; lean_object* v_r_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___y_935_; uint8_t v___y_936_; uint8_t v___y_937_; uint8_t v___y_961_; lean_object* v___x_967_; lean_object* v___x_968_; uint8_t v___x_969_; 
v_l_930_ = lean_ctor_get(v___x_929_, 0);
v_r_931_ = lean_ctor_get(v___x_929_, 1);
v___x_932_ = lean_unsigned_to_nat(1u);
v___x_933_ = lean_nat_shiftr(v_l_930_, v___x_932_);
v___x_967_ = lean_nat_land(v___x_932_, v_l_930_);
v___x_968_ = lean_unsigned_to_nat(0u);
v___x_969_ = lean_nat_dec_eq(v___x_967_, v___x_968_);
lean_dec(v___x_967_);
if (v___x_969_ == 0)
{
uint8_t v___x_970_; 
v___x_970_ = 1;
v___y_961_ = v___x_970_;
goto v___jp_960_;
}
else
{
v___y_961_ = v___x_926_;
goto v___jp_960_;
}
v___jp_934_:
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v_fst_957_; lean_object* v_snd_958_; 
v___x_938_ = l_Nat_reprFast(v_idx_920_);
v___x_939_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___redArg___closed__1));
lean_inc_ref(v___x_938_);
v___x_940_ = lean_string_append(v___x_938_, v___x_939_);
lean_inc(v___x_933_);
v___x_941_ = l_Nat_reprFast(v___x_933_);
v___x_942_ = lean_string_append(v___x_940_, v___x_941_);
lean_dec_ref(v___x_941_);
v___x_943_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_936_);
v___x_944_ = lean_string_append(v___x_942_, v___x_943_);
lean_dec_ref(v___x_943_);
v___x_945_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___redArg___closed__2));
v___x_946_ = lean_string_append(v___x_944_, v___x_945_);
v___x_947_ = lean_string_append(v___x_946_, v___x_938_);
lean_dec_ref(v___x_938_);
v___x_948_ = lean_string_append(v___x_947_, v___x_939_);
lean_inc(v___y_935_);
v___x_949_ = l_Nat_reprFast(v___y_935_);
v___x_950_ = lean_string_append(v___x_948_, v___x_949_);
lean_dec_ref(v___x_949_);
v___x_951_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_937_);
v___x_952_ = lean_string_append(v___x_950_, v___x_951_);
lean_dec_ref(v___x_951_);
v___x_953_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___redArg___closed__3));
v___x_954_ = lean_string_append(v___x_952_, v___x_953_);
v___x_955_ = lean_string_append(v_acc_918_, v___x_954_);
lean_dec_ref(v___x_954_);
v___x_956_ = l_Std_Sat_AIG_toGraphviz_go___redArg(v___x_955_, v_decls_919_, v___x_933_, v___x_928_);
v_fst_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_fst_957_);
v_snd_958_ = lean_ctor_get(v___x_956_, 1);
lean_inc(v_snd_958_);
lean_dec_ref(v___x_956_);
v_acc_918_ = v_fst_957_;
v_idx_920_ = v___y_935_;
v_a_921_ = v_snd_958_;
goto _start;
}
v___jp_960_:
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; uint8_t v___x_965_; 
v___x_962_ = lean_nat_shiftr(v_r_931_, v___x_932_);
v___x_963_ = lean_nat_land(v___x_932_, v_r_931_);
v___x_964_ = lean_unsigned_to_nat(0u);
v___x_965_ = lean_nat_dec_eq(v___x_963_, v___x_964_);
lean_dec(v___x_963_);
if (v___x_965_ == 0)
{
uint8_t v___x_966_; 
v___x_966_ = 1;
v___y_935_ = v___x_962_;
v___y_936_ = v___y_961_;
v___y_937_ = v___x_966_;
goto v___jp_934_;
}
else
{
v___y_935_ = v___x_962_;
v___y_936_ = v___y_961_;
v___y_937_ = v___x_926_;
goto v___jp_934_;
}
}
}
else
{
lean_object* v___x_971_; 
lean_dec(v_idx_920_);
v___x_971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_971_, 0, v_acc_918_);
lean_ctor_set(v___x_971_, 1, v___x_928_);
return v___x_971_;
}
}
else
{
lean_object* v___x_972_; 
lean_dec_ref(v___f_924_);
lean_dec(v_idx_920_);
v___x_972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_972_, 0, v_acc_918_);
lean_ctor_set(v___x_972_, 1, v_a_921_);
return v___x_972_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___redArg___boxed(lean_object* v_acc_973_, lean_object* v_decls_974_, lean_object* v_idx_975_, lean_object* v_a_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Std_Sat_AIG_toGraphviz_go___redArg(v_acc_973_, v_decls_974_, v_idx_975_, v_a_976_);
lean_dec_ref(v_decls_974_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go(lean_object* v_00_u03b1_978_, lean_object* v_inst_979_, lean_object* v_inst_980_, lean_object* v_inst_981_, lean_object* v_acc_982_, lean_object* v_decls_983_, lean_object* v_hinv_984_, lean_object* v_idx_985_, lean_object* v_hidx_986_, lean_object* v_a_987_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l_Std_Sat_AIG_toGraphviz_go___redArg(v_acc_982_, v_decls_983_, v_idx_985_, v_a_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___boxed(lean_object* v_00_u03b1_989_, lean_object* v_inst_990_, lean_object* v_inst_991_, lean_object* v_inst_992_, lean_object* v_acc_993_, lean_object* v_decls_994_, lean_object* v_hinv_995_, lean_object* v_idx_996_, lean_object* v_hidx_997_, lean_object* v_a_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Std_Sat_AIG_toGraphviz_go(v_00_u03b1_989_, v_inst_990_, v_inst_991_, v_inst_992_, v_acc_993_, v_decls_994_, v_hinv_995_, v_idx_996_, v_hidx_997_, v_a_998_);
lean_dec_ref(v_decls_994_);
lean_dec_ref(v_inst_992_);
lean_dec_ref(v_inst_991_);
lean_dec_ref(v_inst_990_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter___redArg(lean_object* v_x_1000_, lean_object* v_h__1_1001_, lean_object* v_h__2_1002_, lean_object* v_h__3_1003_){
_start:
{
switch(lean_obj_tag(v_x_1000_))
{
case 0:
{
lean_object* v___x_1004_; 
lean_dec(v_h__3_1003_);
lean_dec(v_h__2_1002_);
v___x_1004_ = lean_apply_1(v_h__1_1001_, lean_box(0));
return v___x_1004_;
}
case 1:
{
lean_object* v_idx_1005_; lean_object* v___x_1006_; 
lean_dec(v_h__3_1003_);
lean_dec(v_h__1_1001_);
v_idx_1005_ = lean_ctor_get(v_x_1000_, 0);
lean_inc(v_idx_1005_);
lean_dec_ref_known(v_x_1000_, 1);
v___x_1006_ = lean_apply_2(v_h__2_1002_, v_idx_1005_, lean_box(0));
return v___x_1006_;
}
default: 
{
lean_object* v_l_1007_; lean_object* v_r_1008_; lean_object* v___x_1009_; 
lean_dec(v_h__2_1002_);
lean_dec(v_h__1_1001_);
v_l_1007_ = lean_ctor_get(v_x_1000_, 0);
lean_inc(v_l_1007_);
v_r_1008_ = lean_ctor_get(v_x_1000_, 1);
lean_inc(v_r_1008_);
lean_dec_ref_known(v_x_1000_, 2);
v___x_1009_ = lean_apply_3(v_h__3_1003_, v_l_1007_, v_r_1008_, lean_box(0));
return v___x_1009_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter(lean_object* v_00_u03b1_1010_, lean_object* v_motive_1011_, lean_object* v_x_1012_, lean_object* v_h__1_1013_, lean_object* v_h__2_1014_, lean_object* v_h__3_1015_){
_start:
{
switch(lean_obj_tag(v_x_1012_))
{
case 0:
{
lean_object* v___x_1016_; 
lean_dec(v_h__3_1015_);
lean_dec(v_h__2_1014_);
v___x_1016_ = lean_apply_1(v_h__1_1013_, lean_box(0));
return v___x_1016_;
}
case 1:
{
lean_object* v_idx_1017_; lean_object* v___x_1018_; 
lean_dec(v_h__3_1015_);
lean_dec(v_h__1_1013_);
v_idx_1017_ = lean_ctor_get(v_x_1012_, 0);
lean_inc(v_idx_1017_);
lean_dec_ref_known(v_x_1012_, 1);
v___x_1018_ = lean_apply_2(v_h__2_1014_, v_idx_1017_, lean_box(0));
return v___x_1018_;
}
default: 
{
lean_object* v_l_1019_; lean_object* v_r_1020_; lean_object* v___x_1021_; 
lean_dec(v_h__2_1014_);
lean_dec(v_h__1_1013_);
v_l_1019_ = lean_ctor_get(v_x_1012_, 0);
lean_inc(v_l_1019_);
v_r_1020_ = lean_ctor_get(v_x_1012_, 1);
lean_inc(v_r_1020_);
lean_dec_ref_known(v_x_1012_, 2);
v___x_1021_ = lean_apply_3(v_h__3_1015_, v_l_1019_, v_r_1020_, lean_box(0));
return v___x_1021_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg(lean_object* v_inst_1027_, lean_object* v_decls_1028_, lean_object* v_idx_1029_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = lean_array_fget_borrowed(v_decls_1028_, v_idx_1029_);
switch(lean_obj_tag(v___x_1030_))
{
case 0:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
lean_dec_ref(v_inst_1027_);
v___x_1031_ = l_Nat_reprFast(v_idx_1029_);
v___x_1032_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__0));
v___x_1033_ = lean_string_append(v___x_1031_, v___x_1032_);
v___x_1034_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__1));
v___x_1035_ = lean_string_append(v___x_1033_, v___x_1034_);
v___x_1036_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__2));
v___x_1037_ = lean_string_append(v___x_1035_, v___x_1036_);
return v___x_1037_;
}
case 1:
{
lean_object* v_idx_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v_idx_1038_ = lean_ctor_get(v___x_1030_, 0);
v___x_1039_ = l_Nat_reprFast(v_idx_1029_);
v___x_1040_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__0));
v___x_1041_ = lean_string_append(v___x_1039_, v___x_1040_);
lean_inc(v_idx_1038_);
v___x_1042_ = lean_apply_1(v_inst_1027_, v_idx_1038_);
v___x_1043_ = lean_string_append(v___x_1041_, v___x_1042_);
lean_dec_ref(v___x_1042_);
v___x_1044_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__3));
v___x_1045_ = lean_string_append(v___x_1043_, v___x_1044_);
return v___x_1045_;
}
default: 
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
lean_dec_ref(v_inst_1027_);
v___x_1046_ = l_Nat_reprFast(v_idx_1029_);
v___x_1047_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__0));
lean_inc_ref(v___x_1046_);
v___x_1048_ = lean_string_append(v___x_1046_, v___x_1047_);
v___x_1049_ = lean_string_append(v___x_1048_, v___x_1046_);
lean_dec_ref(v___x_1046_);
v___x_1050_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__4));
v___x_1051_ = lean_string_append(v___x_1049_, v___x_1050_);
return v___x_1051_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___boxed(lean_object* v_inst_1052_, lean_object* v_decls_1053_, lean_object* v_idx_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg(v_inst_1052_, v_decls_1053_, v_idx_1054_);
lean_dec_ref(v_decls_1053_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString(lean_object* v_00_u03b1_1056_, lean_object* v_inst_1057_, lean_object* v_inst_1058_, lean_object* v_inst_1059_, lean_object* v_decls_1060_, lean_object* v_idx_1061_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg(v_inst_1058_, v_decls_1060_, v_idx_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___boxed(lean_object* v_00_u03b1_1063_, lean_object* v_inst_1064_, lean_object* v_inst_1065_, lean_object* v_inst_1066_, lean_object* v_decls_1067_, lean_object* v_idx_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString(v_00_u03b1_1063_, v_inst_1064_, v_inst_1065_, v_inst_1066_, v_decls_1067_, v_idx_1068_);
lean_dec_ref(v_decls_1067_);
lean_dec_ref(v_inst_1066_);
lean_dec_ref(v_inst_1064_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___redArg___lam__0(lean_object* v_inst_1070_, lean_object* v_decls_1071_, lean_object* v_x1_1072_, lean_object* v_x2_1073_, lean_object* v_x3_1074_){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg(v_inst_1070_, v_decls_1071_, v_x2_1073_);
v___x_1076_ = lean_string_append(v_x1_1072_, v___x_1075_);
lean_dec_ref(v___x_1075_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___redArg___lam__0___boxed(lean_object* v_inst_1077_, lean_object* v_decls_1078_, lean_object* v_x1_1079_, lean_object* v_x2_1080_, lean_object* v_x3_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Std_Sat_AIG_toGraphviz___redArg___lam__0(v_inst_1077_, v_decls_1078_, v_x1_1079_, v_x2_1080_, v_x3_1081_);
lean_dec_ref(v_decls_1078_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___redArg___lam__1(lean_object* v___x_1083_, lean_object* v___f_1084_, lean_object* v_acc_1085_, lean_object* v_l_1086_){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1083_, v___f_1084_, v_acc_1085_, v_l_1086_);
return v___x_1087_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___redArg___closed__1(void){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1089_ = lean_box(0);
v___x_1090_ = lean_unsigned_to_nat(16u);
v___x_1091_ = lean_mk_array(v___x_1090_, v___x_1089_);
return v___x_1091_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___redArg___closed__2(void){
_start:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1092_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___redArg___closed__1, &l_Std_Sat_AIG_toGraphviz___redArg___closed__1_once, _init_l_Std_Sat_AIG_toGraphviz___redArg___closed__1);
v___x_1093_ = lean_unsigned_to_nat(0u);
v___x_1094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1093_);
lean_ctor_set(v___x_1094_, 1, v___x_1092_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___redArg(lean_object* v_inst_1116_, lean_object* v_entry_1117_){
_start:
{
lean_object* v_aig_1118_; lean_object* v_ref_1119_; lean_object* v_decls_1120_; lean_object* v_gate_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v_fst_1126_; lean_object* v_snd_1127_; lean_object* v___y_1129_; lean_object* v___x_1135_; lean_object* v_buckets_1136_; lean_object* v___x_1137_; uint8_t v___x_1138_; 
v_aig_1118_ = lean_ctor_get(v_entry_1117_, 0);
lean_inc_ref(v_aig_1118_);
v_ref_1119_ = lean_ctor_get(v_entry_1117_, 1);
lean_inc_ref(v_ref_1119_);
lean_dec_ref(v_entry_1117_);
v_decls_1120_ = lean_ctor_get(v_aig_1118_, 0);
lean_inc_ref(v_decls_1120_);
lean_dec_ref(v_aig_1118_);
v_gate_1121_ = lean_ctor_get(v_ref_1119_, 0);
lean_inc(v_gate_1121_);
lean_dec_ref(v_ref_1119_);
v___x_1122_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___redArg___closed__0));
v___x_1123_ = lean_unsigned_to_nat(0u);
v___x_1124_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___redArg___closed__2, &l_Std_Sat_AIG_toGraphviz___redArg___closed__2_once, _init_l_Std_Sat_AIG_toGraphviz___redArg___closed__2);
v___x_1125_ = l_Std_Sat_AIG_toGraphviz_go___redArg(v___x_1122_, v_decls_1120_, v_gate_1121_, v___x_1124_);
v_fst_1126_ = lean_ctor_get(v___x_1125_, 0);
lean_inc(v_fst_1126_);
v_snd_1127_ = lean_ctor_get(v___x_1125_, 1);
lean_inc(v_snd_1127_);
lean_dec_ref(v___x_1125_);
v___x_1135_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___redArg___closed__14));
v_buckets_1136_ = lean_ctor_get(v_snd_1127_, 1);
lean_inc_ref(v_buckets_1136_);
lean_dec(v_snd_1127_);
v___x_1137_ = lean_array_get_size(v_buckets_1136_);
v___x_1138_ = lean_nat_dec_lt(v___x_1123_, v___x_1137_);
if (v___x_1138_ == 0)
{
lean_dec_ref(v_buckets_1136_);
lean_dec_ref(v_decls_1120_);
lean_dec_ref(v_inst_1116_);
v___y_1129_ = v___x_1122_;
goto v___jp_1128_;
}
else
{
lean_object* v___f_1139_; lean_object* v___f_1140_; size_t v___x_1141_; size_t v___x_1142_; lean_object* v___x_1143_; 
v___f_1139_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_toGraphviz___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1139_, 0, v_inst_1116_);
lean_closure_set(v___f_1139_, 1, v_decls_1120_);
v___f_1140_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_toGraphviz___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1140_, 0, v___x_1135_);
lean_closure_set(v___f_1140_, 1, v___f_1139_);
v___x_1141_ = ((size_t)0ULL);
v___x_1142_ = lean_usize_of_nat(v___x_1137_);
v___x_1143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1135_, v___f_1140_, v_buckets_1136_, v___x_1141_, v___x_1142_, v___x_1122_);
v___y_1129_ = v___x_1143_;
goto v___jp_1128_;
}
v___jp_1128_:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1130_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___redArg___closed__3));
v___x_1131_ = lean_string_append(v___x_1130_, v___y_1129_);
lean_dec_ref(v___y_1129_);
v___x_1132_ = lean_string_append(v___x_1131_, v_fst_1126_);
lean_dec(v_fst_1126_);
v___x_1133_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___redArg___closed__4));
v___x_1134_ = lean_string_append(v___x_1132_, v___x_1133_);
return v___x_1134_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz(lean_object* v_00_u03b1_1144_, lean_object* v_inst_1145_, lean_object* v_inst_1146_, lean_object* v_inst_1147_, lean_object* v_entry_1148_){
_start:
{
lean_object* v___x_1149_; 
v___x_1149_ = l_Std_Sat_AIG_toGraphviz___redArg(v_inst_1146_, v_entry_1148_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___boxed(lean_object* v_00_u03b1_1150_, lean_object* v_inst_1151_, lean_object* v_inst_1152_, lean_object* v_inst_1153_, lean_object* v_entry_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Std_Sat_AIG_toGraphviz(v_00_u03b1_1150_, v_inst_1151_, v_inst_1152_, v_inst_1153_, v_entry_1154_);
lean_dec_ref(v_inst_1153_);
lean_dec_ref(v_inst_1151_);
return v_res_1155_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote_go___redArg(lean_object* v_x_1156_, lean_object* v_decls_1157_, lean_object* v_assign_1158_){
_start:
{
uint8_t v___y_1160_; uint8_t v___y_1161_; lean_object* v___x_1163_; 
v___x_1163_ = lean_array_fget_borrowed(v_decls_1157_, v_x_1156_);
switch(lean_obj_tag(v___x_1163_))
{
case 0:
{
uint8_t v___x_1164_; 
lean_dec_ref(v_assign_1158_);
v___x_1164_ = 0;
return v___x_1164_;
}
case 1:
{
lean_object* v_idx_1165_; lean_object* v___x_1166_; uint8_t v___x_1167_; 
v_idx_1165_ = lean_ctor_get(v___x_1163_, 0);
lean_inc(v_idx_1165_);
v___x_1166_ = lean_apply_1(v_assign_1158_, v_idx_1165_);
v___x_1167_ = lean_unbox(v___x_1166_);
return v___x_1167_;
}
default: 
{
lean_object* v_l_1168_; lean_object* v_r_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; uint8_t v_lval_1172_; lean_object* v___x_1173_; uint8_t v_rval_1174_; uint8_t v___y_1176_; uint8_t v___y_1181_; lean_object* v___x_1183_; lean_object* v___x_1184_; uint8_t v___x_1185_; 
v_l_1168_ = lean_ctor_get(v___x_1163_, 0);
v_r_1169_ = lean_ctor_get(v___x_1163_, 1);
v___x_1170_ = lean_unsigned_to_nat(1u);
v___x_1171_ = lean_nat_shiftr(v_l_1168_, v___x_1170_);
lean_inc_ref(v_assign_1158_);
v_lval_1172_ = l_Std_Sat_AIG_denote_go___redArg(v___x_1171_, v_decls_1157_, v_assign_1158_);
lean_dec(v___x_1171_);
v___x_1173_ = lean_nat_shiftr(v_r_1169_, v___x_1170_);
v_rval_1174_ = l_Std_Sat_AIG_denote_go___redArg(v___x_1173_, v_decls_1157_, v_assign_1158_);
lean_dec(v___x_1173_);
v___x_1183_ = lean_nat_land(v___x_1170_, v_l_1168_);
v___x_1184_ = lean_unsigned_to_nat(0u);
v___x_1185_ = lean_nat_dec_eq(v___x_1183_, v___x_1184_);
lean_dec(v___x_1183_);
if (v___x_1185_ == 0)
{
v___y_1181_ = v_lval_1172_;
goto v___jp_1180_;
}
else
{
if (v_lval_1172_ == 0)
{
v___y_1181_ = v___x_1185_;
goto v___jp_1180_;
}
else
{
uint8_t v___x_1186_; 
v___x_1186_ = 0;
v___y_1176_ = v___x_1186_;
goto v___jp_1175_;
}
}
v___jp_1175_:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; uint8_t v___x_1179_; 
v___x_1177_ = lean_nat_land(v___x_1170_, v_r_1169_);
v___x_1178_ = lean_unsigned_to_nat(0u);
v___x_1179_ = lean_nat_dec_eq(v___x_1177_, v___x_1178_);
lean_dec(v___x_1177_);
if (v___x_1179_ == 0)
{
v___y_1160_ = v___y_1176_;
v___y_1161_ = v_rval_1174_;
goto v___jp_1159_;
}
else
{
if (v_rval_1174_ == 0)
{
v___y_1160_ = v___y_1176_;
v___y_1161_ = v___x_1179_;
goto v___jp_1159_;
}
else
{
return v_rval_1174_;
}
}
}
v___jp_1180_:
{
if (v___y_1181_ == 0)
{
v___y_1176_ = v___y_1181_;
goto v___jp_1175_;
}
else
{
uint8_t v___x_1182_; 
v___x_1182_ = 0;
return v___x_1182_;
}
}
}
}
v___jp_1159_:
{
if (v___y_1161_ == 0)
{
uint8_t v___x_1162_; 
v___x_1162_ = 1;
return v___x_1162_;
}
else
{
return v___y_1160_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote_go___redArg___boxed(lean_object* v_x_1187_, lean_object* v_decls_1188_, lean_object* v_assign_1189_){
_start:
{
uint8_t v_res_1190_; lean_object* v_r_1191_; 
v_res_1190_ = l_Std_Sat_AIG_denote_go___redArg(v_x_1187_, v_decls_1188_, v_assign_1189_);
lean_dec_ref(v_decls_1188_);
lean_dec(v_x_1187_);
v_r_1191_ = lean_box(v_res_1190_);
return v_r_1191_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote_go(lean_object* v_00_u03b1_1192_, lean_object* v_x_1193_, lean_object* v_decls_1194_, lean_object* v_assign_1195_, lean_object* v_h1_1196_, lean_object* v_h2_1197_){
_start:
{
uint8_t v___x_1198_; 
v___x_1198_ = l_Std_Sat_AIG_denote_go___redArg(v_x_1193_, v_decls_1194_, v_assign_1195_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote_go___boxed(lean_object* v_00_u03b1_1199_, lean_object* v_x_1200_, lean_object* v_decls_1201_, lean_object* v_assign_1202_, lean_object* v_h1_1203_, lean_object* v_h2_1204_){
_start:
{
uint8_t v_res_1205_; lean_object* v_r_1206_; 
v_res_1205_ = l_Std_Sat_AIG_denote_go(v_00_u03b1_1199_, v_x_1200_, v_decls_1201_, v_assign_1202_, v_h1_1203_, v_h2_1204_);
lean_dec_ref(v_decls_1201_);
lean_dec(v_x_1200_);
v_r_1206_ = lean_box(v_res_1205_);
return v_r_1206_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote___redArg(lean_object* v_assign_1207_, lean_object* v_entry_1208_){
_start:
{
lean_object* v_ref_1209_; lean_object* v_aig_1210_; lean_object* v_gate_1211_; uint8_t v_invert_1212_; lean_object* v_decls_1213_; uint8_t v___x_1214_; 
v_ref_1209_ = lean_ctor_get(v_entry_1208_, 1);
v_aig_1210_ = lean_ctor_get(v_entry_1208_, 0);
v_gate_1211_ = lean_ctor_get(v_ref_1209_, 0);
v_invert_1212_ = lean_ctor_get_uint8(v_ref_1209_, sizeof(void*)*1);
v_decls_1213_ = lean_ctor_get(v_aig_1210_, 0);
v___x_1214_ = l_Std_Sat_AIG_denote_go___redArg(v_gate_1211_, v_decls_1213_, v_assign_1207_);
if (v_invert_1212_ == 0)
{
return v___x_1214_;
}
else
{
if (v___x_1214_ == 0)
{
return v_invert_1212_;
}
else
{
uint8_t v___x_1215_; 
v___x_1215_ = 0;
return v___x_1215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote___redArg___boxed(lean_object* v_assign_1216_, lean_object* v_entry_1217_){
_start:
{
uint8_t v_res_1218_; lean_object* v_r_1219_; 
v_res_1218_ = l_Std_Sat_AIG_denote___redArg(v_assign_1216_, v_entry_1217_);
lean_dec_ref(v_entry_1217_);
v_r_1219_ = lean_box(v_res_1218_);
return v_r_1219_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote(lean_object* v_00_u03b1_1220_, lean_object* v_inst_1221_, lean_object* v_inst_1222_, lean_object* v_assign_1223_, lean_object* v_entry_1224_){
_start:
{
uint8_t v___x_1225_; 
v___x_1225_ = l_Std_Sat_AIG_denote___redArg(v_assign_1223_, v_entry_1224_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote___boxed(lean_object* v_00_u03b1_1226_, lean_object* v_inst_1227_, lean_object* v_inst_1228_, lean_object* v_assign_1229_, lean_object* v_entry_1230_){
_start:
{
uint8_t v_res_1231_; lean_object* v_r_1232_; 
v_res_1231_ = l_Std_Sat_AIG_denote(v_00_u03b1_1226_, v_inst_1227_, v_inst_1228_, v_assign_1229_, v_entry_1230_);
lean_dec_ref(v_entry_1230_);
lean_dec_ref(v_inst_1228_);
lean_dec_ref(v_inst_1227_);
v_r_1232_ = lean_box(v_res_1231_);
return v_r_1232_;
}
}
static lean_object* _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6(void){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__5));
v___x_1315_ = l_String_toRawSubstring_x27(v___x_1314_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1(lean_object* v_x_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_){
_start:
{
lean_object* v___x_1340_; uint8_t v___x_1341_; 
v___x_1340_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
lean_inc(v_x_1337_);
v___x_1341_ = l_Lean_Syntax_isOfKind(v_x_1337_, v___x_1340_);
if (v___x_1341_ == 0)
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
lean_dec(v_x_1337_);
v___x_1342_ = lean_box(1);
v___x_1343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1342_);
lean_ctor_set(v___x_1343_, 1, v_a_1339_);
return v___x_1343_;
}
else
{
lean_object* v_quotContext_1344_; lean_object* v_currMacroScope_1345_; lean_object* v_ref_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; uint8_t v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v_quotContext_1344_ = lean_ctor_get(v_a_1338_, 1);
v_currMacroScope_1345_ = lean_ctor_get(v_a_1338_, 2);
v_ref_1346_ = lean_ctor_get(v_a_1338_, 5);
v___x_1347_ = lean_unsigned_to_nat(1u);
v___x_1348_ = l_Lean_Syntax_getArg(v_x_1337_, v___x_1347_);
v___x_1349_ = lean_unsigned_to_nat(3u);
v___x_1350_ = l_Lean_Syntax_getArg(v_x_1337_, v___x_1349_);
lean_dec(v_x_1337_);
v___x_1351_ = 0;
v___x_1352_ = l_Lean_SourceInfo_fromRef(v_ref_1346_, v___x_1351_);
v___x_1353_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4));
v___x_1354_ = lean_obj_once(&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6, &l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6_once, _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6);
v___x_1355_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__7));
lean_inc(v_currMacroScope_1345_);
lean_inc(v_quotContext_1344_);
v___x_1356_ = l_Lean_addMacroScope(v_quotContext_1344_, v___x_1355_, v_currMacroScope_1345_);
v___x_1357_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__12));
lean_inc_n(v___x_1352_, 2);
v___x_1358_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1352_);
lean_ctor_set(v___x_1358_, 1, v___x_1354_);
lean_ctor_set(v___x_1358_, 2, v___x_1356_);
lean_ctor_set(v___x_1358_, 3, v___x_1357_);
v___x_1359_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__14));
v___x_1360_ = l_Lean_Syntax_node2(v___x_1352_, v___x_1359_, v___x_1350_, v___x_1348_);
v___x_1361_ = l_Lean_Syntax_node2(v___x_1352_, v___x_1353_, v___x_1358_, v___x_1360_);
v___x_1362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1361_);
lean_ctor_set(v___x_1362_, 1, v_a_1339_);
return v___x_1362_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___boxed(lean_object* v_x_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1(v_x_1363_, v_a_1364_, v_a_1365_);
lean_dec_ref(v_a_1364_);
return v_res_1366_;
}
}
static lean_object* _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__7(void){
_start:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1383_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___redArg___closed__0));
v___x_1384_ = l_String_toRawSubstring_x27(v___x_1383_);
return v___x_1384_;
}
}
static lean_object* _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__12(void){
_start:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1395_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__11));
v___x_1396_ = l_String_toRawSubstring_x27(v___x_1395_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1(lean_object* v_x_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_){
_start:
{
lean_object* v___x_1423_; uint8_t v___x_1424_; 
v___x_1423_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__1));
lean_inc(v_x_1420_);
v___x_1424_ = l_Lean_Syntax_isOfKind(v_x_1420_, v___x_1423_);
if (v___x_1424_ == 0)
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
lean_dec(v_x_1420_);
v___x_1425_ = lean_box(1);
v___x_1426_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1425_);
lean_ctor_set(v___x_1426_, 1, v_a_1422_);
return v___x_1426_;
}
else
{
lean_object* v_quotContext_1427_; lean_object* v_currMacroScope_1428_; lean_object* v_ref_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; uint8_t v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v_quotContext_1427_ = lean_ctor_get(v_a_1421_, 1);
v_currMacroScope_1428_ = lean_ctor_get(v_a_1421_, 2);
v_ref_1429_ = lean_ctor_get(v_a_1421_, 5);
v___x_1430_ = lean_unsigned_to_nat(1u);
v___x_1431_ = l_Lean_Syntax_getArg(v_x_1420_, v___x_1430_);
v___x_1432_ = lean_unsigned_to_nat(3u);
v___x_1433_ = l_Lean_Syntax_getArg(v_x_1420_, v___x_1432_);
v___x_1434_ = lean_unsigned_to_nat(5u);
v___x_1435_ = l_Lean_Syntax_getArg(v_x_1420_, v___x_1434_);
lean_dec(v_x_1420_);
v___x_1436_ = 0;
v___x_1437_ = l_Lean_SourceInfo_fromRef(v_ref_1429_, v___x_1436_);
v___x_1438_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4));
v___x_1439_ = lean_obj_once(&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6, &l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6_once, _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6);
v___x_1440_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__7));
lean_inc_n(v_currMacroScope_1428_, 3);
lean_inc_n(v_quotContext_1427_, 3);
v___x_1441_ = l_Lean_addMacroScope(v_quotContext_1427_, v___x_1440_, v_currMacroScope_1428_);
v___x_1442_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__12));
lean_inc_n(v___x_1437_, 11);
v___x_1443_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1437_);
lean_ctor_set(v___x_1443_, 1, v___x_1439_);
lean_ctor_set(v___x_1443_, 2, v___x_1441_);
lean_ctor_set(v___x_1443_, 3, v___x_1442_);
v___x_1444_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__14));
v___x_1445_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__1));
v___x_1446_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__3));
v___x_1447_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__4));
v___x_1448_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1437_);
lean_ctor_set(v___x_1448_, 1, v___x_1447_);
v___x_1449_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__6));
v___x_1450_ = lean_obj_once(&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__7, &l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__7_once, _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__7);
v___x_1451_ = lean_box(0);
v___x_1452_ = l_Lean_addMacroScope(v_quotContext_1427_, v___x_1451_, v_currMacroScope_1428_);
v___x_1453_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__10));
v___x_1454_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1437_);
lean_ctor_set(v___x_1454_, 1, v___x_1450_);
lean_ctor_set(v___x_1454_, 2, v___x_1452_);
lean_ctor_set(v___x_1454_, 3, v___x_1453_);
v___x_1455_ = l_Lean_Syntax_node1(v___x_1437_, v___x_1449_, v___x_1454_);
v___x_1456_ = l_Lean_Syntax_node2(v___x_1437_, v___x_1446_, v___x_1448_, v___x_1455_);
v___x_1457_ = lean_obj_once(&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__12, &l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__12_once, _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__12);
v___x_1458_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__15));
v___x_1459_ = l_Lean_addMacroScope(v_quotContext_1427_, v___x_1458_, v_currMacroScope_1428_);
v___x_1460_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__20));
v___x_1461_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1437_);
lean_ctor_set(v___x_1461_, 1, v___x_1457_);
lean_ctor_set(v___x_1461_, 2, v___x_1459_);
lean_ctor_set(v___x_1461_, 3, v___x_1460_);
v___x_1462_ = l_Lean_Syntax_node2(v___x_1437_, v___x_1444_, v___x_1431_, v___x_1433_);
v___x_1463_ = l_Lean_Syntax_node2(v___x_1437_, v___x_1438_, v___x_1461_, v___x_1462_);
v___x_1464_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__21));
v___x_1465_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1437_);
lean_ctor_set(v___x_1465_, 1, v___x_1464_);
v___x_1466_ = l_Lean_Syntax_node3(v___x_1437_, v___x_1445_, v___x_1456_, v___x_1463_, v___x_1465_);
v___x_1467_ = l_Lean_Syntax_node2(v___x_1437_, v___x_1444_, v___x_1435_, v___x_1466_);
v___x_1468_ = l_Lean_Syntax_node2(v___x_1437_, v___x_1438_, v___x_1443_, v___x_1467_);
v___x_1469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1468_);
lean_ctor_set(v___x_1469_, 1, v_a_1422_);
return v___x_1469_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___boxed(lean_object* v_x_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1(v_x_1470_, v_a_1471_, v_a_1472_);
lean_dec_ref(v_a_1471_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_unexpandDenote(lean_object* v_x_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_){
_start:
{
lean_object* v___x_1531_; uint8_t v___x_1532_; 
v___x_1531_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4));
lean_inc(v_x_1528_);
v___x_1532_ = l_Lean_Syntax_isOfKind(v_x_1528_, v___x_1531_);
if (v___x_1532_ == 0)
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
lean_dec(v_x_1528_);
v___x_1533_ = lean_box(0);
v___x_1534_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1533_);
lean_ctor_set(v___x_1534_, 1, v_a_1530_);
return v___x_1534_;
}
else
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; uint8_t v___x_1538_; 
v___x_1535_ = lean_unsigned_to_nat(1u);
v___x_1536_ = l_Lean_Syntax_getArg(v_x_1528_, v___x_1535_);
lean_dec(v_x_1528_);
v___x_1537_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1536_);
v___x_1538_ = l_Lean_Syntax_matchesNull(v___x_1536_, v___x_1537_);
if (v___x_1538_ == 0)
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
lean_dec(v___x_1536_);
v___x_1539_ = lean_box(0);
v___x_1540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1539_);
lean_ctor_set(v___x_1540_, 1, v_a_1530_);
return v___x_1540_;
}
else
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; uint8_t v___x_1544_; 
v___x_1541_ = lean_unsigned_to_nat(0u);
v___x_1542_ = l_Lean_Syntax_getArg(v___x_1536_, v___x_1541_);
v___x_1543_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__1));
lean_inc(v___x_1542_);
v___x_1544_ = l_Lean_Syntax_isOfKind(v___x_1542_, v___x_1543_);
if (v___x_1544_ == 0)
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1545_ = l_Lean_Syntax_getArg(v___x_1536_, v___x_1535_);
lean_dec(v___x_1536_);
v___x_1546_ = l_Lean_SourceInfo_fromRef(v_a_1529_, v___x_1544_);
v___x_1547_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1548_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1546_, 3);
v___x_1549_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1546_);
lean_ctor_set(v___x_1549_, 1, v___x_1548_);
v___x_1550_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1551_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1546_);
lean_ctor_set(v___x_1551_, 1, v___x_1550_);
v___x_1552_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1553_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1546_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
v___x_1554_ = l_Lean_Syntax_node5(v___x_1546_, v___x_1547_, v___x_1549_, v___x_1542_, v___x_1551_, v___x_1545_, v___x_1553_);
v___x_1555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1554_);
lean_ctor_set(v___x_1555_, 1, v_a_1530_);
return v___x_1555_;
}
else
{
lean_object* v___x_1556_; uint8_t v___x_1557_; 
v___x_1556_ = l_Lean_Syntax_getArg(v___x_1542_, v___x_1535_);
v___x_1557_ = l_Lean_Syntax_matchesNull(v___x_1556_, v___x_1541_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1558_ = l_Lean_Syntax_getArg(v___x_1536_, v___x_1535_);
lean_dec(v___x_1536_);
v___x_1559_ = l_Lean_SourceInfo_fromRef(v_a_1529_, v___x_1557_);
v___x_1560_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1561_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1559_, 3);
v___x_1562_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1559_);
lean_ctor_set(v___x_1562_, 1, v___x_1561_);
v___x_1563_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1564_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1559_);
lean_ctor_set(v___x_1564_, 1, v___x_1563_);
v___x_1565_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1566_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1559_);
lean_ctor_set(v___x_1566_, 1, v___x_1565_);
v___x_1567_ = l_Lean_Syntax_node5(v___x_1559_, v___x_1560_, v___x_1562_, v___x_1542_, v___x_1564_, v___x_1558_, v___x_1566_);
v___x_1568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1567_);
lean_ctor_set(v___x_1568_, 1, v_a_1530_);
return v___x_1568_;
}
else
{
lean_object* v___x_1569_; lean_object* v___x_1570_; uint8_t v___x_1571_; 
v___x_1569_ = l_Lean_Syntax_getArg(v___x_1542_, v___x_1537_);
v___x_1570_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__4));
lean_inc(v___x_1569_);
v___x_1571_ = l_Lean_Syntax_isOfKind(v___x_1569_, v___x_1570_);
if (v___x_1571_ == 0)
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
lean_dec(v___x_1569_);
v___x_1572_ = l_Lean_Syntax_getArg(v___x_1536_, v___x_1535_);
lean_dec(v___x_1536_);
v___x_1573_ = l_Lean_SourceInfo_fromRef(v_a_1529_, v___x_1571_);
v___x_1574_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1575_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1573_, 3);
v___x_1576_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1573_);
lean_ctor_set(v___x_1576_, 1, v___x_1575_);
v___x_1577_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1578_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1573_);
lean_ctor_set(v___x_1578_, 1, v___x_1577_);
v___x_1579_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1580_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1573_);
lean_ctor_set(v___x_1580_, 1, v___x_1579_);
v___x_1581_ = l_Lean_Syntax_node5(v___x_1573_, v___x_1574_, v___x_1576_, v___x_1542_, v___x_1578_, v___x_1572_, v___x_1580_);
v___x_1582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1581_);
lean_ctor_set(v___x_1582_, 1, v_a_1530_);
return v___x_1582_;
}
else
{
lean_object* v___x_1583_; lean_object* v___x_1584_; uint8_t v___x_1585_; 
v___x_1583_ = l_Lean_Syntax_getArg(v___x_1569_, v___x_1541_);
lean_dec(v___x_1569_);
v___x_1584_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_1583_);
v___x_1585_ = l_Lean_Syntax_matchesNull(v___x_1583_, v___x_1584_);
if (v___x_1585_ == 0)
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
lean_dec(v___x_1583_);
v___x_1586_ = l_Lean_Syntax_getArg(v___x_1536_, v___x_1535_);
lean_dec(v___x_1536_);
v___x_1587_ = l_Lean_SourceInfo_fromRef(v_a_1529_, v___x_1585_);
v___x_1588_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1589_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1587_, 3);
v___x_1590_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1587_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
v___x_1591_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1592_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1587_);
lean_ctor_set(v___x_1592_, 1, v___x_1591_);
v___x_1593_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1594_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1587_);
lean_ctor_set(v___x_1594_, 1, v___x_1593_);
v___x_1595_ = l_Lean_Syntax_node5(v___x_1587_, v___x_1588_, v___x_1590_, v___x_1542_, v___x_1592_, v___x_1586_, v___x_1594_);
v___x_1596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1595_);
lean_ctor_set(v___x_1596_, 1, v_a_1530_);
return v___x_1596_;
}
else
{
lean_object* v___x_1597_; lean_object* v___x_1598_; uint8_t v___x_1599_; 
v___x_1597_ = l_Lean_Syntax_getArg(v___x_1583_, v___x_1541_);
v___x_1598_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__6));
lean_inc(v___x_1597_);
v___x_1599_ = l_Lean_Syntax_isOfKind(v___x_1597_, v___x_1598_);
if (v___x_1599_ == 0)
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
lean_dec(v___x_1597_);
lean_dec(v___x_1583_);
v___x_1600_ = l_Lean_Syntax_getArg(v___x_1536_, v___x_1535_);
lean_dec(v___x_1536_);
v___x_1601_ = l_Lean_SourceInfo_fromRef(v_a_1529_, v___x_1599_);
v___x_1602_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1603_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1601_, 3);
v___x_1604_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1601_);
lean_ctor_set(v___x_1604_, 1, v___x_1603_);
v___x_1605_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1606_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1601_);
lean_ctor_set(v___x_1606_, 1, v___x_1605_);
v___x_1607_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1608_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1601_);
lean_ctor_set(v___x_1608_, 1, v___x_1607_);
v___x_1609_ = l_Lean_Syntax_node5(v___x_1601_, v___x_1602_, v___x_1604_, v___x_1542_, v___x_1606_, v___x_1600_, v___x_1608_);
v___x_1610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1609_);
lean_ctor_set(v___x_1610_, 1, v_a_1530_);
return v___x_1610_;
}
else
{
lean_object* v___x_1611_; lean_object* v___x_1612_; uint8_t v___x_1613_; 
v___x_1611_ = l_Lean_Syntax_getArg(v___x_1597_, v___x_1541_);
v___x_1612_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__8));
lean_inc(v___x_1611_);
v___x_1613_ = l_Lean_Syntax_isOfKind(v___x_1611_, v___x_1612_);
if (v___x_1613_ == 0)
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
lean_dec(v___x_1611_);
lean_dec(v___x_1597_);
lean_dec(v___x_1583_);
v___x_1614_ = l_Lean_Syntax_getArg(v___x_1536_, v___x_1535_);
lean_dec(v___x_1536_);
v___x_1615_ = l_Lean_SourceInfo_fromRef(v_a_1529_, v___x_1613_);
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
v___x_1623_ = l_Lean_Syntax_node5(v___x_1615_, v___x_1616_, v___x_1618_, v___x_1542_, v___x_1620_, v___x_1614_, v___x_1622_);
v___x_1624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1623_);
lean_ctor_set(v___x_1624_, 1, v_a_1530_);
return v___x_1624_;
}
else
{
lean_object* v___x_1625_; lean_object* v___x_1626_; uint8_t v___x_1627_; 
v___x_1625_ = l_Lean_Syntax_getArg(v___x_1611_, v___x_1541_);
v___x_1626_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__10));
v___x_1627_ = l_Lean_Syntax_matchesIdent(v___x_1625_, v___x_1626_);
lean_dec(v___x_1625_);
if (v___x_1627_ == 0)
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
lean_dec(v___x_1611_);
lean_dec(v___x_1597_);
lean_dec(v___x_1583_);
v___x_1628_ = l_Lean_Syntax_getArg(v___x_1536_, v___x_1535_);
lean_dec(v___x_1536_);
v___x_1629_ = l_Lean_SourceInfo_fromRef(v_a_1529_, v___x_1627_);
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
v___x_1637_ = l_Lean_Syntax_node5(v___x_1629_, v___x_1630_, v___x_1632_, v___x_1542_, v___x_1634_, v___x_1628_, v___x_1636_);
v___x_1638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1637_);
lean_ctor_set(v___x_1638_, 1, v_a_1530_);
return v___x_1638_;
}
else
{
lean_object* v___x_1639_; uint8_t v___x_1640_; 
v___x_1639_ = l_Lean_Syntax_getArg(v___x_1611_, v___x_1535_);
lean_dec(v___x_1611_);
v___x_1640_ = l_Lean_Syntax_matchesNull(v___x_1639_, v___x_1541_);
if (v___x_1640_ == 0)
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
lean_dec(v___x_1597_);
lean_dec(v___x_1583_);
v___x_1641_ = l_Lean_Syntax_getArg(v___x_1536_, v___x_1535_);
lean_dec(v___x_1536_);
v___x_1642_ = l_Lean_SourceInfo_fromRef(v_a_1529_, v___x_1640_);
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
v___x_1650_ = l_Lean_Syntax_node5(v___x_1642_, v___x_1643_, v___x_1645_, v___x_1542_, v___x_1647_, v___x_1641_, v___x_1649_);
v___x_1651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1650_);
lean_ctor_set(v___x_1651_, 1, v_a_1530_);
return v___x_1651_;
}
else
{
lean_object* v___x_1652_; lean_object* v___x_1653_; uint8_t v___x_1654_; 
v___x_1652_ = l_Lean_Syntax_getArg(v___x_1597_, v___x_1535_);
lean_dec(v___x_1597_);
v___x_1653_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_1652_);
v___x_1654_ = l_Lean_Syntax_matchesNull(v___x_1652_, v___x_1653_);
if (v___x_1654_ == 0)
{
lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
lean_dec(v___x_1652_);
lean_dec(v___x_1583_);
v___x_1655_ = l_Lean_Syntax_getArg(v___x_1536_, v___x_1535_);
lean_dec(v___x_1536_);
v___x_1656_ = l_Lean_SourceInfo_fromRef(v_a_1529_, v___x_1654_);
v___x_1657_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1658_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1656_, 3);
v___x_1659_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1656_);
lean_ctor_set(v___x_1659_, 1, v___x_1658_);
v___x_1660_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1661_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1656_);
lean_ctor_set(v___x_1661_, 1, v___x_1660_);
v___x_1662_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1663_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1656_);
lean_ctor_set(v___x_1663_, 1, v___x_1662_);
v___x_1664_ = l_Lean_Syntax_node5(v___x_1656_, v___x_1657_, v___x_1659_, v___x_1542_, v___x_1661_, v___x_1655_, v___x_1663_);
v___x_1665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1664_);
lean_ctor_set(v___x_1665_, 1, v_a_1530_);
return v___x_1665_;
}
else
{
lean_object* v___x_1666_; uint8_t v___x_1667_; 
v___x_1666_ = l_Lean_Syntax_getArg(v___x_1652_, v___x_1541_);
v___x_1667_ = l_Lean_Syntax_matchesNull(v___x_1666_, v___x_1541_);
if (v___x_1667_ == 0)
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
lean_dec(v___x_1652_);
lean_dec(v___x_1583_);
v___x_1668_ = l_Lean_Syntax_getArg(v___x_1536_, v___x_1535_);
lean_dec(v___x_1536_);
v___x_1669_ = l_Lean_SourceInfo_fromRef(v_a_1529_, v___x_1667_);
v___x_1670_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1671_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1669_, 3);
v___x_1672_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1669_);
lean_ctor_set(v___x_1672_, 1, v___x_1671_);
v___x_1673_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1674_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1669_);
lean_ctor_set(v___x_1674_, 1, v___x_1673_);
v___x_1675_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1676_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1669_);
lean_ctor_set(v___x_1676_, 1, v___x_1675_);
v___x_1677_ = l_Lean_Syntax_node5(v___x_1669_, v___x_1670_, v___x_1672_, v___x_1542_, v___x_1674_, v___x_1668_, v___x_1676_);
v___x_1678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1677_);
lean_ctor_set(v___x_1678_, 1, v_a_1530_);
return v___x_1678_;
}
else
{
lean_object* v___x_1679_; uint8_t v___x_1680_; 
v___x_1679_ = l_Lean_Syntax_getArg(v___x_1652_, v___x_1535_);
v___x_1680_ = l_Lean_Syntax_matchesNull(v___x_1679_, v___x_1541_);
if (v___x_1680_ == 0)
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
lean_dec(v___x_1652_);
lean_dec(v___x_1583_);
v___x_1681_ = l_Lean_Syntax_getArg(v___x_1536_, v___x_1535_);
lean_dec(v___x_1536_);
v___x_1682_ = l_Lean_SourceInfo_fromRef(v_a_1529_, v___x_1680_);
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
v___x_1690_ = l_Lean_Syntax_node5(v___x_1682_, v___x_1683_, v___x_1685_, v___x_1542_, v___x_1687_, v___x_1681_, v___x_1689_);
v___x_1691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1690_);
lean_ctor_set(v___x_1691_, 1, v_a_1530_);
return v___x_1691_;
}
else
{
lean_object* v___x_1692_; lean_object* v___x_1693_; uint8_t v___x_1694_; 
v___x_1692_ = l_Lean_Syntax_getArg(v___x_1652_, v___x_1537_);
lean_dec(v___x_1652_);
v___x_1693_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__12));
lean_inc(v___x_1692_);
v___x_1694_ = l_Lean_Syntax_isOfKind(v___x_1692_, v___x_1693_);
if (v___x_1694_ == 0)
{
lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
lean_dec(v___x_1692_);
lean_dec(v___x_1583_);
v___x_1695_ = l_Lean_Syntax_getArg(v___x_1536_, v___x_1535_);
lean_dec(v___x_1536_);
v___x_1696_ = l_Lean_SourceInfo_fromRef(v_a_1529_, v___x_1694_);
v___x_1697_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1698_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1696_, 3);
v___x_1699_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1696_);
lean_ctor_set(v___x_1699_, 1, v___x_1698_);
v___x_1700_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1701_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1696_);
lean_ctor_set(v___x_1701_, 1, v___x_1700_);
v___x_1702_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1703_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1696_);
lean_ctor_set(v___x_1703_, 1, v___x_1702_);
v___x_1704_ = l_Lean_Syntax_node5(v___x_1696_, v___x_1697_, v___x_1699_, v___x_1542_, v___x_1701_, v___x_1695_, v___x_1703_);
v___x_1705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1704_);
lean_ctor_set(v___x_1705_, 1, v_a_1530_);
return v___x_1705_;
}
else
{
lean_object* v___x_1706_; uint8_t v___x_1707_; 
v___x_1706_ = l_Lean_Syntax_getArg(v___x_1692_, v___x_1535_);
v___x_1707_ = l_Lean_Syntax_matchesNull(v___x_1706_, v___x_1541_);
if (v___x_1707_ == 0)
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
lean_dec(v___x_1692_);
lean_dec(v___x_1583_);
v___x_1708_ = l_Lean_Syntax_getArg(v___x_1536_, v___x_1535_);
lean_dec(v___x_1536_);
v___x_1709_ = l_Lean_SourceInfo_fromRef(v_a_1529_, v___x_1707_);
v___x_1710_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1711_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1709_, 3);
v___x_1712_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1712_, 0, v___x_1709_);
lean_ctor_set(v___x_1712_, 1, v___x_1711_);
v___x_1713_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1714_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1714_, 0, v___x_1709_);
lean_ctor_set(v___x_1714_, 1, v___x_1713_);
v___x_1715_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1716_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1709_);
lean_ctor_set(v___x_1716_, 1, v___x_1715_);
v___x_1717_ = l_Lean_Syntax_node5(v___x_1709_, v___x_1710_, v___x_1712_, v___x_1542_, v___x_1714_, v___x_1708_, v___x_1716_);
v___x_1718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1717_);
lean_ctor_set(v___x_1718_, 1, v_a_1530_);
return v___x_1718_;
}
else
{
lean_object* v___x_1719_; uint8_t v___x_1720_; 
v___x_1719_ = l_Lean_Syntax_getArg(v___x_1583_, v___x_1537_);
lean_inc(v___x_1719_);
v___x_1720_ = l_Lean_Syntax_isOfKind(v___x_1719_, v___x_1598_);
if (v___x_1720_ == 0)
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
lean_dec(v___x_1719_);
lean_dec(v___x_1692_);
lean_dec(v___x_1583_);
v___x_1721_ = l_Lean_Syntax_getArg(v___x_1536_, v___x_1535_);
lean_dec(v___x_1536_);
v___x_1722_ = l_Lean_SourceInfo_fromRef(v_a_1529_, v___x_1720_);
v___x_1723_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1724_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1722_, 3);
v___x_1725_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1722_);
lean_ctor_set(v___x_1725_, 1, v___x_1724_);
v___x_1726_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1727_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1722_);
lean_ctor_set(v___x_1727_, 1, v___x_1726_);
v___x_1728_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1729_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1722_);
lean_ctor_set(v___x_1729_, 1, v___x_1728_);
v___x_1730_ = l_Lean_Syntax_node5(v___x_1722_, v___x_1723_, v___x_1725_, v___x_1542_, v___x_1727_, v___x_1721_, v___x_1729_);
v___x_1731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1730_);
lean_ctor_set(v___x_1731_, 1, v_a_1530_);
return v___x_1731_;
}
else
{
lean_object* v___x_1732_; uint8_t v___x_1733_; 
v___x_1732_ = l_Lean_Syntax_getArg(v___x_1719_, v___x_1541_);
lean_inc(v___x_1732_);
v___x_1733_ = l_Lean_Syntax_isOfKind(v___x_1732_, v___x_1612_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
lean_dec(v___x_1732_);
lean_dec(v___x_1719_);
lean_dec(v___x_1692_);
lean_dec(v___x_1583_);
v___x_1734_ = l_Lean_Syntax_getArg(v___x_1536_, v___x_1535_);
lean_dec(v___x_1536_);
v___x_1735_ = l_Lean_SourceInfo_fromRef(v_a_1529_, v___x_1733_);
v___x_1736_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1737_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1735_, 3);
v___x_1738_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1735_);
lean_ctor_set(v___x_1738_, 1, v___x_1737_);
v___x_1739_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1740_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1735_);
lean_ctor_set(v___x_1740_, 1, v___x_1739_);
v___x_1741_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1742_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1735_);
lean_ctor_set(v___x_1742_, 1, v___x_1741_);
v___x_1743_ = l_Lean_Syntax_node5(v___x_1735_, v___x_1736_, v___x_1738_, v___x_1542_, v___x_1740_, v___x_1734_, v___x_1742_);
v___x_1744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1743_);
lean_ctor_set(v___x_1744_, 1, v_a_1530_);
return v___x_1744_;
}
else
{
lean_object* v___x_1745_; lean_object* v___x_1746_; uint8_t v___x_1747_; 
v___x_1745_ = l_Lean_Syntax_getArg(v___x_1732_, v___x_1541_);
v___x_1746_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__14));
v___x_1747_ = l_Lean_Syntax_matchesIdent(v___x_1745_, v___x_1746_);
lean_dec(v___x_1745_);
if (v___x_1747_ == 0)
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
lean_dec(v___x_1732_);
lean_dec(v___x_1719_);
lean_dec(v___x_1692_);
lean_dec(v___x_1583_);
v___x_1748_ = l_Lean_Syntax_getArg(v___x_1536_, v___x_1535_);
lean_dec(v___x_1536_);
v___x_1749_ = l_Lean_SourceInfo_fromRef(v_a_1529_, v___x_1747_);
v___x_1750_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1751_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1749_, 3);
v___x_1752_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1749_);
lean_ctor_set(v___x_1752_, 1, v___x_1751_);
v___x_1753_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1754_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1749_);
lean_ctor_set(v___x_1754_, 1, v___x_1753_);
v___x_1755_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1756_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1749_);
lean_ctor_set(v___x_1756_, 1, v___x_1755_);
v___x_1757_ = l_Lean_Syntax_node5(v___x_1749_, v___x_1750_, v___x_1752_, v___x_1542_, v___x_1754_, v___x_1748_, v___x_1756_);
v___x_1758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1757_);
lean_ctor_set(v___x_1758_, 1, v_a_1530_);
return v___x_1758_;
}
else
{
lean_object* v___x_1759_; uint8_t v___x_1760_; 
v___x_1759_ = l_Lean_Syntax_getArg(v___x_1732_, v___x_1535_);
lean_dec(v___x_1732_);
v___x_1760_ = l_Lean_Syntax_matchesNull(v___x_1759_, v___x_1541_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
lean_dec(v___x_1719_);
lean_dec(v___x_1692_);
lean_dec(v___x_1583_);
v___x_1761_ = l_Lean_Syntax_getArg(v___x_1536_, v___x_1535_);
lean_dec(v___x_1536_);
v___x_1762_ = l_Lean_SourceInfo_fromRef(v_a_1529_, v___x_1760_);
v___x_1763_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1764_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1762_, 3);
v___x_1765_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1762_);
lean_ctor_set(v___x_1765_, 1, v___x_1764_);
v___x_1766_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1767_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1762_);
lean_ctor_set(v___x_1767_, 1, v___x_1766_);
v___x_1768_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1769_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1762_);
lean_ctor_set(v___x_1769_, 1, v___x_1768_);
v___x_1770_ = l_Lean_Syntax_node5(v___x_1762_, v___x_1763_, v___x_1765_, v___x_1542_, v___x_1767_, v___x_1761_, v___x_1769_);
v___x_1771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1770_);
lean_ctor_set(v___x_1771_, 1, v_a_1530_);
return v___x_1771_;
}
else
{
lean_object* v___x_1772_; uint8_t v___x_1773_; 
v___x_1772_ = l_Lean_Syntax_getArg(v___x_1719_, v___x_1535_);
lean_dec(v___x_1719_);
lean_inc(v___x_1772_);
v___x_1773_ = l_Lean_Syntax_matchesNull(v___x_1772_, v___x_1653_);
if (v___x_1773_ == 0)
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
lean_dec(v___x_1772_);
lean_dec(v___x_1692_);
lean_dec(v___x_1583_);
v___x_1774_ = l_Lean_Syntax_getArg(v___x_1536_, v___x_1535_);
lean_dec(v___x_1536_);
v___x_1775_ = l_Lean_SourceInfo_fromRef(v_a_1529_, v___x_1773_);
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
v___x_1783_ = l_Lean_Syntax_node5(v___x_1775_, v___x_1776_, v___x_1778_, v___x_1542_, v___x_1780_, v___x_1774_, v___x_1782_);
v___x_1784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1783_);
lean_ctor_set(v___x_1784_, 1, v_a_1530_);
return v___x_1784_;
}
else
{
lean_object* v___x_1785_; uint8_t v___x_1786_; 
v___x_1785_ = l_Lean_Syntax_getArg(v___x_1772_, v___x_1541_);
v___x_1786_ = l_Lean_Syntax_matchesNull(v___x_1785_, v___x_1541_);
if (v___x_1786_ == 0)
{
lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
lean_dec(v___x_1772_);
lean_dec(v___x_1692_);
lean_dec(v___x_1583_);
v___x_1787_ = l_Lean_Syntax_getArg(v___x_1536_, v___x_1535_);
lean_dec(v___x_1536_);
v___x_1788_ = l_Lean_SourceInfo_fromRef(v_a_1529_, v___x_1786_);
v___x_1789_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1790_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1788_, 3);
v___x_1791_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1788_);
lean_ctor_set(v___x_1791_, 1, v___x_1790_);
v___x_1792_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1793_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1788_);
lean_ctor_set(v___x_1793_, 1, v___x_1792_);
v___x_1794_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1795_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1788_);
lean_ctor_set(v___x_1795_, 1, v___x_1794_);
v___x_1796_ = l_Lean_Syntax_node5(v___x_1788_, v___x_1789_, v___x_1791_, v___x_1542_, v___x_1793_, v___x_1787_, v___x_1795_);
v___x_1797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1796_);
lean_ctor_set(v___x_1797_, 1, v_a_1530_);
return v___x_1797_;
}
else
{
lean_object* v___x_1798_; uint8_t v___x_1799_; 
v___x_1798_ = l_Lean_Syntax_getArg(v___x_1772_, v___x_1535_);
v___x_1799_ = l_Lean_Syntax_matchesNull(v___x_1798_, v___x_1541_);
if (v___x_1799_ == 0)
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
lean_dec(v___x_1772_);
lean_dec(v___x_1692_);
lean_dec(v___x_1583_);
v___x_1800_ = l_Lean_Syntax_getArg(v___x_1536_, v___x_1535_);
lean_dec(v___x_1536_);
v___x_1801_ = l_Lean_SourceInfo_fromRef(v_a_1529_, v___x_1799_);
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
v___x_1809_ = l_Lean_Syntax_node5(v___x_1801_, v___x_1802_, v___x_1804_, v___x_1542_, v___x_1806_, v___x_1800_, v___x_1808_);
v___x_1810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1809_);
lean_ctor_set(v___x_1810_, 1, v_a_1530_);
return v___x_1810_;
}
else
{
lean_object* v___x_1811_; uint8_t v___x_1812_; 
v___x_1811_ = l_Lean_Syntax_getArg(v___x_1772_, v___x_1537_);
lean_dec(v___x_1772_);
lean_inc(v___x_1811_);
v___x_1812_ = l_Lean_Syntax_isOfKind(v___x_1811_, v___x_1693_);
if (v___x_1812_ == 0)
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
lean_dec(v___x_1811_);
lean_dec(v___x_1692_);
lean_dec(v___x_1583_);
v___x_1813_ = l_Lean_Syntax_getArg(v___x_1536_, v___x_1535_);
lean_dec(v___x_1536_);
v___x_1814_ = l_Lean_SourceInfo_fromRef(v_a_1529_, v___x_1812_);
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
v___x_1822_ = l_Lean_Syntax_node5(v___x_1814_, v___x_1815_, v___x_1817_, v___x_1542_, v___x_1819_, v___x_1813_, v___x_1821_);
v___x_1823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
lean_ctor_set(v___x_1823_, 1, v_a_1530_);
return v___x_1823_;
}
else
{
lean_object* v___x_1824_; uint8_t v___x_1825_; 
v___x_1824_ = l_Lean_Syntax_getArg(v___x_1811_, v___x_1535_);
v___x_1825_ = l_Lean_Syntax_matchesNull(v___x_1824_, v___x_1541_);
if (v___x_1825_ == 0)
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
lean_dec(v___x_1811_);
lean_dec(v___x_1692_);
lean_dec(v___x_1583_);
v___x_1826_ = l_Lean_Syntax_getArg(v___x_1536_, v___x_1535_);
lean_dec(v___x_1536_);
v___x_1827_ = l_Lean_SourceInfo_fromRef(v_a_1529_, v___x_1825_);
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
v___x_1835_ = l_Lean_Syntax_node5(v___x_1827_, v___x_1828_, v___x_1830_, v___x_1542_, v___x_1832_, v___x_1826_, v___x_1834_);
v___x_1836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1835_);
lean_ctor_set(v___x_1836_, 1, v_a_1530_);
return v___x_1836_;
}
else
{
lean_object* v___x_1837_; lean_object* v___x_1838_; uint8_t v___x_1839_; 
v___x_1837_ = lean_unsigned_to_nat(4u);
v___x_1838_ = l_Lean_Syntax_getArg(v___x_1583_, v___x_1837_);
lean_dec(v___x_1583_);
lean_inc(v___x_1838_);
v___x_1839_ = l_Lean_Syntax_isOfKind(v___x_1838_, v___x_1598_);
if (v___x_1839_ == 0)
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
lean_dec(v___x_1838_);
lean_dec(v___x_1811_);
lean_dec(v___x_1692_);
v___x_1840_ = l_Lean_Syntax_getArg(v___x_1536_, v___x_1535_);
lean_dec(v___x_1536_);
v___x_1841_ = l_Lean_SourceInfo_fromRef(v_a_1529_, v___x_1839_);
v___x_1842_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1843_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1841_, 3);
v___x_1844_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1841_);
lean_ctor_set(v___x_1844_, 1, v___x_1843_);
v___x_1845_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1846_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1841_);
lean_ctor_set(v___x_1846_, 1, v___x_1845_);
v___x_1847_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1848_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1841_);
lean_ctor_set(v___x_1848_, 1, v___x_1847_);
v___x_1849_ = l_Lean_Syntax_node5(v___x_1841_, v___x_1842_, v___x_1844_, v___x_1542_, v___x_1846_, v___x_1840_, v___x_1848_);
v___x_1850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1849_);
lean_ctor_set(v___x_1850_, 1, v_a_1530_);
return v___x_1850_;
}
else
{
lean_object* v___x_1851_; uint8_t v___x_1852_; 
v___x_1851_ = l_Lean_Syntax_getArg(v___x_1838_, v___x_1541_);
lean_inc(v___x_1851_);
v___x_1852_ = l_Lean_Syntax_isOfKind(v___x_1851_, v___x_1612_);
if (v___x_1852_ == 0)
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
lean_dec(v___x_1851_);
lean_dec(v___x_1838_);
lean_dec(v___x_1811_);
lean_dec(v___x_1692_);
v___x_1853_ = l_Lean_Syntax_getArg(v___x_1536_, v___x_1535_);
lean_dec(v___x_1536_);
v___x_1854_ = l_Lean_SourceInfo_fromRef(v_a_1529_, v___x_1852_);
v___x_1855_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1856_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1854_, 3);
v___x_1857_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1854_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
v___x_1858_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1859_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1854_);
lean_ctor_set(v___x_1859_, 1, v___x_1858_);
v___x_1860_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1861_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1854_);
lean_ctor_set(v___x_1861_, 1, v___x_1860_);
v___x_1862_ = l_Lean_Syntax_node5(v___x_1854_, v___x_1855_, v___x_1857_, v___x_1542_, v___x_1859_, v___x_1853_, v___x_1861_);
v___x_1863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1862_);
lean_ctor_set(v___x_1863_, 1, v_a_1530_);
return v___x_1863_;
}
else
{
lean_object* v___x_1864_; lean_object* v___x_1865_; uint8_t v___x_1866_; 
v___x_1864_ = l_Lean_Syntax_getArg(v___x_1851_, v___x_1541_);
v___x_1865_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__16));
v___x_1866_ = l_Lean_Syntax_matchesIdent(v___x_1864_, v___x_1865_);
lean_dec(v___x_1864_);
if (v___x_1866_ == 0)
{
lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
lean_dec(v___x_1851_);
lean_dec(v___x_1838_);
lean_dec(v___x_1811_);
lean_dec(v___x_1692_);
v___x_1867_ = l_Lean_Syntax_getArg(v___x_1536_, v___x_1535_);
lean_dec(v___x_1536_);
v___x_1868_ = l_Lean_SourceInfo_fromRef(v_a_1529_, v___x_1866_);
v___x_1869_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1870_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1868_, 3);
v___x_1871_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1868_);
lean_ctor_set(v___x_1871_, 1, v___x_1870_);
v___x_1872_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1873_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1868_);
lean_ctor_set(v___x_1873_, 1, v___x_1872_);
v___x_1874_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1875_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1868_);
lean_ctor_set(v___x_1875_, 1, v___x_1874_);
v___x_1876_ = l_Lean_Syntax_node5(v___x_1868_, v___x_1869_, v___x_1871_, v___x_1542_, v___x_1873_, v___x_1867_, v___x_1875_);
v___x_1877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
lean_ctor_set(v___x_1877_, 1, v_a_1530_);
return v___x_1877_;
}
else
{
lean_object* v___x_1878_; uint8_t v___x_1879_; 
v___x_1878_ = l_Lean_Syntax_getArg(v___x_1851_, v___x_1535_);
lean_dec(v___x_1851_);
v___x_1879_ = l_Lean_Syntax_matchesNull(v___x_1878_, v___x_1541_);
if (v___x_1879_ == 0)
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
lean_dec(v___x_1838_);
lean_dec(v___x_1811_);
lean_dec(v___x_1692_);
v___x_1880_ = l_Lean_Syntax_getArg(v___x_1536_, v___x_1535_);
lean_dec(v___x_1536_);
v___x_1881_ = l_Lean_SourceInfo_fromRef(v_a_1529_, v___x_1879_);
v___x_1882_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1883_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1881_, 3);
v___x_1884_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1881_);
lean_ctor_set(v___x_1884_, 1, v___x_1883_);
v___x_1885_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1886_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1881_);
lean_ctor_set(v___x_1886_, 1, v___x_1885_);
v___x_1887_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1888_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1881_);
lean_ctor_set(v___x_1888_, 1, v___x_1887_);
v___x_1889_ = l_Lean_Syntax_node5(v___x_1881_, v___x_1882_, v___x_1884_, v___x_1542_, v___x_1886_, v___x_1880_, v___x_1888_);
v___x_1890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1889_);
lean_ctor_set(v___x_1890_, 1, v_a_1530_);
return v___x_1890_;
}
else
{
lean_object* v___x_1891_; uint8_t v___x_1892_; 
v___x_1891_ = l_Lean_Syntax_getArg(v___x_1838_, v___x_1535_);
lean_dec(v___x_1838_);
lean_inc(v___x_1891_);
v___x_1892_ = l_Lean_Syntax_matchesNull(v___x_1891_, v___x_1653_);
if (v___x_1892_ == 0)
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
lean_dec(v___x_1891_);
lean_dec(v___x_1811_);
lean_dec(v___x_1692_);
v___x_1893_ = l_Lean_Syntax_getArg(v___x_1536_, v___x_1535_);
lean_dec(v___x_1536_);
v___x_1894_ = l_Lean_SourceInfo_fromRef(v_a_1529_, v___x_1892_);
v___x_1895_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1896_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1894_, 3);
v___x_1897_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1894_);
lean_ctor_set(v___x_1897_, 1, v___x_1896_);
v___x_1898_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1899_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1894_);
lean_ctor_set(v___x_1899_, 1, v___x_1898_);
v___x_1900_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1901_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1894_);
lean_ctor_set(v___x_1901_, 1, v___x_1900_);
v___x_1902_ = l_Lean_Syntax_node5(v___x_1894_, v___x_1895_, v___x_1897_, v___x_1542_, v___x_1899_, v___x_1893_, v___x_1901_);
v___x_1903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1902_);
lean_ctor_set(v___x_1903_, 1, v_a_1530_);
return v___x_1903_;
}
else
{
lean_object* v___x_1904_; uint8_t v___x_1905_; 
v___x_1904_ = l_Lean_Syntax_getArg(v___x_1891_, v___x_1541_);
v___x_1905_ = l_Lean_Syntax_matchesNull(v___x_1904_, v___x_1541_);
if (v___x_1905_ == 0)
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
lean_dec(v___x_1891_);
lean_dec(v___x_1811_);
lean_dec(v___x_1692_);
v___x_1906_ = l_Lean_Syntax_getArg(v___x_1536_, v___x_1535_);
lean_dec(v___x_1536_);
v___x_1907_ = l_Lean_SourceInfo_fromRef(v_a_1529_, v___x_1905_);
v___x_1908_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1909_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1907_, 3);
v___x_1910_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1907_);
lean_ctor_set(v___x_1910_, 1, v___x_1909_);
v___x_1911_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1912_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1907_);
lean_ctor_set(v___x_1912_, 1, v___x_1911_);
v___x_1913_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1914_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1907_);
lean_ctor_set(v___x_1914_, 1, v___x_1913_);
v___x_1915_ = l_Lean_Syntax_node5(v___x_1907_, v___x_1908_, v___x_1910_, v___x_1542_, v___x_1912_, v___x_1906_, v___x_1914_);
v___x_1916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1915_);
lean_ctor_set(v___x_1916_, 1, v_a_1530_);
return v___x_1916_;
}
else
{
lean_object* v___x_1917_; uint8_t v___x_1918_; 
v___x_1917_ = l_Lean_Syntax_getArg(v___x_1891_, v___x_1535_);
v___x_1918_ = l_Lean_Syntax_matchesNull(v___x_1917_, v___x_1541_);
if (v___x_1918_ == 0)
{
lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
lean_dec(v___x_1891_);
lean_dec(v___x_1811_);
lean_dec(v___x_1692_);
v___x_1919_ = l_Lean_Syntax_getArg(v___x_1536_, v___x_1535_);
lean_dec(v___x_1536_);
v___x_1920_ = l_Lean_SourceInfo_fromRef(v_a_1529_, v___x_1918_);
v___x_1921_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1922_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1920_, 3);
v___x_1923_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1920_);
lean_ctor_set(v___x_1923_, 1, v___x_1922_);
v___x_1924_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1925_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1920_);
lean_ctor_set(v___x_1925_, 1, v___x_1924_);
v___x_1926_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1927_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1920_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
v___x_1928_ = l_Lean_Syntax_node5(v___x_1920_, v___x_1921_, v___x_1923_, v___x_1542_, v___x_1925_, v___x_1919_, v___x_1927_);
v___x_1929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1928_);
lean_ctor_set(v___x_1929_, 1, v_a_1530_);
return v___x_1929_;
}
else
{
lean_object* v___x_1930_; uint8_t v___x_1931_; 
v___x_1930_ = l_Lean_Syntax_getArg(v___x_1891_, v___x_1537_);
lean_dec(v___x_1891_);
lean_inc(v___x_1930_);
v___x_1931_ = l_Lean_Syntax_isOfKind(v___x_1930_, v___x_1693_);
if (v___x_1931_ == 0)
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
lean_dec(v___x_1930_);
lean_dec(v___x_1811_);
lean_dec(v___x_1692_);
v___x_1932_ = l_Lean_Syntax_getArg(v___x_1536_, v___x_1535_);
lean_dec(v___x_1536_);
v___x_1933_ = l_Lean_SourceInfo_fromRef(v_a_1529_, v___x_1931_);
v___x_1934_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1935_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1933_, 3);
v___x_1936_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1933_);
lean_ctor_set(v___x_1936_, 1, v___x_1935_);
v___x_1937_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1938_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1933_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
v___x_1939_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1940_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1933_);
lean_ctor_set(v___x_1940_, 1, v___x_1939_);
v___x_1941_ = l_Lean_Syntax_node5(v___x_1933_, v___x_1934_, v___x_1936_, v___x_1542_, v___x_1938_, v___x_1932_, v___x_1940_);
v___x_1942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1941_);
lean_ctor_set(v___x_1942_, 1, v_a_1530_);
return v___x_1942_;
}
else
{
lean_object* v___x_1943_; uint8_t v___x_1944_; 
v___x_1943_ = l_Lean_Syntax_getArg(v___x_1930_, v___x_1535_);
v___x_1944_ = l_Lean_Syntax_matchesNull(v___x_1943_, v___x_1541_);
if (v___x_1944_ == 0)
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
lean_dec(v___x_1930_);
lean_dec(v___x_1811_);
lean_dec(v___x_1692_);
v___x_1945_ = l_Lean_Syntax_getArg(v___x_1536_, v___x_1535_);
lean_dec(v___x_1536_);
v___x_1946_ = l_Lean_SourceInfo_fromRef(v_a_1529_, v___x_1944_);
v___x_1947_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1948_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1946_, 3);
v___x_1949_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1946_);
lean_ctor_set(v___x_1949_, 1, v___x_1948_);
v___x_1950_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1951_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1946_);
lean_ctor_set(v___x_1951_, 1, v___x_1950_);
v___x_1952_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1953_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1946_);
lean_ctor_set(v___x_1953_, 1, v___x_1952_);
v___x_1954_ = l_Lean_Syntax_node5(v___x_1946_, v___x_1947_, v___x_1949_, v___x_1542_, v___x_1951_, v___x_1945_, v___x_1953_);
v___x_1955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1954_);
lean_ctor_set(v___x_1955_, 1, v_a_1530_);
return v___x_1955_;
}
else
{
lean_object* v___x_1956_; lean_object* v___x_1957_; uint8_t v___x_1958_; 
v___x_1956_ = l_Lean_Syntax_getArg(v___x_1542_, v___x_1653_);
v___x_1957_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__18));
lean_inc(v___x_1956_);
v___x_1958_ = l_Lean_Syntax_isOfKind(v___x_1956_, v___x_1957_);
if (v___x_1958_ == 0)
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
lean_dec(v___x_1956_);
lean_dec(v___x_1930_);
lean_dec(v___x_1811_);
lean_dec(v___x_1692_);
v___x_1959_ = l_Lean_Syntax_getArg(v___x_1536_, v___x_1535_);
lean_dec(v___x_1536_);
v___x_1960_ = l_Lean_SourceInfo_fromRef(v_a_1529_, v___x_1958_);
v___x_1961_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1962_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1960_, 3);
v___x_1963_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1960_);
lean_ctor_set(v___x_1963_, 1, v___x_1962_);
v___x_1964_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1965_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1960_);
lean_ctor_set(v___x_1965_, 1, v___x_1964_);
v___x_1966_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1967_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1960_);
lean_ctor_set(v___x_1967_, 1, v___x_1966_);
v___x_1968_ = l_Lean_Syntax_node5(v___x_1960_, v___x_1961_, v___x_1963_, v___x_1542_, v___x_1965_, v___x_1959_, v___x_1967_);
v___x_1969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1968_);
lean_ctor_set(v___x_1969_, 1, v_a_1530_);
return v___x_1969_;
}
else
{
lean_object* v___x_1970_; uint8_t v___x_1971_; 
v___x_1970_ = l_Lean_Syntax_getArg(v___x_1956_, v___x_1541_);
lean_dec(v___x_1956_);
v___x_1971_ = l_Lean_Syntax_matchesNull(v___x_1970_, v___x_1541_);
if (v___x_1971_ == 0)
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; 
lean_dec(v___x_1930_);
lean_dec(v___x_1811_);
lean_dec(v___x_1692_);
v___x_1972_ = l_Lean_Syntax_getArg(v___x_1536_, v___x_1535_);
lean_dec(v___x_1536_);
v___x_1973_ = l_Lean_SourceInfo_fromRef(v_a_1529_, v___x_1971_);
v___x_1974_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1975_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1973_, 3);
v___x_1976_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1973_);
lean_ctor_set(v___x_1976_, 1, v___x_1975_);
v___x_1977_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1978_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1973_);
lean_ctor_set(v___x_1978_, 1, v___x_1977_);
v___x_1979_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1980_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1973_);
lean_ctor_set(v___x_1980_, 1, v___x_1979_);
v___x_1981_ = l_Lean_Syntax_node5(v___x_1973_, v___x_1974_, v___x_1976_, v___x_1542_, v___x_1978_, v___x_1972_, v___x_1980_);
v___x_1982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1981_);
lean_ctor_set(v___x_1982_, 1, v_a_1530_);
return v___x_1982_;
}
else
{
lean_object* v___x_1983_; uint8_t v___x_1984_; 
v___x_1983_ = l_Lean_Syntax_getArg(v___x_1542_, v___x_1837_);
v___x_1984_ = l_Lean_Syntax_matchesNull(v___x_1983_, v___x_1541_);
if (v___x_1984_ == 0)
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
lean_dec(v___x_1930_);
lean_dec(v___x_1811_);
lean_dec(v___x_1692_);
v___x_1985_ = l_Lean_Syntax_getArg(v___x_1536_, v___x_1535_);
lean_dec(v___x_1536_);
v___x_1986_ = l_Lean_SourceInfo_fromRef(v_a_1529_, v___x_1984_);
v___x_1987_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1988_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1986_, 3);
v___x_1989_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1986_);
lean_ctor_set(v___x_1989_, 1, v___x_1988_);
v___x_1990_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1991_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1986_);
lean_ctor_set(v___x_1991_, 1, v___x_1990_);
v___x_1992_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1993_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1986_);
lean_ctor_set(v___x_1993_, 1, v___x_1992_);
v___x_1994_ = l_Lean_Syntax_node5(v___x_1986_, v___x_1987_, v___x_1989_, v___x_1542_, v___x_1991_, v___x_1985_, v___x_1993_);
v___x_1995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1994_);
lean_ctor_set(v___x_1995_, 1, v_a_1530_);
return v___x_1995_;
}
else
{
lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; uint8_t v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
lean_dec(v___x_1542_);
v___x_1996_ = l_Lean_Syntax_getArg(v___x_1692_, v___x_1537_);
lean_dec(v___x_1692_);
v___x_1997_ = l_Lean_Syntax_getArg(v___x_1811_, v___x_1537_);
lean_dec(v___x_1811_);
v___x_1998_ = l_Lean_Syntax_getArg(v___x_1930_, v___x_1537_);
lean_dec(v___x_1930_);
v___x_1999_ = l_Lean_Syntax_getArg(v___x_1536_, v___x_1535_);
lean_dec(v___x_1536_);
v___x_2000_ = 0;
v___x_2001_ = l_Lean_SourceInfo_fromRef(v_a_1529_, v___x_2000_);
v___x_2002_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__1));
v___x_2003_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2001_, 7);
v___x_2004_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2001_);
lean_ctor_set(v___x_2004_, 1, v___x_2003_);
v___x_2005_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2006_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2006_, 0, v___x_2001_);
lean_ctor_set(v___x_2006_, 1, v___x_2005_);
v___x_2007_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__20));
v___x_2008_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__21));
v___x_2009_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2001_);
lean_ctor_set(v___x_2009_, 1, v___x_2008_);
v___x_2010_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__14));
lean_inc_ref_n(v___x_2006_, 2);
v___x_2011_ = l_Lean_Syntax_node3(v___x_2001_, v___x_2010_, v___x_1997_, v___x_2006_, v___x_1998_);
v___x_2012_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__22));
v___x_2013_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2001_);
lean_ctor_set(v___x_2013_, 1, v___x_2012_);
v___x_2014_ = l_Lean_Syntax_node3(v___x_2001_, v___x_2007_, v___x_2009_, v___x_2011_, v___x_2013_);
v___x_2015_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2016_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2001_);
lean_ctor_set(v___x_2016_, 1, v___x_2015_);
v___x_2017_ = l_Lean_Syntax_node7(v___x_2001_, v___x_2002_, v___x_2004_, v___x_1996_, v___x_2006_, v___x_2014_, v___x_2006_, v___x_1999_, v___x_2016_);
v___x_2018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2018_, 0, v___x_2017_);
lean_ctor_set(v___x_2018_, 1, v_a_1530_);
return v___x_2018_;
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_unexpandDenote___boxed(lean_object* v_x_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l_Std_Sat_AIG_unexpandDenote(v_x_2019_, v_a_2020_, v_a_2021_);
lean_dec(v_a_2020_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGate___redArg(lean_object* v_aig_2023_, lean_object* v_input_2024_){
_start:
{
lean_object* v_lhs_2025_; lean_object* v_rhs_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2064_; 
v_lhs_2025_ = lean_ctor_get(v_input_2024_, 0);
v_rhs_2026_ = lean_ctor_get(v_input_2024_, 1);
v_isSharedCheck_2064_ = !lean_is_exclusive(v_input_2024_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2028_ = v_input_2024_;
v_isShared_2029_ = v_isSharedCheck_2064_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_rhs_2026_);
lean_inc(v_lhs_2025_);
lean_dec(v_input_2024_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2064_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v_decls_2030_; lean_object* v_cache_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2063_; 
v_decls_2030_ = lean_ctor_get(v_aig_2023_, 0);
v_cache_2031_ = lean_ctor_get(v_aig_2023_, 1);
v_isSharedCheck_2063_ = !lean_is_exclusive(v_aig_2023_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2033_ = v_aig_2023_;
v_isShared_2034_ = v_isSharedCheck_2063_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_cache_2031_);
lean_inc(v_decls_2030_);
lean_dec(v_aig_2023_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2063_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v_gate_2035_; uint8_t v_invert_2036_; lean_object* v_gate_2037_; uint8_t v_invert_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2062_; 
v_gate_2035_ = lean_ctor_get(v_lhs_2025_, 0);
lean_inc(v_gate_2035_);
v_invert_2036_ = lean_ctor_get_uint8(v_lhs_2025_, sizeof(void*)*1);
lean_dec_ref(v_lhs_2025_);
v_gate_2037_ = lean_ctor_get(v_rhs_2026_, 0);
v_invert_2038_ = lean_ctor_get_uint8(v_rhs_2026_, sizeof(void*)*1);
v_isSharedCheck_2062_ = !lean_is_exclusive(v_rhs_2026_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2040_ = v_rhs_2026_;
v_isShared_2041_ = v_isSharedCheck_2062_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_gate_2037_);
lean_dec(v_rhs_2026_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2062_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v_g_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2051_; 
v_g_2042_ = lean_array_get_size(v_decls_2030_);
v___x_2043_ = lean_unsigned_to_nat(2u);
v___x_2044_ = lean_nat_mul(v_gate_2035_, v___x_2043_);
lean_dec(v_gate_2035_);
v___x_2045_ = l_Bool_toNat(v_invert_2036_);
v___x_2046_ = lean_nat_lor(v___x_2044_, v___x_2045_);
lean_dec(v___x_2045_);
lean_dec(v___x_2044_);
v___x_2047_ = lean_nat_mul(v_gate_2037_, v___x_2043_);
lean_dec(v_gate_2037_);
v___x_2048_ = l_Bool_toNat(v_invert_2038_);
v___x_2049_ = lean_nat_lor(v___x_2047_, v___x_2048_);
lean_dec(v___x_2048_);
lean_dec(v___x_2047_);
if (v_isShared_2029_ == 0)
{
lean_ctor_set_tag(v___x_2028_, 2);
lean_ctor_set(v___x_2028_, 1, v___x_2049_);
lean_ctor_set(v___x_2028_, 0, v___x_2046_);
v___x_2051_ = v___x_2028_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v___x_2046_);
lean_ctor_set(v_reuseFailAlloc_2061_, 1, v___x_2049_);
v___x_2051_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
lean_object* v_decls_2052_; lean_object* v___x_2054_; 
v_decls_2052_ = lean_array_push(v_decls_2030_, v___x_2051_);
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 0, v_decls_2052_);
v___x_2054_ = v___x_2033_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_decls_2052_);
lean_ctor_set(v_reuseFailAlloc_2060_, 1, v_cache_2031_);
v___x_2054_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
uint8_t v___x_2055_; lean_object* v___x_2057_; 
v___x_2055_ = 0;
if (v_isShared_2041_ == 0)
{
lean_ctor_set(v___x_2040_, 0, v_g_2042_);
v___x_2057_ = v___x_2040_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_g_2042_);
v___x_2057_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
lean_object* v___x_2058_; 
lean_ctor_set_uint8(v___x_2057_, sizeof(void*)*1, v___x_2055_);
v___x_2058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2054_);
lean_ctor_set(v___x_2058_, 1, v___x_2057_);
return v___x_2058_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGate(lean_object* v_00_u03b1_2065_, lean_object* v_inst_2066_, lean_object* v_inst_2067_, lean_object* v_aig_2068_, lean_object* v_input_2069_){
_start:
{
lean_object* v___x_2070_; 
v___x_2070_ = l_Std_Sat_AIG_mkGate___redArg(v_aig_2068_, v_input_2069_);
return v___x_2070_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGate___boxed(lean_object* v_00_u03b1_2071_, lean_object* v_inst_2072_, lean_object* v_inst_2073_, lean_object* v_aig_2074_, lean_object* v_input_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l_Std_Sat_AIG_mkGate(v_00_u03b1_2071_, v_inst_2072_, v_inst_2073_, v_aig_2074_, v_input_2075_);
lean_dec_ref(v_inst_2073_);
lean_dec_ref(v_inst_2072_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtom___redArg(lean_object* v_aig_2077_, lean_object* v_n_2078_){
_start:
{
lean_object* v_decls_2079_; lean_object* v_cache_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2093_; 
v_decls_2079_ = lean_ctor_get(v_aig_2077_, 0);
v_cache_2080_ = lean_ctor_get(v_aig_2077_, 1);
v_isSharedCheck_2093_ = !lean_is_exclusive(v_aig_2077_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2082_ = v_aig_2077_;
v_isShared_2083_ = v_isSharedCheck_2093_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_cache_2080_);
lean_inc(v_decls_2079_);
lean_dec(v_aig_2077_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2093_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v_g_2084_; lean_object* v___x_2085_; lean_object* v_decls_2086_; lean_object* v___x_2088_; 
v_g_2084_ = lean_array_get_size(v_decls_2079_);
v___x_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2085_, 0, v_n_2078_);
v_decls_2086_ = lean_array_push(v_decls_2079_, v___x_2085_);
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 0, v_decls_2086_);
v___x_2088_ = v___x_2082_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_decls_2086_);
lean_ctor_set(v_reuseFailAlloc_2092_, 1, v_cache_2080_);
v___x_2088_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
uint8_t v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2089_ = 0;
v___x_2090_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2090_, 0, v_g_2084_);
lean_ctor_set_uint8(v___x_2090_, sizeof(void*)*1, v___x_2089_);
v___x_2091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2088_);
lean_ctor_set(v___x_2091_, 1, v___x_2090_);
return v___x_2091_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtom(lean_object* v_00_u03b1_2094_, lean_object* v_inst_2095_, lean_object* v_inst_2096_, lean_object* v_aig_2097_, lean_object* v_n_2098_){
_start:
{
lean_object* v___x_2099_; 
v___x_2099_ = l_Std_Sat_AIG_mkAtom___redArg(v_aig_2097_, v_n_2098_);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtom___boxed(lean_object* v_00_u03b1_2100_, lean_object* v_inst_2101_, lean_object* v_inst_2102_, lean_object* v_aig_2103_, lean_object* v_n_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_Std_Sat_AIG_mkAtom(v_00_u03b1_2100_, v_inst_2101_, v_inst_2102_, v_aig_2103_, v_n_2104_);
lean_dec_ref(v_inst_2102_);
lean_dec_ref(v_inst_2101_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConst___redArg(lean_object* v_aig_2106_, uint8_t v_val_2107_){
_start:
{
lean_object* v_decls_2108_; lean_object* v_cache_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2121_; 
v_decls_2108_ = lean_ctor_get(v_aig_2106_, 0);
v_cache_2109_ = lean_ctor_get(v_aig_2106_, 1);
v_isSharedCheck_2121_ = !lean_is_exclusive(v_aig_2106_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2111_ = v_aig_2106_;
v_isShared_2112_ = v_isSharedCheck_2121_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_cache_2109_);
lean_inc(v_decls_2108_);
lean_dec(v_aig_2106_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2121_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v_g_2113_; lean_object* v___x_2114_; lean_object* v_decls_2115_; lean_object* v___x_2117_; 
v_g_2113_ = lean_array_get_size(v_decls_2108_);
v___x_2114_ = lean_box(0);
v_decls_2115_ = lean_array_push(v_decls_2108_, v___x_2114_);
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 0, v_decls_2115_);
v___x_2117_ = v___x_2111_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_decls_2115_);
lean_ctor_set(v_reuseFailAlloc_2120_, 1, v_cache_2109_);
v___x_2117_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2118_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2118_, 0, v_g_2113_);
lean_ctor_set_uint8(v___x_2118_, sizeof(void*)*1, v_val_2107_);
v___x_2119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2117_);
lean_ctor_set(v___x_2119_, 1, v___x_2118_);
return v___x_2119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConst___redArg___boxed(lean_object* v_aig_2122_, lean_object* v_val_2123_){
_start:
{
uint8_t v_val_boxed_2124_; lean_object* v_res_2125_; 
v_val_boxed_2124_ = lean_unbox(v_val_2123_);
v_res_2125_ = l_Std_Sat_AIG_mkConst___redArg(v_aig_2122_, v_val_boxed_2124_);
return v_res_2125_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConst(lean_object* v_00_u03b1_2126_, lean_object* v_inst_2127_, lean_object* v_inst_2128_, lean_object* v_aig_2129_, uint8_t v_val_2130_){
_start:
{
lean_object* v___x_2131_; 
v___x_2131_ = l_Std_Sat_AIG_mkConst___redArg(v_aig_2129_, v_val_2130_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConst___boxed(lean_object* v_00_u03b1_2132_, lean_object* v_inst_2133_, lean_object* v_inst_2134_, lean_object* v_aig_2135_, lean_object* v_val_2136_){
_start:
{
uint8_t v_val_boxed_2137_; lean_object* v_res_2138_; 
v_val_boxed_2137_ = lean_unbox(v_val_2136_);
v_res_2138_ = l_Std_Sat_AIG_mkConst(v_00_u03b1_2132_, v_inst_2133_, v_inst_2134_, v_aig_2135_, v_val_boxed_2137_);
lean_dec_ref(v_inst_2134_);
lean_dec_ref(v_inst_2133_);
return v_res_2138_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_isConstant___redArg(lean_object* v_aig_2139_, lean_object* v_ref_2140_, uint8_t v_b_2141_){
_start:
{
lean_object* v_gate_2142_; uint8_t v_invert_2143_; lean_object* v_decls_2144_; lean_object* v_decl_2145_; uint8_t v___y_2147_; 
v_gate_2142_ = lean_ctor_get(v_ref_2140_, 0);
v_invert_2143_ = lean_ctor_get_uint8(v_ref_2140_, sizeof(void*)*1);
v_decls_2144_ = lean_ctor_get(v_aig_2139_, 0);
v_decl_2145_ = lean_array_fget_borrowed(v_decls_2144_, v_gate_2142_);
if (v_b_2141_ == 0)
{
if (v_invert_2143_ == 0)
{
uint8_t v___x_2149_; 
v___x_2149_ = 1;
v___y_2147_ = v___x_2149_;
goto v___jp_2146_;
}
else
{
v___y_2147_ = v_b_2141_;
goto v___jp_2146_;
}
}
else
{
v___y_2147_ = v_invert_2143_;
goto v___jp_2146_;
}
v___jp_2146_:
{
if (lean_obj_tag(v_decl_2145_) == 0)
{
return v___y_2147_;
}
else
{
uint8_t v___x_2148_; 
v___x_2148_ = 0;
return v___x_2148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_isConstant___redArg___boxed(lean_object* v_aig_2150_, lean_object* v_ref_2151_, lean_object* v_b_2152_){
_start:
{
uint8_t v_b_boxed_2153_; uint8_t v_res_2154_; lean_object* v_r_2155_; 
v_b_boxed_2153_ = lean_unbox(v_b_2152_);
v_res_2154_ = l_Std_Sat_AIG_isConstant___redArg(v_aig_2150_, v_ref_2151_, v_b_boxed_2153_);
lean_dec_ref(v_ref_2151_);
lean_dec_ref(v_aig_2150_);
v_r_2155_ = lean_box(v_res_2154_);
return v_r_2155_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_isConstant(lean_object* v_00_u03b1_2156_, lean_object* v_inst_2157_, lean_object* v_inst_2158_, lean_object* v_aig_2159_, lean_object* v_ref_2160_, uint8_t v_b_2161_){
_start:
{
uint8_t v___x_2162_; 
v___x_2162_ = l_Std_Sat_AIG_isConstant___redArg(v_aig_2159_, v_ref_2160_, v_b_2161_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_isConstant___boxed(lean_object* v_00_u03b1_2163_, lean_object* v_inst_2164_, lean_object* v_inst_2165_, lean_object* v_aig_2166_, lean_object* v_ref_2167_, lean_object* v_b_2168_){
_start:
{
uint8_t v_b_boxed_2169_; uint8_t v_res_2170_; lean_object* v_r_2171_; 
v_b_boxed_2169_ = lean_unbox(v_b_2168_);
v_res_2170_ = l_Std_Sat_AIG_isConstant(v_00_u03b1_2163_, v_inst_2164_, v_inst_2165_, v_aig_2166_, v_ref_2167_, v_b_boxed_2169_);
lean_dec_ref(v_ref_2167_);
lean_dec_ref(v_aig_2166_);
lean_dec_ref(v_inst_2165_);
lean_dec_ref(v_inst_2164_);
v_r_2171_ = lean_box(v_res_2170_);
return v_r_2171_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___redArg(lean_object* v_aig_2172_, lean_object* v_ref_2173_){
_start:
{
lean_object* v_gate_2174_; uint8_t v_invert_2175_; lean_object* v_decls_2176_; lean_object* v_decl_2177_; 
v_gate_2174_ = lean_ctor_get(v_ref_2173_, 0);
v_invert_2175_ = lean_ctor_get_uint8(v_ref_2173_, sizeof(void*)*1);
v_decls_2176_ = lean_ctor_get(v_aig_2172_, 0);
v_decl_2177_ = lean_array_fget_borrowed(v_decls_2176_, v_gate_2174_);
if (lean_obj_tag(v_decl_2177_) == 0)
{
lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2178_ = lean_box(v_invert_2175_);
v___x_2179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2179_, 0, v___x_2178_);
return v___x_2179_;
}
else
{
lean_object* v___x_2180_; 
v___x_2180_ = lean_box(0);
return v___x_2180_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___redArg___boxed(lean_object* v_aig_2181_, lean_object* v_ref_2182_){
_start:
{
lean_object* v_res_2183_; 
v_res_2183_ = l_Std_Sat_AIG_getConstant___redArg(v_aig_2181_, v_ref_2182_);
lean_dec_ref(v_ref_2182_);
lean_dec_ref(v_aig_2181_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant(lean_object* v_00_u03b1_2184_, lean_object* v_inst_2185_, lean_object* v_inst_2186_, lean_object* v_aig_2187_, lean_object* v_ref_2188_){
_start:
{
lean_object* v___x_2189_; 
v___x_2189_ = l_Std_Sat_AIG_getConstant___redArg(v_aig_2187_, v_ref_2188_);
return v___x_2189_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___boxed(lean_object* v_00_u03b1_2190_, lean_object* v_inst_2191_, lean_object* v_inst_2192_, lean_object* v_aig_2193_, lean_object* v_ref_2194_){
_start:
{
lean_object* v_res_2195_; 
v_res_2195_ = l_Std_Sat_AIG_getConstant(v_00_u03b1_2190_, v_inst_2191_, v_inst_2192_, v_aig_2193_, v_ref_2194_);
lean_dec_ref(v_ref_2194_);
lean_dec_ref(v_aig_2193_);
lean_dec_ref(v_inst_2192_);
lean_dec_ref(v_inst_2191_);
return v_res_2195_;
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
