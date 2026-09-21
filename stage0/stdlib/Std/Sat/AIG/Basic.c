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
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Bool_toNat(uint8_t);
lean_object* lean_nat_lxor(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
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
static const lean_string_object l_Std_Sat_AIG_Cache_empty___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_Sat_AIG_Cache_empty___auto__1___closed__0 = (const lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__0_value;
static const lean_string_object l_Std_Sat_AIG_Cache_empty___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_Sat_AIG_Cache_empty___auto__1___closed__1 = (const lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__1_value;
static const lean_string_object l_Std_Sat_AIG_Cache_empty___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Std_Sat_AIG_Cache_empty___auto__1___closed__2 = (const lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__2_value;
static const lean_string_object l_Std_Sat_AIG_Cache_empty___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Std_Sat_AIG_Cache_empty___auto__1___closed__3 = (const lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__3_value;
static const lean_ctor_object l_Std_Sat_AIG_Cache_empty___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Sat_AIG_Cache_empty___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__4_value_aux_0),((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Sat_AIG_Cache_empty___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__4_value_aux_1),((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Sat_AIG_Cache_empty___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__4_value_aux_2),((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Std_Sat_AIG_Cache_empty___auto__1___closed__4 = (const lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__4_value;
static const lean_array_object l_Std_Sat_AIG_Cache_empty___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Sat_AIG_Cache_empty___auto__1___closed__5 = (const lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__5_value;
static const lean_string_object l_Std_Sat_AIG_Cache_empty___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Std_Sat_AIG_Cache_empty___auto__1___closed__6 = (const lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__6_value;
static const lean_ctor_object l_Std_Sat_AIG_Cache_empty___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Sat_AIG_Cache_empty___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__7_value_aux_0),((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Sat_AIG_Cache_empty___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__7_value_aux_1),((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Sat_AIG_Cache_empty___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__7_value_aux_2),((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Std_Sat_AIG_Cache_empty___auto__1___closed__7 = (const lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__7_value;
static const lean_string_object l_Std_Sat_AIG_Cache_empty___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_Sat_AIG_Cache_empty___auto__1___closed__8 = (const lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__8_value;
static const lean_ctor_object l_Std_Sat_AIG_Cache_empty___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_Sat_AIG_Cache_empty___auto__1___closed__9 = (const lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__9_value;
static const lean_string_object l_Std_Sat_AIG_Cache_empty___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_Std_Sat_AIG_Cache_empty___auto__1___closed__10 = (const lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__10_value;
static const lean_ctor_object l_Std_Sat_AIG_Cache_empty___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Sat_AIG_Cache_empty___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__11_value_aux_0),((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Sat_AIG_Cache_empty___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__11_value_aux_1),((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Sat_AIG_Cache_empty___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__11_value_aux_2),((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* l_Std_Sat_AIG_Cache_empty___auto__1___closed__11 = (const lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__11_value;
static lean_once_cell_t l_Std_Sat_AIG_Cache_empty___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_Cache_empty___auto__1___closed__12;
static lean_once_cell_t l_Std_Sat_AIG_Cache_empty___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_Cache_empty___auto__1___closed__13;
static const lean_string_object l_Std_Sat_AIG_Cache_empty___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Std_Sat_AIG_Cache_empty___auto__1___closed__14 = (const lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__14_value;
static const lean_ctor_object l_Std_Sat_AIG_Cache_empty___auto__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Sat_AIG_Cache_empty___auto__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__15_value_aux_0),((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Sat_AIG_Cache_empty___auto__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__15_value_aux_1),((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Sat_AIG_Cache_empty___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__15_value_aux_2),((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Std_Sat_AIG_Cache_empty___auto__1___closed__15 = (const lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__15_value;
static const lean_ctor_object l_Std_Sat_AIG_Cache_empty___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__9_value),((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__5_value)}};
static const lean_object* l_Std_Sat_AIG_Cache_empty___auto__1___closed__16 = (const lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__16_value;
static lean_once_cell_t l_Std_Sat_AIG_Cache_empty___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_Cache_empty___auto__1___closed__17;
static lean_once_cell_t l_Std_Sat_AIG_Cache_empty___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_Cache_empty___auto__1___closed__18;
static lean_once_cell_t l_Std_Sat_AIG_Cache_empty___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_Cache_empty___auto__1___closed__19;
static lean_once_cell_t l_Std_Sat_AIG_Cache_empty___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_Cache_empty___auto__1___closed__20;
static lean_once_cell_t l_Std_Sat_AIG_Cache_empty___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_Cache_empty___auto__1___closed__21;
static lean_once_cell_t l_Std_Sat_AIG_Cache_empty___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_Cache_empty___auto__1___closed__22;
static lean_once_cell_t l_Std_Sat_AIG_Cache_empty___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_Cache_empty___auto__1___closed__23;
static lean_once_cell_t l_Std_Sat_AIG_Cache_empty___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_Cache_empty___auto__1___closed__24;
static lean_once_cell_t l_Std_Sat_AIG_Cache_empty___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_Cache_empty___auto__1___closed__25;
static lean_once_cell_t l_Std_Sat_AIG_Cache_empty___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_Cache_empty___auto__1___closed__26;
static lean_once_cell_t l_Std_Sat_AIG_Cache_empty___auto__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_Cache_empty___auto__1___closed__27;
static lean_once_cell_t l_Std_Sat_AIG_Cache_empty___auto__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_Cache_empty___auto__1___closed__28;
static lean_once_cell_t l_Std_Sat_AIG_Cache_empty___auto__1___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_Cache_empty___auto__1___closed__29;
static lean_once_cell_t l_Std_Sat_AIG_Cache_empty___auto__1___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_Cache_empty___auto__1___closed__30;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_empty___auto__1;
static lean_once_cell_t l_Std_Sat_AIG_Cache_empty___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_Cache_empty___redArg___closed__0;
static lean_once_cell_t l_Std_Sat_AIG_Cache_empty___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_Cache_empty___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_empty___redArg();
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_empty___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_empty(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_empty___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_Cache_insert___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_Cache_get_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_Cache_get_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_ofAtoms_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_ofAtoms_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_ofAtoms_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_ofAtoms_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_Cache_ofAtoms_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_Cache_ofAtoms_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_ofAtoms___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_ofAtoms___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_ofAtoms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_ofAtoms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__0 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__0_value;
static const lean_string_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__1 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__1_value;
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2_value_aux_0),((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2_value_aux_1),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2_value_aux_2),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2_value;
static const lean_string_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "denote"};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__3 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__3_value;
static lean_once_cell_t l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4;
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(104, 157, 36, 77, 177, 136, 111, 163)}};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__5 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__5_value;
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6_value_aux_0),((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__1_value),LEAN_SCALAR_PTR_LITERAL(171, 82, 193, 103, 140, 69, 25, 78)}};
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6_value_aux_1),((lean_object*)&l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__2_value),LEAN_SCALAR_PTR_LITERAL(159, 100, 232, 179, 195, 137, 50, 146)}};
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6_value_aux_2),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(92, 0, 130, 77, 137, 144, 235, 232)}};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6_value;
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__7 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__7_value;
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6_value)}};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__8 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__8_value;
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__9 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__9_value;
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__7_value),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__9_value)}};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__10 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__10_value;
LEAN_EXPORT lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__0 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__0_value;
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__1_value_aux_0),((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__1_value_aux_1),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__1_value_aux_2),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__1 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__1_value;
static const lean_string_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__2 = (const lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__2_value;
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__3_value_aux_0),((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__3_value_aux_1),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
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
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__1_value_aux_0),((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__1_value_aux_1),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__1_value_aux_2),((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__0_value),LEAN_SCALAR_PTR_LITERAL(50, 43, 73, 62, 118, 124, 31, 28)}};
static const lean_object* l_Std_Sat_AIG_unexpandDenote___closed__1 = (const lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__1_value;
static const lean_string_object l_Std_Sat_AIG_unexpandDenote___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Std_Sat_AIG_unexpandDenote___closed__2 = (const lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__2_value;
static const lean_string_object l_Std_Sat_AIG_unexpandDenote___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l_Std_Sat_AIG_unexpandDenote___closed__3 = (const lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__3_value;
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__4_value_aux_0),((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__4_value_aux_1),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__4_value_aux_2),((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l_Std_Sat_AIG_unexpandDenote___closed__4 = (const lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__4_value;
static const lean_string_object l_Std_Sat_AIG_unexpandDenote___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "structInstField"};
static const lean_object* l_Std_Sat_AIG_unexpandDenote___closed__5 = (const lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__5_value;
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__6_value_aux_0),((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__6_value_aux_1),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__6_value_aux_2),((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__5_value),LEAN_SCALAR_PTR_LITERAL(50, 77, 20, 88, 28, 210, 230, 84)}};
static const lean_object* l_Std_Sat_AIG_unexpandDenote___closed__6 = (const lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__6_value;
static const lean_string_object l_Std_Sat_AIG_unexpandDenote___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "structInstLVal"};
static const lean_object* l_Std_Sat_AIG_unexpandDenote___closed__7 = (const lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__7_value;
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__8_value_aux_0),((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__8_value_aux_1),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__8_value_aux_2),((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__7_value),LEAN_SCALAR_PTR_LITERAL(185, 133, 6, 147, 6, 183, 100, 198)}};
static const lean_object* l_Std_Sat_AIG_unexpandDenote___closed__8 = (const lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__8_value;
static const lean_string_object l_Std_Sat_AIG_unexpandDenote___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "aig"};
static const lean_object* l_Std_Sat_AIG_unexpandDenote___closed__9 = (const lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__9_value;
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__9_value),LEAN_SCALAR_PTR_LITERAL(115, 31, 37, 57, 248, 230, 152, 117)}};
static const lean_object* l_Std_Sat_AIG_unexpandDenote___closed__10 = (const lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__10_value;
static const lean_string_object l_Std_Sat_AIG_unexpandDenote___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "structInstFieldDef"};
static const lean_object* l_Std_Sat_AIG_unexpandDenote___closed__11 = (const lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__11_value;
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__12_value_aux_0),((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__12_value_aux_1),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
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
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__18_value_aux_0),((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__18_value_aux_1),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__18_value_aux_2),((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__17_value),LEAN_SCALAR_PTR_LITERAL(13, 1, 242, 203, 207, 188, 181, 160)}};
static const lean_object* l_Std_Sat_AIG_unexpandDenote___closed__18 = (const lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__18_value;
static const lean_string_object l_Std_Sat_AIG_unexpandDenote___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "anonymousCtor"};
static const lean_object* l_Std_Sat_AIG_unexpandDenote___closed__19 = (const lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__19_value;
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__20_value_aux_0),((lean_object*)&l_Std_Sat_AIG_Cache_empty___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__20_value_aux_1),((lean_object*)&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Sat_AIG_unexpandDenote___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__20_value_aux_2),((lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__19_value),LEAN_SCALAR_PTR_LITERAL(56, 53, 154, 97, 179, 232, 94, 186)}};
static const lean_object* l_Std_Sat_AIG_unexpandDenote___closed__20 = (const lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__20_value;
static const lean_string_object l_Std_Sat_AIG_unexpandDenote___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟨"};
static const lean_object* l_Std_Sat_AIG_unexpandDenote___closed__21 = (const lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__21_value;
static const lean_string_object l_Std_Sat_AIG_unexpandDenote___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟩"};
static const lean_object* l_Std_Sat_AIG_unexpandDenote___closed__22 = (const lean_object*)&l_Std_Sat_AIG_unexpandDenote___closed__22_value;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_unexpandDenote(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_unexpandDenote___boxed(lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__12(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__10));
v___x_386_ = l_Lean_mkAtom(v___x_385_);
return v___x_386_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__13(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_387_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__12, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__12_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__12);
v___x_388_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__5));
v___x_389_ = lean_array_push(v___x_388_, v___x_387_);
return v___x_389_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__17(void){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_400_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__16));
v___x_401_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__5));
v___x_402_ = lean_array_push(v___x_401_, v___x_400_);
return v___x_402_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__18(void){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_403_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__17, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__17_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__17);
v___x_404_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__15));
v___x_405_ = lean_box(2);
v___x_406_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
lean_ctor_set(v___x_406_, 1, v___x_404_);
lean_ctor_set(v___x_406_, 2, v___x_403_);
return v___x_406_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__19(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_407_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__18, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__18_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__18);
v___x_408_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__13, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__13_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__13);
v___x_409_ = lean_array_push(v___x_408_, v___x_407_);
return v___x_409_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__20(void){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_410_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__16));
v___x_411_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__19, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__19_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__19);
v___x_412_ = lean_array_push(v___x_411_, v___x_410_);
return v___x_412_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__21(void){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_413_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__16));
v___x_414_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__20, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__20_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__20);
v___x_415_ = lean_array_push(v___x_414_, v___x_413_);
return v___x_415_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__22(void){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_416_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__16));
v___x_417_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__21, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__21_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__21);
v___x_418_ = lean_array_push(v___x_417_, v___x_416_);
return v___x_418_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__23(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_419_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__16));
v___x_420_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__22, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__22_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__22);
v___x_421_ = lean_array_push(v___x_420_, v___x_419_);
return v___x_421_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__24(void){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_422_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__23, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__23_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__23);
v___x_423_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__11));
v___x_424_ = lean_box(2);
v___x_425_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
lean_ctor_set(v___x_425_, 1, v___x_423_);
lean_ctor_set(v___x_425_, 2, v___x_422_);
return v___x_425_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__25(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_426_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__24, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__24_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__24);
v___x_427_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__5));
v___x_428_ = lean_array_push(v___x_427_, v___x_426_);
return v___x_428_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__26(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_429_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__25, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__25_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__25);
v___x_430_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__9));
v___x_431_ = lean_box(2);
v___x_432_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
lean_ctor_set(v___x_432_, 1, v___x_430_);
lean_ctor_set(v___x_432_, 2, v___x_429_);
return v___x_432_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__27(void){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_433_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__26, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__26_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__26);
v___x_434_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__5));
v___x_435_ = lean_array_push(v___x_434_, v___x_433_);
return v___x_435_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__28(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_436_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__27, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__27_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__27);
v___x_437_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__7));
v___x_438_ = lean_box(2);
v___x_439_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
lean_ctor_set(v___x_439_, 1, v___x_437_);
lean_ctor_set(v___x_439_, 2, v___x_436_);
return v___x_439_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__29(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_440_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__28, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__28_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__28);
v___x_441_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__5));
v___x_442_ = lean_array_push(v___x_441_, v___x_440_);
return v___x_442_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__30(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_443_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__29, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__29_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__29);
v___x_444_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__4));
v___x_445_ = lean_box(2);
v___x_446_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
lean_ctor_set(v___x_446_, 1, v___x_444_);
lean_ctor_set(v___x_446_, 2, v___x_443_);
return v___x_446_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1(void){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__30, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__30_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__30);
return v___x_447_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___redArg___closed__0(void){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_448_ = lean_box(0);
v___x_449_ = lean_unsigned_to_nat(16u);
v___x_450_ = lean_mk_array(v___x_449_, v___x_448_);
return v___x_450_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___redArg___closed__1(void){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_451_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___redArg___closed__0, &l_Std_Sat_AIG_Cache_empty___redArg___closed__0_once, _init_l_Std_Sat_AIG_Cache_empty___redArg___closed__0);
v___x_452_ = lean_unsigned_to_nat(0u);
v___x_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
lean_ctor_set(v___x_453_, 1, v___x_451_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_empty___redArg(){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___redArg___closed__1, &l_Std_Sat_AIG_Cache_empty___redArg___closed__1_once, _init_l_Std_Sat_AIG_Cache_empty___redArg___closed__1);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_empty___redArg___boxed(lean_object* v___dummy_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Std_Sat_AIG_Cache_empty___redArg();
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_empty(lean_object* v_00_u03b1_458_, lean_object* v_inst_459_, lean_object* v_inst_460_, lean_object* v_decls_461_, lean_object* v_hatoms_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___redArg___closed__1, &l_Std_Sat_AIG_Cache_empty___redArg___closed__1_once, _init_l_Std_Sat_AIG_Cache_empty___redArg___closed__1);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_empty___boxed(lean_object* v_00_u03b1_464_, lean_object* v_inst_465_, lean_object* v_inst_466_, lean_object* v_decls_467_, lean_object* v_hatoms_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Std_Sat_AIG_Cache_empty(v_00_u03b1_464_, v_inst_465_, v_inst_466_, v_decls_467_, v_hatoms_468_);
lean_dec_ref(v_decls_467_);
lean_dec_ref(v_inst_466_);
lean_dec_ref(v_inst_465_);
return v_res_469_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_Cache_insert___redArg___lam__0(lean_object* v_inst_470_, lean_object* v_a_471_, lean_object* v_b_472_){
_start:
{
uint8_t v___x_473_; 
v___x_473_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v_inst_470_, v_a_471_, v_b_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed(lean_object* v_inst_474_, lean_object* v_a_475_, lean_object* v_b_476_){
_start:
{
uint8_t v_res_477_; lean_object* v_r_478_; 
v_res_477_ = l_Std_Sat_AIG_Cache_insert___redArg___lam__0(v_inst_474_, v_a_475_, v_b_476_);
v_r_478_ = lean_box(v_res_477_);
return v_r_478_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___redArg(lean_object* v_inst_479_, lean_object* v_inst_480_, lean_object* v_decls_481_, lean_object* v_cache_482_, lean_object* v_decl_483_){
_start:
{
lean_object* v___f_484_; lean_object* v___x_485_; lean_object* v___f_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___f_484_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_484_, 0, v_inst_480_);
v___x_485_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_485_, 0, lean_box(0));
lean_closure_set(v___x_485_, 1, v_inst_479_);
v___f_486_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_486_, 0, v___f_484_);
v___x_487_ = lean_array_get_size(v_decls_481_);
v___x_488_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_486_, v___x_485_, v_cache_482_, v_decl_483_, v___x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___redArg___boxed(lean_object* v_inst_489_, lean_object* v_inst_490_, lean_object* v_decls_491_, lean_object* v_cache_492_, lean_object* v_decl_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Std_Sat_AIG_Cache_insert___redArg(v_inst_489_, v_inst_490_, v_decls_491_, v_cache_492_, v_decl_493_);
lean_dec_ref(v_decls_491_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert(lean_object* v_00_u03b1_495_, lean_object* v_inst_496_, lean_object* v_inst_497_, lean_object* v_decls_498_, lean_object* v_cache_499_, lean_object* v_decl_500_, lean_object* v_hmiss_501_){
_start:
{
lean_object* v___f_502_; lean_object* v___x_503_; lean_object* v___f_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___f_502_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_502_, 0, v_inst_497_);
v___x_503_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_503_, 0, lean_box(0));
lean_closure_set(v___x_503_, 1, v_inst_496_);
v___f_504_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_504_, 0, v___f_502_);
v___x_505_ = lean_array_get_size(v_decls_498_);
v___x_506_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_504_, v___x_503_, v_cache_499_, v_decl_500_, v___x_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___boxed(lean_object* v_00_u03b1_507_, lean_object* v_inst_508_, lean_object* v_inst_509_, lean_object* v_decls_510_, lean_object* v_cache_511_, lean_object* v_decl_512_, lean_object* v_hmiss_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Std_Sat_AIG_Cache_insert(v_00_u03b1_507_, v_inst_508_, v_inst_509_, v_decls_510_, v_cache_511_, v_decl_512_, v_hmiss_513_);
lean_dec_ref(v_decls_510_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f___redArg(lean_object* v_inst_515_, lean_object* v_inst_516_, lean_object* v_cache_517_, lean_object* v_decl_518_){
_start:
{
lean_object* v___f_519_; lean_object* v___x_520_; lean_object* v___f_521_; lean_object* v___x_522_; 
v___f_519_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_519_, 0, v_inst_516_);
v___x_520_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_520_, 0, lean_box(0));
lean_closure_set(v___x_520_, 1, v_inst_515_);
v___f_521_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_521_, 0, v___f_519_);
v___x_522_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_521_, v___x_520_, v_cache_517_, v_decl_518_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v___x_523_; 
v___x_523_ = lean_box(0);
return v___x_523_;
}
else
{
lean_object* v_val_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_531_; 
v_val_524_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_531_ == 0)
{
v___x_526_ = v___x_522_;
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_val_524_);
lean_dec(v___x_522_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_529_; 
if (v_isShared_527_ == 0)
{
v___x_529_ = v___x_526_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_val_524_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f___redArg___boxed(lean_object* v_inst_532_, lean_object* v_inst_533_, lean_object* v_cache_534_, lean_object* v_decl_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Std_Sat_AIG_Cache_get_x3f___redArg(v_inst_532_, v_inst_533_, v_cache_534_, v_decl_535_);
lean_dec_ref(v_cache_534_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f(lean_object* v_00_u03b1_537_, lean_object* v_inst_538_, lean_object* v_inst_539_, lean_object* v_decls_540_, lean_object* v_cache_541_, lean_object* v_decl_542_){
_start:
{
lean_object* v___f_543_; lean_object* v___x_544_; lean_object* v___f_545_; lean_object* v___x_546_; 
v___f_543_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_543_, 0, v_inst_539_);
v___x_544_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_544_, 0, lean_box(0));
lean_closure_set(v___x_544_, 1, v_inst_538_);
v___f_545_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_545_, 0, v___f_543_);
v___x_546_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_545_, v___x_544_, v_cache_541_, v_decl_542_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v___x_547_; 
v___x_547_ = lean_box(0);
return v___x_547_;
}
else
{
lean_object* v_val_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_555_; 
v_val_548_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_555_ == 0)
{
v___x_550_ = v___x_546_;
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_val_548_);
lean_dec(v___x_546_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_553_; 
if (v_isShared_551_ == 0)
{
v___x_553_ = v___x_550_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_val_548_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f___boxed(lean_object* v_00_u03b1_556_, lean_object* v_inst_557_, lean_object* v_inst_558_, lean_object* v_decls_559_, lean_object* v_cache_560_, lean_object* v_decl_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Std_Sat_AIG_Cache_get_x3f(v_00_u03b1_556_, v_inst_557_, v_inst_558_, v_decls_559_, v_cache_560_, v_decl_561_);
lean_dec_ref(v_cache_560_);
lean_dec_ref(v_decls_559_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_Cache_get_x3f_match__1_splitter___redArg(lean_object* v_x_563_, lean_object* v_h__1_564_, lean_object* v_h__2_565_){
_start:
{
if (lean_obj_tag(v_x_563_) == 0)
{
lean_object* v___x_566_; 
lean_dec(v_h__1_564_);
v___x_566_ = lean_apply_1(v_h__2_565_, lean_box(0));
return v___x_566_;
}
else
{
lean_object* v_val_567_; lean_object* v___x_568_; 
lean_dec(v_h__2_565_);
v_val_567_ = lean_ctor_get(v_x_563_, 0);
lean_inc(v_val_567_);
lean_dec_ref_known(v_x_563_, 1);
v___x_568_ = lean_apply_2(v_h__1_564_, v_val_567_, lean_box(0));
return v___x_568_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_Cache_get_x3f_match__1_splitter(lean_object* v_motive_569_, lean_object* v_x_570_, lean_object* v_h__1_571_, lean_object* v_h__2_572_){
_start:
{
if (lean_obj_tag(v_x_570_) == 0)
{
lean_object* v___x_573_; 
lean_dec(v_h__1_571_);
v___x_573_ = lean_apply_1(v_h__2_572_, lean_box(0));
return v___x_573_;
}
else
{
lean_object* v_val_574_; lean_object* v___x_575_; 
lean_dec(v_h__2_572_);
v_val_574_ = lean_ctor_get(v_x_570_, 0);
lean_inc(v_val_574_);
lean_dec_ref_known(v_x_570_, 1);
v___x_575_ = lean_apply_2(v_h__1_571_, v_val_574_, lean_box(0));
return v___x_575_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_ofAtoms_go___redArg(lean_object* v_inst_576_, lean_object* v_inst_577_, lean_object* v_decls_578_, lean_object* v_idx_579_, lean_object* v_map_580_){
_start:
{
lean_object* v___x_581_; uint8_t v___x_582_; 
v___x_581_ = lean_array_get_size(v_decls_578_);
v___x_582_ = lean_nat_dec_lt(v_idx_579_, v___x_581_);
if (v___x_582_ == 0)
{
lean_dec(v_idx_579_);
lean_dec_ref(v_inst_577_);
lean_dec_ref(v_inst_576_);
return v_map_580_;
}
else
{
lean_object* v___x_583_; 
v___x_583_ = lean_array_fget_borrowed(v_decls_578_, v_idx_579_);
if (lean_obj_tag(v___x_583_) == 1)
{
lean_object* v___f_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___f_588_; lean_object* v___x_589_; 
lean_inc_ref(v_inst_577_);
v___f_584_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_584_, 0, v_inst_577_);
lean_inc_ref(v_inst_576_);
v___x_585_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_585_, 0, lean_box(0));
lean_closure_set(v___x_585_, 1, v_inst_576_);
v___x_586_ = lean_unsigned_to_nat(1u);
v___x_587_ = lean_nat_add(v_idx_579_, v___x_586_);
v___f_588_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_588_, 0, v___f_584_);
lean_inc_ref(v___x_583_);
v___x_589_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_588_, v___x_585_, v_map_580_, v___x_583_, v_idx_579_);
v_idx_579_ = v___x_587_;
v_map_580_ = v___x_589_;
goto _start;
}
else
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = lean_unsigned_to_nat(1u);
v___x_592_ = lean_nat_add(v_idx_579_, v___x_591_);
lean_dec(v_idx_579_);
v_idx_579_ = v___x_592_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_ofAtoms_go___redArg___boxed(lean_object* v_inst_594_, lean_object* v_inst_595_, lean_object* v_decls_596_, lean_object* v_idx_597_, lean_object* v_map_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Std_Sat_AIG_Cache_ofAtoms_go___redArg(v_inst_594_, v_inst_595_, v_decls_596_, v_idx_597_, v_map_598_);
lean_dec_ref(v_decls_596_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_ofAtoms_go(lean_object* v_00_u03b1_600_, lean_object* v_inst_601_, lean_object* v_inst_602_, lean_object* v_decls_603_, lean_object* v_huniq_604_, lean_object* v_idx_605_, lean_object* v_map_606_, lean_object* v_hsound_607_, lean_object* v_hcomp_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l_Std_Sat_AIG_Cache_ofAtoms_go___redArg(v_inst_601_, v_inst_602_, v_decls_603_, v_idx_605_, v_map_606_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_ofAtoms_go___boxed(lean_object* v_00_u03b1_610_, lean_object* v_inst_611_, lean_object* v_inst_612_, lean_object* v_decls_613_, lean_object* v_huniq_614_, lean_object* v_idx_615_, lean_object* v_map_616_, lean_object* v_hsound_617_, lean_object* v_hcomp_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Std_Sat_AIG_Cache_ofAtoms_go(v_00_u03b1_610_, v_inst_611_, v_inst_612_, v_decls_613_, v_huniq_614_, v_idx_615_, v_map_616_, v_hsound_617_, v_hcomp_618_);
lean_dec_ref(v_decls_613_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_Cache_ofAtoms_go_match__1_splitter___redArg(lean_object* v_x_620_, lean_object* v_h__1_621_, lean_object* v_h__2_622_, lean_object* v_h__3_623_){
_start:
{
switch(lean_obj_tag(v_x_620_))
{
case 0:
{
lean_object* v___x_624_; 
lean_dec(v_h__3_623_);
lean_dec(v_h__1_621_);
v___x_624_ = lean_apply_1(v_h__2_622_, lean_box(0));
return v___x_624_;
}
case 1:
{
lean_object* v_idx_625_; lean_object* v___x_626_; 
lean_dec(v_h__3_623_);
lean_dec(v_h__2_622_);
v_idx_625_ = lean_ctor_get(v_x_620_, 0);
lean_inc(v_idx_625_);
lean_dec_ref_known(v_x_620_, 1);
v___x_626_ = lean_apply_2(v_h__1_621_, v_idx_625_, lean_box(0));
return v___x_626_;
}
default: 
{
lean_object* v_l_627_; lean_object* v_r_628_; lean_object* v___x_629_; 
lean_dec(v_h__2_622_);
lean_dec(v_h__1_621_);
v_l_627_ = lean_ctor_get(v_x_620_, 0);
lean_inc(v_l_627_);
v_r_628_ = lean_ctor_get(v_x_620_, 1);
lean_inc(v_r_628_);
lean_dec_ref_known(v_x_620_, 2);
v___x_629_ = lean_apply_3(v_h__3_623_, v_l_627_, v_r_628_, lean_box(0));
return v___x_629_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_Cache_ofAtoms_go_match__1_splitter(lean_object* v_00_u03b1_630_, lean_object* v_motive_631_, lean_object* v_x_632_, lean_object* v_h__1_633_, lean_object* v_h__2_634_, lean_object* v_h__3_635_){
_start:
{
switch(lean_obj_tag(v_x_632_))
{
case 0:
{
lean_object* v___x_636_; 
lean_dec(v_h__3_635_);
lean_dec(v_h__1_633_);
v___x_636_ = lean_apply_1(v_h__2_634_, lean_box(0));
return v___x_636_;
}
case 1:
{
lean_object* v_idx_637_; lean_object* v___x_638_; 
lean_dec(v_h__3_635_);
lean_dec(v_h__2_634_);
v_idx_637_ = lean_ctor_get(v_x_632_, 0);
lean_inc(v_idx_637_);
lean_dec_ref_known(v_x_632_, 1);
v___x_638_ = lean_apply_2(v_h__1_633_, v_idx_637_, lean_box(0));
return v___x_638_;
}
default: 
{
lean_object* v_l_639_; lean_object* v_r_640_; lean_object* v___x_641_; 
lean_dec(v_h__2_634_);
lean_dec(v_h__1_633_);
v_l_639_ = lean_ctor_get(v_x_632_, 0);
lean_inc(v_l_639_);
v_r_640_ = lean_ctor_get(v_x_632_, 1);
lean_inc(v_r_640_);
lean_dec_ref_known(v_x_632_, 2);
v___x_641_ = lean_apply_3(v_h__3_635_, v_l_639_, v_r_640_, lean_box(0));
return v___x_641_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_ofAtoms___redArg(lean_object* v_inst_642_, lean_object* v_inst_643_, lean_object* v_decls_644_){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_645_ = lean_unsigned_to_nat(0u);
v___x_646_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___redArg___closed__1, &l_Std_Sat_AIG_Cache_empty___redArg___closed__1_once, _init_l_Std_Sat_AIG_Cache_empty___redArg___closed__1);
v___x_647_ = l_Std_Sat_AIG_Cache_ofAtoms_go___redArg(v_inst_642_, v_inst_643_, v_decls_644_, v___x_645_, v___x_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_ofAtoms___redArg___boxed(lean_object* v_inst_648_, lean_object* v_inst_649_, lean_object* v_decls_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Std_Sat_AIG_Cache_ofAtoms___redArg(v_inst_648_, v_inst_649_, v_decls_650_);
lean_dec_ref(v_decls_650_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_ofAtoms(lean_object* v_00_u03b1_652_, lean_object* v_inst_653_, lean_object* v_inst_654_, lean_object* v_decls_655_, lean_object* v_huniq_656_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Std_Sat_AIG_Cache_ofAtoms___redArg(v_inst_653_, v_inst_654_, v_decls_655_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_ofAtoms___boxed(lean_object* v_00_u03b1_658_, lean_object* v_inst_659_, lean_object* v_inst_660_, lean_object* v_decls_661_, lean_object* v_huniq_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Std_Sat_AIG_Cache_ofAtoms(v_00_u03b1_658_, v_inst_659_, v_inst_660_, v_decls_661_, v_huniq_662_);
lean_dec_ref(v_decls_661_);
return v_res_663_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___redArg___closed__1(void){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_668_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___redArg___closed__1, &l_Std_Sat_AIG_Cache_empty___redArg___closed__1_once, _init_l_Std_Sat_AIG_Cache_empty___redArg___closed__1);
v___x_669_ = ((lean_object*)(l_Std_Sat_AIG_empty___redArg___closed__0));
v___x_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
lean_ctor_set(v___x_670_, 1, v___x_668_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_empty___redArg(){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = lean_obj_once(&l_Std_Sat_AIG_empty___redArg___closed__1, &l_Std_Sat_AIG_empty___redArg___closed__1_once, _init_l_Std_Sat_AIG_empty___redArg___closed__1);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_empty___redArg___boxed(lean_object* v___dummy_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Std_Sat_AIG_empty___redArg();
return v_res_674_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___closed__0(void){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Std_Sat_AIG_empty___redArg();
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_empty(lean_object* v_00_u03b1_676_, lean_object* v_inst_677_, lean_object* v_inst_678_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = lean_obj_once(&l_Std_Sat_AIG_empty___closed__0, &l_Std_Sat_AIG_empty___closed__0_once, _init_l_Std_Sat_AIG_empty___closed__0);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_empty___boxed(lean_object* v_00_u03b1_680_, lean_object* v_inst_681_, lean_object* v_inst_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Std_Sat_AIG_empty(v_00_u03b1_680_, v_inst_681_, v_inst_682_);
lean_dec_ref(v_inst_682_);
lean_dec_ref(v_inst_681_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instMembership___redArg(){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = lean_box(0);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instMembership___redArg___boxed(lean_object* v___dummy_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Std_Sat_AIG_instMembership___redArg();
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instMembership(lean_object* v_00_u03b1_688_, lean_object* v_inst_689_, lean_object* v_inst_690_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = lean_box(0);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instMembership___boxed(lean_object* v_00_u03b1_692_, lean_object* v_inst_693_, lean_object* v_inst_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Std_Sat_AIG_instMembership(v_00_u03b1_692_, v_inst_693_, v_inst_694_);
lean_dec_ref(v_inst_694_);
lean_dec_ref(v_inst_693_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_cast___redArg(lean_object* v_ref_696_){
_start:
{
lean_object* v_gate_697_; uint8_t v_invert_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
v_gate_697_ = lean_ctor_get(v_ref_696_, 0);
v_invert_698_ = lean_ctor_get_uint8(v_ref_696_, sizeof(void*)*1);
v_isSharedCheck_705_ = !lean_is_exclusive(v_ref_696_);
if (v_isSharedCheck_705_ == 0)
{
v___x_700_ = v_ref_696_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_gate_697_);
lean_dec(v_ref_696_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_gate_697_);
lean_ctor_set_uint8(v_reuseFailAlloc_704_, sizeof(void*)*1, v_invert_698_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_cast(lean_object* v_00_u03b1_706_, lean_object* v_inst_707_, lean_object* v_inst_708_, lean_object* v_aig1_709_, lean_object* v_aig2_710_, lean_object* v_ref_711_, lean_object* v_h_712_){
_start:
{
lean_object* v_gate_713_; uint8_t v_invert_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
v_gate_713_ = lean_ctor_get(v_ref_711_, 0);
v_invert_714_ = lean_ctor_get_uint8(v_ref_711_, sizeof(void*)*1);
v_isSharedCheck_721_ = !lean_is_exclusive(v_ref_711_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v_ref_711_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_gate_713_);
lean_dec(v_ref_711_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_gate_713_);
lean_ctor_set_uint8(v_reuseFailAlloc_720_, sizeof(void*)*1, v_invert_714_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_cast___boxed(lean_object* v_00_u03b1_722_, lean_object* v_inst_723_, lean_object* v_inst_724_, lean_object* v_aig1_725_, lean_object* v_aig2_726_, lean_object* v_ref_727_, lean_object* v_h_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Std_Sat_AIG_Ref_cast(v_00_u03b1_722_, v_inst_723_, v_inst_724_, v_aig1_725_, v_aig2_726_, v_ref_727_, v_h_728_);
lean_dec_ref(v_aig2_726_);
lean_dec_ref(v_aig1_725_);
lean_dec_ref(v_inst_724_);
lean_dec_ref(v_inst_723_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_flip___redArg(lean_object* v_ref_730_, uint8_t v_inv_731_){
_start:
{
lean_object* v_gate_732_; uint8_t v_invert_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_745_; 
v_gate_732_ = lean_ctor_get(v_ref_730_, 0);
v_invert_733_ = lean_ctor_get_uint8(v_ref_730_, sizeof(void*)*1);
v_isSharedCheck_745_ = !lean_is_exclusive(v_ref_730_);
if (v_isSharedCheck_745_ == 0)
{
v___x_735_ = v_ref_730_;
v_isShared_736_ = v_isSharedCheck_745_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_gate_732_);
lean_dec(v_ref_730_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_745_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
if (v_invert_733_ == 0)
{
if (v_inv_731_ == 0)
{
lean_del_object(v___x_735_);
goto v___jp_742_;
}
else
{
goto v___jp_737_;
}
}
else
{
if (v_inv_731_ == 0)
{
goto v___jp_737_;
}
else
{
lean_del_object(v___x_735_);
goto v___jp_742_;
}
}
v___jp_737_:
{
uint8_t v___x_738_; lean_object* v___x_740_; 
v___x_738_ = 1;
if (v_isShared_736_ == 0)
{
v___x_740_ = v___x_735_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_gate_732_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
lean_ctor_set_uint8(v___x_740_, sizeof(void*)*1, v___x_738_);
return v___x_740_;
}
}
v___jp_742_:
{
uint8_t v___x_743_; lean_object* v___x_744_; 
v___x_743_ = 0;
v___x_744_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_744_, 0, v_gate_732_);
lean_ctor_set_uint8(v___x_744_, sizeof(void*)*1, v___x_743_);
return v___x_744_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_flip___redArg___boxed(lean_object* v_ref_746_, lean_object* v_inv_747_){
_start:
{
uint8_t v_inv_boxed_748_; lean_object* v_res_749_; 
v_inv_boxed_748_ = lean_unbox(v_inv_747_);
v_res_749_ = l_Std_Sat_AIG_Ref_flip___redArg(v_ref_746_, v_inv_boxed_748_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_flip(lean_object* v_00_u03b1_750_, lean_object* v_inst_751_, lean_object* v_inst_752_, lean_object* v_aig_753_, lean_object* v_ref_754_, uint8_t v_inv_755_){
_start:
{
lean_object* v_gate_756_; uint8_t v_invert_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_769_; 
v_gate_756_ = lean_ctor_get(v_ref_754_, 0);
v_invert_757_ = lean_ctor_get_uint8(v_ref_754_, sizeof(void*)*1);
v_isSharedCheck_769_ = !lean_is_exclusive(v_ref_754_);
if (v_isSharedCheck_769_ == 0)
{
v___x_759_ = v_ref_754_;
v_isShared_760_ = v_isSharedCheck_769_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_gate_756_);
lean_dec(v_ref_754_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_769_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
if (v_invert_757_ == 0)
{
if (v_inv_755_ == 0)
{
lean_del_object(v___x_759_);
goto v___jp_766_;
}
else
{
goto v___jp_761_;
}
}
else
{
if (v_inv_755_ == 0)
{
goto v___jp_761_;
}
else
{
lean_del_object(v___x_759_);
goto v___jp_766_;
}
}
v___jp_761_:
{
uint8_t v___x_762_; lean_object* v___x_764_; 
v___x_762_ = 1;
if (v_isShared_760_ == 0)
{
v___x_764_ = v___x_759_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_gate_756_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
lean_ctor_set_uint8(v___x_764_, sizeof(void*)*1, v___x_762_);
return v___x_764_;
}
}
v___jp_766_:
{
uint8_t v___x_767_; lean_object* v___x_768_; 
v___x_767_ = 0;
v___x_768_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_768_, 0, v_gate_756_);
lean_ctor_set_uint8(v___x_768_, sizeof(void*)*1, v___x_767_);
return v___x_768_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_flip___boxed(lean_object* v_00_u03b1_770_, lean_object* v_inst_771_, lean_object* v_inst_772_, lean_object* v_aig_773_, lean_object* v_ref_774_, lean_object* v_inv_775_){
_start:
{
uint8_t v_inv_boxed_776_; lean_object* v_res_777_; 
v_inv_boxed_776_ = lean_unbox(v_inv_775_);
v_res_777_ = l_Std_Sat_AIG_Ref_flip(v_00_u03b1_770_, v_inst_771_, v_inst_772_, v_aig_773_, v_ref_774_, v_inv_boxed_776_);
lean_dec_ref(v_aig_773_);
lean_dec_ref(v_inst_772_);
lean_dec_ref(v_inst_771_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_not___redArg(lean_object* v_ref_778_){
_start:
{
uint8_t v_invert_779_; 
v_invert_779_ = lean_ctor_get_uint8(v_ref_778_, sizeof(void*)*1);
if (v_invert_779_ == 0)
{
lean_object* v_gate_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_788_; 
v_gate_780_ = lean_ctor_get(v_ref_778_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v_ref_778_);
if (v_isSharedCheck_788_ == 0)
{
v___x_782_ = v_ref_778_;
v_isShared_783_ = v_isSharedCheck_788_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_gate_780_);
lean_dec(v_ref_778_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_788_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
uint8_t v___x_784_; lean_object* v___x_786_; 
v___x_784_ = 1;
if (v_isShared_783_ == 0)
{
v___x_786_ = v___x_782_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_gate_780_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
lean_ctor_set_uint8(v___x_786_, sizeof(void*)*1, v___x_784_);
return v___x_786_;
}
}
}
else
{
lean_object* v_gate_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_797_; 
v_gate_789_ = lean_ctor_get(v_ref_778_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v_ref_778_);
if (v_isSharedCheck_797_ == 0)
{
v___x_791_ = v_ref_778_;
v_isShared_792_ = v_isSharedCheck_797_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_gate_789_);
lean_dec(v_ref_778_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_797_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
uint8_t v___x_793_; lean_object* v___x_795_; 
v___x_793_ = 0;
if (v_isShared_792_ == 0)
{
v___x_795_ = v___x_791_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_gate_789_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
lean_ctor_set_uint8(v___x_795_, sizeof(void*)*1, v___x_793_);
return v___x_795_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_not(lean_object* v_00_u03b1_798_, lean_object* v_inst_799_, lean_object* v_inst_800_, lean_object* v_aig_801_, lean_object* v_ref_802_){
_start:
{
uint8_t v_invert_803_; 
v_invert_803_ = lean_ctor_get_uint8(v_ref_802_, sizeof(void*)*1);
if (v_invert_803_ == 0)
{
lean_object* v_gate_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_812_; 
v_gate_804_ = lean_ctor_get(v_ref_802_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v_ref_802_);
if (v_isSharedCheck_812_ == 0)
{
v___x_806_ = v_ref_802_;
v_isShared_807_ = v_isSharedCheck_812_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_gate_804_);
lean_dec(v_ref_802_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_812_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
uint8_t v___x_808_; lean_object* v___x_810_; 
v___x_808_ = 1;
if (v_isShared_807_ == 0)
{
v___x_810_ = v___x_806_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_gate_804_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
lean_ctor_set_uint8(v___x_810_, sizeof(void*)*1, v___x_808_);
return v___x_810_;
}
}
}
else
{
lean_object* v_gate_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_821_; 
v_gate_813_ = lean_ctor_get(v_ref_802_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v_ref_802_);
if (v_isSharedCheck_821_ == 0)
{
v___x_815_ = v_ref_802_;
v_isShared_816_ = v_isSharedCheck_821_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_gate_813_);
lean_dec(v_ref_802_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_821_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
uint8_t v___x_817_; lean_object* v___x_819_; 
v___x_817_ = 0;
if (v_isShared_816_ == 0)
{
v___x_819_ = v___x_815_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_gate_813_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
lean_ctor_set_uint8(v___x_819_, sizeof(void*)*1, v___x_817_);
return v___x_819_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_not___boxed(lean_object* v_00_u03b1_822_, lean_object* v_inst_823_, lean_object* v_inst_824_, lean_object* v_aig_825_, lean_object* v_ref_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Std_Sat_AIG_Ref_not(v_00_u03b1_822_, v_inst_823_, v_inst_824_, v_aig_825_, v_ref_826_);
lean_dec_ref(v_aig_825_);
lean_dec_ref(v_inst_824_);
lean_dec_ref(v_inst_823_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_cast___redArg(lean_object* v_input_828_){
_start:
{
lean_object* v_lhs_829_; lean_object* v_rhs_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_855_; 
v_lhs_829_ = lean_ctor_get(v_input_828_, 0);
v_rhs_830_ = lean_ctor_get(v_input_828_, 1);
v_isSharedCheck_855_ = !lean_is_exclusive(v_input_828_);
if (v_isSharedCheck_855_ == 0)
{
v___x_832_ = v_input_828_;
v_isShared_833_ = v_isSharedCheck_855_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_rhs_830_);
lean_inc(v_lhs_829_);
lean_dec(v_input_828_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_855_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v_gate_834_; uint8_t v_invert_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_854_; 
v_gate_834_ = lean_ctor_get(v_lhs_829_, 0);
v_invert_835_ = lean_ctor_get_uint8(v_lhs_829_, sizeof(void*)*1);
v_isSharedCheck_854_ = !lean_is_exclusive(v_lhs_829_);
if (v_isSharedCheck_854_ == 0)
{
v___x_837_ = v_lhs_829_;
v_isShared_838_ = v_isSharedCheck_854_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_gate_834_);
lean_dec(v_lhs_829_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_854_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v_gate_839_; uint8_t v_invert_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_853_; 
v_gate_839_ = lean_ctor_get(v_rhs_830_, 0);
v_invert_840_ = lean_ctor_get_uint8(v_rhs_830_, sizeof(void*)*1);
v_isSharedCheck_853_ = !lean_is_exclusive(v_rhs_830_);
if (v_isSharedCheck_853_ == 0)
{
v___x_842_ = v_rhs_830_;
v_isShared_843_ = v_isSharedCheck_853_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_gate_839_);
lean_dec(v_rhs_830_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_853_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v_gate_834_);
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_gate_834_);
v___x_845_ = v_reuseFailAlloc_852_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
lean_object* v___x_847_; 
lean_ctor_set_uint8(v___x_845_, sizeof(void*)*1, v_invert_835_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 0, v_gate_839_);
v___x_847_ = v___x_837_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_gate_839_);
v___x_847_ = v_reuseFailAlloc_851_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
lean_object* v___x_849_; 
lean_ctor_set_uint8(v___x_847_, sizeof(void*)*1, v_invert_840_);
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 1, v___x_847_);
lean_ctor_set(v___x_832_, 0, v___x_845_);
v___x_849_ = v___x_832_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_845_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v___x_847_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_cast(lean_object* v_00_u03b1_856_, lean_object* v_inst_857_, lean_object* v_inst_858_, lean_object* v_aig1_859_, lean_object* v_aig2_860_, lean_object* v_input_861_, lean_object* v_h_862_){
_start:
{
lean_object* v_lhs_863_; lean_object* v_rhs_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_889_; 
v_lhs_863_ = lean_ctor_get(v_input_861_, 0);
v_rhs_864_ = lean_ctor_get(v_input_861_, 1);
v_isSharedCheck_889_ = !lean_is_exclusive(v_input_861_);
if (v_isSharedCheck_889_ == 0)
{
v___x_866_ = v_input_861_;
v_isShared_867_ = v_isSharedCheck_889_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_rhs_864_);
lean_inc(v_lhs_863_);
lean_dec(v_input_861_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_889_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v_gate_868_; uint8_t v_invert_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_888_; 
v_gate_868_ = lean_ctor_get(v_lhs_863_, 0);
v_invert_869_ = lean_ctor_get_uint8(v_lhs_863_, sizeof(void*)*1);
v_isSharedCheck_888_ = !lean_is_exclusive(v_lhs_863_);
if (v_isSharedCheck_888_ == 0)
{
v___x_871_ = v_lhs_863_;
v_isShared_872_ = v_isSharedCheck_888_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_gate_868_);
lean_dec(v_lhs_863_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_888_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v_gate_873_; uint8_t v_invert_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_887_; 
v_gate_873_ = lean_ctor_get(v_rhs_864_, 0);
v_invert_874_ = lean_ctor_get_uint8(v_rhs_864_, sizeof(void*)*1);
v_isSharedCheck_887_ = !lean_is_exclusive(v_rhs_864_);
if (v_isSharedCheck_887_ == 0)
{
v___x_876_ = v_rhs_864_;
v_isShared_877_ = v_isSharedCheck_887_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_gate_873_);
lean_dec(v_rhs_864_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_887_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_879_; 
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 0, v_gate_868_);
v___x_879_ = v___x_876_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_gate_868_);
v___x_879_ = v_reuseFailAlloc_886_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
lean_object* v___x_881_; 
lean_ctor_set_uint8(v___x_879_, sizeof(void*)*1, v_invert_869_);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 0, v_gate_873_);
v___x_881_ = v___x_871_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_gate_873_);
v___x_881_ = v_reuseFailAlloc_885_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
lean_object* v___x_883_; 
lean_ctor_set_uint8(v___x_881_, sizeof(void*)*1, v_invert_874_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 1, v___x_881_);
lean_ctor_set(v___x_866_, 0, v___x_879_);
v___x_883_ = v___x_866_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_879_);
lean_ctor_set(v_reuseFailAlloc_884_, 1, v___x_881_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_cast___boxed(lean_object* v_00_u03b1_890_, lean_object* v_inst_891_, lean_object* v_inst_892_, lean_object* v_aig1_893_, lean_object* v_aig2_894_, lean_object* v_input_895_, lean_object* v_h_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_Std_Sat_AIG_BinaryInput_cast(v_00_u03b1_890_, v_inst_891_, v_inst_892_, v_aig1_893_, v_aig2_894_, v_input_895_, v_h_896_);
lean_dec_ref(v_aig2_894_);
lean_dec_ref(v_aig1_893_);
lean_dec_ref(v_inst_892_);
lean_dec_ref(v_inst_891_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_invert___redArg(lean_object* v_input_898_, uint8_t v_linv_899_, uint8_t v_rinv_900_){
_start:
{
lean_object* v___y_902_; lean_object* v___y_903_; lean_object* v___y_908_; lean_object* v___y_909_; lean_object* v_lhs_913_; lean_object* v_rhs_914_; lean_object* v___y_916_; lean_object* v_gate_922_; uint8_t v_invert_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_935_; 
v_lhs_913_ = lean_ctor_get(v_input_898_, 0);
lean_inc_ref(v_lhs_913_);
v_rhs_914_ = lean_ctor_get(v_input_898_, 1);
lean_inc_ref(v_rhs_914_);
lean_dec_ref(v_input_898_);
v_gate_922_ = lean_ctor_get(v_lhs_913_, 0);
v_invert_923_ = lean_ctor_get_uint8(v_lhs_913_, sizeof(void*)*1);
v_isSharedCheck_935_ = !lean_is_exclusive(v_lhs_913_);
if (v_isSharedCheck_935_ == 0)
{
v___x_925_ = v_lhs_913_;
v_isShared_926_ = v_isSharedCheck_935_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_gate_922_);
lean_dec(v_lhs_913_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_935_;
goto v_resetjp_924_;
}
v___jp_901_:
{
uint8_t v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_904_ = 0;
v___x_905_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_905_, 0, v___y_902_);
lean_ctor_set_uint8(v___x_905_, sizeof(void*)*1, v___x_904_);
v___x_906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_906_, 0, v___y_903_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
return v___x_906_;
}
v___jp_907_:
{
uint8_t v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_910_ = 1;
v___x_911_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_911_, 0, v___y_908_);
lean_ctor_set_uint8(v___x_911_, sizeof(void*)*1, v___x_910_);
v___x_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_912_, 0, v___y_909_);
lean_ctor_set(v___x_912_, 1, v___x_911_);
return v___x_912_;
}
v___jp_915_:
{
uint8_t v_invert_917_; 
v_invert_917_ = lean_ctor_get_uint8(v_rhs_914_, sizeof(void*)*1);
if (v_invert_917_ == 0)
{
if (v_rinv_900_ == 0)
{
lean_object* v_gate_918_; 
v_gate_918_ = lean_ctor_get(v_rhs_914_, 0);
lean_inc(v_gate_918_);
lean_dec_ref(v_rhs_914_);
v___y_902_ = v_gate_918_;
v___y_903_ = v___y_916_;
goto v___jp_901_;
}
else
{
lean_object* v_gate_919_; 
v_gate_919_ = lean_ctor_get(v_rhs_914_, 0);
lean_inc(v_gate_919_);
lean_dec_ref(v_rhs_914_);
v___y_908_ = v_gate_919_;
v___y_909_ = v___y_916_;
goto v___jp_907_;
}
}
else
{
if (v_rinv_900_ == 0)
{
lean_object* v_gate_920_; 
v_gate_920_ = lean_ctor_get(v_rhs_914_, 0);
lean_inc(v_gate_920_);
lean_dec_ref(v_rhs_914_);
v___y_908_ = v_gate_920_;
v___y_909_ = v___y_916_;
goto v___jp_907_;
}
else
{
lean_object* v_gate_921_; 
v_gate_921_ = lean_ctor_get(v_rhs_914_, 0);
lean_inc(v_gate_921_);
lean_dec_ref(v_rhs_914_);
v___y_902_ = v_gate_921_;
v___y_903_ = v___y_916_;
goto v___jp_901_;
}
}
}
v_resetjp_924_:
{
if (v_invert_923_ == 0)
{
if (v_linv_899_ == 0)
{
lean_del_object(v___x_925_);
goto v___jp_932_;
}
else
{
goto v___jp_927_;
}
}
else
{
if (v_linv_899_ == 0)
{
goto v___jp_927_;
}
else
{
lean_del_object(v___x_925_);
goto v___jp_932_;
}
}
v___jp_927_:
{
uint8_t v___x_928_; lean_object* v___x_930_; 
v___x_928_ = 1;
if (v_isShared_926_ == 0)
{
v___x_930_ = v___x_925_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_gate_922_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
lean_ctor_set_uint8(v___x_930_, sizeof(void*)*1, v___x_928_);
v___y_916_ = v___x_930_;
goto v___jp_915_;
}
}
v___jp_932_:
{
uint8_t v___x_933_; lean_object* v___x_934_; 
v___x_933_ = 0;
v___x_934_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_934_, 0, v_gate_922_);
lean_ctor_set_uint8(v___x_934_, sizeof(void*)*1, v___x_933_);
v___y_916_ = v___x_934_;
goto v___jp_915_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_invert___redArg___boxed(lean_object* v_input_936_, lean_object* v_linv_937_, lean_object* v_rinv_938_){
_start:
{
uint8_t v_linv_boxed_939_; uint8_t v_rinv_boxed_940_; lean_object* v_res_941_; 
v_linv_boxed_939_ = lean_unbox(v_linv_937_);
v_rinv_boxed_940_ = lean_unbox(v_rinv_938_);
v_res_941_ = l_Std_Sat_AIG_BinaryInput_invert___redArg(v_input_936_, v_linv_boxed_939_, v_rinv_boxed_940_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_invert(lean_object* v_00_u03b1_942_, lean_object* v_inst_943_, lean_object* v_inst_944_, lean_object* v_aig_945_, lean_object* v_input_946_, uint8_t v_linv_947_, uint8_t v_rinv_948_){
_start:
{
lean_object* v___y_950_; lean_object* v___y_951_; lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v_lhs_961_; lean_object* v_rhs_962_; lean_object* v___y_964_; lean_object* v_gate_970_; uint8_t v_invert_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_983_; 
v_lhs_961_ = lean_ctor_get(v_input_946_, 0);
lean_inc_ref(v_lhs_961_);
v_rhs_962_ = lean_ctor_get(v_input_946_, 1);
lean_inc_ref(v_rhs_962_);
lean_dec_ref(v_input_946_);
v_gate_970_ = lean_ctor_get(v_lhs_961_, 0);
v_invert_971_ = lean_ctor_get_uint8(v_lhs_961_, sizeof(void*)*1);
v_isSharedCheck_983_ = !lean_is_exclusive(v_lhs_961_);
if (v_isSharedCheck_983_ == 0)
{
v___x_973_ = v_lhs_961_;
v_isShared_974_ = v_isSharedCheck_983_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_gate_970_);
lean_dec(v_lhs_961_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_983_;
goto v_resetjp_972_;
}
v___jp_949_:
{
uint8_t v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_952_ = 0;
v___x_953_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_953_, 0, v___y_950_);
lean_ctor_set_uint8(v___x_953_, sizeof(void*)*1, v___x_952_);
v___x_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_954_, 0, v___y_951_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
return v___x_954_;
}
v___jp_955_:
{
uint8_t v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_958_ = 1;
v___x_959_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_959_, 0, v___y_956_);
lean_ctor_set_uint8(v___x_959_, sizeof(void*)*1, v___x_958_);
v___x_960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_960_, 0, v___y_957_);
lean_ctor_set(v___x_960_, 1, v___x_959_);
return v___x_960_;
}
v___jp_963_:
{
uint8_t v_invert_965_; 
v_invert_965_ = lean_ctor_get_uint8(v_rhs_962_, sizeof(void*)*1);
if (v_invert_965_ == 0)
{
if (v_rinv_948_ == 0)
{
lean_object* v_gate_966_; 
v_gate_966_ = lean_ctor_get(v_rhs_962_, 0);
lean_inc(v_gate_966_);
lean_dec_ref(v_rhs_962_);
v___y_950_ = v_gate_966_;
v___y_951_ = v___y_964_;
goto v___jp_949_;
}
else
{
lean_object* v_gate_967_; 
v_gate_967_ = lean_ctor_get(v_rhs_962_, 0);
lean_inc(v_gate_967_);
lean_dec_ref(v_rhs_962_);
v___y_956_ = v_gate_967_;
v___y_957_ = v___y_964_;
goto v___jp_955_;
}
}
else
{
if (v_rinv_948_ == 0)
{
lean_object* v_gate_968_; 
v_gate_968_ = lean_ctor_get(v_rhs_962_, 0);
lean_inc(v_gate_968_);
lean_dec_ref(v_rhs_962_);
v___y_956_ = v_gate_968_;
v___y_957_ = v___y_964_;
goto v___jp_955_;
}
else
{
lean_object* v_gate_969_; 
v_gate_969_ = lean_ctor_get(v_rhs_962_, 0);
lean_inc(v_gate_969_);
lean_dec_ref(v_rhs_962_);
v___y_950_ = v_gate_969_;
v___y_951_ = v___y_964_;
goto v___jp_949_;
}
}
}
v_resetjp_972_:
{
if (v_invert_971_ == 0)
{
if (v_linv_947_ == 0)
{
lean_del_object(v___x_973_);
goto v___jp_980_;
}
else
{
goto v___jp_975_;
}
}
else
{
if (v_linv_947_ == 0)
{
goto v___jp_975_;
}
else
{
lean_del_object(v___x_973_);
goto v___jp_980_;
}
}
v___jp_975_:
{
uint8_t v___x_976_; lean_object* v___x_978_; 
v___x_976_ = 1;
if (v_isShared_974_ == 0)
{
v___x_978_ = v___x_973_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_gate_970_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
lean_ctor_set_uint8(v___x_978_, sizeof(void*)*1, v___x_976_);
v___y_964_ = v___x_978_;
goto v___jp_963_;
}
}
v___jp_980_:
{
uint8_t v___x_981_; lean_object* v___x_982_; 
v___x_981_ = 0;
v___x_982_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_982_, 0, v_gate_970_);
lean_ctor_set_uint8(v___x_982_, sizeof(void*)*1, v___x_981_);
v___y_964_ = v___x_982_;
goto v___jp_963_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_invert___boxed(lean_object* v_00_u03b1_984_, lean_object* v_inst_985_, lean_object* v_inst_986_, lean_object* v_aig_987_, lean_object* v_input_988_, lean_object* v_linv_989_, lean_object* v_rinv_990_){
_start:
{
uint8_t v_linv_boxed_991_; uint8_t v_rinv_boxed_992_; lean_object* v_res_993_; 
v_linv_boxed_991_ = lean_unbox(v_linv_989_);
v_rinv_boxed_992_ = lean_unbox(v_rinv_990_);
v_res_993_ = l_Std_Sat_AIG_BinaryInput_invert(v_00_u03b1_984_, v_inst_985_, v_inst_986_, v_aig_987_, v_input_988_, v_linv_boxed_991_, v_rinv_boxed_992_);
lean_dec_ref(v_aig_987_);
lean_dec_ref(v_inst_986_);
lean_dec_ref(v_inst_985_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_TernaryInput_cast___redArg(lean_object* v_input_994_){
_start:
{
lean_object* v_discr_995_; lean_object* v_lhs_996_; lean_object* v_rhs_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1031_; 
v_discr_995_ = lean_ctor_get(v_input_994_, 0);
v_lhs_996_ = lean_ctor_get(v_input_994_, 1);
v_rhs_997_ = lean_ctor_get(v_input_994_, 2);
v_isSharedCheck_1031_ = !lean_is_exclusive(v_input_994_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_999_ = v_input_994_;
v_isShared_1000_ = v_isSharedCheck_1031_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_rhs_997_);
lean_inc(v_lhs_996_);
lean_inc(v_discr_995_);
lean_dec(v_input_994_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1031_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v_gate_1001_; uint8_t v_invert_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1030_; 
v_gate_1001_ = lean_ctor_get(v_discr_995_, 0);
v_invert_1002_ = lean_ctor_get_uint8(v_discr_995_, sizeof(void*)*1);
v_isSharedCheck_1030_ = !lean_is_exclusive(v_discr_995_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1004_ = v_discr_995_;
v_isShared_1005_ = v_isSharedCheck_1030_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_gate_1001_);
lean_dec(v_discr_995_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1030_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v_gate_1006_; uint8_t v_invert_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1029_; 
v_gate_1006_ = lean_ctor_get(v_lhs_996_, 0);
v_invert_1007_ = lean_ctor_get_uint8(v_lhs_996_, sizeof(void*)*1);
v_isSharedCheck_1029_ = !lean_is_exclusive(v_lhs_996_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1009_ = v_lhs_996_;
v_isShared_1010_ = v_isSharedCheck_1029_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_gate_1006_);
lean_dec(v_lhs_996_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1029_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v_gate_1011_; uint8_t v_invert_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1028_; 
v_gate_1011_ = lean_ctor_get(v_rhs_997_, 0);
v_invert_1012_ = lean_ctor_get_uint8(v_rhs_997_, sizeof(void*)*1);
v_isSharedCheck_1028_ = !lean_is_exclusive(v_rhs_997_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1014_ = v_rhs_997_;
v_isShared_1015_ = v_isSharedCheck_1028_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_gate_1011_);
lean_dec(v_rhs_997_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1028_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1017_; 
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 0, v_gate_1001_);
v___x_1017_ = v___x_1014_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_gate_1001_);
v___x_1017_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
lean_object* v___x_1019_; 
lean_ctor_set_uint8(v___x_1017_, sizeof(void*)*1, v_invert_1002_);
if (v_isShared_1010_ == 0)
{
v___x_1019_ = v___x_1009_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_gate_1006_);
lean_ctor_set_uint8(v_reuseFailAlloc_1026_, sizeof(void*)*1, v_invert_1007_);
v___x_1019_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
lean_object* v___x_1021_; 
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 0, v_gate_1011_);
v___x_1021_ = v___x_1004_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_gate_1011_);
v___x_1021_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
lean_object* v___x_1023_; 
lean_ctor_set_uint8(v___x_1021_, sizeof(void*)*1, v_invert_1012_);
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 2, v___x_1021_);
lean_ctor_set(v___x_999_, 1, v___x_1019_);
lean_ctor_set(v___x_999_, 0, v___x_1017_);
v___x_1023_ = v___x_999_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1017_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v___x_1019_);
lean_ctor_set(v_reuseFailAlloc_1024_, 2, v___x_1021_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_TernaryInput_cast(lean_object* v_00_u03b1_1032_, lean_object* v_inst_1033_, lean_object* v_inst_1034_, lean_object* v_aig1_1035_, lean_object* v_aig2_1036_, lean_object* v_input_1037_, lean_object* v_h_1038_){
_start:
{
lean_object* v_discr_1039_; lean_object* v_lhs_1040_; lean_object* v_rhs_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1075_; 
v_discr_1039_ = lean_ctor_get(v_input_1037_, 0);
v_lhs_1040_ = lean_ctor_get(v_input_1037_, 1);
v_rhs_1041_ = lean_ctor_get(v_input_1037_, 2);
v_isSharedCheck_1075_ = !lean_is_exclusive(v_input_1037_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1043_ = v_input_1037_;
v_isShared_1044_ = v_isSharedCheck_1075_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_rhs_1041_);
lean_inc(v_lhs_1040_);
lean_inc(v_discr_1039_);
lean_dec(v_input_1037_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1075_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v_gate_1045_; uint8_t v_invert_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1074_; 
v_gate_1045_ = lean_ctor_get(v_discr_1039_, 0);
v_invert_1046_ = lean_ctor_get_uint8(v_discr_1039_, sizeof(void*)*1);
v_isSharedCheck_1074_ = !lean_is_exclusive(v_discr_1039_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1048_ = v_discr_1039_;
v_isShared_1049_ = v_isSharedCheck_1074_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_gate_1045_);
lean_dec(v_discr_1039_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1074_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v_gate_1050_; uint8_t v_invert_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1073_; 
v_gate_1050_ = lean_ctor_get(v_lhs_1040_, 0);
v_invert_1051_ = lean_ctor_get_uint8(v_lhs_1040_, sizeof(void*)*1);
v_isSharedCheck_1073_ = !lean_is_exclusive(v_lhs_1040_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1053_ = v_lhs_1040_;
v_isShared_1054_ = v_isSharedCheck_1073_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_gate_1050_);
lean_dec(v_lhs_1040_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1073_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v_gate_1055_; uint8_t v_invert_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1072_; 
v_gate_1055_ = lean_ctor_get(v_rhs_1041_, 0);
v_invert_1056_ = lean_ctor_get_uint8(v_rhs_1041_, sizeof(void*)*1);
v_isSharedCheck_1072_ = !lean_is_exclusive(v_rhs_1041_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1058_ = v_rhs_1041_;
v_isShared_1059_ = v_isSharedCheck_1072_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_gate_1055_);
lean_dec(v_rhs_1041_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1072_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 0, v_gate_1045_);
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_gate_1045_);
v___x_1061_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
lean_object* v___x_1063_; 
lean_ctor_set_uint8(v___x_1061_, sizeof(void*)*1, v_invert_1046_);
if (v_isShared_1054_ == 0)
{
v___x_1063_ = v___x_1053_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_gate_1050_);
lean_ctor_set_uint8(v_reuseFailAlloc_1070_, sizeof(void*)*1, v_invert_1051_);
v___x_1063_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
lean_object* v___x_1065_; 
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 0, v_gate_1055_);
v___x_1065_ = v___x_1048_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_gate_1055_);
v___x_1065_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
lean_object* v___x_1067_; 
lean_ctor_set_uint8(v___x_1065_, sizeof(void*)*1, v_invert_1056_);
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 2, v___x_1065_);
lean_ctor_set(v___x_1043_, 1, v___x_1063_);
lean_ctor_set(v___x_1043_, 0, v___x_1061_);
v___x_1067_ = v___x_1043_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1061_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v___x_1063_);
lean_ctor_set(v_reuseFailAlloc_1068_, 2, v___x_1065_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_TernaryInput_cast___boxed(lean_object* v_00_u03b1_1076_, lean_object* v_inst_1077_, lean_object* v_inst_1078_, lean_object* v_aig1_1079_, lean_object* v_aig2_1080_, lean_object* v_input_1081_, lean_object* v_h_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_Std_Sat_AIG_TernaryInput_cast(v_00_u03b1_1076_, v_inst_1077_, v_inst_1078_, v_aig1_1079_, v_aig2_1080_, v_input_1081_, v_h_1082_);
lean_dec_ref(v_aig2_1080_);
lean_dec_ref(v_aig1_1079_);
lean_dec_ref(v_inst_1078_);
lean_dec_ref(v_inst_1077_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_invEdgeStyle(uint8_t v_isInv_1086_){
_start:
{
if (v_isInv_1086_ == 0)
{
lean_object* v___x_1087_; 
v___x_1087_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_invEdgeStyle___closed__0));
return v___x_1087_;
}
else
{
lean_object* v___x_1088_; 
v___x_1088_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_invEdgeStyle___closed__1));
return v___x_1088_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_invEdgeStyle___boxed(lean_object* v_isInv_1089_){
_start:
{
uint8_t v_isInv_boxed_1090_; lean_object* v_res_1091_; 
v_isInv_boxed_1090_ = lean_unbox(v_isInv_1089_);
v_res_1091_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v_isInv_boxed_1090_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___redArg(lean_object* v_acc_1096_, lean_object* v_decls_1097_, lean_object* v_idx_1098_, lean_object* v_a_1099_){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___f_1102_; lean_object* v___f_1103_; uint8_t v___x_1104_; 
v___x_1100_ = lean_array_get_size(v_decls_1097_);
v___x_1101_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_1101_, 0, v___x_1100_);
v___f_1102_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1102_, 0, v___x_1101_);
v___f_1103_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___redArg___closed__0));
lean_inc(v_idx_1098_);
lean_inc_ref(v___f_1102_);
v___x_1104_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1102_, v___f_1103_, v_a_1099_, v_idx_1098_);
if (v___x_1104_ == 0)
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1105_ = lean_box(0);
lean_inc(v_idx_1098_);
v___x_1106_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___f_1102_, v___f_1103_, v_a_1099_, v_idx_1098_, v___x_1105_);
v___x_1107_ = lean_array_fget_borrowed(v_decls_1097_, v_idx_1098_);
if (lean_obj_tag(v___x_1107_) == 2)
{
lean_object* v_l_1108_; lean_object* v_r_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; uint8_t v___y_1113_; lean_object* v___y_1114_; uint8_t v___y_1115_; uint8_t v___y_1139_; lean_object* v___x_1145_; lean_object* v___x_1146_; uint8_t v___x_1147_; 
v_l_1108_ = lean_ctor_get(v___x_1107_, 0);
v_r_1109_ = lean_ctor_get(v___x_1107_, 1);
v___x_1110_ = lean_unsigned_to_nat(1u);
v___x_1111_ = lean_nat_shiftr(v_l_1108_, v___x_1110_);
v___x_1145_ = lean_nat_land(v___x_1110_, v_l_1108_);
v___x_1146_ = lean_unsigned_to_nat(0u);
v___x_1147_ = lean_nat_dec_eq(v___x_1145_, v___x_1146_);
lean_dec(v___x_1145_);
if (v___x_1147_ == 0)
{
uint8_t v___x_1148_; 
v___x_1148_ = 1;
v___y_1139_ = v___x_1148_;
goto v___jp_1138_;
}
else
{
v___y_1139_ = v___x_1104_;
goto v___jp_1138_;
}
v___jp_1112_:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v_fst_1135_; lean_object* v_snd_1136_; 
v___x_1116_ = l_Nat_reprFast(v_idx_1098_);
v___x_1117_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___redArg___closed__1));
lean_inc_ref(v___x_1116_);
v___x_1118_ = lean_string_append(v___x_1116_, v___x_1117_);
lean_inc(v___x_1111_);
v___x_1119_ = l_Nat_reprFast(v___x_1111_);
v___x_1120_ = lean_string_append(v___x_1118_, v___x_1119_);
lean_dec_ref(v___x_1119_);
v___x_1121_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_1113_);
v___x_1122_ = lean_string_append(v___x_1120_, v___x_1121_);
lean_dec_ref(v___x_1121_);
v___x_1123_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___redArg___closed__2));
v___x_1124_ = lean_string_append(v___x_1122_, v___x_1123_);
v___x_1125_ = lean_string_append(v___x_1124_, v___x_1116_);
lean_dec_ref(v___x_1116_);
v___x_1126_ = lean_string_append(v___x_1125_, v___x_1117_);
lean_inc(v___y_1114_);
v___x_1127_ = l_Nat_reprFast(v___y_1114_);
v___x_1128_ = lean_string_append(v___x_1126_, v___x_1127_);
lean_dec_ref(v___x_1127_);
v___x_1129_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_1115_);
v___x_1130_ = lean_string_append(v___x_1128_, v___x_1129_);
lean_dec_ref(v___x_1129_);
v___x_1131_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___redArg___closed__3));
v___x_1132_ = lean_string_append(v___x_1130_, v___x_1131_);
v___x_1133_ = lean_string_append(v_acc_1096_, v___x_1132_);
lean_dec_ref(v___x_1132_);
v___x_1134_ = l_Std_Sat_AIG_toGraphviz_go___redArg(v___x_1133_, v_decls_1097_, v___x_1111_, v___x_1106_);
v_fst_1135_ = lean_ctor_get(v___x_1134_, 0);
lean_inc(v_fst_1135_);
v_snd_1136_ = lean_ctor_get(v___x_1134_, 1);
lean_inc(v_snd_1136_);
lean_dec_ref(v___x_1134_);
v_acc_1096_ = v_fst_1135_;
v_idx_1098_ = v___y_1114_;
v_a_1099_ = v_snd_1136_;
goto _start;
}
v___jp_1138_:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; uint8_t v___x_1143_; 
v___x_1140_ = lean_nat_shiftr(v_r_1109_, v___x_1110_);
v___x_1141_ = lean_nat_land(v___x_1110_, v_r_1109_);
v___x_1142_ = lean_unsigned_to_nat(0u);
v___x_1143_ = lean_nat_dec_eq(v___x_1141_, v___x_1142_);
lean_dec(v___x_1141_);
if (v___x_1143_ == 0)
{
uint8_t v___x_1144_; 
v___x_1144_ = 1;
v___y_1113_ = v___y_1139_;
v___y_1114_ = v___x_1140_;
v___y_1115_ = v___x_1144_;
goto v___jp_1112_;
}
else
{
v___y_1113_ = v___y_1139_;
v___y_1114_ = v___x_1140_;
v___y_1115_ = v___x_1104_;
goto v___jp_1112_;
}
}
}
else
{
lean_object* v___x_1149_; 
lean_dec(v_idx_1098_);
v___x_1149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1149_, 0, v_acc_1096_);
lean_ctor_set(v___x_1149_, 1, v___x_1106_);
return v___x_1149_;
}
}
else
{
lean_object* v___x_1150_; 
lean_dec_ref(v___f_1102_);
lean_dec(v_idx_1098_);
v___x_1150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1150_, 0, v_acc_1096_);
lean_ctor_set(v___x_1150_, 1, v_a_1099_);
return v___x_1150_;
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___redArg___lam__1(lean_object* v___x_1261_, lean_object* v___f_1262_, lean_object* v_acc_1263_, lean_object* v_l_1264_){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1261_, v___f_1262_, v_acc_1263_, v_l_1264_);
return v___x_1265_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___redArg___closed__1(void){
_start:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1267_ = lean_box(0);
v___x_1268_ = lean_unsigned_to_nat(16u);
v___x_1269_ = lean_mk_array(v___x_1268_, v___x_1267_);
return v___x_1269_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___redArg___closed__2(void){
_start:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1270_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___redArg___closed__1, &l_Std_Sat_AIG_toGraphviz___redArg___closed__1_once, _init_l_Std_Sat_AIG_toGraphviz___redArg___closed__1);
v___x_1271_ = lean_unsigned_to_nat(0u);
v___x_1272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1271_);
lean_ctor_set(v___x_1272_, 1, v___x_1270_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___redArg(lean_object* v_inst_1294_, lean_object* v_entry_1295_){
_start:
{
lean_object* v_aig_1296_; lean_object* v_ref_1297_; lean_object* v_decls_1298_; lean_object* v_gate_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v_fst_1304_; lean_object* v_snd_1305_; lean_object* v___y_1307_; lean_object* v___x_1313_; lean_object* v_buckets_1314_; lean_object* v___x_1315_; uint8_t v___x_1316_; 
v_aig_1296_ = lean_ctor_get(v_entry_1295_, 0);
lean_inc_ref(v_aig_1296_);
v_ref_1297_ = lean_ctor_get(v_entry_1295_, 1);
lean_inc_ref(v_ref_1297_);
lean_dec_ref(v_entry_1295_);
v_decls_1298_ = lean_ctor_get(v_aig_1296_, 0);
lean_inc_ref(v_decls_1298_);
lean_dec_ref(v_aig_1296_);
v_gate_1299_ = lean_ctor_get(v_ref_1297_, 0);
lean_inc(v_gate_1299_);
lean_dec_ref(v_ref_1297_);
v___x_1300_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___redArg___closed__0));
v___x_1301_ = lean_unsigned_to_nat(0u);
v___x_1302_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___redArg___closed__2, &l_Std_Sat_AIG_toGraphviz___redArg___closed__2_once, _init_l_Std_Sat_AIG_toGraphviz___redArg___closed__2);
v___x_1303_ = l_Std_Sat_AIG_toGraphviz_go___redArg(v___x_1300_, v_decls_1298_, v_gate_1299_, v___x_1302_);
v_fst_1304_ = lean_ctor_get(v___x_1303_, 0);
lean_inc(v_fst_1304_);
v_snd_1305_ = lean_ctor_get(v___x_1303_, 1);
lean_inc(v_snd_1305_);
lean_dec_ref(v___x_1303_);
v___x_1313_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___redArg___closed__14));
v_buckets_1314_ = lean_ctor_get(v_snd_1305_, 1);
lean_inc_ref(v_buckets_1314_);
lean_dec(v_snd_1305_);
v___x_1315_ = lean_array_get_size(v_buckets_1314_);
v___x_1316_ = lean_nat_dec_lt(v___x_1301_, v___x_1315_);
if (v___x_1316_ == 0)
{
lean_dec_ref(v_buckets_1314_);
lean_dec_ref(v_decls_1298_);
lean_dec_ref(v_inst_1294_);
v___y_1307_ = v___x_1300_;
goto v___jp_1306_;
}
else
{
lean_object* v___f_1317_; lean_object* v___f_1318_; size_t v___x_1319_; size_t v___x_1320_; lean_object* v___x_1321_; 
v___f_1317_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_toGraphviz___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1317_, 0, v_inst_1294_);
lean_closure_set(v___f_1317_, 1, v_decls_1298_);
v___f_1318_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_toGraphviz___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1318_, 0, v___x_1313_);
lean_closure_set(v___f_1318_, 1, v___f_1317_);
v___x_1319_ = ((size_t)0ULL);
v___x_1320_ = lean_usize_of_nat(v___x_1315_);
v___x_1321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1313_, v___f_1318_, v_buckets_1314_, v___x_1319_, v___x_1320_, v___x_1300_);
v___y_1307_ = v___x_1321_;
goto v___jp_1306_;
}
v___jp_1306_:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1308_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___redArg___closed__3));
v___x_1309_ = lean_string_append(v___x_1308_, v___y_1307_);
lean_dec_ref(v___y_1307_);
v___x_1310_ = lean_string_append(v___x_1309_, v_fst_1304_);
lean_dec(v_fst_1304_);
v___x_1311_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___redArg___closed__4));
v___x_1312_ = lean_string_append(v___x_1310_, v___x_1311_);
return v___x_1312_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz(lean_object* v_00_u03b1_1322_, lean_object* v_inst_1323_, lean_object* v_inst_1324_, lean_object* v_inst_1325_, lean_object* v_entry_1326_){
_start:
{
lean_object* v___x_1327_; 
v___x_1327_ = l_Std_Sat_AIG_toGraphviz___redArg(v_inst_1324_, v_entry_1326_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___boxed(lean_object* v_00_u03b1_1328_, lean_object* v_inst_1329_, lean_object* v_inst_1330_, lean_object* v_inst_1331_, lean_object* v_entry_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Std_Sat_AIG_toGraphviz(v_00_u03b1_1328_, v_inst_1329_, v_inst_1330_, v_inst_1331_, v_entry_1332_);
lean_dec_ref(v_inst_1331_);
lean_dec_ref(v_inst_1329_);
return v_res_1333_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote_go___redArg(lean_object* v_x_1334_, lean_object* v_decls_1335_, lean_object* v_assign_1336_){
_start:
{
uint8_t v___y_1338_; uint8_t v___y_1339_; lean_object* v___x_1341_; 
v___x_1341_ = lean_array_fget_borrowed(v_decls_1335_, v_x_1334_);
switch(lean_obj_tag(v___x_1341_))
{
case 0:
{
uint8_t v___x_1342_; 
lean_dec_ref(v_assign_1336_);
v___x_1342_ = 0;
return v___x_1342_;
}
case 1:
{
lean_object* v_idx_1343_; lean_object* v___x_1344_; uint8_t v___x_1345_; 
v_idx_1343_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_idx_1343_);
v___x_1344_ = lean_apply_1(v_assign_1336_, v_idx_1343_);
v___x_1345_ = lean_unbox(v___x_1344_);
return v___x_1345_;
}
default: 
{
lean_object* v_l_1346_; lean_object* v_r_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; uint8_t v_lval_1350_; lean_object* v___x_1351_; uint8_t v_rval_1352_; uint8_t v___y_1354_; uint8_t v___y_1359_; lean_object* v___x_1361_; lean_object* v___x_1362_; uint8_t v___x_1363_; 
v_l_1346_ = lean_ctor_get(v___x_1341_, 0);
v_r_1347_ = lean_ctor_get(v___x_1341_, 1);
v___x_1348_ = lean_unsigned_to_nat(1u);
v___x_1349_ = lean_nat_shiftr(v_l_1346_, v___x_1348_);
lean_inc_ref(v_assign_1336_);
v_lval_1350_ = l_Std_Sat_AIG_denote_go___redArg(v___x_1349_, v_decls_1335_, v_assign_1336_);
lean_dec(v___x_1349_);
v___x_1351_ = lean_nat_shiftr(v_r_1347_, v___x_1348_);
v_rval_1352_ = l_Std_Sat_AIG_denote_go___redArg(v___x_1351_, v_decls_1335_, v_assign_1336_);
lean_dec(v___x_1351_);
v___x_1361_ = lean_nat_land(v___x_1348_, v_l_1346_);
v___x_1362_ = lean_unsigned_to_nat(0u);
v___x_1363_ = lean_nat_dec_eq(v___x_1361_, v___x_1362_);
lean_dec(v___x_1361_);
if (v___x_1363_ == 0)
{
v___y_1359_ = v_lval_1350_;
goto v___jp_1358_;
}
else
{
if (v_lval_1350_ == 0)
{
v___y_1359_ = v___x_1363_;
goto v___jp_1358_;
}
else
{
uint8_t v___x_1364_; 
v___x_1364_ = 0;
v___y_1354_ = v___x_1364_;
goto v___jp_1353_;
}
}
v___jp_1353_:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; uint8_t v___x_1357_; 
v___x_1355_ = lean_nat_land(v___x_1348_, v_r_1347_);
v___x_1356_ = lean_unsigned_to_nat(0u);
v___x_1357_ = lean_nat_dec_eq(v___x_1355_, v___x_1356_);
lean_dec(v___x_1355_);
if (v___x_1357_ == 0)
{
v___y_1338_ = v___y_1354_;
v___y_1339_ = v_rval_1352_;
goto v___jp_1337_;
}
else
{
if (v_rval_1352_ == 0)
{
v___y_1338_ = v___y_1354_;
v___y_1339_ = v___x_1357_;
goto v___jp_1337_;
}
else
{
return v_rval_1352_;
}
}
}
v___jp_1358_:
{
if (v___y_1359_ == 0)
{
v___y_1354_ = v___y_1359_;
goto v___jp_1353_;
}
else
{
uint8_t v___x_1360_; 
v___x_1360_ = 0;
return v___x_1360_;
}
}
}
}
v___jp_1337_:
{
if (v___y_1339_ == 0)
{
uint8_t v___x_1340_; 
v___x_1340_ = 1;
return v___x_1340_;
}
else
{
return v___y_1338_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote_go___redArg___boxed(lean_object* v_x_1365_, lean_object* v_decls_1366_, lean_object* v_assign_1367_){
_start:
{
uint8_t v_res_1368_; lean_object* v_r_1369_; 
v_res_1368_ = l_Std_Sat_AIG_denote_go___redArg(v_x_1365_, v_decls_1366_, v_assign_1367_);
lean_dec_ref(v_decls_1366_);
lean_dec(v_x_1365_);
v_r_1369_ = lean_box(v_res_1368_);
return v_r_1369_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote_go(lean_object* v_00_u03b1_1370_, lean_object* v_x_1371_, lean_object* v_decls_1372_, lean_object* v_assign_1373_, lean_object* v_h1_1374_, lean_object* v_h2_1375_){
_start:
{
uint8_t v___x_1376_; 
v___x_1376_ = l_Std_Sat_AIG_denote_go___redArg(v_x_1371_, v_decls_1372_, v_assign_1373_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote_go___boxed(lean_object* v_00_u03b1_1377_, lean_object* v_x_1378_, lean_object* v_decls_1379_, lean_object* v_assign_1380_, lean_object* v_h1_1381_, lean_object* v_h2_1382_){
_start:
{
uint8_t v_res_1383_; lean_object* v_r_1384_; 
v_res_1383_ = l_Std_Sat_AIG_denote_go(v_00_u03b1_1377_, v_x_1378_, v_decls_1379_, v_assign_1380_, v_h1_1381_, v_h2_1382_);
lean_dec_ref(v_decls_1379_);
lean_dec(v_x_1378_);
v_r_1384_ = lean_box(v_res_1383_);
return v_r_1384_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote___redArg(lean_object* v_assign_1385_, lean_object* v_entry_1386_){
_start:
{
lean_object* v_ref_1387_; lean_object* v_aig_1388_; lean_object* v_gate_1389_; uint8_t v_invert_1390_; lean_object* v_decls_1391_; uint8_t v___x_1392_; 
v_ref_1387_ = lean_ctor_get(v_entry_1386_, 1);
v_aig_1388_ = lean_ctor_get(v_entry_1386_, 0);
v_gate_1389_ = lean_ctor_get(v_ref_1387_, 0);
v_invert_1390_ = lean_ctor_get_uint8(v_ref_1387_, sizeof(void*)*1);
v_decls_1391_ = lean_ctor_get(v_aig_1388_, 0);
v___x_1392_ = l_Std_Sat_AIG_denote_go___redArg(v_gate_1389_, v_decls_1391_, v_assign_1385_);
if (v_invert_1390_ == 0)
{
return v___x_1392_;
}
else
{
if (v___x_1392_ == 0)
{
return v_invert_1390_;
}
else
{
uint8_t v___x_1393_; 
v___x_1393_ = 0;
return v___x_1393_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote___redArg___boxed(lean_object* v_assign_1394_, lean_object* v_entry_1395_){
_start:
{
uint8_t v_res_1396_; lean_object* v_r_1397_; 
v_res_1396_ = l_Std_Sat_AIG_denote___redArg(v_assign_1394_, v_entry_1395_);
lean_dec_ref(v_entry_1395_);
v_r_1397_ = lean_box(v_res_1396_);
return v_r_1397_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote(lean_object* v_00_u03b1_1398_, lean_object* v_inst_1399_, lean_object* v_inst_1400_, lean_object* v_assign_1401_, lean_object* v_entry_1402_){
_start:
{
uint8_t v___x_1403_; 
v___x_1403_ = l_Std_Sat_AIG_denote___redArg(v_assign_1401_, v_entry_1402_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote___boxed(lean_object* v_00_u03b1_1404_, lean_object* v_inst_1405_, lean_object* v_inst_1406_, lean_object* v_assign_1407_, lean_object* v_entry_1408_){
_start:
{
uint8_t v_res_1409_; lean_object* v_r_1410_; 
v_res_1409_ = l_Std_Sat_AIG_denote(v_00_u03b1_1404_, v_inst_1405_, v_inst_1406_, v_assign_1407_, v_entry_1408_);
lean_dec_ref(v_entry_1408_);
lean_dec_ref(v_inst_1406_);
lean_dec_ref(v_inst_1405_);
v_r_1410_ = lean_box(v_res_1409_);
return v_r_1410_;
}
}
static lean_object* _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4(void){
_start:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1490_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__3));
v___x_1491_ = l_String_toRawSubstring_x27(v___x_1490_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1(lean_object* v_x_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_){
_start:
{
lean_object* v___x_1513_; uint8_t v___x_1514_; 
v___x_1513_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
lean_inc(v_x_1510_);
v___x_1514_ = l_Lean_Syntax_isOfKind(v_x_1510_, v___x_1513_);
if (v___x_1514_ == 0)
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
lean_dec(v_x_1510_);
v___x_1515_ = lean_box(1);
v___x_1516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1515_);
lean_ctor_set(v___x_1516_, 1, v_a_1512_);
return v___x_1516_;
}
else
{
lean_object* v_quotContext_1517_; lean_object* v_currMacroScope_1518_; lean_object* v_ref_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; uint8_t v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
v_quotContext_1517_ = lean_ctor_get(v_a_1511_, 1);
v_currMacroScope_1518_ = lean_ctor_get(v_a_1511_, 2);
v_ref_1519_ = lean_ctor_get(v_a_1511_, 5);
v___x_1520_ = lean_unsigned_to_nat(1u);
v___x_1521_ = l_Lean_Syntax_getArg(v_x_1510_, v___x_1520_);
v___x_1522_ = lean_unsigned_to_nat(3u);
v___x_1523_ = l_Lean_Syntax_getArg(v_x_1510_, v___x_1522_);
lean_dec(v_x_1510_);
v___x_1524_ = 0;
v___x_1525_ = l_Lean_SourceInfo_fromRef(v_ref_1519_, v___x_1524_);
v___x_1526_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2));
v___x_1527_ = lean_obj_once(&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4, &l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4_once, _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4);
v___x_1528_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__5));
lean_inc(v_currMacroScope_1518_);
lean_inc(v_quotContext_1517_);
v___x_1529_ = l_Lean_addMacroScope(v_quotContext_1517_, v___x_1528_, v_currMacroScope_1518_);
v___x_1530_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__10));
lean_inc_n(v___x_1525_, 2);
v___x_1531_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1525_);
lean_ctor_set(v___x_1531_, 1, v___x_1527_);
lean_ctor_set(v___x_1531_, 2, v___x_1529_);
lean_ctor_set(v___x_1531_, 3, v___x_1530_);
v___x_1532_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__9));
v___x_1533_ = l_Lean_Syntax_node2(v___x_1525_, v___x_1532_, v___x_1523_, v___x_1521_);
v___x_1534_ = l_Lean_Syntax_node2(v___x_1525_, v___x_1526_, v___x_1531_, v___x_1533_);
v___x_1535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1534_);
lean_ctor_set(v___x_1535_, 1, v_a_1512_);
return v___x_1535_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___boxed(lean_object* v_x_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1(v_x_1536_, v_a_1537_, v_a_1538_);
lean_dec_ref(v_a_1537_);
return v_res_1539_;
}
}
static lean_object* _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__7(void){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1556_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___redArg___closed__0));
v___x_1557_ = l_String_toRawSubstring_x27(v___x_1556_);
return v___x_1557_;
}
}
static lean_object* _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__12(void){
_start:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1568_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__11));
v___x_1569_ = l_String_toRawSubstring_x27(v___x_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1(lean_object* v_x_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_){
_start:
{
lean_object* v___x_1596_; uint8_t v___x_1597_; 
v___x_1596_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__1));
lean_inc(v_x_1593_);
v___x_1597_ = l_Lean_Syntax_isOfKind(v_x_1593_, v___x_1596_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
lean_dec(v_x_1593_);
v___x_1598_ = lean_box(1);
v___x_1599_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1598_);
lean_ctor_set(v___x_1599_, 1, v_a_1595_);
return v___x_1599_;
}
else
{
lean_object* v_quotContext_1600_; lean_object* v_currMacroScope_1601_; lean_object* v_ref_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; uint8_t v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v_quotContext_1600_ = lean_ctor_get(v_a_1594_, 1);
v_currMacroScope_1601_ = lean_ctor_get(v_a_1594_, 2);
v_ref_1602_ = lean_ctor_get(v_a_1594_, 5);
v___x_1603_ = lean_unsigned_to_nat(1u);
v___x_1604_ = l_Lean_Syntax_getArg(v_x_1593_, v___x_1603_);
v___x_1605_ = lean_unsigned_to_nat(3u);
v___x_1606_ = l_Lean_Syntax_getArg(v_x_1593_, v___x_1605_);
v___x_1607_ = lean_unsigned_to_nat(5u);
v___x_1608_ = l_Lean_Syntax_getArg(v_x_1593_, v___x_1607_);
lean_dec(v_x_1593_);
v___x_1609_ = 0;
v___x_1610_ = l_Lean_SourceInfo_fromRef(v_ref_1602_, v___x_1609_);
v___x_1611_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2));
v___x_1612_ = lean_obj_once(&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4, &l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4_once, _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4);
v___x_1613_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__5));
lean_inc_n(v_currMacroScope_1601_, 3);
lean_inc_n(v_quotContext_1600_, 3);
v___x_1614_ = l_Lean_addMacroScope(v_quotContext_1600_, v___x_1613_, v_currMacroScope_1601_);
v___x_1615_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__10));
lean_inc_n(v___x_1610_, 11);
v___x_1616_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1610_);
lean_ctor_set(v___x_1616_, 1, v___x_1612_);
lean_ctor_set(v___x_1616_, 2, v___x_1614_);
lean_ctor_set(v___x_1616_, 3, v___x_1615_);
v___x_1617_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__9));
v___x_1618_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__1));
v___x_1619_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__3));
v___x_1620_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__4));
v___x_1621_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1610_);
lean_ctor_set(v___x_1621_, 1, v___x_1620_);
v___x_1622_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__6));
v___x_1623_ = lean_obj_once(&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__7, &l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__7_once, _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__7);
v___x_1624_ = lean_box(0);
v___x_1625_ = l_Lean_addMacroScope(v_quotContext_1600_, v___x_1624_, v_currMacroScope_1601_);
v___x_1626_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__10));
v___x_1627_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1610_);
lean_ctor_set(v___x_1627_, 1, v___x_1623_);
lean_ctor_set(v___x_1627_, 2, v___x_1625_);
lean_ctor_set(v___x_1627_, 3, v___x_1626_);
v___x_1628_ = l_Lean_Syntax_node1(v___x_1610_, v___x_1622_, v___x_1627_);
v___x_1629_ = l_Lean_Syntax_node2(v___x_1610_, v___x_1619_, v___x_1621_, v___x_1628_);
v___x_1630_ = lean_obj_once(&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__12, &l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__12_once, _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__12);
v___x_1631_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__15));
v___x_1632_ = l_Lean_addMacroScope(v_quotContext_1600_, v___x_1631_, v_currMacroScope_1601_);
v___x_1633_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__20));
v___x_1634_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1610_);
lean_ctor_set(v___x_1634_, 1, v___x_1630_);
lean_ctor_set(v___x_1634_, 2, v___x_1632_);
lean_ctor_set(v___x_1634_, 3, v___x_1633_);
v___x_1635_ = l_Lean_Syntax_node2(v___x_1610_, v___x_1617_, v___x_1604_, v___x_1606_);
v___x_1636_ = l_Lean_Syntax_node2(v___x_1610_, v___x_1611_, v___x_1634_, v___x_1635_);
v___x_1637_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__21));
v___x_1638_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1610_);
lean_ctor_set(v___x_1638_, 1, v___x_1637_);
v___x_1639_ = l_Lean_Syntax_node3(v___x_1610_, v___x_1618_, v___x_1629_, v___x_1636_, v___x_1638_);
v___x_1640_ = l_Lean_Syntax_node2(v___x_1610_, v___x_1617_, v___x_1608_, v___x_1639_);
v___x_1641_ = l_Lean_Syntax_node2(v___x_1610_, v___x_1611_, v___x_1616_, v___x_1640_);
v___x_1642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1641_);
lean_ctor_set(v___x_1642_, 1, v_a_1595_);
return v___x_1642_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___boxed(lean_object* v_x_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1(v_x_1643_, v_a_1644_, v_a_1645_);
lean_dec_ref(v_a_1644_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_unexpandDenote(lean_object* v_x_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_){
_start:
{
lean_object* v___x_1704_; uint8_t v___x_1705_; 
v___x_1704_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2));
lean_inc(v_x_1701_);
v___x_1705_ = l_Lean_Syntax_isOfKind(v_x_1701_, v___x_1704_);
if (v___x_1705_ == 0)
{
lean_object* v___x_1706_; lean_object* v___x_1707_; 
lean_dec(v_x_1701_);
v___x_1706_ = lean_box(0);
v___x_1707_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1706_);
lean_ctor_set(v___x_1707_, 1, v_a_1703_);
return v___x_1707_;
}
else
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; uint8_t v___x_1711_; 
v___x_1708_ = lean_unsigned_to_nat(1u);
v___x_1709_ = l_Lean_Syntax_getArg(v_x_1701_, v___x_1708_);
lean_dec(v_x_1701_);
v___x_1710_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1709_);
v___x_1711_ = l_Lean_Syntax_matchesNull(v___x_1709_, v___x_1710_);
if (v___x_1711_ == 0)
{
lean_object* v___x_1712_; lean_object* v___x_1713_; 
lean_dec(v___x_1709_);
v___x_1712_ = lean_box(0);
v___x_1713_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1712_);
lean_ctor_set(v___x_1713_, 1, v_a_1703_);
return v___x_1713_;
}
else
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; uint8_t v___x_1717_; 
v___x_1714_ = lean_unsigned_to_nat(0u);
v___x_1715_ = l_Lean_Syntax_getArg(v___x_1709_, v___x_1714_);
v___x_1716_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__1));
lean_inc(v___x_1715_);
v___x_1717_ = l_Lean_Syntax_isOfKind(v___x_1715_, v___x_1716_);
if (v___x_1717_ == 0)
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1718_ = l_Lean_Syntax_getArg(v___x_1709_, v___x_1708_);
lean_dec(v___x_1709_);
v___x_1719_ = l_Lean_SourceInfo_fromRef(v_a_1702_, v___x_1717_);
v___x_1720_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1721_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1719_, 3);
v___x_1722_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1719_);
lean_ctor_set(v___x_1722_, 1, v___x_1721_);
v___x_1723_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1724_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1719_);
lean_ctor_set(v___x_1724_, 1, v___x_1723_);
v___x_1725_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1726_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1719_);
lean_ctor_set(v___x_1726_, 1, v___x_1725_);
v___x_1727_ = l_Lean_Syntax_node5(v___x_1719_, v___x_1720_, v___x_1722_, v___x_1715_, v___x_1724_, v___x_1718_, v___x_1726_);
v___x_1728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1727_);
lean_ctor_set(v___x_1728_, 1, v_a_1703_);
return v___x_1728_;
}
else
{
lean_object* v___x_1729_; uint8_t v___x_1730_; 
v___x_1729_ = l_Lean_Syntax_getArg(v___x_1715_, v___x_1708_);
v___x_1730_ = l_Lean_Syntax_matchesNull(v___x_1729_, v___x_1714_);
if (v___x_1730_ == 0)
{
lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___x_1731_ = l_Lean_Syntax_getArg(v___x_1709_, v___x_1708_);
lean_dec(v___x_1709_);
v___x_1732_ = l_Lean_SourceInfo_fromRef(v_a_1702_, v___x_1730_);
v___x_1733_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1734_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1732_, 3);
v___x_1735_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1732_);
lean_ctor_set(v___x_1735_, 1, v___x_1734_);
v___x_1736_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1737_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1732_);
lean_ctor_set(v___x_1737_, 1, v___x_1736_);
v___x_1738_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1739_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1732_);
lean_ctor_set(v___x_1739_, 1, v___x_1738_);
v___x_1740_ = l_Lean_Syntax_node5(v___x_1732_, v___x_1733_, v___x_1735_, v___x_1715_, v___x_1737_, v___x_1731_, v___x_1739_);
v___x_1741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1740_);
lean_ctor_set(v___x_1741_, 1, v_a_1703_);
return v___x_1741_;
}
else
{
lean_object* v___x_1742_; lean_object* v___x_1743_; uint8_t v___x_1744_; 
v___x_1742_ = l_Lean_Syntax_getArg(v___x_1715_, v___x_1710_);
v___x_1743_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__4));
lean_inc(v___x_1742_);
v___x_1744_ = l_Lean_Syntax_isOfKind(v___x_1742_, v___x_1743_);
if (v___x_1744_ == 0)
{
lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
lean_dec(v___x_1742_);
v___x_1745_ = l_Lean_Syntax_getArg(v___x_1709_, v___x_1708_);
lean_dec(v___x_1709_);
v___x_1746_ = l_Lean_SourceInfo_fromRef(v_a_1702_, v___x_1744_);
v___x_1747_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1748_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1746_, 3);
v___x_1749_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1746_);
lean_ctor_set(v___x_1749_, 1, v___x_1748_);
v___x_1750_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1751_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1746_);
lean_ctor_set(v___x_1751_, 1, v___x_1750_);
v___x_1752_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1753_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1746_);
lean_ctor_set(v___x_1753_, 1, v___x_1752_);
v___x_1754_ = l_Lean_Syntax_node5(v___x_1746_, v___x_1747_, v___x_1749_, v___x_1715_, v___x_1751_, v___x_1745_, v___x_1753_);
v___x_1755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1754_);
lean_ctor_set(v___x_1755_, 1, v_a_1703_);
return v___x_1755_;
}
else
{
lean_object* v___x_1756_; lean_object* v___x_1757_; uint8_t v___x_1758_; 
v___x_1756_ = l_Lean_Syntax_getArg(v___x_1742_, v___x_1714_);
lean_dec(v___x_1742_);
v___x_1757_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_1756_);
v___x_1758_ = l_Lean_Syntax_matchesNull(v___x_1756_, v___x_1757_);
if (v___x_1758_ == 0)
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
lean_dec(v___x_1756_);
v___x_1759_ = l_Lean_Syntax_getArg(v___x_1709_, v___x_1708_);
lean_dec(v___x_1709_);
v___x_1760_ = l_Lean_SourceInfo_fromRef(v_a_1702_, v___x_1758_);
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
v___x_1768_ = l_Lean_Syntax_node5(v___x_1760_, v___x_1761_, v___x_1763_, v___x_1715_, v___x_1765_, v___x_1759_, v___x_1767_);
v___x_1769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1768_);
lean_ctor_set(v___x_1769_, 1, v_a_1703_);
return v___x_1769_;
}
else
{
lean_object* v___x_1770_; lean_object* v___x_1771_; uint8_t v___x_1772_; 
v___x_1770_ = l_Lean_Syntax_getArg(v___x_1756_, v___x_1714_);
v___x_1771_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__6));
lean_inc(v___x_1770_);
v___x_1772_ = l_Lean_Syntax_isOfKind(v___x_1770_, v___x_1771_);
if (v___x_1772_ == 0)
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
lean_dec(v___x_1770_);
lean_dec(v___x_1756_);
v___x_1773_ = l_Lean_Syntax_getArg(v___x_1709_, v___x_1708_);
lean_dec(v___x_1709_);
v___x_1774_ = l_Lean_SourceInfo_fromRef(v_a_1702_, v___x_1772_);
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
v___x_1782_ = l_Lean_Syntax_node5(v___x_1774_, v___x_1775_, v___x_1777_, v___x_1715_, v___x_1779_, v___x_1773_, v___x_1781_);
v___x_1783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1782_);
lean_ctor_set(v___x_1783_, 1, v_a_1703_);
return v___x_1783_;
}
else
{
lean_object* v___x_1784_; lean_object* v___x_1785_; uint8_t v___x_1786_; 
v___x_1784_ = l_Lean_Syntax_getArg(v___x_1770_, v___x_1714_);
v___x_1785_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__8));
lean_inc(v___x_1784_);
v___x_1786_ = l_Lean_Syntax_isOfKind(v___x_1784_, v___x_1785_);
if (v___x_1786_ == 0)
{
lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
lean_dec(v___x_1784_);
lean_dec(v___x_1770_);
lean_dec(v___x_1756_);
v___x_1787_ = l_Lean_Syntax_getArg(v___x_1709_, v___x_1708_);
lean_dec(v___x_1709_);
v___x_1788_ = l_Lean_SourceInfo_fromRef(v_a_1702_, v___x_1786_);
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
v___x_1796_ = l_Lean_Syntax_node5(v___x_1788_, v___x_1789_, v___x_1791_, v___x_1715_, v___x_1793_, v___x_1787_, v___x_1795_);
v___x_1797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1796_);
lean_ctor_set(v___x_1797_, 1, v_a_1703_);
return v___x_1797_;
}
else
{
lean_object* v___x_1798_; lean_object* v___x_1799_; uint8_t v___x_1800_; 
v___x_1798_ = l_Lean_Syntax_getArg(v___x_1784_, v___x_1714_);
v___x_1799_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__10));
v___x_1800_ = l_Lean_Syntax_matchesIdent(v___x_1798_, v___x_1799_);
lean_dec(v___x_1798_);
if (v___x_1800_ == 0)
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
lean_dec(v___x_1784_);
lean_dec(v___x_1770_);
lean_dec(v___x_1756_);
v___x_1801_ = l_Lean_Syntax_getArg(v___x_1709_, v___x_1708_);
lean_dec(v___x_1709_);
v___x_1802_ = l_Lean_SourceInfo_fromRef(v_a_1702_, v___x_1800_);
v___x_1803_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1804_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1802_, 3);
v___x_1805_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1802_);
lean_ctor_set(v___x_1805_, 1, v___x_1804_);
v___x_1806_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1807_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1802_);
lean_ctor_set(v___x_1807_, 1, v___x_1806_);
v___x_1808_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1809_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1802_);
lean_ctor_set(v___x_1809_, 1, v___x_1808_);
v___x_1810_ = l_Lean_Syntax_node5(v___x_1802_, v___x_1803_, v___x_1805_, v___x_1715_, v___x_1807_, v___x_1801_, v___x_1809_);
v___x_1811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1810_);
lean_ctor_set(v___x_1811_, 1, v_a_1703_);
return v___x_1811_;
}
else
{
lean_object* v___x_1812_; uint8_t v___x_1813_; 
v___x_1812_ = l_Lean_Syntax_getArg(v___x_1784_, v___x_1708_);
lean_dec(v___x_1784_);
v___x_1813_ = l_Lean_Syntax_matchesNull(v___x_1812_, v___x_1714_);
if (v___x_1813_ == 0)
{
lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
lean_dec(v___x_1770_);
lean_dec(v___x_1756_);
v___x_1814_ = l_Lean_Syntax_getArg(v___x_1709_, v___x_1708_);
lean_dec(v___x_1709_);
v___x_1815_ = l_Lean_SourceInfo_fromRef(v_a_1702_, v___x_1813_);
v___x_1816_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1817_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1815_, 3);
v___x_1818_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1815_);
lean_ctor_set(v___x_1818_, 1, v___x_1817_);
v___x_1819_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1820_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1815_);
lean_ctor_set(v___x_1820_, 1, v___x_1819_);
v___x_1821_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1822_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1815_);
lean_ctor_set(v___x_1822_, 1, v___x_1821_);
v___x_1823_ = l_Lean_Syntax_node5(v___x_1815_, v___x_1816_, v___x_1818_, v___x_1715_, v___x_1820_, v___x_1814_, v___x_1822_);
v___x_1824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1823_);
lean_ctor_set(v___x_1824_, 1, v_a_1703_);
return v___x_1824_;
}
else
{
lean_object* v___x_1825_; lean_object* v___x_1826_; uint8_t v___x_1827_; 
v___x_1825_ = l_Lean_Syntax_getArg(v___x_1770_, v___x_1708_);
lean_dec(v___x_1770_);
v___x_1826_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_1825_);
v___x_1827_ = l_Lean_Syntax_matchesNull(v___x_1825_, v___x_1826_);
if (v___x_1827_ == 0)
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
lean_dec(v___x_1825_);
lean_dec(v___x_1756_);
v___x_1828_ = l_Lean_Syntax_getArg(v___x_1709_, v___x_1708_);
lean_dec(v___x_1709_);
v___x_1829_ = l_Lean_SourceInfo_fromRef(v_a_1702_, v___x_1827_);
v___x_1830_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1831_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1829_, 3);
v___x_1832_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1829_);
lean_ctor_set(v___x_1832_, 1, v___x_1831_);
v___x_1833_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1834_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1829_);
lean_ctor_set(v___x_1834_, 1, v___x_1833_);
v___x_1835_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1836_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1829_);
lean_ctor_set(v___x_1836_, 1, v___x_1835_);
v___x_1837_ = l_Lean_Syntax_node5(v___x_1829_, v___x_1830_, v___x_1832_, v___x_1715_, v___x_1834_, v___x_1828_, v___x_1836_);
v___x_1838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1837_);
lean_ctor_set(v___x_1838_, 1, v_a_1703_);
return v___x_1838_;
}
else
{
lean_object* v___x_1839_; uint8_t v___x_1840_; 
v___x_1839_ = l_Lean_Syntax_getArg(v___x_1825_, v___x_1714_);
v___x_1840_ = l_Lean_Syntax_matchesNull(v___x_1839_, v___x_1714_);
if (v___x_1840_ == 0)
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
lean_dec(v___x_1825_);
lean_dec(v___x_1756_);
v___x_1841_ = l_Lean_Syntax_getArg(v___x_1709_, v___x_1708_);
lean_dec(v___x_1709_);
v___x_1842_ = l_Lean_SourceInfo_fromRef(v_a_1702_, v___x_1840_);
v___x_1843_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1844_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1842_, 3);
v___x_1845_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1842_);
lean_ctor_set(v___x_1845_, 1, v___x_1844_);
v___x_1846_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1847_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1842_);
lean_ctor_set(v___x_1847_, 1, v___x_1846_);
v___x_1848_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1849_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1842_);
lean_ctor_set(v___x_1849_, 1, v___x_1848_);
v___x_1850_ = l_Lean_Syntax_node5(v___x_1842_, v___x_1843_, v___x_1845_, v___x_1715_, v___x_1847_, v___x_1841_, v___x_1849_);
v___x_1851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
lean_ctor_set(v___x_1851_, 1, v_a_1703_);
return v___x_1851_;
}
else
{
lean_object* v___x_1852_; uint8_t v___x_1853_; 
v___x_1852_ = l_Lean_Syntax_getArg(v___x_1825_, v___x_1708_);
v___x_1853_ = l_Lean_Syntax_matchesNull(v___x_1852_, v___x_1714_);
if (v___x_1853_ == 0)
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
lean_dec(v___x_1825_);
lean_dec(v___x_1756_);
v___x_1854_ = l_Lean_Syntax_getArg(v___x_1709_, v___x_1708_);
lean_dec(v___x_1709_);
v___x_1855_ = l_Lean_SourceInfo_fromRef(v_a_1702_, v___x_1853_);
v___x_1856_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1857_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1855_, 3);
v___x_1858_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1855_);
lean_ctor_set(v___x_1858_, 1, v___x_1857_);
v___x_1859_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1860_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1855_);
lean_ctor_set(v___x_1860_, 1, v___x_1859_);
v___x_1861_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1862_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1855_);
lean_ctor_set(v___x_1862_, 1, v___x_1861_);
v___x_1863_ = l_Lean_Syntax_node5(v___x_1855_, v___x_1856_, v___x_1858_, v___x_1715_, v___x_1860_, v___x_1854_, v___x_1862_);
v___x_1864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1863_);
lean_ctor_set(v___x_1864_, 1, v_a_1703_);
return v___x_1864_;
}
else
{
lean_object* v___x_1865_; lean_object* v___x_1866_; uint8_t v___x_1867_; 
v___x_1865_ = l_Lean_Syntax_getArg(v___x_1825_, v___x_1710_);
lean_dec(v___x_1825_);
v___x_1866_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__12));
lean_inc(v___x_1865_);
v___x_1867_ = l_Lean_Syntax_isOfKind(v___x_1865_, v___x_1866_);
if (v___x_1867_ == 0)
{
lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
lean_dec(v___x_1865_);
lean_dec(v___x_1756_);
v___x_1868_ = l_Lean_Syntax_getArg(v___x_1709_, v___x_1708_);
lean_dec(v___x_1709_);
v___x_1869_ = l_Lean_SourceInfo_fromRef(v_a_1702_, v___x_1867_);
v___x_1870_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1871_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1869_, 3);
v___x_1872_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1869_);
lean_ctor_set(v___x_1872_, 1, v___x_1871_);
v___x_1873_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1874_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1869_);
lean_ctor_set(v___x_1874_, 1, v___x_1873_);
v___x_1875_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1876_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1869_);
lean_ctor_set(v___x_1876_, 1, v___x_1875_);
v___x_1877_ = l_Lean_Syntax_node5(v___x_1869_, v___x_1870_, v___x_1872_, v___x_1715_, v___x_1874_, v___x_1868_, v___x_1876_);
v___x_1878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1877_);
lean_ctor_set(v___x_1878_, 1, v_a_1703_);
return v___x_1878_;
}
else
{
lean_object* v___x_1879_; uint8_t v___x_1880_; 
v___x_1879_ = l_Lean_Syntax_getArg(v___x_1865_, v___x_1708_);
v___x_1880_ = l_Lean_Syntax_matchesNull(v___x_1879_, v___x_1714_);
if (v___x_1880_ == 0)
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
lean_dec(v___x_1865_);
lean_dec(v___x_1756_);
v___x_1881_ = l_Lean_Syntax_getArg(v___x_1709_, v___x_1708_);
lean_dec(v___x_1709_);
v___x_1882_ = l_Lean_SourceInfo_fromRef(v_a_1702_, v___x_1880_);
v___x_1883_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1884_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1882_, 3);
v___x_1885_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1882_);
lean_ctor_set(v___x_1885_, 1, v___x_1884_);
v___x_1886_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1887_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1887_, 0, v___x_1882_);
lean_ctor_set(v___x_1887_, 1, v___x_1886_);
v___x_1888_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1889_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1882_);
lean_ctor_set(v___x_1889_, 1, v___x_1888_);
v___x_1890_ = l_Lean_Syntax_node5(v___x_1882_, v___x_1883_, v___x_1885_, v___x_1715_, v___x_1887_, v___x_1881_, v___x_1889_);
v___x_1891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1890_);
lean_ctor_set(v___x_1891_, 1, v_a_1703_);
return v___x_1891_;
}
else
{
lean_object* v___x_1892_; uint8_t v___x_1893_; 
v___x_1892_ = l_Lean_Syntax_getArg(v___x_1756_, v___x_1710_);
lean_inc(v___x_1892_);
v___x_1893_ = l_Lean_Syntax_isOfKind(v___x_1892_, v___x_1771_);
if (v___x_1893_ == 0)
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
lean_dec(v___x_1892_);
lean_dec(v___x_1865_);
lean_dec(v___x_1756_);
v___x_1894_ = l_Lean_Syntax_getArg(v___x_1709_, v___x_1708_);
lean_dec(v___x_1709_);
v___x_1895_ = l_Lean_SourceInfo_fromRef(v_a_1702_, v___x_1893_);
v___x_1896_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1897_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1895_, 3);
v___x_1898_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1895_);
lean_ctor_set(v___x_1898_, 1, v___x_1897_);
v___x_1899_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1900_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1895_);
lean_ctor_set(v___x_1900_, 1, v___x_1899_);
v___x_1901_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1902_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1895_);
lean_ctor_set(v___x_1902_, 1, v___x_1901_);
v___x_1903_ = l_Lean_Syntax_node5(v___x_1895_, v___x_1896_, v___x_1898_, v___x_1715_, v___x_1900_, v___x_1894_, v___x_1902_);
v___x_1904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1903_);
lean_ctor_set(v___x_1904_, 1, v_a_1703_);
return v___x_1904_;
}
else
{
lean_object* v___x_1905_; uint8_t v___x_1906_; 
v___x_1905_ = l_Lean_Syntax_getArg(v___x_1892_, v___x_1714_);
lean_inc(v___x_1905_);
v___x_1906_ = l_Lean_Syntax_isOfKind(v___x_1905_, v___x_1785_);
if (v___x_1906_ == 0)
{
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
lean_dec(v___x_1905_);
lean_dec(v___x_1892_);
lean_dec(v___x_1865_);
lean_dec(v___x_1756_);
v___x_1907_ = l_Lean_Syntax_getArg(v___x_1709_, v___x_1708_);
lean_dec(v___x_1709_);
v___x_1908_ = l_Lean_SourceInfo_fromRef(v_a_1702_, v___x_1906_);
v___x_1909_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1910_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1908_, 3);
v___x_1911_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1908_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
v___x_1912_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1913_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1908_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
v___x_1914_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1915_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1908_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
v___x_1916_ = l_Lean_Syntax_node5(v___x_1908_, v___x_1909_, v___x_1911_, v___x_1715_, v___x_1913_, v___x_1907_, v___x_1915_);
v___x_1917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1916_);
lean_ctor_set(v___x_1917_, 1, v_a_1703_);
return v___x_1917_;
}
else
{
lean_object* v___x_1918_; lean_object* v___x_1919_; uint8_t v___x_1920_; 
v___x_1918_ = l_Lean_Syntax_getArg(v___x_1905_, v___x_1714_);
v___x_1919_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__14));
v___x_1920_ = l_Lean_Syntax_matchesIdent(v___x_1918_, v___x_1919_);
lean_dec(v___x_1918_);
if (v___x_1920_ == 0)
{
lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
lean_dec(v___x_1905_);
lean_dec(v___x_1892_);
lean_dec(v___x_1865_);
lean_dec(v___x_1756_);
v___x_1921_ = l_Lean_Syntax_getArg(v___x_1709_, v___x_1708_);
lean_dec(v___x_1709_);
v___x_1922_ = l_Lean_SourceInfo_fromRef(v_a_1702_, v___x_1920_);
v___x_1923_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1924_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1922_, 3);
v___x_1925_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1922_);
lean_ctor_set(v___x_1925_, 1, v___x_1924_);
v___x_1926_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1927_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1922_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
v___x_1928_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1929_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1922_);
lean_ctor_set(v___x_1929_, 1, v___x_1928_);
v___x_1930_ = l_Lean_Syntax_node5(v___x_1922_, v___x_1923_, v___x_1925_, v___x_1715_, v___x_1927_, v___x_1921_, v___x_1929_);
v___x_1931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1930_);
lean_ctor_set(v___x_1931_, 1, v_a_1703_);
return v___x_1931_;
}
else
{
lean_object* v___x_1932_; uint8_t v___x_1933_; 
v___x_1932_ = l_Lean_Syntax_getArg(v___x_1905_, v___x_1708_);
lean_dec(v___x_1905_);
v___x_1933_ = l_Lean_Syntax_matchesNull(v___x_1932_, v___x_1714_);
if (v___x_1933_ == 0)
{
lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
lean_dec(v___x_1892_);
lean_dec(v___x_1865_);
lean_dec(v___x_1756_);
v___x_1934_ = l_Lean_Syntax_getArg(v___x_1709_, v___x_1708_);
lean_dec(v___x_1709_);
v___x_1935_ = l_Lean_SourceInfo_fromRef(v_a_1702_, v___x_1933_);
v___x_1936_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1937_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1935_, 3);
v___x_1938_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1935_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
v___x_1939_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1940_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1935_);
lean_ctor_set(v___x_1940_, 1, v___x_1939_);
v___x_1941_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1942_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1935_);
lean_ctor_set(v___x_1942_, 1, v___x_1941_);
v___x_1943_ = l_Lean_Syntax_node5(v___x_1935_, v___x_1936_, v___x_1938_, v___x_1715_, v___x_1940_, v___x_1934_, v___x_1942_);
v___x_1944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1943_);
lean_ctor_set(v___x_1944_, 1, v_a_1703_);
return v___x_1944_;
}
else
{
lean_object* v___x_1945_; uint8_t v___x_1946_; 
v___x_1945_ = l_Lean_Syntax_getArg(v___x_1892_, v___x_1708_);
lean_dec(v___x_1892_);
lean_inc(v___x_1945_);
v___x_1946_ = l_Lean_Syntax_matchesNull(v___x_1945_, v___x_1826_);
if (v___x_1946_ == 0)
{
lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; 
lean_dec(v___x_1945_);
lean_dec(v___x_1865_);
lean_dec(v___x_1756_);
v___x_1947_ = l_Lean_Syntax_getArg(v___x_1709_, v___x_1708_);
lean_dec(v___x_1709_);
v___x_1948_ = l_Lean_SourceInfo_fromRef(v_a_1702_, v___x_1946_);
v___x_1949_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1950_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1948_, 3);
v___x_1951_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1948_);
lean_ctor_set(v___x_1951_, 1, v___x_1950_);
v___x_1952_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1953_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1948_);
lean_ctor_set(v___x_1953_, 1, v___x_1952_);
v___x_1954_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1955_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1948_);
lean_ctor_set(v___x_1955_, 1, v___x_1954_);
v___x_1956_ = l_Lean_Syntax_node5(v___x_1948_, v___x_1949_, v___x_1951_, v___x_1715_, v___x_1953_, v___x_1947_, v___x_1955_);
v___x_1957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1956_);
lean_ctor_set(v___x_1957_, 1, v_a_1703_);
return v___x_1957_;
}
else
{
lean_object* v___x_1958_; uint8_t v___x_1959_; 
v___x_1958_ = l_Lean_Syntax_getArg(v___x_1945_, v___x_1714_);
v___x_1959_ = l_Lean_Syntax_matchesNull(v___x_1958_, v___x_1714_);
if (v___x_1959_ == 0)
{
lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
lean_dec(v___x_1945_);
lean_dec(v___x_1865_);
lean_dec(v___x_1756_);
v___x_1960_ = l_Lean_Syntax_getArg(v___x_1709_, v___x_1708_);
lean_dec(v___x_1709_);
v___x_1961_ = l_Lean_SourceInfo_fromRef(v_a_1702_, v___x_1959_);
v___x_1962_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1963_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1961_, 3);
v___x_1964_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1961_);
lean_ctor_set(v___x_1964_, 1, v___x_1963_);
v___x_1965_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1966_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1961_);
lean_ctor_set(v___x_1966_, 1, v___x_1965_);
v___x_1967_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1968_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1961_);
lean_ctor_set(v___x_1968_, 1, v___x_1967_);
v___x_1969_ = l_Lean_Syntax_node5(v___x_1961_, v___x_1962_, v___x_1964_, v___x_1715_, v___x_1966_, v___x_1960_, v___x_1968_);
v___x_1970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1969_);
lean_ctor_set(v___x_1970_, 1, v_a_1703_);
return v___x_1970_;
}
else
{
lean_object* v___x_1971_; uint8_t v___x_1972_; 
v___x_1971_ = l_Lean_Syntax_getArg(v___x_1945_, v___x_1708_);
v___x_1972_ = l_Lean_Syntax_matchesNull(v___x_1971_, v___x_1714_);
if (v___x_1972_ == 0)
{
lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; 
lean_dec(v___x_1945_);
lean_dec(v___x_1865_);
lean_dec(v___x_1756_);
v___x_1973_ = l_Lean_Syntax_getArg(v___x_1709_, v___x_1708_);
lean_dec(v___x_1709_);
v___x_1974_ = l_Lean_SourceInfo_fromRef(v_a_1702_, v___x_1972_);
v___x_1975_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1976_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1974_, 3);
v___x_1977_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1974_);
lean_ctor_set(v___x_1977_, 1, v___x_1976_);
v___x_1978_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1979_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1974_);
lean_ctor_set(v___x_1979_, 1, v___x_1978_);
v___x_1980_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1981_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1974_);
lean_ctor_set(v___x_1981_, 1, v___x_1980_);
v___x_1982_ = l_Lean_Syntax_node5(v___x_1974_, v___x_1975_, v___x_1977_, v___x_1715_, v___x_1979_, v___x_1973_, v___x_1981_);
v___x_1983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1982_);
lean_ctor_set(v___x_1983_, 1, v_a_1703_);
return v___x_1983_;
}
else
{
lean_object* v___x_1984_; uint8_t v___x_1985_; 
v___x_1984_ = l_Lean_Syntax_getArg(v___x_1945_, v___x_1710_);
lean_dec(v___x_1945_);
lean_inc(v___x_1984_);
v___x_1985_ = l_Lean_Syntax_isOfKind(v___x_1984_, v___x_1866_);
if (v___x_1985_ == 0)
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
lean_dec(v___x_1984_);
lean_dec(v___x_1865_);
lean_dec(v___x_1756_);
v___x_1986_ = l_Lean_Syntax_getArg(v___x_1709_, v___x_1708_);
lean_dec(v___x_1709_);
v___x_1987_ = l_Lean_SourceInfo_fromRef(v_a_1702_, v___x_1985_);
v___x_1988_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1989_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1987_, 3);
v___x_1990_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1987_);
lean_ctor_set(v___x_1990_, 1, v___x_1989_);
v___x_1991_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1992_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1987_);
lean_ctor_set(v___x_1992_, 1, v___x_1991_);
v___x_1993_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1994_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1987_);
lean_ctor_set(v___x_1994_, 1, v___x_1993_);
v___x_1995_ = l_Lean_Syntax_node5(v___x_1987_, v___x_1988_, v___x_1990_, v___x_1715_, v___x_1992_, v___x_1986_, v___x_1994_);
v___x_1996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1995_);
lean_ctor_set(v___x_1996_, 1, v_a_1703_);
return v___x_1996_;
}
else
{
lean_object* v___x_1997_; uint8_t v___x_1998_; 
v___x_1997_ = l_Lean_Syntax_getArg(v___x_1984_, v___x_1708_);
v___x_1998_ = l_Lean_Syntax_matchesNull(v___x_1997_, v___x_1714_);
if (v___x_1998_ == 0)
{
lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
lean_dec(v___x_1984_);
lean_dec(v___x_1865_);
lean_dec(v___x_1756_);
v___x_1999_ = l_Lean_Syntax_getArg(v___x_1709_, v___x_1708_);
lean_dec(v___x_1709_);
v___x_2000_ = l_Lean_SourceInfo_fromRef(v_a_1702_, v___x_1998_);
v___x_2001_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2002_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2000_, 3);
v___x_2003_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2003_, 0, v___x_2000_);
lean_ctor_set(v___x_2003_, 1, v___x_2002_);
v___x_2004_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2005_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2005_, 0, v___x_2000_);
lean_ctor_set(v___x_2005_, 1, v___x_2004_);
v___x_2006_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2007_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2000_);
lean_ctor_set(v___x_2007_, 1, v___x_2006_);
v___x_2008_ = l_Lean_Syntax_node5(v___x_2000_, v___x_2001_, v___x_2003_, v___x_1715_, v___x_2005_, v___x_1999_, v___x_2007_);
v___x_2009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2008_);
lean_ctor_set(v___x_2009_, 1, v_a_1703_);
return v___x_2009_;
}
else
{
lean_object* v___x_2010_; lean_object* v___x_2011_; uint8_t v___x_2012_; 
v___x_2010_ = lean_unsigned_to_nat(4u);
v___x_2011_ = l_Lean_Syntax_getArg(v___x_1756_, v___x_2010_);
lean_dec(v___x_1756_);
lean_inc(v___x_2011_);
v___x_2012_ = l_Lean_Syntax_isOfKind(v___x_2011_, v___x_1771_);
if (v___x_2012_ == 0)
{
lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
lean_dec(v___x_2011_);
lean_dec(v___x_1984_);
lean_dec(v___x_1865_);
v___x_2013_ = l_Lean_Syntax_getArg(v___x_1709_, v___x_1708_);
lean_dec(v___x_1709_);
v___x_2014_ = l_Lean_SourceInfo_fromRef(v_a_1702_, v___x_2012_);
v___x_2015_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2016_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2014_, 3);
v___x_2017_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2014_);
lean_ctor_set(v___x_2017_, 1, v___x_2016_);
v___x_2018_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2019_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2014_);
lean_ctor_set(v___x_2019_, 1, v___x_2018_);
v___x_2020_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2021_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2014_);
lean_ctor_set(v___x_2021_, 1, v___x_2020_);
v___x_2022_ = l_Lean_Syntax_node5(v___x_2014_, v___x_2015_, v___x_2017_, v___x_1715_, v___x_2019_, v___x_2013_, v___x_2021_);
v___x_2023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2022_);
lean_ctor_set(v___x_2023_, 1, v_a_1703_);
return v___x_2023_;
}
else
{
lean_object* v___x_2024_; uint8_t v___x_2025_; 
v___x_2024_ = l_Lean_Syntax_getArg(v___x_2011_, v___x_1714_);
lean_inc(v___x_2024_);
v___x_2025_ = l_Lean_Syntax_isOfKind(v___x_2024_, v___x_1785_);
if (v___x_2025_ == 0)
{
lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
lean_dec(v___x_2024_);
lean_dec(v___x_2011_);
lean_dec(v___x_1984_);
lean_dec(v___x_1865_);
v___x_2026_ = l_Lean_Syntax_getArg(v___x_1709_, v___x_1708_);
lean_dec(v___x_1709_);
v___x_2027_ = l_Lean_SourceInfo_fromRef(v_a_1702_, v___x_2025_);
v___x_2028_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2029_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2027_, 3);
v___x_2030_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2027_);
lean_ctor_set(v___x_2030_, 1, v___x_2029_);
v___x_2031_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2032_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2027_);
lean_ctor_set(v___x_2032_, 1, v___x_2031_);
v___x_2033_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2034_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2027_);
lean_ctor_set(v___x_2034_, 1, v___x_2033_);
v___x_2035_ = l_Lean_Syntax_node5(v___x_2027_, v___x_2028_, v___x_2030_, v___x_1715_, v___x_2032_, v___x_2026_, v___x_2034_);
v___x_2036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2035_);
lean_ctor_set(v___x_2036_, 1, v_a_1703_);
return v___x_2036_;
}
else
{
lean_object* v___x_2037_; lean_object* v___x_2038_; uint8_t v___x_2039_; 
v___x_2037_ = l_Lean_Syntax_getArg(v___x_2024_, v___x_1714_);
v___x_2038_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__16));
v___x_2039_ = l_Lean_Syntax_matchesIdent(v___x_2037_, v___x_2038_);
lean_dec(v___x_2037_);
if (v___x_2039_ == 0)
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
lean_dec(v___x_2024_);
lean_dec(v___x_2011_);
lean_dec(v___x_1984_);
lean_dec(v___x_1865_);
v___x_2040_ = l_Lean_Syntax_getArg(v___x_1709_, v___x_1708_);
lean_dec(v___x_1709_);
v___x_2041_ = l_Lean_SourceInfo_fromRef(v_a_1702_, v___x_2039_);
v___x_2042_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2043_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2041_, 3);
v___x_2044_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2041_);
lean_ctor_set(v___x_2044_, 1, v___x_2043_);
v___x_2045_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2046_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2041_);
lean_ctor_set(v___x_2046_, 1, v___x_2045_);
v___x_2047_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2048_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2041_);
lean_ctor_set(v___x_2048_, 1, v___x_2047_);
v___x_2049_ = l_Lean_Syntax_node5(v___x_2041_, v___x_2042_, v___x_2044_, v___x_1715_, v___x_2046_, v___x_2040_, v___x_2048_);
v___x_2050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2049_);
lean_ctor_set(v___x_2050_, 1, v_a_1703_);
return v___x_2050_;
}
else
{
lean_object* v___x_2051_; uint8_t v___x_2052_; 
v___x_2051_ = l_Lean_Syntax_getArg(v___x_2024_, v___x_1708_);
lean_dec(v___x_2024_);
v___x_2052_ = l_Lean_Syntax_matchesNull(v___x_2051_, v___x_1714_);
if (v___x_2052_ == 0)
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; 
lean_dec(v___x_2011_);
lean_dec(v___x_1984_);
lean_dec(v___x_1865_);
v___x_2053_ = l_Lean_Syntax_getArg(v___x_1709_, v___x_1708_);
lean_dec(v___x_1709_);
v___x_2054_ = l_Lean_SourceInfo_fromRef(v_a_1702_, v___x_2052_);
v___x_2055_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2056_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2054_, 3);
v___x_2057_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2057_, 0, v___x_2054_);
lean_ctor_set(v___x_2057_, 1, v___x_2056_);
v___x_2058_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2059_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2054_);
lean_ctor_set(v___x_2059_, 1, v___x_2058_);
v___x_2060_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2061_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2054_);
lean_ctor_set(v___x_2061_, 1, v___x_2060_);
v___x_2062_ = l_Lean_Syntax_node5(v___x_2054_, v___x_2055_, v___x_2057_, v___x_1715_, v___x_2059_, v___x_2053_, v___x_2061_);
v___x_2063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2062_);
lean_ctor_set(v___x_2063_, 1, v_a_1703_);
return v___x_2063_;
}
else
{
lean_object* v___x_2064_; uint8_t v___x_2065_; 
v___x_2064_ = l_Lean_Syntax_getArg(v___x_2011_, v___x_1708_);
lean_dec(v___x_2011_);
lean_inc(v___x_2064_);
v___x_2065_ = l_Lean_Syntax_matchesNull(v___x_2064_, v___x_1826_);
if (v___x_2065_ == 0)
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
lean_dec(v___x_2064_);
lean_dec(v___x_1984_);
lean_dec(v___x_1865_);
v___x_2066_ = l_Lean_Syntax_getArg(v___x_1709_, v___x_1708_);
lean_dec(v___x_1709_);
v___x_2067_ = l_Lean_SourceInfo_fromRef(v_a_1702_, v___x_2065_);
v___x_2068_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2069_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2067_, 3);
v___x_2070_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2067_);
lean_ctor_set(v___x_2070_, 1, v___x_2069_);
v___x_2071_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2072_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2067_);
lean_ctor_set(v___x_2072_, 1, v___x_2071_);
v___x_2073_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2074_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2067_);
lean_ctor_set(v___x_2074_, 1, v___x_2073_);
v___x_2075_ = l_Lean_Syntax_node5(v___x_2067_, v___x_2068_, v___x_2070_, v___x_1715_, v___x_2072_, v___x_2066_, v___x_2074_);
v___x_2076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2075_);
lean_ctor_set(v___x_2076_, 1, v_a_1703_);
return v___x_2076_;
}
else
{
lean_object* v___x_2077_; uint8_t v___x_2078_; 
v___x_2077_ = l_Lean_Syntax_getArg(v___x_2064_, v___x_1714_);
v___x_2078_ = l_Lean_Syntax_matchesNull(v___x_2077_, v___x_1714_);
if (v___x_2078_ == 0)
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
lean_dec(v___x_2064_);
lean_dec(v___x_1984_);
lean_dec(v___x_1865_);
v___x_2079_ = l_Lean_Syntax_getArg(v___x_1709_, v___x_1708_);
lean_dec(v___x_1709_);
v___x_2080_ = l_Lean_SourceInfo_fromRef(v_a_1702_, v___x_2078_);
v___x_2081_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2082_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2080_, 3);
v___x_2083_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2080_);
lean_ctor_set(v___x_2083_, 1, v___x_2082_);
v___x_2084_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2085_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2080_);
lean_ctor_set(v___x_2085_, 1, v___x_2084_);
v___x_2086_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2087_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2080_);
lean_ctor_set(v___x_2087_, 1, v___x_2086_);
v___x_2088_ = l_Lean_Syntax_node5(v___x_2080_, v___x_2081_, v___x_2083_, v___x_1715_, v___x_2085_, v___x_2079_, v___x_2087_);
v___x_2089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2088_);
lean_ctor_set(v___x_2089_, 1, v_a_1703_);
return v___x_2089_;
}
else
{
lean_object* v___x_2090_; uint8_t v___x_2091_; 
v___x_2090_ = l_Lean_Syntax_getArg(v___x_2064_, v___x_1708_);
v___x_2091_ = l_Lean_Syntax_matchesNull(v___x_2090_, v___x_1714_);
if (v___x_2091_ == 0)
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
lean_dec(v___x_2064_);
lean_dec(v___x_1984_);
lean_dec(v___x_1865_);
v___x_2092_ = l_Lean_Syntax_getArg(v___x_1709_, v___x_1708_);
lean_dec(v___x_1709_);
v___x_2093_ = l_Lean_SourceInfo_fromRef(v_a_1702_, v___x_2091_);
v___x_2094_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2095_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2093_, 3);
v___x_2096_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2093_);
lean_ctor_set(v___x_2096_, 1, v___x_2095_);
v___x_2097_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2098_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2093_);
lean_ctor_set(v___x_2098_, 1, v___x_2097_);
v___x_2099_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2100_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2093_);
lean_ctor_set(v___x_2100_, 1, v___x_2099_);
v___x_2101_ = l_Lean_Syntax_node5(v___x_2093_, v___x_2094_, v___x_2096_, v___x_1715_, v___x_2098_, v___x_2092_, v___x_2100_);
v___x_2102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2101_);
lean_ctor_set(v___x_2102_, 1, v_a_1703_);
return v___x_2102_;
}
else
{
lean_object* v___x_2103_; uint8_t v___x_2104_; 
v___x_2103_ = l_Lean_Syntax_getArg(v___x_2064_, v___x_1710_);
lean_dec(v___x_2064_);
lean_inc(v___x_2103_);
v___x_2104_ = l_Lean_Syntax_isOfKind(v___x_2103_, v___x_1866_);
if (v___x_2104_ == 0)
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
lean_dec(v___x_2103_);
lean_dec(v___x_1984_);
lean_dec(v___x_1865_);
v___x_2105_ = l_Lean_Syntax_getArg(v___x_1709_, v___x_1708_);
lean_dec(v___x_1709_);
v___x_2106_ = l_Lean_SourceInfo_fromRef(v_a_1702_, v___x_2104_);
v___x_2107_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2108_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2106_, 3);
v___x_2109_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2106_);
lean_ctor_set(v___x_2109_, 1, v___x_2108_);
v___x_2110_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2111_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2106_);
lean_ctor_set(v___x_2111_, 1, v___x_2110_);
v___x_2112_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2113_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2106_);
lean_ctor_set(v___x_2113_, 1, v___x_2112_);
v___x_2114_ = l_Lean_Syntax_node5(v___x_2106_, v___x_2107_, v___x_2109_, v___x_1715_, v___x_2111_, v___x_2105_, v___x_2113_);
v___x_2115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
lean_ctor_set(v___x_2115_, 1, v_a_1703_);
return v___x_2115_;
}
else
{
lean_object* v___x_2116_; uint8_t v___x_2117_; 
v___x_2116_ = l_Lean_Syntax_getArg(v___x_2103_, v___x_1708_);
v___x_2117_ = l_Lean_Syntax_matchesNull(v___x_2116_, v___x_1714_);
if (v___x_2117_ == 0)
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
lean_dec(v___x_2103_);
lean_dec(v___x_1984_);
lean_dec(v___x_1865_);
v___x_2118_ = l_Lean_Syntax_getArg(v___x_1709_, v___x_1708_);
lean_dec(v___x_1709_);
v___x_2119_ = l_Lean_SourceInfo_fromRef(v_a_1702_, v___x_2117_);
v___x_2120_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2121_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2119_, 3);
v___x_2122_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2119_);
lean_ctor_set(v___x_2122_, 1, v___x_2121_);
v___x_2123_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2124_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2119_);
lean_ctor_set(v___x_2124_, 1, v___x_2123_);
v___x_2125_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2126_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2119_);
lean_ctor_set(v___x_2126_, 1, v___x_2125_);
v___x_2127_ = l_Lean_Syntax_node5(v___x_2119_, v___x_2120_, v___x_2122_, v___x_1715_, v___x_2124_, v___x_2118_, v___x_2126_);
v___x_2128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2127_);
lean_ctor_set(v___x_2128_, 1, v_a_1703_);
return v___x_2128_;
}
else
{
lean_object* v___x_2129_; lean_object* v___x_2130_; uint8_t v___x_2131_; 
v___x_2129_ = l_Lean_Syntax_getArg(v___x_1715_, v___x_1826_);
v___x_2130_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__18));
lean_inc(v___x_2129_);
v___x_2131_ = l_Lean_Syntax_isOfKind(v___x_2129_, v___x_2130_);
if (v___x_2131_ == 0)
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
lean_dec(v___x_2129_);
lean_dec(v___x_2103_);
lean_dec(v___x_1984_);
lean_dec(v___x_1865_);
v___x_2132_ = l_Lean_Syntax_getArg(v___x_1709_, v___x_1708_);
lean_dec(v___x_1709_);
v___x_2133_ = l_Lean_SourceInfo_fromRef(v_a_1702_, v___x_2131_);
v___x_2134_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2135_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2133_, 3);
v___x_2136_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2133_);
lean_ctor_set(v___x_2136_, 1, v___x_2135_);
v___x_2137_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2138_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2138_, 0, v___x_2133_);
lean_ctor_set(v___x_2138_, 1, v___x_2137_);
v___x_2139_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2140_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2133_);
lean_ctor_set(v___x_2140_, 1, v___x_2139_);
v___x_2141_ = l_Lean_Syntax_node5(v___x_2133_, v___x_2134_, v___x_2136_, v___x_1715_, v___x_2138_, v___x_2132_, v___x_2140_);
v___x_2142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2141_);
lean_ctor_set(v___x_2142_, 1, v_a_1703_);
return v___x_2142_;
}
else
{
lean_object* v___x_2143_; uint8_t v___x_2144_; 
v___x_2143_ = l_Lean_Syntax_getArg(v___x_2129_, v___x_1714_);
lean_dec(v___x_2129_);
v___x_2144_ = l_Lean_Syntax_matchesNull(v___x_2143_, v___x_1714_);
if (v___x_2144_ == 0)
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; 
lean_dec(v___x_2103_);
lean_dec(v___x_1984_);
lean_dec(v___x_1865_);
v___x_2145_ = l_Lean_Syntax_getArg(v___x_1709_, v___x_1708_);
lean_dec(v___x_1709_);
v___x_2146_ = l_Lean_SourceInfo_fromRef(v_a_1702_, v___x_2144_);
v___x_2147_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2148_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2146_, 3);
v___x_2149_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2146_);
lean_ctor_set(v___x_2149_, 1, v___x_2148_);
v___x_2150_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2151_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2146_);
lean_ctor_set(v___x_2151_, 1, v___x_2150_);
v___x_2152_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2153_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2146_);
lean_ctor_set(v___x_2153_, 1, v___x_2152_);
v___x_2154_ = l_Lean_Syntax_node5(v___x_2146_, v___x_2147_, v___x_2149_, v___x_1715_, v___x_2151_, v___x_2145_, v___x_2153_);
v___x_2155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2154_);
lean_ctor_set(v___x_2155_, 1, v_a_1703_);
return v___x_2155_;
}
else
{
lean_object* v___x_2156_; uint8_t v___x_2157_; 
v___x_2156_ = l_Lean_Syntax_getArg(v___x_1715_, v___x_2010_);
v___x_2157_ = l_Lean_Syntax_matchesNull(v___x_2156_, v___x_1714_);
if (v___x_2157_ == 0)
{
lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
lean_dec(v___x_2103_);
lean_dec(v___x_1984_);
lean_dec(v___x_1865_);
v___x_2158_ = l_Lean_Syntax_getArg(v___x_1709_, v___x_1708_);
lean_dec(v___x_1709_);
v___x_2159_ = l_Lean_SourceInfo_fromRef(v_a_1702_, v___x_2157_);
v___x_2160_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2161_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2159_, 3);
v___x_2162_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2159_);
lean_ctor_set(v___x_2162_, 1, v___x_2161_);
v___x_2163_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2164_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2159_);
lean_ctor_set(v___x_2164_, 1, v___x_2163_);
v___x_2165_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2166_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2159_);
lean_ctor_set(v___x_2166_, 1, v___x_2165_);
v___x_2167_ = l_Lean_Syntax_node5(v___x_2159_, v___x_2160_, v___x_2162_, v___x_1715_, v___x_2164_, v___x_2158_, v___x_2166_);
v___x_2168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2167_);
lean_ctor_set(v___x_2168_, 1, v_a_1703_);
return v___x_2168_;
}
else
{
lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; uint8_t v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; 
lean_dec(v___x_1715_);
v___x_2169_ = l_Lean_Syntax_getArg(v___x_1865_, v___x_1710_);
lean_dec(v___x_1865_);
v___x_2170_ = l_Lean_Syntax_getArg(v___x_1984_, v___x_1710_);
lean_dec(v___x_1984_);
v___x_2171_ = l_Lean_Syntax_getArg(v___x_2103_, v___x_1710_);
lean_dec(v___x_2103_);
v___x_2172_ = l_Lean_Syntax_getArg(v___x_1709_, v___x_1708_);
lean_dec(v___x_1709_);
v___x_2173_ = 0;
v___x_2174_ = l_Lean_SourceInfo_fromRef(v_a_1702_, v___x_2173_);
v___x_2175_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__1));
v___x_2176_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2174_, 7);
v___x_2177_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2174_);
lean_ctor_set(v___x_2177_, 1, v___x_2176_);
v___x_2178_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2179_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2179_, 0, v___x_2174_);
lean_ctor_set(v___x_2179_, 1, v___x_2178_);
v___x_2180_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__20));
v___x_2181_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__21));
v___x_2182_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2174_);
lean_ctor_set(v___x_2182_, 1, v___x_2181_);
v___x_2183_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__9));
lean_inc_ref_n(v___x_2179_, 2);
v___x_2184_ = l_Lean_Syntax_node3(v___x_2174_, v___x_2183_, v___x_2170_, v___x_2179_, v___x_2171_);
v___x_2185_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__22));
v___x_2186_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2174_);
lean_ctor_set(v___x_2186_, 1, v___x_2185_);
v___x_2187_ = l_Lean_Syntax_node3(v___x_2174_, v___x_2180_, v___x_2182_, v___x_2184_, v___x_2186_);
v___x_2188_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2189_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2174_);
lean_ctor_set(v___x_2189_, 1, v___x_2188_);
v___x_2190_ = l_Lean_Syntax_node7(v___x_2174_, v___x_2175_, v___x_2177_, v___x_2169_, v___x_2179_, v___x_2187_, v___x_2179_, v___x_2172_, v___x_2189_);
v___x_2191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2190_);
lean_ctor_set(v___x_2191_, 1, v_a_1703_);
return v___x_2191_;
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_unexpandDenote___boxed(lean_object* v_x_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_){
_start:
{
lean_object* v_res_2195_; 
v_res_2195_ = l_Std_Sat_AIG_unexpandDenote(v_x_2192_, v_a_2193_, v_a_2194_);
lean_dec(v_a_2193_);
return v_res_2195_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_isConstant___redArg(lean_object* v_aig_2196_, lean_object* v_ref_2197_, uint8_t v_b_2198_){
_start:
{
lean_object* v_gate_2199_; uint8_t v_invert_2200_; lean_object* v_decls_2201_; lean_object* v_decl_2202_; 
v_gate_2199_ = lean_ctor_get(v_ref_2197_, 0);
v_invert_2200_ = lean_ctor_get_uint8(v_ref_2197_, sizeof(void*)*1);
v_decls_2201_ = lean_ctor_get(v_aig_2196_, 0);
v_decl_2202_ = lean_array_fget_borrowed(v_decls_2201_, v_gate_2199_);
if (lean_obj_tag(v_decl_2202_) == 0)
{
if (v_b_2198_ == 0)
{
if (v_invert_2200_ == 0)
{
uint8_t v___x_2203_; 
v___x_2203_ = 1;
return v___x_2203_;
}
else
{
return v_b_2198_;
}
}
else
{
return v_invert_2200_;
}
}
else
{
uint8_t v___x_2204_; 
v___x_2204_ = 0;
return v___x_2204_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_isConstant___redArg___boxed(lean_object* v_aig_2205_, lean_object* v_ref_2206_, lean_object* v_b_2207_){
_start:
{
uint8_t v_b_boxed_2208_; uint8_t v_res_2209_; lean_object* v_r_2210_; 
v_b_boxed_2208_ = lean_unbox(v_b_2207_);
v_res_2209_ = l_Std_Sat_AIG_isConstant___redArg(v_aig_2205_, v_ref_2206_, v_b_boxed_2208_);
lean_dec_ref(v_ref_2206_);
lean_dec_ref(v_aig_2205_);
v_r_2210_ = lean_box(v_res_2209_);
return v_r_2210_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_isConstant(lean_object* v_00_u03b1_2211_, lean_object* v_inst_2212_, lean_object* v_inst_2213_, lean_object* v_aig_2214_, lean_object* v_ref_2215_, uint8_t v_b_2216_){
_start:
{
uint8_t v___x_2217_; 
v___x_2217_ = l_Std_Sat_AIG_isConstant___redArg(v_aig_2214_, v_ref_2215_, v_b_2216_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_isConstant___boxed(lean_object* v_00_u03b1_2218_, lean_object* v_inst_2219_, lean_object* v_inst_2220_, lean_object* v_aig_2221_, lean_object* v_ref_2222_, lean_object* v_b_2223_){
_start:
{
uint8_t v_b_boxed_2224_; uint8_t v_res_2225_; lean_object* v_r_2226_; 
v_b_boxed_2224_ = lean_unbox(v_b_2223_);
v_res_2225_ = l_Std_Sat_AIG_isConstant(v_00_u03b1_2218_, v_inst_2219_, v_inst_2220_, v_aig_2221_, v_ref_2222_, v_b_boxed_2224_);
lean_dec_ref(v_ref_2222_);
lean_dec_ref(v_aig_2221_);
lean_dec_ref(v_inst_2220_);
lean_dec_ref(v_inst_2219_);
v_r_2226_ = lean_box(v_res_2225_);
return v_r_2226_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___redArg(lean_object* v_aig_2227_, lean_object* v_ref_2228_){
_start:
{
lean_object* v_gate_2229_; uint8_t v_invert_2230_; lean_object* v_decls_2231_; lean_object* v_decl_2232_; 
v_gate_2229_ = lean_ctor_get(v_ref_2228_, 0);
v_invert_2230_ = lean_ctor_get_uint8(v_ref_2228_, sizeof(void*)*1);
v_decls_2231_ = lean_ctor_get(v_aig_2227_, 0);
v_decl_2232_ = lean_array_fget_borrowed(v_decls_2231_, v_gate_2229_);
if (lean_obj_tag(v_decl_2232_) == 0)
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2233_ = lean_box(v_invert_2230_);
v___x_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2233_);
return v___x_2234_;
}
else
{
lean_object* v___x_2235_; 
v___x_2235_ = lean_box(0);
return v___x_2235_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___redArg___boxed(lean_object* v_aig_2236_, lean_object* v_ref_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l_Std_Sat_AIG_getConstant___redArg(v_aig_2236_, v_ref_2237_);
lean_dec_ref(v_ref_2237_);
lean_dec_ref(v_aig_2236_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant(lean_object* v_00_u03b1_2239_, lean_object* v_inst_2240_, lean_object* v_inst_2241_, lean_object* v_aig_2242_, lean_object* v_ref_2243_){
_start:
{
lean_object* v___x_2244_; 
v___x_2244_ = l_Std_Sat_AIG_getConstant___redArg(v_aig_2242_, v_ref_2243_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___boxed(lean_object* v_00_u03b1_2245_, lean_object* v_inst_2246_, lean_object* v_inst_2247_, lean_object* v_aig_2248_, lean_object* v_ref_2249_){
_start:
{
lean_object* v_res_2250_; 
v_res_2250_ = l_Std_Sat_AIG_getConstant(v_00_u03b1_2245_, v_inst_2246_, v_inst_2247_, v_aig_2248_, v_ref_2249_);
lean_dec_ref(v_ref_2249_);
lean_dec_ref(v_aig_2248_);
lean_dec_ref(v_inst_2247_);
lean_dec_ref(v_inst_2246_);
return v_res_2250_;
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
l_Std_Sat_AIG_Cache_empty___auto__1 = _init_l_Std_Sat_AIG_Cache_empty___auto__1();
lean_mark_persistent(l_Std_Sat_AIG_Cache_empty___auto__1);
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
