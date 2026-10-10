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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_ctorIdx___impl___boxed(lean_object*, lean_object*);
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
uint64_t l_Std_Sat_AIG_instHashableFanin_hash(lean_object* v_x_1_){
_start:
{
uint64_t v___x_2_; uint64_t v___x_3_; uint64_t v___x_4_; 
v___x_2_ = 0ULL;
v___x_3_ = lean_uint64_of_nat(v_x_1_);
v___x_4_ = lean_uint64_mix_hash(v___x_2_, v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT void l_Std_Sat_AIG_instHashableFanin_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1_ = stack[0].m_obj;
uint64_t v_res_5_;
v_res_5_ = l_Std_Sat_AIG_instHashableFanin_hash(v_x_1_);
stack->m_num = v_res_5_;
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableFanin_hash___boxed(lean_object* v_x_6_){
_start:
{
uint64_t v_res_7_; lean_object* v_r_8_; 
v_res_7_ = l_Std_Sat_AIG_instHashableFanin_hash(v_x_6_);
lean_dec(v_x_6_);
v_r_8_ = lean_box_uint64(v_res_7_);
return v_r_8_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Sat_AIG_instReprFanin_repr_spec__0(lean_object* v_a_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_nat_to_int(v_a_11_);
return v___x_12_;
}
}
static lean_object* _init_l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = lean_unsigned_to_nat(7u);
v___x_27_ = lean_nat_to_int(v___x_26_);
return v___x_27_;
}
}
static lean_object* _init_l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_29_ = ((lean_object*)(l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__0));
v___x_30_ = lean_string_length(v___x_29_);
return v___x_30_;
}
}
static lean_object* _init_l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_31_ = lean_obj_once(&l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__9, &l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__9_once, _init_l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__9);
v___x_32_ = lean_nat_to_int(v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprFanin_repr___redArg(lean_object* v_x_37_){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; uint8_t v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_38_ = ((lean_object*)(l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__6));
v___x_39_ = lean_obj_once(&l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__7, &l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__7_once, _init_l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__7);
v___x_40_ = l_Nat_reprFast(v_x_37_);
v___x_41_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_41_, 0, v___x_40_);
v___x_42_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_42_, 0, v___x_39_);
lean_ctor_set(v___x_42_, 1, v___x_41_);
v___x_43_ = 0;
v___x_44_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_44_, 0, v___x_42_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*1, v___x_43_);
v___x_45_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_45_, 0, v___x_38_);
lean_ctor_set(v___x_45_, 1, v___x_44_);
v___x_46_ = lean_obj_once(&l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__10, &l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__10_once, _init_l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__10);
v___x_47_ = ((lean_object*)(l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__11));
v___x_48_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
lean_ctor_set(v___x_48_, 1, v___x_45_);
v___x_49_ = ((lean_object*)(l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__12));
v___x_50_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_50_, 0, v___x_48_);
lean_ctor_set(v___x_50_, 1, v___x_49_);
v___x_51_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_51_, 0, v___x_46_);
lean_ctor_set(v___x_51_, 1, v___x_50_);
v___x_52_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_52_, 0, v___x_51_);
lean_ctor_set_uint8(v___x_52_, sizeof(void*)*1, v___x_43_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprFanin_repr(lean_object* v_x_53_, lean_object* v_prec_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Std_Sat_AIG_instReprFanin_repr___redArg(v_x_53_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprFanin_repr___boxed(lean_object* v_x_56_, lean_object* v_prec_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Std_Sat_AIG_instReprFanin_repr(v_x_56_, v_prec_57_);
lean_dec(v_prec_57_);
return v_res_58_;
}
}
uint8_t l_Std_Sat_AIG_instDecidableEqFanin_decEq(lean_object* v_x_61_, lean_object* v_x_62_){
_start:
{
uint8_t v___x_63_; 
v___x_63_ = lean_nat_dec_eq(v_x_61_, v_x_62_);
return v___x_63_;
}
}
LEAN_EXPORT void l_Std_Sat_AIG_instDecidableEqFanin_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_61_ = stack[0].m_obj;
lean_object* v_x_62_ = stack[1].m_obj;
uint8_t v_res_64_;
v_res_64_ = l_Std_Sat_AIG_instDecidableEqFanin_decEq(v_x_61_, v_x_62_);
stack->m_num = v_res_64_;
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instDecidableEqFanin_decEq___boxed(lean_object* v_x_65_, lean_object* v_x_66_){
_start:
{
uint8_t v_res_67_; lean_object* v_r_68_; 
v_res_67_ = l_Std_Sat_AIG_instDecidableEqFanin_decEq(v_x_65_, v_x_66_);
lean_dec(v_x_66_);
lean_dec(v_x_65_);
v_r_68_ = lean_box(v_res_67_);
return v_r_68_;
}
}
uint8_t l_Std_Sat_AIG_instDecidableEqFanin(lean_object* v_x_69_, lean_object* v_x_70_){
_start:
{
uint8_t v___x_71_; 
v___x_71_ = lean_nat_dec_eq(v_x_69_, v_x_70_);
return v___x_71_;
}
}
LEAN_EXPORT void l_Std_Sat_AIG_instDecidableEqFanin_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_69_ = stack[0].m_obj;
lean_object* v_x_70_ = stack[1].m_obj;
uint8_t v_res_72_;
v_res_72_ = l_Std_Sat_AIG_instDecidableEqFanin(v_x_69_, v_x_70_);
stack->m_num = v_res_72_;
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instDecidableEqFanin___boxed(lean_object* v_x_73_, lean_object* v_x_74_){
_start:
{
uint8_t v_res_75_; lean_object* v_r_76_; 
v_res_75_ = l_Std_Sat_AIG_instDecidableEqFanin(v_x_73_, v_x_74_);
lean_dec(v_x_74_);
lean_dec(v_x_73_);
v_r_76_ = lean_box(v_res_75_);
return v_r_76_;
}
}
static lean_object* _init_l_Std_Sat_AIG_instInhabitedFanin_default(void){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_unsigned_to_nat(0u);
return v___x_77_;
}
}
static lean_object* _init_l_Std_Sat_AIG_instInhabitedFanin(void){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = lean_unsigned_to_nat(0u);
return v___x_78_;
}
}
lean_object* l_Std_Sat_AIG_Fanin_mk(lean_object* v_gate_79_, uint8_t v_invert_80_){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_81_ = lean_unsigned_to_nat(2u);
v___x_82_ = lean_nat_mul(v_gate_79_, v___x_81_);
v___x_83_ = l_Bool_toNat(v_invert_80_);
v___x_84_ = lean_nat_lor(v___x_82_, v___x_83_);
lean_dec(v___x_83_);
lean_dec(v___x_82_);
return v___x_84_;
}
}
LEAN_EXPORT void l_Std_Sat_AIG_Fanin_mk_0interp(lean_interpreter_value* stack)
{
lean_object* v_gate_79_ = stack[0].m_obj;
uint8_t v_invert_80_ = stack[1].m_num;
lean_object* v_res_85_;
v_res_85_ = l_Std_Sat_AIG_Fanin_mk(v_gate_79_, v_invert_80_);
stack->m_obj
 = v_res_85_;
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Fanin_mk___boxed(lean_object* v_gate_86_, lean_object* v_invert_87_){
_start:
{
uint8_t v_invert_boxed_88_; lean_object* v_res_89_; 
v_invert_boxed_88_ = lean_unbox(v_invert_87_);
v_res_89_ = l_Std_Sat_AIG_Fanin_mk(v_gate_86_, v_invert_boxed_88_);
lean_dec(v_gate_86_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Fanin_gate(lean_object* v_f_90_){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = lean_unsigned_to_nat(1u);
v___x_92_ = lean_nat_shiftr(v_f_90_, v___x_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Fanin_gate___boxed(lean_object* v_f_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Std_Sat_AIG_Fanin_gate(v_f_93_);
lean_dec(v_f_93_);
return v_res_94_;
}
}
uint8_t l_Std_Sat_AIG_Fanin_invert(lean_object* v_f_95_){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_96_ = lean_unsigned_to_nat(1u);
v___x_97_ = lean_nat_land(v___x_96_, v_f_95_);
v___x_98_ = lean_unsigned_to_nat(0u);
v___x_99_ = lean_nat_dec_eq(v___x_97_, v___x_98_);
lean_dec(v___x_97_);
if (v___x_99_ == 0)
{
uint8_t v___x_100_; 
v___x_100_ = 1;
return v___x_100_;
}
else
{
uint8_t v___x_101_; 
v___x_101_ = 0;
return v___x_101_;
}
}
}
LEAN_EXPORT void l_Std_Sat_AIG_Fanin_invert_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_95_ = stack[0].m_obj;
uint8_t v_res_102_;
v_res_102_ = l_Std_Sat_AIG_Fanin_invert(v_f_95_);
stack->m_num = v_res_102_;
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Fanin_invert___boxed(lean_object* v_f_103_){
_start:
{
uint8_t v_res_104_; lean_object* v_r_105_; 
v_res_104_ = l_Std_Sat_AIG_Fanin_invert(v_f_103_);
lean_dec(v_f_103_);
v_r_105_ = lean_box(v_res_104_);
return v_r_105_;
}
}
lean_object* l_Std_Sat_AIG_Fanin_flip(lean_object* v_f_106_, uint8_t v_val_107_){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = l_Bool_toNat(v_val_107_);
v___x_109_ = lean_nat_lxor(v_f_106_, v___x_108_);
lean_dec(v___x_108_);
return v___x_109_;
}
}
LEAN_EXPORT void l_Std_Sat_AIG_Fanin_flip_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_106_ = stack[0].m_obj;
uint8_t v_val_107_ = stack[1].m_num;
lean_object* v_res_110_;
v_res_110_ = l_Std_Sat_AIG_Fanin_flip(v_f_106_, v_val_107_);
stack->m_obj
 = v_res_110_;
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Fanin_flip___boxed(lean_object* v_f_111_, lean_object* v_val_112_){
_start:
{
uint8_t v_val_boxed_113_; lean_object* v_res_114_; 
v_val_boxed_113_ = lean_unbox(v_val_112_);
v_res_114_ = l_Std_Sat_AIG_Fanin_flip(v_f_111_, v_val_boxed_113_);
lean_dec(v_f_111_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_ctorIdx___impl___redArg(lean_object* v_x_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = lean_obj_tag_nat(v_x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_ctorIdx___impl___redArg___boxed(lean_object* v_x_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Std_Sat_AIG_Decl_ctorIdx___impl___redArg(v_x_117_);
lean_dec(v_x_117_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_ctorIdx___impl(lean_object* v_00_u03b1_119_, lean_object* v_x_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = lean_obj_tag_nat(v_x_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_ctorIdx___impl___boxed(lean_object* v_00_u03b1_122_, lean_object* v_x_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Std_Sat_AIG_Decl_ctorIdx___impl(v_00_u03b1_122_, v_x_123_);
lean_dec(v_x_123_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_ctorElim___redArg(lean_object* v_t_125_, lean_object* v_k_126_){
_start:
{
switch(lean_obj_tag(v_t_125_))
{
case 0:
{
return v_k_126_;
}
case 1:
{
lean_object* v_idx_127_; lean_object* v___x_128_; 
v_idx_127_ = lean_ctor_get(v_t_125_, 0);
lean_inc(v_idx_127_);
lean_dec_ref_known(v_t_125_, 1);
v___x_128_ = lean_apply_1(v_k_126_, v_idx_127_);
return v___x_128_;
}
default: 
{
lean_object* v_l_129_; lean_object* v_r_130_; lean_object* v___x_131_; 
v_l_129_ = lean_ctor_get(v_t_125_, 0);
lean_inc(v_l_129_);
v_r_130_ = lean_ctor_get(v_t_125_, 1);
lean_inc(v_r_130_);
lean_dec_ref_known(v_t_125_, 2);
v___x_131_ = lean_apply_2(v_k_126_, v_l_129_, v_r_130_);
return v___x_131_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_ctorElim(lean_object* v_00_u03b1_132_, lean_object* v_motive_133_, lean_object* v_ctorIdx_134_, lean_object* v_t_135_, lean_object* v_h_136_, lean_object* v_k_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_Std_Sat_AIG_Decl_ctorElim___redArg(v_t_135_, v_k_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_ctorElim___boxed(lean_object* v_00_u03b1_139_, lean_object* v_motive_140_, lean_object* v_ctorIdx_141_, lean_object* v_t_142_, lean_object* v_h_143_, lean_object* v_k_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Std_Sat_AIG_Decl_ctorElim(v_00_u03b1_139_, v_motive_140_, v_ctorIdx_141_, v_t_142_, v_h_143_, v_k_144_);
lean_dec(v_ctorIdx_141_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_false_elim___redArg(lean_object* v_t_146_, lean_object* v_false_147_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Std_Sat_AIG_Decl_ctorElim___redArg(v_t_146_, v_false_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_false_elim(lean_object* v_00_u03b1_149_, lean_object* v_motive_150_, lean_object* v_t_151_, lean_object* v_h_152_, lean_object* v_false_153_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_Std_Sat_AIG_Decl_ctorElim___redArg(v_t_151_, v_false_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_atom_elim___redArg(lean_object* v_t_155_, lean_object* v_atom_156_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l_Std_Sat_AIG_Decl_ctorElim___redArg(v_t_155_, v_atom_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_atom_elim(lean_object* v_00_u03b1_158_, lean_object* v_motive_159_, lean_object* v_t_160_, lean_object* v_h_161_, lean_object* v_atom_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l_Std_Sat_AIG_Decl_ctorElim___redArg(v_t_160_, v_atom_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_gate_elim___redArg(lean_object* v_t_164_, lean_object* v_gate_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = l_Std_Sat_AIG_Decl_ctorElim___redArg(v_t_164_, v_gate_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_gate_elim(lean_object* v_00_u03b1_167_, lean_object* v_motive_168_, lean_object* v_t_169_, lean_object* v_h_170_, lean_object* v_gate_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Std_Sat_AIG_Decl_ctorElim___redArg(v_t_169_, v_gate_171_);
return v___x_172_;
}
}
uint64_t l_Std_Sat_AIG_instHashableDecl_hash___redArg(lean_object* v_inst_173_, lean_object* v_x_174_){
_start:
{
switch(lean_obj_tag(v_x_174_))
{
case 0:
{
uint64_t v___x_175_; 
lean_dec_ref(v_inst_173_);
v___x_175_ = 0ULL;
return v___x_175_;
}
case 1:
{
lean_object* v_idx_176_; uint64_t v___x_177_; lean_object* v___x_178_; uint64_t v___x_179_; uint64_t v___x_180_; 
v_idx_176_ = lean_ctor_get(v_x_174_, 0);
lean_inc(v_idx_176_);
lean_dec_ref_known(v_x_174_, 1);
v___x_177_ = 1ULL;
v___x_178_ = lean_apply_1(v_inst_173_, v_idx_176_);
v___x_179_ = lean_unbox_uint64(v___x_178_);
lean_dec_ref(v___x_178_);
v___x_180_ = lean_uint64_mix_hash(v___x_177_, v___x_179_);
return v___x_180_;
}
default: 
{
lean_object* v_l_181_; lean_object* v_r_182_; uint64_t v___x_183_; uint64_t v___x_184_; uint64_t v___x_185_; uint64_t v___x_186_; uint64_t v___x_187_; 
lean_dec_ref(v_inst_173_);
v_l_181_ = lean_ctor_get(v_x_174_, 0);
lean_inc(v_l_181_);
v_r_182_ = lean_ctor_get(v_x_174_, 1);
lean_inc(v_r_182_);
lean_dec_ref_known(v_x_174_, 2);
v___x_183_ = 2ULL;
v___x_184_ = l_Std_Sat_AIG_instHashableFanin_hash(v_l_181_);
lean_dec(v_l_181_);
v___x_185_ = lean_uint64_mix_hash(v___x_183_, v___x_184_);
v___x_186_ = l_Std_Sat_AIG_instHashableFanin_hash(v_r_182_);
lean_dec(v_r_182_);
v___x_187_ = lean_uint64_mix_hash(v___x_185_, v___x_186_);
return v___x_187_;
}
}
}
}
LEAN_EXPORT void l_Std_Sat_AIG_instHashableDecl_hash___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_173_ = stack[0].m_obj;
lean_object* v_x_174_ = stack[1].m_obj;
uint64_t v_res_188_;
v_res_188_ = l_Std_Sat_AIG_instHashableDecl_hash___redArg(v_inst_173_, v_x_174_);
stack->m_num = v_res_188_;
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableDecl_hash___redArg___boxed(lean_object* v_inst_189_, lean_object* v_x_190_){
_start:
{
uint64_t v_res_191_; lean_object* v_r_192_; 
v_res_191_ = l_Std_Sat_AIG_instHashableDecl_hash___redArg(v_inst_189_, v_x_190_);
v_r_192_ = lean_box_uint64(v_res_191_);
return v_r_192_;
}
}
uint64_t l_Std_Sat_AIG_instHashableDecl_hash(lean_object* v_00_u03b1_193_, lean_object* v_inst_194_, lean_object* v_x_195_){
_start:
{
uint64_t v___x_196_; 
v___x_196_ = l_Std_Sat_AIG_instHashableDecl_hash___redArg(v_inst_194_, v_x_195_);
return v___x_196_;
}
}
LEAN_EXPORT void l_Std_Sat_AIG_instHashableDecl_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_194_ = stack[1].m_obj;
lean_object* v_x_195_ = stack[2].m_obj;
uint64_t v_res_197_;
v_res_197_ = l_Std_Sat_AIG_instHashableDecl_hash(lean_box(0), v_inst_194_, v_x_195_);
stack->m_num = v_res_197_;
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableDecl_hash___boxed(lean_object* v_00_u03b1_198_, lean_object* v_inst_199_, lean_object* v_x_200_){
_start:
{
uint64_t v_res_201_; lean_object* v_r_202_; 
v_res_201_ = l_Std_Sat_AIG_instHashableDecl_hash(v_00_u03b1_198_, v_inst_199_, v_x_200_);
v_r_202_ = lean_box_uint64(v_res_201_);
return v_r_202_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableDecl___redArg(lean_object* v_inst_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_204_, 0, lean_box(0));
lean_closure_set(v___x_204_, 1, v_inst_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableDecl(lean_object* v_00_u03b1_205_, lean_object* v_inst_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_207_, 0, lean_box(0));
lean_closure_set(v___x_207_, 1, v_inst_206_);
return v___x_207_;
}
}
static lean_object* _init_l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = lean_unsigned_to_nat(2u);
v___x_212_ = lean_nat_to_int(v___x_211_);
return v___x_212_;
}
}
static lean_object* _init_l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = lean_unsigned_to_nat(1u);
v___x_214_ = lean_nat_to_int(v___x_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprDecl_repr___redArg(lean_object* v_inst_227_, lean_object* v_x_228_, lean_object* v_prec_229_){
_start:
{
lean_object* v___y_231_; 
switch(lean_obj_tag(v_x_228_))
{
case 0:
{
lean_object* v___x_237_; uint8_t v___x_238_; 
lean_dec_ref(v_inst_227_);
v___x_237_ = lean_unsigned_to_nat(1024u);
v___x_238_ = lean_nat_dec_le(v___x_237_, v_prec_229_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; 
v___x_239_ = lean_obj_once(&l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2, &l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2_once, _init_l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2);
v___y_231_ = v___x_239_;
goto v___jp_230_;
}
else
{
lean_object* v___x_240_; 
v___x_240_ = lean_obj_once(&l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3, &l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3_once, _init_l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3);
v___y_231_ = v___x_240_;
goto v___jp_230_;
}
}
case 1:
{
lean_object* v_idx_241_; lean_object* v___y_243_; lean_object* v___x_252_; uint8_t v___x_253_; 
v_idx_241_ = lean_ctor_get(v_x_228_, 0);
lean_inc(v_idx_241_);
lean_dec_ref_known(v_x_228_, 1);
v___x_252_ = lean_unsigned_to_nat(1024u);
v___x_253_ = lean_nat_dec_le(v___x_252_, v_prec_229_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; 
v___x_254_ = lean_obj_once(&l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2, &l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2_once, _init_l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2);
v___y_243_ = v___x_254_;
goto v___jp_242_;
}
else
{
lean_object* v___x_255_; 
v___x_255_ = lean_obj_once(&l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3, &l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3_once, _init_l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3);
v___y_243_ = v___x_255_;
goto v___jp_242_;
}
v___jp_242_:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; uint8_t v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_244_ = ((lean_object*)(l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__6));
v___x_245_ = lean_unsigned_to_nat(1024u);
v___x_246_ = lean_apply_2(v_inst_227_, v_idx_241_, v___x_245_);
v___x_247_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_244_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
lean_inc(v___y_243_);
v___x_248_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_248_, 0, v___y_243_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
v___x_249_ = 0;
v___x_250_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_250_, 0, v___x_248_);
lean_ctor_set_uint8(v___x_250_, sizeof(void*)*1, v___x_249_);
v___x_251_ = l_Repr_addAppParen(v___x_250_, v_prec_229_);
return v___x_251_;
}
}
default: 
{
lean_object* v_l_256_; lean_object* v_r_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_280_; 
lean_dec_ref(v_inst_227_);
v_l_256_ = lean_ctor_get(v_x_228_, 0);
v_r_257_ = lean_ctor_get(v_x_228_, 1);
v_isSharedCheck_280_ = !lean_is_exclusive(v_x_228_);
if (v_isSharedCheck_280_ == 0)
{
v___x_259_ = v_x_228_;
v_isShared_260_ = v_isSharedCheck_280_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_r_257_);
lean_inc(v_l_256_);
lean_dec(v_x_228_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_280_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___y_262_; lean_object* v___x_276_; uint8_t v___x_277_; 
v___x_276_ = lean_unsigned_to_nat(1024u);
v___x_277_ = lean_nat_dec_le(v___x_276_, v_prec_229_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; 
v___x_278_ = lean_obj_once(&l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2, &l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2_once, _init_l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2);
v___y_262_ = v___x_278_;
goto v___jp_261_;
}
else
{
lean_object* v___x_279_; 
v___x_279_ = lean_obj_once(&l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3, &l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3_once, _init_l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3);
v___y_262_ = v___x_279_;
goto v___jp_261_;
}
v___jp_261_:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_267_; 
v___x_263_ = lean_box(1);
v___x_264_ = ((lean_object*)(l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__9));
v___x_265_ = l_Std_Sat_AIG_instReprFanin_repr___redArg(v_l_256_);
if (v_isShared_260_ == 0)
{
lean_ctor_set_tag(v___x_259_, 5);
lean_ctor_set(v___x_259_, 1, v___x_265_);
lean_ctor_set(v___x_259_, 0, v___x_264_);
v___x_267_ = v___x_259_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v___x_264_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v___x_265_);
v___x_267_ = v_reuseFailAlloc_275_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_268_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
lean_ctor_set(v___x_268_, 1, v___x_263_);
v___x_269_ = l_Std_Sat_AIG_instReprFanin_repr___redArg(v_r_257_);
v___x_270_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_268_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
lean_inc(v___y_262_);
v___x_271_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_271_, 0, v___y_262_);
lean_ctor_set(v___x_271_, 1, v___x_270_);
v___x_272_ = 0;
v___x_273_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_273_, 0, v___x_271_);
lean_ctor_set_uint8(v___x_273_, sizeof(void*)*1, v___x_272_);
v___x_274_ = l_Repr_addAppParen(v___x_273_, v_prec_229_);
return v___x_274_;
}
}
}
}
}
v___jp_230_:
{
lean_object* v___x_232_; lean_object* v___x_233_; uint8_t v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_232_ = ((lean_object*)(l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__1));
lean_inc(v___y_231_);
v___x_233_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_233_, 0, v___y_231_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
v___x_234_ = 0;
v___x_235_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_235_, 0, v___x_233_);
lean_ctor_set_uint8(v___x_235_, sizeof(void*)*1, v___x_234_);
v___x_236_ = l_Repr_addAppParen(v___x_235_, v_prec_229_);
return v___x_236_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprDecl_repr___redArg___boxed(lean_object* v_inst_281_, lean_object* v_x_282_, lean_object* v_prec_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Std_Sat_AIG_instReprDecl_repr___redArg(v_inst_281_, v_x_282_, v_prec_283_);
lean_dec(v_prec_283_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprDecl_repr(lean_object* v_00_u03b1_285_, lean_object* v_inst_286_, lean_object* v_x_287_, lean_object* v_prec_288_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = l_Std_Sat_AIG_instReprDecl_repr___redArg(v_inst_286_, v_x_287_, v_prec_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprDecl_repr___boxed(lean_object* v_00_u03b1_290_, lean_object* v_inst_291_, lean_object* v_x_292_, lean_object* v_prec_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Std_Sat_AIG_instReprDecl_repr(v_00_u03b1_290_, v_inst_291_, v_x_292_, v_prec_293_);
lean_dec(v_prec_293_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprDecl___redArg(lean_object* v_inst_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instReprDecl_repr___boxed), 4, 2);
lean_closure_set(v___x_296_, 0, lean_box(0));
lean_closure_set(v___x_296_, 1, v_inst_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprDecl(lean_object* v_00_u03b1_297_, lean_object* v_inst_298_){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instReprDecl_repr___boxed), 4, 2);
lean_closure_set(v___x_299_, 0, lean_box(0));
lean_closure_set(v___x_299_, 1, v_inst_298_);
return v___x_299_;
}
}
uint8_t l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(lean_object* v_inst_300_, lean_object* v_x_301_, lean_object* v_x_302_){
_start:
{
switch(lean_obj_tag(v_x_301_))
{
case 0:
{
lean_dec_ref(v_inst_300_);
if (lean_obj_tag(v_x_302_) == 0)
{
uint8_t v___x_303_; 
v___x_303_ = 1;
return v___x_303_;
}
else
{
uint8_t v___x_304_; 
lean_dec(v_x_302_);
v___x_304_ = 0;
return v___x_304_;
}
}
case 1:
{
if (lean_obj_tag(v_x_302_) == 1)
{
lean_object* v_idx_305_; lean_object* v_idx_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v_idx_305_ = lean_ctor_get(v_x_301_, 0);
lean_inc(v_idx_305_);
lean_dec_ref_known(v_x_301_, 1);
v_idx_306_ = lean_ctor_get(v_x_302_, 0);
lean_inc(v_idx_306_);
lean_dec_ref_known(v_x_302_, 1);
v___x_307_ = lean_apply_2(v_inst_300_, v_idx_305_, v_idx_306_);
v___x_308_ = lean_unbox(v___x_307_);
return v___x_308_;
}
else
{
uint8_t v___x_309_; 
lean_dec_ref_known(v_x_301_, 1);
lean_dec(v_x_302_);
lean_dec_ref(v_inst_300_);
v___x_309_ = 0;
return v___x_309_;
}
}
default: 
{
lean_dec_ref(v_inst_300_);
if (lean_obj_tag(v_x_302_) == 2)
{
lean_object* v_l_310_; lean_object* v_r_311_; lean_object* v_l_312_; lean_object* v_r_313_; uint8_t v___x_314_; 
v_l_310_ = lean_ctor_get(v_x_301_, 0);
lean_inc(v_l_310_);
v_r_311_ = lean_ctor_get(v_x_301_, 1);
lean_inc(v_r_311_);
lean_dec_ref_known(v_x_301_, 2);
v_l_312_ = lean_ctor_get(v_x_302_, 0);
lean_inc(v_l_312_);
v_r_313_ = lean_ctor_get(v_x_302_, 1);
lean_inc(v_r_313_);
lean_dec_ref_known(v_x_302_, 2);
v___x_314_ = lean_nat_dec_eq(v_l_310_, v_l_312_);
lean_dec(v_l_312_);
lean_dec(v_l_310_);
if (v___x_314_ == 0)
{
lean_dec(v_r_313_);
lean_dec(v_r_311_);
return v___x_314_;
}
else
{
uint8_t v___x_315_; 
v___x_315_ = lean_nat_dec_eq(v_r_311_, v_r_313_);
lean_dec(v_r_313_);
lean_dec(v_r_311_);
return v___x_315_;
}
}
else
{
uint8_t v___x_316_; 
lean_dec_ref_known(v_x_301_, 2);
lean_dec(v_x_302_);
v___x_316_ = 0;
return v___x_316_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_300_ = stack[0].m_obj;
lean_object* v_x_301_ = stack[1].m_obj;
lean_object* v_x_302_ = stack[2].m_obj;
uint8_t v_res_317_;
v_res_317_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v_inst_300_, v_x_301_, v_x_302_);
stack->m_num = v_res_317_;
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg___boxed(lean_object* v_inst_318_, lean_object* v_x_319_, lean_object* v_x_320_){
_start:
{
uint8_t v_res_321_; lean_object* v_r_322_; 
v_res_321_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v_inst_318_, v_x_319_, v_x_320_);
v_r_322_ = lean_box(v_res_321_);
return v_r_322_;
}
}
uint8_t l_Std_Sat_AIG_instDecidableEqDecl_decEq(lean_object* v_00_u03b1_323_, lean_object* v_inst_324_, lean_object* v_x_325_, lean_object* v_x_326_){
_start:
{
uint8_t v___x_327_; 
v___x_327_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v_inst_324_, v_x_325_, v_x_326_);
return v___x_327_;
}
}
LEAN_EXPORT void l_Std_Sat_AIG_instDecidableEqDecl_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_324_ = stack[1].m_obj;
lean_object* v_x_325_ = stack[2].m_obj;
lean_object* v_x_326_ = stack[3].m_obj;
uint8_t v_res_328_;
v_res_328_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq(lean_box(0), v_inst_324_, v_x_325_, v_x_326_);
stack->m_num = v_res_328_;
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instDecidableEqDecl_decEq___boxed(lean_object* v_00_u03b1_329_, lean_object* v_inst_330_, lean_object* v_x_331_, lean_object* v_x_332_){
_start:
{
uint8_t v_res_333_; lean_object* v_r_334_; 
v_res_333_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq(v_00_u03b1_329_, v_inst_330_, v_x_331_, v_x_332_);
v_r_334_ = lean_box(v_res_333_);
return v_r_334_;
}
}
uint8_t l_Std_Sat_AIG_instDecidableEqDecl___redArg(lean_object* v_inst_335_, lean_object* v_x_336_, lean_object* v_x_337_){
_start:
{
uint8_t v___x_338_; 
v___x_338_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v_inst_335_, v_x_336_, v_x_337_);
return v___x_338_;
}
}
LEAN_EXPORT void l_Std_Sat_AIG_instDecidableEqDecl___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_335_ = stack[0].m_obj;
lean_object* v_x_336_ = stack[1].m_obj;
lean_object* v_x_337_ = stack[2].m_obj;
uint8_t v_res_339_;
v_res_339_ = l_Std_Sat_AIG_instDecidableEqDecl___redArg(v_inst_335_, v_x_336_, v_x_337_);
stack->m_num = v_res_339_;
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instDecidableEqDecl___redArg___boxed(lean_object* v_inst_340_, lean_object* v_x_341_, lean_object* v_x_342_){
_start:
{
uint8_t v_res_343_; lean_object* v_r_344_; 
v_res_343_ = l_Std_Sat_AIG_instDecidableEqDecl___redArg(v_inst_340_, v_x_341_, v_x_342_);
v_r_344_ = lean_box(v_res_343_);
return v_r_344_;
}
}
uint8_t l_Std_Sat_AIG_instDecidableEqDecl(lean_object* v_00_u03b1_345_, lean_object* v_inst_346_, lean_object* v_x_347_, lean_object* v_x_348_){
_start:
{
uint8_t v___x_349_; 
v___x_349_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v_inst_346_, v_x_347_, v_x_348_);
return v___x_349_;
}
}
LEAN_EXPORT void l_Std_Sat_AIG_instDecidableEqDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_346_ = stack[1].m_obj;
lean_object* v_x_347_ = stack[2].m_obj;
lean_object* v_x_348_ = stack[3].m_obj;
uint8_t v_res_350_;
v_res_350_ = l_Std_Sat_AIG_instDecidableEqDecl(lean_box(0), v_inst_346_, v_x_347_, v_x_348_);
stack->m_num = v_res_350_;
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instDecidableEqDecl___boxed(lean_object* v_00_u03b1_351_, lean_object* v_inst_352_, lean_object* v_x_353_, lean_object* v_x_354_){
_start:
{
uint8_t v_res_355_; lean_object* v_r_356_; 
v_res_355_ = l_Std_Sat_AIG_instDecidableEqDecl(v_00_u03b1_351_, v_inst_352_, v_x_353_, v_x_354_);
v_r_356_ = lean_box(v_res_355_);
return v_r_356_;
}
}
lean_object* l_Std_Sat_AIG_instInhabitedDecl_default___redArg(){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = lean_box(0);
return v___x_358_;
}
}
LEAN_EXPORT void l_Std_Sat_AIG_instInhabitedDecl_default___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_359_;
v_res_359_ = l_Std_Sat_AIG_instInhabitedDecl_default___redArg();
stack->m_obj
 = v_res_359_;
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instInhabitedDecl_default___redArg___boxed(lean_object* v___dummy_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Std_Sat_AIG_instInhabitedDecl_default___redArg();
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instInhabitedDecl_default(lean_object* v_00_u03b1_362_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = lean_box(0);
return v___x_363_;
}
}
lean_object* l_Std_Sat_AIG_instInhabitedDecl___redArg(){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = lean_box(0);
return v___x_365_;
}
}
LEAN_EXPORT void l_Std_Sat_AIG_instInhabitedDecl___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_366_;
v_res_366_ = l_Std_Sat_AIG_instInhabitedDecl___redArg();
stack->m_obj
 = v_res_366_;
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instInhabitedDecl___redArg___boxed(lean_object* v___dummy_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Std_Sat_AIG_instInhabitedDecl___redArg();
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instInhabitedDecl(lean_object* v_a_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = lean_box(0);
return v___x_370_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__12(void){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__10));
v___x_398_ = l_Lean_mkAtom(v___x_397_);
return v___x_398_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__13(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_399_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__12, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__12_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__12);
v___x_400_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__5));
v___x_401_ = lean_array_push(v___x_400_, v___x_399_);
return v___x_401_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__17(void){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_412_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__16));
v___x_413_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__5));
v___x_414_ = lean_array_push(v___x_413_, v___x_412_);
return v___x_414_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__18(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_415_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__17, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__17_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__17);
v___x_416_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__15));
v___x_417_ = lean_box(2);
v___x_418_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
lean_ctor_set(v___x_418_, 1, v___x_416_);
lean_ctor_set(v___x_418_, 2, v___x_415_);
return v___x_418_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__19(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_419_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__18, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__18_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__18);
v___x_420_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__13, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__13_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__13);
v___x_421_ = lean_array_push(v___x_420_, v___x_419_);
return v___x_421_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__20(void){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_422_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__16));
v___x_423_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__19, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__19_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__19);
v___x_424_ = lean_array_push(v___x_423_, v___x_422_);
return v___x_424_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__21(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_425_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__16));
v___x_426_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__20, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__20_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__20);
v___x_427_ = lean_array_push(v___x_426_, v___x_425_);
return v___x_427_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__22(void){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_428_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__16));
v___x_429_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__21, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__21_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__21);
v___x_430_ = lean_array_push(v___x_429_, v___x_428_);
return v___x_430_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__23(void){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_431_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__16));
v___x_432_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__22, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__22_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__22);
v___x_433_ = lean_array_push(v___x_432_, v___x_431_);
return v___x_433_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__24(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_434_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__23, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__23_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__23);
v___x_435_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__11));
v___x_436_ = lean_box(2);
v___x_437_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
lean_ctor_set(v___x_437_, 1, v___x_435_);
lean_ctor_set(v___x_437_, 2, v___x_434_);
return v___x_437_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__25(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_438_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__24, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__24_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__24);
v___x_439_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__5));
v___x_440_ = lean_array_push(v___x_439_, v___x_438_);
return v___x_440_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__26(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_441_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__25, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__25_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__25);
v___x_442_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__9));
v___x_443_ = lean_box(2);
v___x_444_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
lean_ctor_set(v___x_444_, 1, v___x_442_);
lean_ctor_set(v___x_444_, 2, v___x_441_);
return v___x_444_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__27(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_445_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__26, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__26_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__26);
v___x_446_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__5));
v___x_447_ = lean_array_push(v___x_446_, v___x_445_);
return v___x_447_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__28(void){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_448_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__27, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__27_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__27);
v___x_449_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__7));
v___x_450_ = lean_box(2);
v___x_451_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_451_, 0, v___x_450_);
lean_ctor_set(v___x_451_, 1, v___x_449_);
lean_ctor_set(v___x_451_, 2, v___x_448_);
return v___x_451_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__29(void){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_452_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__28, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__28_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__28);
v___x_453_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__5));
v___x_454_ = lean_array_push(v___x_453_, v___x_452_);
return v___x_454_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__30(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_455_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__29, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__29_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__29);
v___x_456_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__4));
v___x_457_ = lean_box(2);
v___x_458_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
lean_ctor_set(v___x_458_, 1, v___x_456_);
lean_ctor_set(v___x_458_, 2, v___x_455_);
return v___x_458_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1(void){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__30, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__30_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__30);
return v___x_459_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___redArg___closed__0(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_460_ = lean_box(0);
v___x_461_ = lean_unsigned_to_nat(16u);
v___x_462_ = lean_mk_array(v___x_461_, v___x_460_);
return v___x_462_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___redArg___closed__1(void){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_463_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___redArg___closed__0, &l_Std_Sat_AIG_Cache_empty___redArg___closed__0_once, _init_l_Std_Sat_AIG_Cache_empty___redArg___closed__0);
v___x_464_ = lean_unsigned_to_nat(0u);
v___x_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
lean_ctor_set(v___x_465_, 1, v___x_463_);
return v___x_465_;
}
}
lean_object* l_Std_Sat_AIG_Cache_empty___redArg(){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___redArg___closed__1, &l_Std_Sat_AIG_Cache_empty___redArg___closed__1_once, _init_l_Std_Sat_AIG_Cache_empty___redArg___closed__1);
return v___x_467_;
}
}
LEAN_EXPORT void l_Std_Sat_AIG_Cache_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_468_;
v_res_468_ = l_Std_Sat_AIG_Cache_empty___redArg();
stack->m_obj
 = v_res_468_;
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_empty___redArg___boxed(lean_object* v___dummy_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Std_Sat_AIG_Cache_empty___redArg();
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_empty(lean_object* v_00_u03b1_471_, lean_object* v_inst_472_, lean_object* v_inst_473_, lean_object* v_decls_474_, lean_object* v_hatoms_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___redArg___closed__1, &l_Std_Sat_AIG_Cache_empty___redArg___closed__1_once, _init_l_Std_Sat_AIG_Cache_empty___redArg___closed__1);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_empty___boxed(lean_object* v_00_u03b1_477_, lean_object* v_inst_478_, lean_object* v_inst_479_, lean_object* v_decls_480_, lean_object* v_hatoms_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Std_Sat_AIG_Cache_empty(v_00_u03b1_477_, v_inst_478_, v_inst_479_, v_decls_480_, v_hatoms_481_);
lean_dec_ref(v_decls_480_);
lean_dec_ref(v_inst_479_);
lean_dec_ref(v_inst_478_);
return v_res_482_;
}
}
uint8_t l_Std_Sat_AIG_Cache_insert___redArg___lam__0(lean_object* v_inst_483_, lean_object* v_a_484_, lean_object* v_b_485_){
_start:
{
uint8_t v___x_486_; 
v___x_486_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v_inst_483_, v_a_484_, v_b_485_);
return v___x_486_;
}
}
LEAN_EXPORT void l_Std_Sat_AIG_Cache_insert___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_483_ = stack[0].m_obj;
lean_object* v_a_484_ = stack[1].m_obj;
lean_object* v_b_485_ = stack[2].m_obj;
uint8_t v_res_487_;
v_res_487_ = l_Std_Sat_AIG_Cache_insert___redArg___lam__0(v_inst_483_, v_a_484_, v_b_485_);
stack->m_num = v_res_487_;
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed(lean_object* v_inst_488_, lean_object* v_a_489_, lean_object* v_b_490_){
_start:
{
uint8_t v_res_491_; lean_object* v_r_492_; 
v_res_491_ = l_Std_Sat_AIG_Cache_insert___redArg___lam__0(v_inst_488_, v_a_489_, v_b_490_);
v_r_492_ = lean_box(v_res_491_);
return v_r_492_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___redArg(lean_object* v_inst_493_, lean_object* v_inst_494_, lean_object* v_decls_495_, lean_object* v_cache_496_, lean_object* v_decl_497_){
_start:
{
lean_object* v___f_498_; lean_object* v___x_499_; lean_object* v___f_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___f_498_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_498_, 0, v_inst_494_);
v___x_499_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_499_, 0, lean_box(0));
lean_closure_set(v___x_499_, 1, v_inst_493_);
v___f_500_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_500_, 0, v___f_498_);
v___x_501_ = lean_array_get_size(v_decls_495_);
v___x_502_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_500_, v___x_499_, v_cache_496_, v_decl_497_, v___x_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___redArg___boxed(lean_object* v_inst_503_, lean_object* v_inst_504_, lean_object* v_decls_505_, lean_object* v_cache_506_, lean_object* v_decl_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Std_Sat_AIG_Cache_insert___redArg(v_inst_503_, v_inst_504_, v_decls_505_, v_cache_506_, v_decl_507_);
lean_dec_ref(v_decls_505_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert(lean_object* v_00_u03b1_509_, lean_object* v_inst_510_, lean_object* v_inst_511_, lean_object* v_decls_512_, lean_object* v_cache_513_, lean_object* v_decl_514_, lean_object* v_hmiss_515_){
_start:
{
lean_object* v___f_516_; lean_object* v___x_517_; lean_object* v___f_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___f_516_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_516_, 0, v_inst_511_);
v___x_517_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_517_, 0, lean_box(0));
lean_closure_set(v___x_517_, 1, v_inst_510_);
v___f_518_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_518_, 0, v___f_516_);
v___x_519_ = lean_array_get_size(v_decls_512_);
v___x_520_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_518_, v___x_517_, v_cache_513_, v_decl_514_, v___x_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___boxed(lean_object* v_00_u03b1_521_, lean_object* v_inst_522_, lean_object* v_inst_523_, lean_object* v_decls_524_, lean_object* v_cache_525_, lean_object* v_decl_526_, lean_object* v_hmiss_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Std_Sat_AIG_Cache_insert(v_00_u03b1_521_, v_inst_522_, v_inst_523_, v_decls_524_, v_cache_525_, v_decl_526_, v_hmiss_527_);
lean_dec_ref(v_decls_524_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f___redArg(lean_object* v_inst_529_, lean_object* v_inst_530_, lean_object* v_cache_531_, lean_object* v_decl_532_){
_start:
{
lean_object* v___f_533_; lean_object* v___x_534_; lean_object* v___f_535_; lean_object* v___x_536_; 
v___f_533_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_533_, 0, v_inst_530_);
v___x_534_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_534_, 0, lean_box(0));
lean_closure_set(v___x_534_, 1, v_inst_529_);
v___f_535_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_535_, 0, v___f_533_);
v___x_536_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_535_, v___x_534_, v_cache_531_, v_decl_532_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v___x_537_; 
v___x_537_ = lean_box(0);
return v___x_537_;
}
else
{
lean_object* v_val_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_545_; 
v_val_538_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_545_ == 0)
{
v___x_540_ = v___x_536_;
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_val_538_);
lean_dec(v___x_536_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_val_538_);
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
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f___redArg___boxed(lean_object* v_inst_546_, lean_object* v_inst_547_, lean_object* v_cache_548_, lean_object* v_decl_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Std_Sat_AIG_Cache_get_x3f___redArg(v_inst_546_, v_inst_547_, v_cache_548_, v_decl_549_);
lean_dec_ref(v_cache_548_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f(lean_object* v_00_u03b1_551_, lean_object* v_inst_552_, lean_object* v_inst_553_, lean_object* v_decls_554_, lean_object* v_cache_555_, lean_object* v_decl_556_){
_start:
{
lean_object* v___f_557_; lean_object* v___x_558_; lean_object* v___f_559_; lean_object* v___x_560_; 
v___f_557_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_557_, 0, v_inst_553_);
v___x_558_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_558_, 0, lean_box(0));
lean_closure_set(v___x_558_, 1, v_inst_552_);
v___f_559_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_559_, 0, v___f_557_);
v___x_560_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_559_, v___x_558_, v_cache_555_, v_decl_556_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v___x_561_; 
v___x_561_ = lean_box(0);
return v___x_561_;
}
else
{
lean_object* v_val_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_569_; 
v_val_562_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_569_ == 0)
{
v___x_564_ = v___x_560_;
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_val_562_);
lean_dec(v___x_560_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_567_; 
if (v_isShared_565_ == 0)
{
v___x_567_ = v___x_564_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_val_562_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f___boxed(lean_object* v_00_u03b1_570_, lean_object* v_inst_571_, lean_object* v_inst_572_, lean_object* v_decls_573_, lean_object* v_cache_574_, lean_object* v_decl_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Std_Sat_AIG_Cache_get_x3f(v_00_u03b1_570_, v_inst_571_, v_inst_572_, v_decls_573_, v_cache_574_, v_decl_575_);
lean_dec_ref(v_cache_574_);
lean_dec_ref(v_decls_573_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_Cache_get_x3f_match__1_splitter___redArg(lean_object* v_x_577_, lean_object* v_h__1_578_, lean_object* v_h__2_579_){
_start:
{
if (lean_obj_tag(v_x_577_) == 0)
{
lean_object* v___x_580_; 
lean_dec(v_h__1_578_);
v___x_580_ = lean_apply_1(v_h__2_579_, lean_box(0));
return v___x_580_;
}
else
{
lean_object* v_val_581_; lean_object* v___x_582_; 
lean_dec(v_h__2_579_);
v_val_581_ = lean_ctor_get(v_x_577_, 0);
lean_inc(v_val_581_);
lean_dec_ref_known(v_x_577_, 1);
v___x_582_ = lean_apply_2(v_h__1_578_, v_val_581_, lean_box(0));
return v___x_582_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_Cache_get_x3f_match__1_splitter(lean_object* v_motive_583_, lean_object* v_x_584_, lean_object* v_h__1_585_, lean_object* v_h__2_586_){
_start:
{
if (lean_obj_tag(v_x_584_) == 0)
{
lean_object* v___x_587_; 
lean_dec(v_h__1_585_);
v___x_587_ = lean_apply_1(v_h__2_586_, lean_box(0));
return v___x_587_;
}
else
{
lean_object* v_val_588_; lean_object* v___x_589_; 
lean_dec(v_h__2_586_);
v_val_588_ = lean_ctor_get(v_x_584_, 0);
lean_inc(v_val_588_);
lean_dec_ref_known(v_x_584_, 1);
v___x_589_ = lean_apply_2(v_h__1_585_, v_val_588_, lean_box(0));
return v___x_589_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_ofAtoms_go___redArg(lean_object* v_inst_590_, lean_object* v_inst_591_, lean_object* v_decls_592_, lean_object* v_idx_593_, lean_object* v_map_594_){
_start:
{
lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_595_ = lean_array_get_size(v_decls_592_);
v___x_596_ = lean_nat_dec_lt(v_idx_593_, v___x_595_);
if (v___x_596_ == 0)
{
lean_dec(v_idx_593_);
lean_dec_ref(v_inst_591_);
lean_dec_ref(v_inst_590_);
return v_map_594_;
}
else
{
lean_object* v___x_597_; 
v___x_597_ = lean_array_fget_borrowed(v_decls_592_, v_idx_593_);
if (lean_obj_tag(v___x_597_) == 1)
{
lean_object* v___f_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___f_602_; lean_object* v___x_603_; 
lean_inc_ref(v_inst_591_);
v___f_598_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_598_, 0, v_inst_591_);
lean_inc_ref(v_inst_590_);
v___x_599_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_599_, 0, lean_box(0));
lean_closure_set(v___x_599_, 1, v_inst_590_);
v___x_600_ = lean_unsigned_to_nat(1u);
v___x_601_ = lean_nat_add(v_idx_593_, v___x_600_);
v___f_602_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_602_, 0, v___f_598_);
lean_inc_ref(v___x_597_);
v___x_603_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_602_, v___x_599_, v_map_594_, v___x_597_, v_idx_593_);
v_idx_593_ = v___x_601_;
v_map_594_ = v___x_603_;
goto _start;
}
else
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = lean_unsigned_to_nat(1u);
v___x_606_ = lean_nat_add(v_idx_593_, v___x_605_);
lean_dec(v_idx_593_);
v_idx_593_ = v___x_606_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_ofAtoms_go___redArg___boxed(lean_object* v_inst_608_, lean_object* v_inst_609_, lean_object* v_decls_610_, lean_object* v_idx_611_, lean_object* v_map_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Std_Sat_AIG_Cache_ofAtoms_go___redArg(v_inst_608_, v_inst_609_, v_decls_610_, v_idx_611_, v_map_612_);
lean_dec_ref(v_decls_610_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_ofAtoms_go(lean_object* v_00_u03b1_614_, lean_object* v_inst_615_, lean_object* v_inst_616_, lean_object* v_decls_617_, lean_object* v_huniq_618_, lean_object* v_idx_619_, lean_object* v_map_620_, lean_object* v_hsound_621_, lean_object* v_hcomp_622_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Std_Sat_AIG_Cache_ofAtoms_go___redArg(v_inst_615_, v_inst_616_, v_decls_617_, v_idx_619_, v_map_620_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_ofAtoms_go___boxed(lean_object* v_00_u03b1_624_, lean_object* v_inst_625_, lean_object* v_inst_626_, lean_object* v_decls_627_, lean_object* v_huniq_628_, lean_object* v_idx_629_, lean_object* v_map_630_, lean_object* v_hsound_631_, lean_object* v_hcomp_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Std_Sat_AIG_Cache_ofAtoms_go(v_00_u03b1_624_, v_inst_625_, v_inst_626_, v_decls_627_, v_huniq_628_, v_idx_629_, v_map_630_, v_hsound_631_, v_hcomp_632_);
lean_dec_ref(v_decls_627_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_Cache_ofAtoms_go_match__1_splitter___redArg(lean_object* v_x_634_, lean_object* v_h__1_635_, lean_object* v_h__2_636_, lean_object* v_h__3_637_){
_start:
{
switch(lean_obj_tag(v_x_634_))
{
case 0:
{
lean_object* v___x_638_; 
lean_dec(v_h__3_637_);
lean_dec(v_h__1_635_);
v___x_638_ = lean_apply_1(v_h__2_636_, lean_box(0));
return v___x_638_;
}
case 1:
{
lean_object* v_idx_639_; lean_object* v___x_640_; 
lean_dec(v_h__3_637_);
lean_dec(v_h__2_636_);
v_idx_639_ = lean_ctor_get(v_x_634_, 0);
lean_inc(v_idx_639_);
lean_dec_ref_known(v_x_634_, 1);
v___x_640_ = lean_apply_2(v_h__1_635_, v_idx_639_, lean_box(0));
return v___x_640_;
}
default: 
{
lean_object* v_l_641_; lean_object* v_r_642_; lean_object* v___x_643_; 
lean_dec(v_h__2_636_);
lean_dec(v_h__1_635_);
v_l_641_ = lean_ctor_get(v_x_634_, 0);
lean_inc(v_l_641_);
v_r_642_ = lean_ctor_get(v_x_634_, 1);
lean_inc(v_r_642_);
lean_dec_ref_known(v_x_634_, 2);
v___x_643_ = lean_apply_3(v_h__3_637_, v_l_641_, v_r_642_, lean_box(0));
return v___x_643_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_Cache_ofAtoms_go_match__1_splitter(lean_object* v_00_u03b1_644_, lean_object* v_motive_645_, lean_object* v_x_646_, lean_object* v_h__1_647_, lean_object* v_h__2_648_, lean_object* v_h__3_649_){
_start:
{
switch(lean_obj_tag(v_x_646_))
{
case 0:
{
lean_object* v___x_650_; 
lean_dec(v_h__3_649_);
lean_dec(v_h__1_647_);
v___x_650_ = lean_apply_1(v_h__2_648_, lean_box(0));
return v___x_650_;
}
case 1:
{
lean_object* v_idx_651_; lean_object* v___x_652_; 
lean_dec(v_h__3_649_);
lean_dec(v_h__2_648_);
v_idx_651_ = lean_ctor_get(v_x_646_, 0);
lean_inc(v_idx_651_);
lean_dec_ref_known(v_x_646_, 1);
v___x_652_ = lean_apply_2(v_h__1_647_, v_idx_651_, lean_box(0));
return v___x_652_;
}
default: 
{
lean_object* v_l_653_; lean_object* v_r_654_; lean_object* v___x_655_; 
lean_dec(v_h__2_648_);
lean_dec(v_h__1_647_);
v_l_653_ = lean_ctor_get(v_x_646_, 0);
lean_inc(v_l_653_);
v_r_654_ = lean_ctor_get(v_x_646_, 1);
lean_inc(v_r_654_);
lean_dec_ref_known(v_x_646_, 2);
v___x_655_ = lean_apply_3(v_h__3_649_, v_l_653_, v_r_654_, lean_box(0));
return v___x_655_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_ofAtoms___redArg(lean_object* v_inst_656_, lean_object* v_inst_657_, lean_object* v_decls_658_){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_659_ = lean_unsigned_to_nat(0u);
v___x_660_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___redArg___closed__1, &l_Std_Sat_AIG_Cache_empty___redArg___closed__1_once, _init_l_Std_Sat_AIG_Cache_empty___redArg___closed__1);
v___x_661_ = l_Std_Sat_AIG_Cache_ofAtoms_go___redArg(v_inst_656_, v_inst_657_, v_decls_658_, v___x_659_, v___x_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_ofAtoms___redArg___boxed(lean_object* v_inst_662_, lean_object* v_inst_663_, lean_object* v_decls_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Std_Sat_AIG_Cache_ofAtoms___redArg(v_inst_662_, v_inst_663_, v_decls_664_);
lean_dec_ref(v_decls_664_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_ofAtoms(lean_object* v_00_u03b1_666_, lean_object* v_inst_667_, lean_object* v_inst_668_, lean_object* v_decls_669_, lean_object* v_huniq_670_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l_Std_Sat_AIG_Cache_ofAtoms___redArg(v_inst_667_, v_inst_668_, v_decls_669_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_ofAtoms___boxed(lean_object* v_00_u03b1_672_, lean_object* v_inst_673_, lean_object* v_inst_674_, lean_object* v_decls_675_, lean_object* v_huniq_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Std_Sat_AIG_Cache_ofAtoms(v_00_u03b1_672_, v_inst_673_, v_inst_674_, v_decls_675_, v_huniq_676_);
lean_dec_ref(v_decls_675_);
return v_res_677_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___redArg___closed__1(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_682_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___redArg___closed__1, &l_Std_Sat_AIG_Cache_empty___redArg___closed__1_once, _init_l_Std_Sat_AIG_Cache_empty___redArg___closed__1);
v___x_683_ = ((lean_object*)(l_Std_Sat_AIG_empty___redArg___closed__0));
v___x_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
lean_ctor_set(v___x_684_, 1, v___x_682_);
return v___x_684_;
}
}
lean_object* l_Std_Sat_AIG_empty___redArg(){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = lean_obj_once(&l_Std_Sat_AIG_empty___redArg___closed__1, &l_Std_Sat_AIG_empty___redArg___closed__1_once, _init_l_Std_Sat_AIG_empty___redArg___closed__1);
return v___x_686_;
}
}
LEAN_EXPORT void l_Std_Sat_AIG_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_687_;
v_res_687_ = l_Std_Sat_AIG_empty___redArg();
stack->m_obj
 = v_res_687_;
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_empty___redArg___boxed(lean_object* v___dummy_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Std_Sat_AIG_empty___redArg();
return v_res_689_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___closed__0(void){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_Std_Sat_AIG_empty___redArg();
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_empty(lean_object* v_00_u03b1_691_, lean_object* v_inst_692_, lean_object* v_inst_693_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = lean_obj_once(&l_Std_Sat_AIG_empty___closed__0, &l_Std_Sat_AIG_empty___closed__0_once, _init_l_Std_Sat_AIG_empty___closed__0);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_empty___boxed(lean_object* v_00_u03b1_695_, lean_object* v_inst_696_, lean_object* v_inst_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Std_Sat_AIG_empty(v_00_u03b1_695_, v_inst_696_, v_inst_697_);
lean_dec_ref(v_inst_697_);
lean_dec_ref(v_inst_696_);
return v_res_698_;
}
}
lean_object* l_Std_Sat_AIG_instMembership___redArg(){
_start:
{
lean_object* v___x_700_; 
v___x_700_ = lean_box(0);
return v___x_700_;
}
}
LEAN_EXPORT void l_Std_Sat_AIG_instMembership___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_701_;
v_res_701_ = l_Std_Sat_AIG_instMembership___redArg();
stack->m_obj
 = v_res_701_;
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instMembership___redArg___boxed(lean_object* v___dummy_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_Std_Sat_AIG_instMembership___redArg();
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instMembership(lean_object* v_00_u03b1_704_, lean_object* v_inst_705_, lean_object* v_inst_706_){
_start:
{
lean_object* v___x_707_; 
v___x_707_ = lean_box(0);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instMembership___boxed(lean_object* v_00_u03b1_708_, lean_object* v_inst_709_, lean_object* v_inst_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Std_Sat_AIG_instMembership(v_00_u03b1_708_, v_inst_709_, v_inst_710_);
lean_dec_ref(v_inst_710_);
lean_dec_ref(v_inst_709_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_cast___redArg(lean_object* v_ref_712_){
_start:
{
lean_object* v_gate_713_; uint8_t v_invert_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
v_gate_713_ = lean_ctor_get(v_ref_712_, 0);
v_invert_714_ = lean_ctor_get_uint8(v_ref_712_, sizeof(void*)*1);
v_isSharedCheck_721_ = !lean_is_exclusive(v_ref_712_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v_ref_712_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_gate_713_);
lean_dec(v_ref_712_);
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_cast(lean_object* v_00_u03b1_722_, lean_object* v_inst_723_, lean_object* v_inst_724_, lean_object* v_aig1_725_, lean_object* v_aig2_726_, lean_object* v_ref_727_, lean_object* v_h_728_){
_start:
{
lean_object* v_gate_729_; uint8_t v_invert_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
v_gate_729_ = lean_ctor_get(v_ref_727_, 0);
v_invert_730_ = lean_ctor_get_uint8(v_ref_727_, sizeof(void*)*1);
v_isSharedCheck_737_ = !lean_is_exclusive(v_ref_727_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v_ref_727_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_gate_729_);
lean_dec(v_ref_727_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_gate_729_);
lean_ctor_set_uint8(v_reuseFailAlloc_736_, sizeof(void*)*1, v_invert_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_cast___boxed(lean_object* v_00_u03b1_738_, lean_object* v_inst_739_, lean_object* v_inst_740_, lean_object* v_aig1_741_, lean_object* v_aig2_742_, lean_object* v_ref_743_, lean_object* v_h_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Std_Sat_AIG_Ref_cast(v_00_u03b1_738_, v_inst_739_, v_inst_740_, v_aig1_741_, v_aig2_742_, v_ref_743_, v_h_744_);
lean_dec_ref(v_aig2_742_);
lean_dec_ref(v_aig1_741_);
lean_dec_ref(v_inst_740_);
lean_dec_ref(v_inst_739_);
return v_res_745_;
}
}
lean_object* l_Std_Sat_AIG_Ref_flip___redArg(lean_object* v_ref_746_, uint8_t v_inv_747_){
_start:
{
lean_object* v_gate_748_; uint8_t v_invert_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_761_; 
v_gate_748_ = lean_ctor_get(v_ref_746_, 0);
v_invert_749_ = lean_ctor_get_uint8(v_ref_746_, sizeof(void*)*1);
v_isSharedCheck_761_ = !lean_is_exclusive(v_ref_746_);
if (v_isSharedCheck_761_ == 0)
{
v___x_751_ = v_ref_746_;
v_isShared_752_ = v_isSharedCheck_761_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_gate_748_);
lean_dec(v_ref_746_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_761_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
if (v_invert_749_ == 0)
{
if (v_inv_747_ == 0)
{
lean_del_object(v___x_751_);
goto v___jp_758_;
}
else
{
goto v___jp_753_;
}
}
else
{
if (v_inv_747_ == 0)
{
goto v___jp_753_;
}
else
{
lean_del_object(v___x_751_);
goto v___jp_758_;
}
}
v___jp_753_:
{
uint8_t v___x_754_; lean_object* v___x_756_; 
v___x_754_ = 1;
if (v_isShared_752_ == 0)
{
v___x_756_ = v___x_751_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_gate_748_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
lean_ctor_set_uint8(v___x_756_, sizeof(void*)*1, v___x_754_);
return v___x_756_;
}
}
v___jp_758_:
{
uint8_t v___x_759_; lean_object* v___x_760_; 
v___x_759_ = 0;
v___x_760_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_760_, 0, v_gate_748_);
lean_ctor_set_uint8(v___x_760_, sizeof(void*)*1, v___x_759_);
return v___x_760_;
}
}
}
}
LEAN_EXPORT void l_Std_Sat_AIG_Ref_flip___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_746_ = stack[0].m_obj;
uint8_t v_inv_747_ = stack[1].m_num;
lean_object* v_res_762_;
v_res_762_ = l_Std_Sat_AIG_Ref_flip___redArg(v_ref_746_, v_inv_747_);
stack->m_obj
 = v_res_762_;
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_flip___redArg___boxed(lean_object* v_ref_763_, lean_object* v_inv_764_){
_start:
{
uint8_t v_inv_boxed_765_; lean_object* v_res_766_; 
v_inv_boxed_765_ = lean_unbox(v_inv_764_);
v_res_766_ = l_Std_Sat_AIG_Ref_flip___redArg(v_ref_763_, v_inv_boxed_765_);
return v_res_766_;
}
}
lean_object* l_Std_Sat_AIG_Ref_flip(lean_object* v_00_u03b1_767_, lean_object* v_inst_768_, lean_object* v_inst_769_, lean_object* v_aig_770_, lean_object* v_ref_771_, uint8_t v_inv_772_){
_start:
{
lean_object* v_gate_773_; uint8_t v_invert_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_786_; 
v_gate_773_ = lean_ctor_get(v_ref_771_, 0);
v_invert_774_ = lean_ctor_get_uint8(v_ref_771_, sizeof(void*)*1);
v_isSharedCheck_786_ = !lean_is_exclusive(v_ref_771_);
if (v_isSharedCheck_786_ == 0)
{
v___x_776_ = v_ref_771_;
v_isShared_777_ = v_isSharedCheck_786_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_gate_773_);
lean_dec(v_ref_771_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_786_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
if (v_invert_774_ == 0)
{
if (v_inv_772_ == 0)
{
lean_del_object(v___x_776_);
goto v___jp_783_;
}
else
{
goto v___jp_778_;
}
}
else
{
if (v_inv_772_ == 0)
{
goto v___jp_778_;
}
else
{
lean_del_object(v___x_776_);
goto v___jp_783_;
}
}
v___jp_778_:
{
uint8_t v___x_779_; lean_object* v___x_781_; 
v___x_779_ = 1;
if (v_isShared_777_ == 0)
{
v___x_781_ = v___x_776_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_gate_773_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_ctor_set_uint8(v___x_781_, sizeof(void*)*1, v___x_779_);
return v___x_781_;
}
}
v___jp_783_:
{
uint8_t v___x_784_; lean_object* v___x_785_; 
v___x_784_ = 0;
v___x_785_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_785_, 0, v_gate_773_);
lean_ctor_set_uint8(v___x_785_, sizeof(void*)*1, v___x_784_);
return v___x_785_;
}
}
}
}
LEAN_EXPORT void l_Std_Sat_AIG_Ref_flip_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_768_ = stack[1].m_obj;
lean_object* v_inst_769_ = stack[2].m_obj;
lean_object* v_aig_770_ = stack[3].m_obj;
lean_object* v_ref_771_ = stack[4].m_obj;
uint8_t v_inv_772_ = stack[5].m_num;
lean_object* v_res_787_;
v_res_787_ = l_Std_Sat_AIG_Ref_flip(lean_box(0), v_inst_768_, v_inst_769_, v_aig_770_, v_ref_771_, v_inv_772_);
stack->m_obj
 = v_res_787_;
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_flip___boxed(lean_object* v_00_u03b1_788_, lean_object* v_inst_789_, lean_object* v_inst_790_, lean_object* v_aig_791_, lean_object* v_ref_792_, lean_object* v_inv_793_){
_start:
{
uint8_t v_inv_boxed_794_; lean_object* v_res_795_; 
v_inv_boxed_794_ = lean_unbox(v_inv_793_);
v_res_795_ = l_Std_Sat_AIG_Ref_flip(v_00_u03b1_788_, v_inst_789_, v_inst_790_, v_aig_791_, v_ref_792_, v_inv_boxed_794_);
lean_dec_ref(v_aig_791_);
lean_dec_ref(v_inst_790_);
lean_dec_ref(v_inst_789_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_not___redArg(lean_object* v_ref_796_){
_start:
{
uint8_t v_invert_797_; 
v_invert_797_ = lean_ctor_get_uint8(v_ref_796_, sizeof(void*)*1);
if (v_invert_797_ == 0)
{
lean_object* v_gate_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_806_; 
v_gate_798_ = lean_ctor_get(v_ref_796_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v_ref_796_);
if (v_isSharedCheck_806_ == 0)
{
v___x_800_ = v_ref_796_;
v_isShared_801_ = v_isSharedCheck_806_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_gate_798_);
lean_dec(v_ref_796_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_806_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
uint8_t v___x_802_; lean_object* v___x_804_; 
v___x_802_ = 1;
if (v_isShared_801_ == 0)
{
v___x_804_ = v___x_800_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_gate_798_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
lean_ctor_set_uint8(v___x_804_, sizeof(void*)*1, v___x_802_);
return v___x_804_;
}
}
}
else
{
lean_object* v_gate_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_815_; 
v_gate_807_ = lean_ctor_get(v_ref_796_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v_ref_796_);
if (v_isSharedCheck_815_ == 0)
{
v___x_809_ = v_ref_796_;
v_isShared_810_ = v_isSharedCheck_815_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_gate_807_);
lean_dec(v_ref_796_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_815_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
uint8_t v___x_811_; lean_object* v___x_813_; 
v___x_811_ = 0;
if (v_isShared_810_ == 0)
{
v___x_813_ = v___x_809_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_gate_807_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
lean_ctor_set_uint8(v___x_813_, sizeof(void*)*1, v___x_811_);
return v___x_813_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_not(lean_object* v_00_u03b1_816_, lean_object* v_inst_817_, lean_object* v_inst_818_, lean_object* v_aig_819_, lean_object* v_ref_820_){
_start:
{
uint8_t v_invert_821_; 
v_invert_821_ = lean_ctor_get_uint8(v_ref_820_, sizeof(void*)*1);
if (v_invert_821_ == 0)
{
lean_object* v_gate_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_830_; 
v_gate_822_ = lean_ctor_get(v_ref_820_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v_ref_820_);
if (v_isSharedCheck_830_ == 0)
{
v___x_824_ = v_ref_820_;
v_isShared_825_ = v_isSharedCheck_830_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_gate_822_);
lean_dec(v_ref_820_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_830_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
uint8_t v___x_826_; lean_object* v___x_828_; 
v___x_826_ = 1;
if (v_isShared_825_ == 0)
{
v___x_828_ = v___x_824_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_gate_822_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
lean_ctor_set_uint8(v___x_828_, sizeof(void*)*1, v___x_826_);
return v___x_828_;
}
}
}
else
{
lean_object* v_gate_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_839_; 
v_gate_831_ = lean_ctor_get(v_ref_820_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v_ref_820_);
if (v_isSharedCheck_839_ == 0)
{
v___x_833_ = v_ref_820_;
v_isShared_834_ = v_isSharedCheck_839_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_gate_831_);
lean_dec(v_ref_820_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_839_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
uint8_t v___x_835_; lean_object* v___x_837_; 
v___x_835_ = 0;
if (v_isShared_834_ == 0)
{
v___x_837_ = v___x_833_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_gate_831_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
lean_ctor_set_uint8(v___x_837_, sizeof(void*)*1, v___x_835_);
return v___x_837_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_not___boxed(lean_object* v_00_u03b1_840_, lean_object* v_inst_841_, lean_object* v_inst_842_, lean_object* v_aig_843_, lean_object* v_ref_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Std_Sat_AIG_Ref_not(v_00_u03b1_840_, v_inst_841_, v_inst_842_, v_aig_843_, v_ref_844_);
lean_dec_ref(v_aig_843_);
lean_dec_ref(v_inst_842_);
lean_dec_ref(v_inst_841_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_cast___redArg(lean_object* v_input_846_){
_start:
{
lean_object* v_lhs_847_; lean_object* v_rhs_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_873_; 
v_lhs_847_ = lean_ctor_get(v_input_846_, 0);
v_rhs_848_ = lean_ctor_get(v_input_846_, 1);
v_isSharedCheck_873_ = !lean_is_exclusive(v_input_846_);
if (v_isSharedCheck_873_ == 0)
{
v___x_850_ = v_input_846_;
v_isShared_851_ = v_isSharedCheck_873_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_rhs_848_);
lean_inc(v_lhs_847_);
lean_dec(v_input_846_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_873_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v_gate_852_; uint8_t v_invert_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_872_; 
v_gate_852_ = lean_ctor_get(v_lhs_847_, 0);
v_invert_853_ = lean_ctor_get_uint8(v_lhs_847_, sizeof(void*)*1);
v_isSharedCheck_872_ = !lean_is_exclusive(v_lhs_847_);
if (v_isSharedCheck_872_ == 0)
{
v___x_855_ = v_lhs_847_;
v_isShared_856_ = v_isSharedCheck_872_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_gate_852_);
lean_dec(v_lhs_847_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_872_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v_gate_857_; uint8_t v_invert_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_871_; 
v_gate_857_ = lean_ctor_get(v_rhs_848_, 0);
v_invert_858_ = lean_ctor_get_uint8(v_rhs_848_, sizeof(void*)*1);
v_isSharedCheck_871_ = !lean_is_exclusive(v_rhs_848_);
if (v_isSharedCheck_871_ == 0)
{
v___x_860_ = v_rhs_848_;
v_isShared_861_ = v_isSharedCheck_871_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_gate_857_);
lean_dec(v_rhs_848_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_871_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 0, v_gate_852_);
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_gate_852_);
v___x_863_ = v_reuseFailAlloc_870_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
lean_object* v___x_865_; 
lean_ctor_set_uint8(v___x_863_, sizeof(void*)*1, v_invert_853_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v_gate_857_);
v___x_865_ = v___x_855_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_gate_857_);
v___x_865_ = v_reuseFailAlloc_869_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
lean_object* v___x_867_; 
lean_ctor_set_uint8(v___x_865_, sizeof(void*)*1, v_invert_858_);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 1, v___x_865_);
lean_ctor_set(v___x_850_, 0, v___x_863_);
v___x_867_ = v___x_850_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v___x_863_);
lean_ctor_set(v_reuseFailAlloc_868_, 1, v___x_865_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_cast(lean_object* v_00_u03b1_874_, lean_object* v_inst_875_, lean_object* v_inst_876_, lean_object* v_aig1_877_, lean_object* v_aig2_878_, lean_object* v_input_879_, lean_object* v_h_880_){
_start:
{
lean_object* v_lhs_881_; lean_object* v_rhs_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_907_; 
v_lhs_881_ = lean_ctor_get(v_input_879_, 0);
v_rhs_882_ = lean_ctor_get(v_input_879_, 1);
v_isSharedCheck_907_ = !lean_is_exclusive(v_input_879_);
if (v_isSharedCheck_907_ == 0)
{
v___x_884_ = v_input_879_;
v_isShared_885_ = v_isSharedCheck_907_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_rhs_882_);
lean_inc(v_lhs_881_);
lean_dec(v_input_879_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_907_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v_gate_886_; uint8_t v_invert_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_906_; 
v_gate_886_ = lean_ctor_get(v_lhs_881_, 0);
v_invert_887_ = lean_ctor_get_uint8(v_lhs_881_, sizeof(void*)*1);
v_isSharedCheck_906_ = !lean_is_exclusive(v_lhs_881_);
if (v_isSharedCheck_906_ == 0)
{
v___x_889_ = v_lhs_881_;
v_isShared_890_ = v_isSharedCheck_906_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_gate_886_);
lean_dec(v_lhs_881_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_906_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v_gate_891_; uint8_t v_invert_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_905_; 
v_gate_891_ = lean_ctor_get(v_rhs_882_, 0);
v_invert_892_ = lean_ctor_get_uint8(v_rhs_882_, sizeof(void*)*1);
v_isSharedCheck_905_ = !lean_is_exclusive(v_rhs_882_);
if (v_isSharedCheck_905_ == 0)
{
v___x_894_ = v_rhs_882_;
v_isShared_895_ = v_isSharedCheck_905_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_gate_891_);
lean_dec(v_rhs_882_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_905_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 0, v_gate_886_);
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_gate_886_);
v___x_897_ = v_reuseFailAlloc_904_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
lean_object* v___x_899_; 
lean_ctor_set_uint8(v___x_897_, sizeof(void*)*1, v_invert_887_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v_gate_891_);
v___x_899_ = v___x_889_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_gate_891_);
v___x_899_ = v_reuseFailAlloc_903_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
lean_object* v___x_901_; 
lean_ctor_set_uint8(v___x_899_, sizeof(void*)*1, v_invert_892_);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 1, v___x_899_);
lean_ctor_set(v___x_884_, 0, v___x_897_);
v___x_901_ = v___x_884_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_897_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v___x_899_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_cast___boxed(lean_object* v_00_u03b1_908_, lean_object* v_inst_909_, lean_object* v_inst_910_, lean_object* v_aig1_911_, lean_object* v_aig2_912_, lean_object* v_input_913_, lean_object* v_h_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Std_Sat_AIG_BinaryInput_cast(v_00_u03b1_908_, v_inst_909_, v_inst_910_, v_aig1_911_, v_aig2_912_, v_input_913_, v_h_914_);
lean_dec_ref(v_aig2_912_);
lean_dec_ref(v_aig1_911_);
lean_dec_ref(v_inst_910_);
lean_dec_ref(v_inst_909_);
return v_res_915_;
}
}
lean_object* l_Std_Sat_AIG_BinaryInput_invert___redArg(lean_object* v_input_916_, uint8_t v_linv_917_, uint8_t v_rinv_918_){
_start:
{
lean_object* v___y_920_; lean_object* v___y_921_; lean_object* v___y_926_; lean_object* v___y_927_; lean_object* v_lhs_931_; lean_object* v_rhs_932_; lean_object* v___y_934_; lean_object* v_gate_940_; uint8_t v_invert_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_953_; 
v_lhs_931_ = lean_ctor_get(v_input_916_, 0);
lean_inc_ref(v_lhs_931_);
v_rhs_932_ = lean_ctor_get(v_input_916_, 1);
lean_inc_ref(v_rhs_932_);
lean_dec_ref(v_input_916_);
v_gate_940_ = lean_ctor_get(v_lhs_931_, 0);
v_invert_941_ = lean_ctor_get_uint8(v_lhs_931_, sizeof(void*)*1);
v_isSharedCheck_953_ = !lean_is_exclusive(v_lhs_931_);
if (v_isSharedCheck_953_ == 0)
{
v___x_943_ = v_lhs_931_;
v_isShared_944_ = v_isSharedCheck_953_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_gate_940_);
lean_dec(v_lhs_931_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_953_;
goto v_resetjp_942_;
}
v___jp_919_:
{
uint8_t v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_922_ = 0;
v___x_923_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_923_, 0, v___y_921_);
lean_ctor_set_uint8(v___x_923_, sizeof(void*)*1, v___x_922_);
v___x_924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_924_, 0, v___y_920_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
return v___x_924_;
}
v___jp_925_:
{
uint8_t v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_928_ = 1;
v___x_929_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_929_, 0, v___y_927_);
lean_ctor_set_uint8(v___x_929_, sizeof(void*)*1, v___x_928_);
v___x_930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_930_, 0, v___y_926_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
return v___x_930_;
}
v___jp_933_:
{
uint8_t v_invert_935_; 
v_invert_935_ = lean_ctor_get_uint8(v_rhs_932_, sizeof(void*)*1);
if (v_invert_935_ == 0)
{
if (v_rinv_918_ == 0)
{
lean_object* v_gate_936_; 
v_gate_936_ = lean_ctor_get(v_rhs_932_, 0);
lean_inc(v_gate_936_);
lean_dec_ref(v_rhs_932_);
v___y_920_ = v___y_934_;
v___y_921_ = v_gate_936_;
goto v___jp_919_;
}
else
{
lean_object* v_gate_937_; 
v_gate_937_ = lean_ctor_get(v_rhs_932_, 0);
lean_inc(v_gate_937_);
lean_dec_ref(v_rhs_932_);
v___y_926_ = v___y_934_;
v___y_927_ = v_gate_937_;
goto v___jp_925_;
}
}
else
{
if (v_rinv_918_ == 0)
{
lean_object* v_gate_938_; 
v_gate_938_ = lean_ctor_get(v_rhs_932_, 0);
lean_inc(v_gate_938_);
lean_dec_ref(v_rhs_932_);
v___y_926_ = v___y_934_;
v___y_927_ = v_gate_938_;
goto v___jp_925_;
}
else
{
lean_object* v_gate_939_; 
v_gate_939_ = lean_ctor_get(v_rhs_932_, 0);
lean_inc(v_gate_939_);
lean_dec_ref(v_rhs_932_);
v___y_920_ = v___y_934_;
v___y_921_ = v_gate_939_;
goto v___jp_919_;
}
}
}
v_resetjp_942_:
{
if (v_invert_941_ == 0)
{
if (v_linv_917_ == 0)
{
lean_del_object(v___x_943_);
goto v___jp_950_;
}
else
{
goto v___jp_945_;
}
}
else
{
if (v_linv_917_ == 0)
{
goto v___jp_945_;
}
else
{
lean_del_object(v___x_943_);
goto v___jp_950_;
}
}
v___jp_945_:
{
uint8_t v___x_946_; lean_object* v___x_948_; 
v___x_946_ = 1;
if (v_isShared_944_ == 0)
{
v___x_948_ = v___x_943_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_gate_940_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
lean_ctor_set_uint8(v___x_948_, sizeof(void*)*1, v___x_946_);
v___y_934_ = v___x_948_;
goto v___jp_933_;
}
}
v___jp_950_:
{
uint8_t v___x_951_; lean_object* v___x_952_; 
v___x_951_ = 0;
v___x_952_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_952_, 0, v_gate_940_);
lean_ctor_set_uint8(v___x_952_, sizeof(void*)*1, v___x_951_);
v___y_934_ = v___x_952_;
goto v___jp_933_;
}
}
}
}
LEAN_EXPORT void l_Std_Sat_AIG_BinaryInput_invert___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_input_916_ = stack[0].m_obj;
uint8_t v_linv_917_ = stack[1].m_num;
uint8_t v_rinv_918_ = stack[2].m_num;
lean_object* v_res_954_;
v_res_954_ = l_Std_Sat_AIG_BinaryInput_invert___redArg(v_input_916_, v_linv_917_, v_rinv_918_);
stack->m_obj
 = v_res_954_;
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_invert___redArg___boxed(lean_object* v_input_955_, lean_object* v_linv_956_, lean_object* v_rinv_957_){
_start:
{
uint8_t v_linv_boxed_958_; uint8_t v_rinv_boxed_959_; lean_object* v_res_960_; 
v_linv_boxed_958_ = lean_unbox(v_linv_956_);
v_rinv_boxed_959_ = lean_unbox(v_rinv_957_);
v_res_960_ = l_Std_Sat_AIG_BinaryInput_invert___redArg(v_input_955_, v_linv_boxed_958_, v_rinv_boxed_959_);
return v_res_960_;
}
}
lean_object* l_Std_Sat_AIG_BinaryInput_invert(lean_object* v_00_u03b1_961_, lean_object* v_inst_962_, lean_object* v_inst_963_, lean_object* v_aig_964_, lean_object* v_input_965_, uint8_t v_linv_966_, uint8_t v_rinv_967_){
_start:
{
lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v_lhs_980_; lean_object* v_rhs_981_; lean_object* v___y_983_; lean_object* v_gate_989_; uint8_t v_invert_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1002_; 
v_lhs_980_ = lean_ctor_get(v_input_965_, 0);
lean_inc_ref(v_lhs_980_);
v_rhs_981_ = lean_ctor_get(v_input_965_, 1);
lean_inc_ref(v_rhs_981_);
lean_dec_ref(v_input_965_);
v_gate_989_ = lean_ctor_get(v_lhs_980_, 0);
v_invert_990_ = lean_ctor_get_uint8(v_lhs_980_, sizeof(void*)*1);
v_isSharedCheck_1002_ = !lean_is_exclusive(v_lhs_980_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_992_ = v_lhs_980_;
v_isShared_993_ = v_isSharedCheck_1002_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_gate_989_);
lean_dec(v_lhs_980_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1002_;
goto v_resetjp_991_;
}
v___jp_968_:
{
uint8_t v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_971_ = 0;
v___x_972_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_972_, 0, v___y_970_);
lean_ctor_set_uint8(v___x_972_, sizeof(void*)*1, v___x_971_);
v___x_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_973_, 0, v___y_969_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
return v___x_973_;
}
v___jp_974_:
{
uint8_t v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_977_ = 1;
v___x_978_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_978_, 0, v___y_976_);
lean_ctor_set_uint8(v___x_978_, sizeof(void*)*1, v___x_977_);
v___x_979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_979_, 0, v___y_975_);
lean_ctor_set(v___x_979_, 1, v___x_978_);
return v___x_979_;
}
v___jp_982_:
{
uint8_t v_invert_984_; 
v_invert_984_ = lean_ctor_get_uint8(v_rhs_981_, sizeof(void*)*1);
if (v_invert_984_ == 0)
{
if (v_rinv_967_ == 0)
{
lean_object* v_gate_985_; 
v_gate_985_ = lean_ctor_get(v_rhs_981_, 0);
lean_inc(v_gate_985_);
lean_dec_ref(v_rhs_981_);
v___y_969_ = v___y_983_;
v___y_970_ = v_gate_985_;
goto v___jp_968_;
}
else
{
lean_object* v_gate_986_; 
v_gate_986_ = lean_ctor_get(v_rhs_981_, 0);
lean_inc(v_gate_986_);
lean_dec_ref(v_rhs_981_);
v___y_975_ = v___y_983_;
v___y_976_ = v_gate_986_;
goto v___jp_974_;
}
}
else
{
if (v_rinv_967_ == 0)
{
lean_object* v_gate_987_; 
v_gate_987_ = lean_ctor_get(v_rhs_981_, 0);
lean_inc(v_gate_987_);
lean_dec_ref(v_rhs_981_);
v___y_975_ = v___y_983_;
v___y_976_ = v_gate_987_;
goto v___jp_974_;
}
else
{
lean_object* v_gate_988_; 
v_gate_988_ = lean_ctor_get(v_rhs_981_, 0);
lean_inc(v_gate_988_);
lean_dec_ref(v_rhs_981_);
v___y_969_ = v___y_983_;
v___y_970_ = v_gate_988_;
goto v___jp_968_;
}
}
}
v_resetjp_991_:
{
if (v_invert_990_ == 0)
{
if (v_linv_966_ == 0)
{
lean_del_object(v___x_992_);
goto v___jp_999_;
}
else
{
goto v___jp_994_;
}
}
else
{
if (v_linv_966_ == 0)
{
goto v___jp_994_;
}
else
{
lean_del_object(v___x_992_);
goto v___jp_999_;
}
}
v___jp_994_:
{
uint8_t v___x_995_; lean_object* v___x_997_; 
v___x_995_ = 1;
if (v_isShared_993_ == 0)
{
v___x_997_ = v___x_992_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_gate_989_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
lean_ctor_set_uint8(v___x_997_, sizeof(void*)*1, v___x_995_);
v___y_983_ = v___x_997_;
goto v___jp_982_;
}
}
v___jp_999_:
{
uint8_t v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = 0;
v___x_1001_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1001_, 0, v_gate_989_);
lean_ctor_set_uint8(v___x_1001_, sizeof(void*)*1, v___x_1000_);
v___y_983_ = v___x_1001_;
goto v___jp_982_;
}
}
}
}
LEAN_EXPORT void l_Std_Sat_AIG_BinaryInput_invert_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_962_ = stack[1].m_obj;
lean_object* v_inst_963_ = stack[2].m_obj;
lean_object* v_aig_964_ = stack[3].m_obj;
lean_object* v_input_965_ = stack[4].m_obj;
uint8_t v_linv_966_ = stack[5].m_num;
uint8_t v_rinv_967_ = stack[6].m_num;
lean_object* v_res_1003_;
v_res_1003_ = l_Std_Sat_AIG_BinaryInput_invert(lean_box(0), v_inst_962_, v_inst_963_, v_aig_964_, v_input_965_, v_linv_966_, v_rinv_967_);
stack->m_obj
 = v_res_1003_;
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_invert___boxed(lean_object* v_00_u03b1_1004_, lean_object* v_inst_1005_, lean_object* v_inst_1006_, lean_object* v_aig_1007_, lean_object* v_input_1008_, lean_object* v_linv_1009_, lean_object* v_rinv_1010_){
_start:
{
uint8_t v_linv_boxed_1011_; uint8_t v_rinv_boxed_1012_; lean_object* v_res_1013_; 
v_linv_boxed_1011_ = lean_unbox(v_linv_1009_);
v_rinv_boxed_1012_ = lean_unbox(v_rinv_1010_);
v_res_1013_ = l_Std_Sat_AIG_BinaryInput_invert(v_00_u03b1_1004_, v_inst_1005_, v_inst_1006_, v_aig_1007_, v_input_1008_, v_linv_boxed_1011_, v_rinv_boxed_1012_);
lean_dec_ref(v_aig_1007_);
lean_dec_ref(v_inst_1006_);
lean_dec_ref(v_inst_1005_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_TernaryInput_cast___redArg(lean_object* v_input_1014_){
_start:
{
lean_object* v_discr_1015_; lean_object* v_lhs_1016_; lean_object* v_rhs_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1051_; 
v_discr_1015_ = lean_ctor_get(v_input_1014_, 0);
v_lhs_1016_ = lean_ctor_get(v_input_1014_, 1);
v_rhs_1017_ = lean_ctor_get(v_input_1014_, 2);
v_isSharedCheck_1051_ = !lean_is_exclusive(v_input_1014_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1019_ = v_input_1014_;
v_isShared_1020_ = v_isSharedCheck_1051_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_rhs_1017_);
lean_inc(v_lhs_1016_);
lean_inc(v_discr_1015_);
lean_dec(v_input_1014_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1051_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v_gate_1021_; uint8_t v_invert_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1050_; 
v_gate_1021_ = lean_ctor_get(v_discr_1015_, 0);
v_invert_1022_ = lean_ctor_get_uint8(v_discr_1015_, sizeof(void*)*1);
v_isSharedCheck_1050_ = !lean_is_exclusive(v_discr_1015_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1024_ = v_discr_1015_;
v_isShared_1025_ = v_isSharedCheck_1050_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_gate_1021_);
lean_dec(v_discr_1015_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1050_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v_gate_1026_; uint8_t v_invert_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1049_; 
v_gate_1026_ = lean_ctor_get(v_lhs_1016_, 0);
v_invert_1027_ = lean_ctor_get_uint8(v_lhs_1016_, sizeof(void*)*1);
v_isSharedCheck_1049_ = !lean_is_exclusive(v_lhs_1016_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1029_ = v_lhs_1016_;
v_isShared_1030_ = v_isSharedCheck_1049_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_gate_1026_);
lean_dec(v_lhs_1016_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1049_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v_gate_1031_; uint8_t v_invert_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1048_; 
v_gate_1031_ = lean_ctor_get(v_rhs_1017_, 0);
v_invert_1032_ = lean_ctor_get_uint8(v_rhs_1017_, sizeof(void*)*1);
v_isSharedCheck_1048_ = !lean_is_exclusive(v_rhs_1017_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1034_ = v_rhs_1017_;
v_isShared_1035_ = v_isSharedCheck_1048_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_gate_1031_);
lean_dec(v_rhs_1017_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1048_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 0, v_gate_1021_);
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_gate_1021_);
v___x_1037_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
lean_object* v___x_1039_; 
lean_ctor_set_uint8(v___x_1037_, sizeof(void*)*1, v_invert_1022_);
if (v_isShared_1030_ == 0)
{
v___x_1039_ = v___x_1029_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_gate_1026_);
lean_ctor_set_uint8(v_reuseFailAlloc_1046_, sizeof(void*)*1, v_invert_1027_);
v___x_1039_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
lean_object* v___x_1041_; 
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 0, v_gate_1031_);
v___x_1041_ = v___x_1024_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_gate_1031_);
v___x_1041_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
lean_object* v___x_1043_; 
lean_ctor_set_uint8(v___x_1041_, sizeof(void*)*1, v_invert_1032_);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 2, v___x_1041_);
lean_ctor_set(v___x_1019_, 1, v___x_1039_);
lean_ctor_set(v___x_1019_, 0, v___x_1037_);
v___x_1043_ = v___x_1019_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1037_);
lean_ctor_set(v_reuseFailAlloc_1044_, 1, v___x_1039_);
lean_ctor_set(v_reuseFailAlloc_1044_, 2, v___x_1041_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_TernaryInput_cast(lean_object* v_00_u03b1_1052_, lean_object* v_inst_1053_, lean_object* v_inst_1054_, lean_object* v_aig1_1055_, lean_object* v_aig2_1056_, lean_object* v_input_1057_, lean_object* v_h_1058_){
_start:
{
lean_object* v_discr_1059_; lean_object* v_lhs_1060_; lean_object* v_rhs_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1095_; 
v_discr_1059_ = lean_ctor_get(v_input_1057_, 0);
v_lhs_1060_ = lean_ctor_get(v_input_1057_, 1);
v_rhs_1061_ = lean_ctor_get(v_input_1057_, 2);
v_isSharedCheck_1095_ = !lean_is_exclusive(v_input_1057_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1063_ = v_input_1057_;
v_isShared_1064_ = v_isSharedCheck_1095_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_rhs_1061_);
lean_inc(v_lhs_1060_);
lean_inc(v_discr_1059_);
lean_dec(v_input_1057_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1095_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v_gate_1065_; uint8_t v_invert_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1094_; 
v_gate_1065_ = lean_ctor_get(v_discr_1059_, 0);
v_invert_1066_ = lean_ctor_get_uint8(v_discr_1059_, sizeof(void*)*1);
v_isSharedCheck_1094_ = !lean_is_exclusive(v_discr_1059_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1068_ = v_discr_1059_;
v_isShared_1069_ = v_isSharedCheck_1094_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_gate_1065_);
lean_dec(v_discr_1059_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1094_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v_gate_1070_; uint8_t v_invert_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1093_; 
v_gate_1070_ = lean_ctor_get(v_lhs_1060_, 0);
v_invert_1071_ = lean_ctor_get_uint8(v_lhs_1060_, sizeof(void*)*1);
v_isSharedCheck_1093_ = !lean_is_exclusive(v_lhs_1060_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1073_ = v_lhs_1060_;
v_isShared_1074_ = v_isSharedCheck_1093_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_gate_1070_);
lean_dec(v_lhs_1060_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1093_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v_gate_1075_; uint8_t v_invert_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1092_; 
v_gate_1075_ = lean_ctor_get(v_rhs_1061_, 0);
v_invert_1076_ = lean_ctor_get_uint8(v_rhs_1061_, sizeof(void*)*1);
v_isSharedCheck_1092_ = !lean_is_exclusive(v_rhs_1061_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1078_ = v_rhs_1061_;
v_isShared_1079_ = v_isSharedCheck_1092_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_gate_1075_);
lean_dec(v_rhs_1061_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1092_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 0, v_gate_1065_);
v___x_1081_ = v___x_1078_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_gate_1065_);
v___x_1081_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
lean_object* v___x_1083_; 
lean_ctor_set_uint8(v___x_1081_, sizeof(void*)*1, v_invert_1066_);
if (v_isShared_1074_ == 0)
{
v___x_1083_ = v___x_1073_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_gate_1070_);
lean_ctor_set_uint8(v_reuseFailAlloc_1090_, sizeof(void*)*1, v_invert_1071_);
v___x_1083_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
lean_object* v___x_1085_; 
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 0, v_gate_1075_);
v___x_1085_ = v___x_1068_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_gate_1075_);
v___x_1085_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
lean_object* v___x_1087_; 
lean_ctor_set_uint8(v___x_1085_, sizeof(void*)*1, v_invert_1076_);
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 2, v___x_1085_);
lean_ctor_set(v___x_1063_, 1, v___x_1083_);
lean_ctor_set(v___x_1063_, 0, v___x_1081_);
v___x_1087_ = v___x_1063_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1081_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v___x_1083_);
lean_ctor_set(v_reuseFailAlloc_1088_, 2, v___x_1085_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_TernaryInput_cast___boxed(lean_object* v_00_u03b1_1096_, lean_object* v_inst_1097_, lean_object* v_inst_1098_, lean_object* v_aig1_1099_, lean_object* v_aig2_1100_, lean_object* v_input_1101_, lean_object* v_h_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Std_Sat_AIG_TernaryInput_cast(v_00_u03b1_1096_, v_inst_1097_, v_inst_1098_, v_aig1_1099_, v_aig2_1100_, v_input_1101_, v_h_1102_);
lean_dec_ref(v_aig2_1100_);
lean_dec_ref(v_aig1_1099_);
lean_dec_ref(v_inst_1098_);
lean_dec_ref(v_inst_1097_);
return v_res_1103_;
}
}
lean_object* l_Std_Sat_AIG_toGraphviz_invEdgeStyle(uint8_t v_isInv_1106_){
_start:
{
if (v_isInv_1106_ == 0)
{
lean_object* v___x_1107_; 
v___x_1107_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_invEdgeStyle___closed__0));
return v___x_1107_;
}
else
{
lean_object* v___x_1108_; 
v___x_1108_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_invEdgeStyle___closed__1));
return v___x_1108_;
}
}
}
LEAN_EXPORT void l_Std_Sat_AIG_toGraphviz_invEdgeStyle_0interp(lean_interpreter_value* stack)
{
uint8_t v_isInv_1106_ = stack[0].m_num;
lean_object* v_res_1109_;
v_res_1109_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v_isInv_1106_);
stack->m_obj
 = v_res_1109_;
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_invEdgeStyle___boxed(lean_object* v_isInv_1110_){
_start:
{
uint8_t v_isInv_boxed_1111_; lean_object* v_res_1112_; 
v_isInv_boxed_1111_ = lean_unbox(v_isInv_1110_);
v_res_1112_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v_isInv_boxed_1111_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___redArg(lean_object* v_acc_1117_, lean_object* v_decls_1118_, lean_object* v_idx_1119_, lean_object* v_a_1120_){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___f_1123_; lean_object* v___f_1124_; uint8_t v___x_1125_; 
v___x_1121_ = lean_array_get_size(v_decls_1118_);
v___x_1122_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_1122_, 0, v___x_1121_);
v___f_1123_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1123_, 0, v___x_1122_);
v___f_1124_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___redArg___closed__0));
lean_inc(v_idx_1119_);
lean_inc_ref(v___f_1123_);
v___x_1125_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1123_, v___f_1124_, v_a_1120_, v_idx_1119_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1126_ = lean_box(0);
lean_inc(v_idx_1119_);
v___x_1127_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___f_1123_, v___f_1124_, v_a_1120_, v_idx_1119_, v___x_1126_);
v___x_1128_ = lean_array_fget_borrowed(v_decls_1118_, v_idx_1119_);
if (lean_obj_tag(v___x_1128_) == 2)
{
lean_object* v_l_1129_; lean_object* v_r_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; uint8_t v___y_1134_; lean_object* v___y_1135_; uint8_t v___y_1136_; uint8_t v___y_1160_; lean_object* v___x_1166_; lean_object* v___x_1167_; uint8_t v___x_1168_; 
v_l_1129_ = lean_ctor_get(v___x_1128_, 0);
v_r_1130_ = lean_ctor_get(v___x_1128_, 1);
v___x_1131_ = lean_unsigned_to_nat(1u);
v___x_1132_ = lean_nat_shiftr(v_l_1129_, v___x_1131_);
v___x_1166_ = lean_nat_land(v___x_1131_, v_l_1129_);
v___x_1167_ = lean_unsigned_to_nat(0u);
v___x_1168_ = lean_nat_dec_eq(v___x_1166_, v___x_1167_);
lean_dec(v___x_1166_);
if (v___x_1168_ == 0)
{
uint8_t v___x_1169_; 
v___x_1169_ = 1;
v___y_1160_ = v___x_1169_;
goto v___jp_1159_;
}
else
{
v___y_1160_ = v___x_1125_;
goto v___jp_1159_;
}
v___jp_1133_:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v_fst_1156_; lean_object* v_snd_1157_; 
v___x_1137_ = l_Nat_reprFast(v_idx_1119_);
v___x_1138_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___redArg___closed__1));
lean_inc_ref(v___x_1137_);
v___x_1139_ = lean_string_append(v___x_1137_, v___x_1138_);
lean_inc(v___x_1132_);
v___x_1140_ = l_Nat_reprFast(v___x_1132_);
v___x_1141_ = lean_string_append(v___x_1139_, v___x_1140_);
lean_dec_ref(v___x_1140_);
v___x_1142_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_1134_);
v___x_1143_ = lean_string_append(v___x_1141_, v___x_1142_);
lean_dec_ref(v___x_1142_);
v___x_1144_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___redArg___closed__2));
v___x_1145_ = lean_string_append(v___x_1143_, v___x_1144_);
v___x_1146_ = lean_string_append(v___x_1145_, v___x_1137_);
lean_dec_ref(v___x_1137_);
v___x_1147_ = lean_string_append(v___x_1146_, v___x_1138_);
lean_inc(v___y_1135_);
v___x_1148_ = l_Nat_reprFast(v___y_1135_);
v___x_1149_ = lean_string_append(v___x_1147_, v___x_1148_);
lean_dec_ref(v___x_1148_);
v___x_1150_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_1136_);
v___x_1151_ = lean_string_append(v___x_1149_, v___x_1150_);
lean_dec_ref(v___x_1150_);
v___x_1152_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___redArg___closed__3));
v___x_1153_ = lean_string_append(v___x_1151_, v___x_1152_);
v___x_1154_ = lean_string_append(v_acc_1117_, v___x_1153_);
lean_dec_ref(v___x_1153_);
v___x_1155_ = l_Std_Sat_AIG_toGraphviz_go___redArg(v___x_1154_, v_decls_1118_, v___x_1132_, v___x_1127_);
v_fst_1156_ = lean_ctor_get(v___x_1155_, 0);
lean_inc(v_fst_1156_);
v_snd_1157_ = lean_ctor_get(v___x_1155_, 1);
lean_inc(v_snd_1157_);
lean_dec_ref(v___x_1155_);
v_acc_1117_ = v_fst_1156_;
v_idx_1119_ = v___y_1135_;
v_a_1120_ = v_snd_1157_;
goto _start;
}
v___jp_1159_:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; uint8_t v___x_1164_; 
v___x_1161_ = lean_nat_shiftr(v_r_1130_, v___x_1131_);
v___x_1162_ = lean_nat_land(v___x_1131_, v_r_1130_);
v___x_1163_ = lean_unsigned_to_nat(0u);
v___x_1164_ = lean_nat_dec_eq(v___x_1162_, v___x_1163_);
lean_dec(v___x_1162_);
if (v___x_1164_ == 0)
{
uint8_t v___x_1165_; 
v___x_1165_ = 1;
v___y_1134_ = v___y_1160_;
v___y_1135_ = v___x_1161_;
v___y_1136_ = v___x_1165_;
goto v___jp_1133_;
}
else
{
v___y_1134_ = v___y_1160_;
v___y_1135_ = v___x_1161_;
v___y_1136_ = v___x_1125_;
goto v___jp_1133_;
}
}
}
else
{
lean_object* v___x_1170_; 
lean_dec(v_idx_1119_);
v___x_1170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1170_, 0, v_acc_1117_);
lean_ctor_set(v___x_1170_, 1, v___x_1127_);
return v___x_1170_;
}
}
else
{
lean_object* v___x_1171_; 
lean_dec_ref(v___f_1123_);
lean_dec(v_idx_1119_);
v___x_1171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1171_, 0, v_acc_1117_);
lean_ctor_set(v___x_1171_, 1, v_a_1120_);
return v___x_1171_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___redArg___boxed(lean_object* v_acc_1172_, lean_object* v_decls_1173_, lean_object* v_idx_1174_, lean_object* v_a_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_Std_Sat_AIG_toGraphviz_go___redArg(v_acc_1172_, v_decls_1173_, v_idx_1174_, v_a_1175_);
lean_dec_ref(v_decls_1173_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go(lean_object* v_00_u03b1_1177_, lean_object* v_inst_1178_, lean_object* v_inst_1179_, lean_object* v_inst_1180_, lean_object* v_acc_1181_, lean_object* v_decls_1182_, lean_object* v_hinv_1183_, lean_object* v_idx_1184_, lean_object* v_hidx_1185_, lean_object* v_a_1186_){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = l_Std_Sat_AIG_toGraphviz_go___redArg(v_acc_1181_, v_decls_1182_, v_idx_1184_, v_a_1186_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___boxed(lean_object* v_00_u03b1_1188_, lean_object* v_inst_1189_, lean_object* v_inst_1190_, lean_object* v_inst_1191_, lean_object* v_acc_1192_, lean_object* v_decls_1193_, lean_object* v_hinv_1194_, lean_object* v_idx_1195_, lean_object* v_hidx_1196_, lean_object* v_a_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Std_Sat_AIG_toGraphviz_go(v_00_u03b1_1188_, v_inst_1189_, v_inst_1190_, v_inst_1191_, v_acc_1192_, v_decls_1193_, v_hinv_1194_, v_idx_1195_, v_hidx_1196_, v_a_1197_);
lean_dec_ref(v_decls_1193_);
lean_dec_ref(v_inst_1191_);
lean_dec_ref(v_inst_1190_);
lean_dec_ref(v_inst_1189_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter___redArg(lean_object* v_x_1199_, lean_object* v_h__1_1200_, lean_object* v_h__2_1201_, lean_object* v_h__3_1202_){
_start:
{
switch(lean_obj_tag(v_x_1199_))
{
case 0:
{
lean_object* v___x_1203_; 
lean_dec(v_h__3_1202_);
lean_dec(v_h__2_1201_);
v___x_1203_ = lean_apply_1(v_h__1_1200_, lean_box(0));
return v___x_1203_;
}
case 1:
{
lean_object* v_idx_1204_; lean_object* v___x_1205_; 
lean_dec(v_h__3_1202_);
lean_dec(v_h__1_1200_);
v_idx_1204_ = lean_ctor_get(v_x_1199_, 0);
lean_inc(v_idx_1204_);
lean_dec_ref_known(v_x_1199_, 1);
v___x_1205_ = lean_apply_2(v_h__2_1201_, v_idx_1204_, lean_box(0));
return v___x_1205_;
}
default: 
{
lean_object* v_l_1206_; lean_object* v_r_1207_; lean_object* v___x_1208_; 
lean_dec(v_h__2_1201_);
lean_dec(v_h__1_1200_);
v_l_1206_ = lean_ctor_get(v_x_1199_, 0);
lean_inc(v_l_1206_);
v_r_1207_ = lean_ctor_get(v_x_1199_, 1);
lean_inc(v_r_1207_);
lean_dec_ref_known(v_x_1199_, 2);
v___x_1208_ = lean_apply_3(v_h__3_1202_, v_l_1206_, v_r_1207_, lean_box(0));
return v___x_1208_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter(lean_object* v_00_u03b1_1209_, lean_object* v_motive_1210_, lean_object* v_x_1211_, lean_object* v_h__1_1212_, lean_object* v_h__2_1213_, lean_object* v_h__3_1214_){
_start:
{
switch(lean_obj_tag(v_x_1211_))
{
case 0:
{
lean_object* v___x_1215_; 
lean_dec(v_h__3_1214_);
lean_dec(v_h__2_1213_);
v___x_1215_ = lean_apply_1(v_h__1_1212_, lean_box(0));
return v___x_1215_;
}
case 1:
{
lean_object* v_idx_1216_; lean_object* v___x_1217_; 
lean_dec(v_h__3_1214_);
lean_dec(v_h__1_1212_);
v_idx_1216_ = lean_ctor_get(v_x_1211_, 0);
lean_inc(v_idx_1216_);
lean_dec_ref_known(v_x_1211_, 1);
v___x_1217_ = lean_apply_2(v_h__2_1213_, v_idx_1216_, lean_box(0));
return v___x_1217_;
}
default: 
{
lean_object* v_l_1218_; lean_object* v_r_1219_; lean_object* v___x_1220_; 
lean_dec(v_h__2_1213_);
lean_dec(v_h__1_1212_);
v_l_1218_ = lean_ctor_get(v_x_1211_, 0);
lean_inc(v_l_1218_);
v_r_1219_ = lean_ctor_get(v_x_1211_, 1);
lean_inc(v_r_1219_);
lean_dec_ref_known(v_x_1211_, 2);
v___x_1220_ = lean_apply_3(v_h__3_1214_, v_l_1218_, v_r_1219_, lean_box(0));
return v___x_1220_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg(lean_object* v_inst_1226_, lean_object* v_decls_1227_, lean_object* v_idx_1228_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = lean_array_fget_borrowed(v_decls_1227_, v_idx_1228_);
switch(lean_obj_tag(v___x_1229_))
{
case 0:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
lean_dec_ref(v_inst_1226_);
v___x_1230_ = l_Nat_reprFast(v_idx_1228_);
v___x_1231_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__0));
v___x_1232_ = lean_string_append(v___x_1230_, v___x_1231_);
v___x_1233_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__1));
v___x_1234_ = lean_string_append(v___x_1232_, v___x_1233_);
v___x_1235_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__2));
v___x_1236_ = lean_string_append(v___x_1234_, v___x_1235_);
return v___x_1236_;
}
case 1:
{
lean_object* v_idx_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v_idx_1237_ = lean_ctor_get(v___x_1229_, 0);
v___x_1238_ = l_Nat_reprFast(v_idx_1228_);
v___x_1239_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__0));
v___x_1240_ = lean_string_append(v___x_1238_, v___x_1239_);
lean_inc(v_idx_1237_);
v___x_1241_ = lean_apply_1(v_inst_1226_, v_idx_1237_);
v___x_1242_ = lean_string_append(v___x_1240_, v___x_1241_);
lean_dec_ref(v___x_1241_);
v___x_1243_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__3));
v___x_1244_ = lean_string_append(v___x_1242_, v___x_1243_);
return v___x_1244_;
}
default: 
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
lean_dec_ref(v_inst_1226_);
v___x_1245_ = l_Nat_reprFast(v_idx_1228_);
v___x_1246_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__0));
lean_inc_ref(v___x_1245_);
v___x_1247_ = lean_string_append(v___x_1245_, v___x_1246_);
v___x_1248_ = lean_string_append(v___x_1247_, v___x_1245_);
lean_dec_ref(v___x_1245_);
v___x_1249_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__4));
v___x_1250_ = lean_string_append(v___x_1248_, v___x_1249_);
return v___x_1250_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___boxed(lean_object* v_inst_1251_, lean_object* v_decls_1252_, lean_object* v_idx_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg(v_inst_1251_, v_decls_1252_, v_idx_1253_);
lean_dec_ref(v_decls_1252_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString(lean_object* v_00_u03b1_1255_, lean_object* v_inst_1256_, lean_object* v_inst_1257_, lean_object* v_inst_1258_, lean_object* v_decls_1259_, lean_object* v_idx_1260_){
_start:
{
lean_object* v___x_1261_; 
v___x_1261_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg(v_inst_1257_, v_decls_1259_, v_idx_1260_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___boxed(lean_object* v_00_u03b1_1262_, lean_object* v_inst_1263_, lean_object* v_inst_1264_, lean_object* v_inst_1265_, lean_object* v_decls_1266_, lean_object* v_idx_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString(v_00_u03b1_1262_, v_inst_1263_, v_inst_1264_, v_inst_1265_, v_decls_1266_, v_idx_1267_);
lean_dec_ref(v_decls_1266_);
lean_dec_ref(v_inst_1265_);
lean_dec_ref(v_inst_1263_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___redArg___lam__0(lean_object* v_inst_1269_, lean_object* v_decls_1270_, lean_object* v_x1_1271_, lean_object* v_x2_1272_, lean_object* v_x3_1273_){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1274_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg(v_inst_1269_, v_decls_1270_, v_x2_1272_);
v___x_1275_ = lean_string_append(v_x1_1271_, v___x_1274_);
lean_dec_ref(v___x_1274_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___redArg___lam__0___boxed(lean_object* v_inst_1276_, lean_object* v_decls_1277_, lean_object* v_x1_1278_, lean_object* v_x2_1279_, lean_object* v_x3_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Std_Sat_AIG_toGraphviz___redArg___lam__0(v_inst_1276_, v_decls_1277_, v_x1_1278_, v_x2_1279_, v_x3_1280_);
lean_dec_ref(v_decls_1277_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___redArg___lam__1(lean_object* v___x_1282_, lean_object* v___f_1283_, lean_object* v_acc_1284_, lean_object* v_l_1285_){
_start:
{
lean_object* v___x_1286_; 
v___x_1286_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1282_, v___f_1283_, v_acc_1284_, v_l_1285_);
return v___x_1286_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___redArg___closed__1(void){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1288_ = lean_box(0);
v___x_1289_ = lean_unsigned_to_nat(16u);
v___x_1290_ = lean_mk_array(v___x_1289_, v___x_1288_);
return v___x_1290_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___redArg___closed__2(void){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1291_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___redArg___closed__1, &l_Std_Sat_AIG_toGraphviz___redArg___closed__1_once, _init_l_Std_Sat_AIG_toGraphviz___redArg___closed__1);
v___x_1292_ = lean_unsigned_to_nat(0u);
v___x_1293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1292_);
lean_ctor_set(v___x_1293_, 1, v___x_1291_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___redArg(lean_object* v_inst_1315_, lean_object* v_entry_1316_){
_start:
{
lean_object* v_aig_1317_; lean_object* v_ref_1318_; lean_object* v_decls_1319_; lean_object* v_gate_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v_fst_1325_; lean_object* v_snd_1326_; lean_object* v___y_1328_; lean_object* v___x_1334_; lean_object* v_buckets_1335_; lean_object* v___x_1336_; uint8_t v___x_1337_; 
v_aig_1317_ = lean_ctor_get(v_entry_1316_, 0);
lean_inc_ref(v_aig_1317_);
v_ref_1318_ = lean_ctor_get(v_entry_1316_, 1);
lean_inc_ref(v_ref_1318_);
lean_dec_ref(v_entry_1316_);
v_decls_1319_ = lean_ctor_get(v_aig_1317_, 0);
lean_inc_ref(v_decls_1319_);
lean_dec_ref(v_aig_1317_);
v_gate_1320_ = lean_ctor_get(v_ref_1318_, 0);
lean_inc(v_gate_1320_);
lean_dec_ref(v_ref_1318_);
v___x_1321_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___redArg___closed__0));
v___x_1322_ = lean_unsigned_to_nat(0u);
v___x_1323_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___redArg___closed__2, &l_Std_Sat_AIG_toGraphviz___redArg___closed__2_once, _init_l_Std_Sat_AIG_toGraphviz___redArg___closed__2);
v___x_1324_ = l_Std_Sat_AIG_toGraphviz_go___redArg(v___x_1321_, v_decls_1319_, v_gate_1320_, v___x_1323_);
v_fst_1325_ = lean_ctor_get(v___x_1324_, 0);
lean_inc(v_fst_1325_);
v_snd_1326_ = lean_ctor_get(v___x_1324_, 1);
lean_inc(v_snd_1326_);
lean_dec_ref(v___x_1324_);
v___x_1334_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___redArg___closed__14));
v_buckets_1335_ = lean_ctor_get(v_snd_1326_, 1);
lean_inc_ref(v_buckets_1335_);
lean_dec(v_snd_1326_);
v___x_1336_ = lean_array_get_size(v_buckets_1335_);
v___x_1337_ = lean_nat_dec_lt(v___x_1322_, v___x_1336_);
if (v___x_1337_ == 0)
{
lean_dec_ref(v_buckets_1335_);
lean_dec_ref(v_decls_1319_);
lean_dec_ref(v_inst_1315_);
v___y_1328_ = v___x_1321_;
goto v___jp_1327_;
}
else
{
lean_object* v___f_1338_; lean_object* v___f_1339_; size_t v___x_1340_; size_t v___x_1341_; lean_object* v___x_1342_; 
v___f_1338_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_toGraphviz___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1338_, 0, v_inst_1315_);
lean_closure_set(v___f_1338_, 1, v_decls_1319_);
v___f_1339_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_toGraphviz___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1339_, 0, v___x_1334_);
lean_closure_set(v___f_1339_, 1, v___f_1338_);
v___x_1340_ = ((size_t)0ULL);
v___x_1341_ = lean_usize_of_nat(v___x_1336_);
v___x_1342_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1334_, v___f_1339_, v_buckets_1335_, v___x_1340_, v___x_1341_, v___x_1321_);
v___y_1328_ = v___x_1342_;
goto v___jp_1327_;
}
v___jp_1327_:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1329_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___redArg___closed__3));
v___x_1330_ = lean_string_append(v___x_1329_, v___y_1328_);
lean_dec_ref(v___y_1328_);
v___x_1331_ = lean_string_append(v___x_1330_, v_fst_1325_);
lean_dec(v_fst_1325_);
v___x_1332_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___redArg___closed__4));
v___x_1333_ = lean_string_append(v___x_1331_, v___x_1332_);
return v___x_1333_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz(lean_object* v_00_u03b1_1343_, lean_object* v_inst_1344_, lean_object* v_inst_1345_, lean_object* v_inst_1346_, lean_object* v_entry_1347_){
_start:
{
lean_object* v___x_1348_; 
v___x_1348_ = l_Std_Sat_AIG_toGraphviz___redArg(v_inst_1345_, v_entry_1347_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___boxed(lean_object* v_00_u03b1_1349_, lean_object* v_inst_1350_, lean_object* v_inst_1351_, lean_object* v_inst_1352_, lean_object* v_entry_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l_Std_Sat_AIG_toGraphviz(v_00_u03b1_1349_, v_inst_1350_, v_inst_1351_, v_inst_1352_, v_entry_1353_);
lean_dec_ref(v_inst_1352_);
lean_dec_ref(v_inst_1350_);
return v_res_1354_;
}
}
uint8_t l_Std_Sat_AIG_denote_go___redArg(lean_object* v_x_1355_, lean_object* v_decls_1356_, lean_object* v_assign_1357_){
_start:
{
uint8_t v___y_1359_; uint8_t v___y_1360_; lean_object* v___x_1362_; 
v___x_1362_ = lean_array_fget_borrowed(v_decls_1356_, v_x_1355_);
switch(lean_obj_tag(v___x_1362_))
{
case 0:
{
uint8_t v___x_1363_; 
lean_dec_ref(v_assign_1357_);
v___x_1363_ = 0;
return v___x_1363_;
}
case 1:
{
lean_object* v_idx_1364_; lean_object* v___x_1365_; uint8_t v___x_1366_; 
v_idx_1364_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_idx_1364_);
v___x_1365_ = lean_apply_1(v_assign_1357_, v_idx_1364_);
v___x_1366_ = lean_unbox(v___x_1365_);
return v___x_1366_;
}
default: 
{
lean_object* v_l_1367_; lean_object* v_r_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; uint8_t v_lval_1371_; lean_object* v___x_1372_; uint8_t v_rval_1373_; uint8_t v___y_1375_; uint8_t v___y_1380_; lean_object* v___x_1382_; lean_object* v___x_1383_; uint8_t v___x_1384_; 
v_l_1367_ = lean_ctor_get(v___x_1362_, 0);
v_r_1368_ = lean_ctor_get(v___x_1362_, 1);
v___x_1369_ = lean_unsigned_to_nat(1u);
v___x_1370_ = lean_nat_shiftr(v_l_1367_, v___x_1369_);
lean_inc_ref(v_assign_1357_);
v_lval_1371_ = l_Std_Sat_AIG_denote_go___redArg(v___x_1370_, v_decls_1356_, v_assign_1357_);
lean_dec(v___x_1370_);
v___x_1372_ = lean_nat_shiftr(v_r_1368_, v___x_1369_);
v_rval_1373_ = l_Std_Sat_AIG_denote_go___redArg(v___x_1372_, v_decls_1356_, v_assign_1357_);
lean_dec(v___x_1372_);
v___x_1382_ = lean_nat_land(v___x_1369_, v_l_1367_);
v___x_1383_ = lean_unsigned_to_nat(0u);
v___x_1384_ = lean_nat_dec_eq(v___x_1382_, v___x_1383_);
lean_dec(v___x_1382_);
if (v___x_1384_ == 0)
{
v___y_1380_ = v_lval_1371_;
goto v___jp_1379_;
}
else
{
if (v_lval_1371_ == 0)
{
v___y_1380_ = v___x_1384_;
goto v___jp_1379_;
}
else
{
uint8_t v___x_1385_; 
v___x_1385_ = 0;
v___y_1375_ = v___x_1385_;
goto v___jp_1374_;
}
}
v___jp_1374_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; uint8_t v___x_1378_; 
v___x_1376_ = lean_nat_land(v___x_1369_, v_r_1368_);
v___x_1377_ = lean_unsigned_to_nat(0u);
v___x_1378_ = lean_nat_dec_eq(v___x_1376_, v___x_1377_);
lean_dec(v___x_1376_);
if (v___x_1378_ == 0)
{
v___y_1359_ = v___y_1375_;
v___y_1360_ = v_rval_1373_;
goto v___jp_1358_;
}
else
{
if (v_rval_1373_ == 0)
{
v___y_1359_ = v___y_1375_;
v___y_1360_ = v___x_1378_;
goto v___jp_1358_;
}
else
{
return v_rval_1373_;
}
}
}
v___jp_1379_:
{
if (v___y_1380_ == 0)
{
v___y_1375_ = v___y_1380_;
goto v___jp_1374_;
}
else
{
uint8_t v___x_1381_; 
v___x_1381_ = 0;
return v___x_1381_;
}
}
}
}
v___jp_1358_:
{
if (v___y_1360_ == 0)
{
uint8_t v___x_1361_; 
v___x_1361_ = 1;
return v___x_1361_;
}
else
{
return v___y_1359_;
}
}
}
}
LEAN_EXPORT void l_Std_Sat_AIG_denote_go___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1355_ = stack[0].m_obj;
lean_object* v_decls_1356_ = stack[1].m_obj;
lean_object* v_assign_1357_ = stack[2].m_obj;
uint8_t v_res_1386_;
v_res_1386_ = l_Std_Sat_AIG_denote_go___redArg(v_x_1355_, v_decls_1356_, v_assign_1357_);
stack->m_num = v_res_1386_;
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote_go___redArg___boxed(lean_object* v_x_1387_, lean_object* v_decls_1388_, lean_object* v_assign_1389_){
_start:
{
uint8_t v_res_1390_; lean_object* v_r_1391_; 
v_res_1390_ = l_Std_Sat_AIG_denote_go___redArg(v_x_1387_, v_decls_1388_, v_assign_1389_);
lean_dec_ref(v_decls_1388_);
lean_dec(v_x_1387_);
v_r_1391_ = lean_box(v_res_1390_);
return v_r_1391_;
}
}
uint8_t l_Std_Sat_AIG_denote_go(lean_object* v_00_u03b1_1392_, lean_object* v_x_1393_, lean_object* v_decls_1394_, lean_object* v_assign_1395_, lean_object* v_h1_1396_, lean_object* v_h2_1397_){
_start:
{
uint8_t v___x_1398_; 
v___x_1398_ = l_Std_Sat_AIG_denote_go___redArg(v_x_1393_, v_decls_1394_, v_assign_1395_);
return v___x_1398_;
}
}
LEAN_EXPORT void l_Std_Sat_AIG_denote_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1393_ = stack[1].m_obj;
lean_object* v_decls_1394_ = stack[2].m_obj;
lean_object* v_assign_1395_ = stack[3].m_obj;
uint8_t v_res_1399_;
v_res_1399_ = l_Std_Sat_AIG_denote_go(lean_box(0), v_x_1393_, v_decls_1394_, v_assign_1395_, lean_box(0), lean_box(0));
stack->m_num = v_res_1399_;
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote_go___boxed(lean_object* v_00_u03b1_1400_, lean_object* v_x_1401_, lean_object* v_decls_1402_, lean_object* v_assign_1403_, lean_object* v_h1_1404_, lean_object* v_h2_1405_){
_start:
{
uint8_t v_res_1406_; lean_object* v_r_1407_; 
v_res_1406_ = l_Std_Sat_AIG_denote_go(v_00_u03b1_1400_, v_x_1401_, v_decls_1402_, v_assign_1403_, v_h1_1404_, v_h2_1405_);
lean_dec_ref(v_decls_1402_);
lean_dec(v_x_1401_);
v_r_1407_ = lean_box(v_res_1406_);
return v_r_1407_;
}
}
uint8_t l_Std_Sat_AIG_denote___redArg(lean_object* v_assign_1408_, lean_object* v_entry_1409_){
_start:
{
lean_object* v_ref_1410_; lean_object* v_aig_1411_; lean_object* v_gate_1412_; uint8_t v_invert_1413_; lean_object* v_decls_1414_; uint8_t v___x_1415_; 
v_ref_1410_ = lean_ctor_get(v_entry_1409_, 1);
v_aig_1411_ = lean_ctor_get(v_entry_1409_, 0);
v_gate_1412_ = lean_ctor_get(v_ref_1410_, 0);
v_invert_1413_ = lean_ctor_get_uint8(v_ref_1410_, sizeof(void*)*1);
v_decls_1414_ = lean_ctor_get(v_aig_1411_, 0);
v___x_1415_ = l_Std_Sat_AIG_denote_go___redArg(v_gate_1412_, v_decls_1414_, v_assign_1408_);
if (v_invert_1413_ == 0)
{
return v___x_1415_;
}
else
{
if (v___x_1415_ == 0)
{
return v_invert_1413_;
}
else
{
uint8_t v___x_1416_; 
v___x_1416_ = 0;
return v___x_1416_;
}
}
}
}
LEAN_EXPORT void l_Std_Sat_AIG_denote___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_assign_1408_ = stack[0].m_obj;
lean_object* v_entry_1409_ = stack[1].m_obj;
uint8_t v_res_1417_;
v_res_1417_ = l_Std_Sat_AIG_denote___redArg(v_assign_1408_, v_entry_1409_);
stack->m_num = v_res_1417_;
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote___redArg___boxed(lean_object* v_assign_1418_, lean_object* v_entry_1419_){
_start:
{
uint8_t v_res_1420_; lean_object* v_r_1421_; 
v_res_1420_ = l_Std_Sat_AIG_denote___redArg(v_assign_1418_, v_entry_1419_);
lean_dec_ref(v_entry_1419_);
v_r_1421_ = lean_box(v_res_1420_);
return v_r_1421_;
}
}
uint8_t l_Std_Sat_AIG_denote(lean_object* v_00_u03b1_1422_, lean_object* v_inst_1423_, lean_object* v_inst_1424_, lean_object* v_assign_1425_, lean_object* v_entry_1426_){
_start:
{
uint8_t v___x_1427_; 
v___x_1427_ = l_Std_Sat_AIG_denote___redArg(v_assign_1425_, v_entry_1426_);
return v___x_1427_;
}
}
LEAN_EXPORT void l_Std_Sat_AIG_denote_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1423_ = stack[1].m_obj;
lean_object* v_inst_1424_ = stack[2].m_obj;
lean_object* v_assign_1425_ = stack[3].m_obj;
lean_object* v_entry_1426_ = stack[4].m_obj;
uint8_t v_res_1428_;
v_res_1428_ = l_Std_Sat_AIG_denote(lean_box(0), v_inst_1423_, v_inst_1424_, v_assign_1425_, v_entry_1426_);
stack->m_num = v_res_1428_;
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote___boxed(lean_object* v_00_u03b1_1429_, lean_object* v_inst_1430_, lean_object* v_inst_1431_, lean_object* v_assign_1432_, lean_object* v_entry_1433_){
_start:
{
uint8_t v_res_1434_; lean_object* v_r_1435_; 
v_res_1434_ = l_Std_Sat_AIG_denote(v_00_u03b1_1429_, v_inst_1430_, v_inst_1431_, v_assign_1432_, v_entry_1433_);
lean_dec_ref(v_entry_1433_);
lean_dec_ref(v_inst_1431_);
lean_dec_ref(v_inst_1430_);
v_r_1435_ = lean_box(v_res_1434_);
return v_r_1435_;
}
}
static lean_object* _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4(void){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1515_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__3));
v___x_1516_ = l_String_toRawSubstring_x27(v___x_1515_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1(lean_object* v_x_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_){
_start:
{
lean_object* v___x_1538_; uint8_t v___x_1539_; 
v___x_1538_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
lean_inc(v_x_1535_);
v___x_1539_ = l_Lean_Syntax_isOfKind(v_x_1535_, v___x_1538_);
if (v___x_1539_ == 0)
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
lean_dec(v_x_1535_);
v___x_1540_ = lean_box(1);
v___x_1541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1540_);
lean_ctor_set(v___x_1541_, 1, v_a_1537_);
return v___x_1541_;
}
else
{
lean_object* v_quotContext_1542_; lean_object* v_currMacroScope_1543_; lean_object* v_ref_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; uint8_t v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v_quotContext_1542_ = lean_ctor_get(v_a_1536_, 1);
v_currMacroScope_1543_ = lean_ctor_get(v_a_1536_, 2);
v_ref_1544_ = lean_ctor_get(v_a_1536_, 5);
v___x_1545_ = lean_unsigned_to_nat(1u);
v___x_1546_ = l_Lean_Syntax_getArg(v_x_1535_, v___x_1545_);
v___x_1547_ = lean_unsigned_to_nat(3u);
v___x_1548_ = l_Lean_Syntax_getArg(v_x_1535_, v___x_1547_);
lean_dec(v_x_1535_);
v___x_1549_ = 0;
v___x_1550_ = l_Lean_SourceInfo_fromRef(v_ref_1544_, v___x_1549_);
v___x_1551_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2));
v___x_1552_ = lean_obj_once(&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4, &l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4_once, _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4);
v___x_1553_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__5));
lean_inc(v_currMacroScope_1543_);
lean_inc(v_quotContext_1542_);
v___x_1554_ = l_Lean_addMacroScope(v_quotContext_1542_, v___x_1553_, v_currMacroScope_1543_);
v___x_1555_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__10));
lean_inc_n(v___x_1550_, 2);
v___x_1556_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1550_);
lean_ctor_set(v___x_1556_, 1, v___x_1552_);
lean_ctor_set(v___x_1556_, 2, v___x_1554_);
lean_ctor_set(v___x_1556_, 3, v___x_1555_);
v___x_1557_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__9));
v___x_1558_ = l_Lean_Syntax_node2(v___x_1550_, v___x_1557_, v___x_1548_, v___x_1546_);
v___x_1559_ = l_Lean_Syntax_node2(v___x_1550_, v___x_1551_, v___x_1556_, v___x_1558_);
v___x_1560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1559_);
lean_ctor_set(v___x_1560_, 1, v_a_1537_);
return v___x_1560_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___boxed(lean_object* v_x_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1(v_x_1561_, v_a_1562_, v_a_1563_);
lean_dec_ref(v_a_1562_);
return v_res_1564_;
}
}
static lean_object* _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__7(void){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1581_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___redArg___closed__0));
v___x_1582_ = l_String_toRawSubstring_x27(v___x_1581_);
return v___x_1582_;
}
}
static lean_object* _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__12(void){
_start:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1593_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__11));
v___x_1594_ = l_String_toRawSubstring_x27(v___x_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1(lean_object* v_x_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_){
_start:
{
lean_object* v___x_1621_; uint8_t v___x_1622_; 
v___x_1621_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__1));
lean_inc(v_x_1618_);
v___x_1622_ = l_Lean_Syntax_isOfKind(v_x_1618_, v___x_1621_);
if (v___x_1622_ == 0)
{
lean_object* v___x_1623_; lean_object* v___x_1624_; 
lean_dec(v_x_1618_);
v___x_1623_ = lean_box(1);
v___x_1624_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1623_);
lean_ctor_set(v___x_1624_, 1, v_a_1620_);
return v___x_1624_;
}
else
{
lean_object* v_quotContext_1625_; lean_object* v_currMacroScope_1626_; lean_object* v_ref_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; uint8_t v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v_quotContext_1625_ = lean_ctor_get(v_a_1619_, 1);
v_currMacroScope_1626_ = lean_ctor_get(v_a_1619_, 2);
v_ref_1627_ = lean_ctor_get(v_a_1619_, 5);
v___x_1628_ = lean_unsigned_to_nat(1u);
v___x_1629_ = l_Lean_Syntax_getArg(v_x_1618_, v___x_1628_);
v___x_1630_ = lean_unsigned_to_nat(3u);
v___x_1631_ = l_Lean_Syntax_getArg(v_x_1618_, v___x_1630_);
v___x_1632_ = lean_unsigned_to_nat(5u);
v___x_1633_ = l_Lean_Syntax_getArg(v_x_1618_, v___x_1632_);
lean_dec(v_x_1618_);
v___x_1634_ = 0;
v___x_1635_ = l_Lean_SourceInfo_fromRef(v_ref_1627_, v___x_1634_);
v___x_1636_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2));
v___x_1637_ = lean_obj_once(&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4, &l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4_once, _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4);
v___x_1638_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__5));
lean_inc_n(v_currMacroScope_1626_, 3);
lean_inc_n(v_quotContext_1625_, 3);
v___x_1639_ = l_Lean_addMacroScope(v_quotContext_1625_, v___x_1638_, v_currMacroScope_1626_);
v___x_1640_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__10));
lean_inc_n(v___x_1635_, 11);
v___x_1641_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1635_);
lean_ctor_set(v___x_1641_, 1, v___x_1637_);
lean_ctor_set(v___x_1641_, 2, v___x_1639_);
lean_ctor_set(v___x_1641_, 3, v___x_1640_);
v___x_1642_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__9));
v___x_1643_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__1));
v___x_1644_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__3));
v___x_1645_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__4));
v___x_1646_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1635_);
lean_ctor_set(v___x_1646_, 1, v___x_1645_);
v___x_1647_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__6));
v___x_1648_ = lean_obj_once(&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__7, &l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__7_once, _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__7);
v___x_1649_ = lean_box(0);
v___x_1650_ = l_Lean_addMacroScope(v_quotContext_1625_, v___x_1649_, v_currMacroScope_1626_);
v___x_1651_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__10));
v___x_1652_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1635_);
lean_ctor_set(v___x_1652_, 1, v___x_1648_);
lean_ctor_set(v___x_1652_, 2, v___x_1650_);
lean_ctor_set(v___x_1652_, 3, v___x_1651_);
v___x_1653_ = l_Lean_Syntax_node1(v___x_1635_, v___x_1647_, v___x_1652_);
v___x_1654_ = l_Lean_Syntax_node2(v___x_1635_, v___x_1644_, v___x_1646_, v___x_1653_);
v___x_1655_ = lean_obj_once(&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__12, &l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__12_once, _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__12);
v___x_1656_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__15));
v___x_1657_ = l_Lean_addMacroScope(v_quotContext_1625_, v___x_1656_, v_currMacroScope_1626_);
v___x_1658_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__20));
v___x_1659_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1635_);
lean_ctor_set(v___x_1659_, 1, v___x_1655_);
lean_ctor_set(v___x_1659_, 2, v___x_1657_);
lean_ctor_set(v___x_1659_, 3, v___x_1658_);
v___x_1660_ = l_Lean_Syntax_node2(v___x_1635_, v___x_1642_, v___x_1629_, v___x_1631_);
v___x_1661_ = l_Lean_Syntax_node2(v___x_1635_, v___x_1636_, v___x_1659_, v___x_1660_);
v___x_1662_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__21));
v___x_1663_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1635_);
lean_ctor_set(v___x_1663_, 1, v___x_1662_);
v___x_1664_ = l_Lean_Syntax_node3(v___x_1635_, v___x_1643_, v___x_1654_, v___x_1661_, v___x_1663_);
v___x_1665_ = l_Lean_Syntax_node2(v___x_1635_, v___x_1642_, v___x_1633_, v___x_1664_);
v___x_1666_ = l_Lean_Syntax_node2(v___x_1635_, v___x_1636_, v___x_1641_, v___x_1665_);
v___x_1667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1666_);
lean_ctor_set(v___x_1667_, 1, v_a_1620_);
return v___x_1667_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___boxed(lean_object* v_x_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1(v_x_1668_, v_a_1669_, v_a_1670_);
lean_dec_ref(v_a_1669_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_unexpandDenote(lean_object* v_x_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_){
_start:
{
lean_object* v___x_1729_; uint8_t v___x_1730_; 
v___x_1729_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2));
lean_inc(v_x_1726_);
v___x_1730_ = l_Lean_Syntax_isOfKind(v_x_1726_, v___x_1729_);
if (v___x_1730_ == 0)
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
lean_dec(v_x_1726_);
v___x_1731_ = lean_box(0);
v___x_1732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1731_);
lean_ctor_set(v___x_1732_, 1, v_a_1728_);
return v___x_1732_;
}
else
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; uint8_t v___x_1736_; 
v___x_1733_ = lean_unsigned_to_nat(1u);
v___x_1734_ = l_Lean_Syntax_getArg(v_x_1726_, v___x_1733_);
lean_dec(v_x_1726_);
v___x_1735_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1734_);
v___x_1736_ = l_Lean_Syntax_matchesNull(v___x_1734_, v___x_1735_);
if (v___x_1736_ == 0)
{
lean_object* v___x_1737_; lean_object* v___x_1738_; 
lean_dec(v___x_1734_);
v___x_1737_ = lean_box(0);
v___x_1738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1737_);
lean_ctor_set(v___x_1738_, 1, v_a_1728_);
return v___x_1738_;
}
else
{
lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; uint8_t v___x_1742_; 
v___x_1739_ = lean_unsigned_to_nat(0u);
v___x_1740_ = l_Lean_Syntax_getArg(v___x_1734_, v___x_1739_);
v___x_1741_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__1));
lean_inc(v___x_1740_);
v___x_1742_ = l_Lean_Syntax_isOfKind(v___x_1740_, v___x_1741_);
if (v___x_1742_ == 0)
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1743_ = l_Lean_Syntax_getArg(v___x_1734_, v___x_1733_);
lean_dec(v___x_1734_);
v___x_1744_ = l_Lean_SourceInfo_fromRef(v_a_1727_, v___x_1742_);
v___x_1745_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1746_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1744_, 3);
v___x_1747_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1744_);
lean_ctor_set(v___x_1747_, 1, v___x_1746_);
v___x_1748_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1749_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1744_);
lean_ctor_set(v___x_1749_, 1, v___x_1748_);
v___x_1750_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1751_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1744_);
lean_ctor_set(v___x_1751_, 1, v___x_1750_);
v___x_1752_ = l_Lean_Syntax_node5(v___x_1744_, v___x_1745_, v___x_1747_, v___x_1740_, v___x_1749_, v___x_1743_, v___x_1751_);
v___x_1753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1752_);
lean_ctor_set(v___x_1753_, 1, v_a_1728_);
return v___x_1753_;
}
else
{
lean_object* v___x_1754_; uint8_t v___x_1755_; 
v___x_1754_ = l_Lean_Syntax_getArg(v___x_1740_, v___x_1733_);
v___x_1755_ = l_Lean_Syntax_matchesNull(v___x_1754_, v___x_1739_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1756_ = l_Lean_Syntax_getArg(v___x_1734_, v___x_1733_);
lean_dec(v___x_1734_);
v___x_1757_ = l_Lean_SourceInfo_fromRef(v_a_1727_, v___x_1755_);
v___x_1758_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1759_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1757_, 3);
v___x_1760_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1757_);
lean_ctor_set(v___x_1760_, 1, v___x_1759_);
v___x_1761_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1762_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1757_);
lean_ctor_set(v___x_1762_, 1, v___x_1761_);
v___x_1763_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1764_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1764_, 0, v___x_1757_);
lean_ctor_set(v___x_1764_, 1, v___x_1763_);
v___x_1765_ = l_Lean_Syntax_node5(v___x_1757_, v___x_1758_, v___x_1760_, v___x_1740_, v___x_1762_, v___x_1756_, v___x_1764_);
v___x_1766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1766_, 0, v___x_1765_);
lean_ctor_set(v___x_1766_, 1, v_a_1728_);
return v___x_1766_;
}
else
{
lean_object* v___x_1767_; lean_object* v___x_1768_; uint8_t v___x_1769_; 
v___x_1767_ = l_Lean_Syntax_getArg(v___x_1740_, v___x_1735_);
v___x_1768_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__4));
lean_inc(v___x_1767_);
v___x_1769_ = l_Lean_Syntax_isOfKind(v___x_1767_, v___x_1768_);
if (v___x_1769_ == 0)
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
lean_dec(v___x_1767_);
v___x_1770_ = l_Lean_Syntax_getArg(v___x_1734_, v___x_1733_);
lean_dec(v___x_1734_);
v___x_1771_ = l_Lean_SourceInfo_fromRef(v_a_1727_, v___x_1769_);
v___x_1772_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1773_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1771_, 3);
v___x_1774_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1771_);
lean_ctor_set(v___x_1774_, 1, v___x_1773_);
v___x_1775_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1776_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1771_);
lean_ctor_set(v___x_1776_, 1, v___x_1775_);
v___x_1777_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1778_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1771_);
lean_ctor_set(v___x_1778_, 1, v___x_1777_);
v___x_1779_ = l_Lean_Syntax_node5(v___x_1771_, v___x_1772_, v___x_1774_, v___x_1740_, v___x_1776_, v___x_1770_, v___x_1778_);
v___x_1780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1779_);
lean_ctor_set(v___x_1780_, 1, v_a_1728_);
return v___x_1780_;
}
else
{
lean_object* v___x_1781_; lean_object* v___x_1782_; uint8_t v___x_1783_; 
v___x_1781_ = l_Lean_Syntax_getArg(v___x_1767_, v___x_1739_);
lean_dec(v___x_1767_);
v___x_1782_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_1781_);
v___x_1783_ = l_Lean_Syntax_matchesNull(v___x_1781_, v___x_1782_);
if (v___x_1783_ == 0)
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
lean_dec(v___x_1781_);
v___x_1784_ = l_Lean_Syntax_getArg(v___x_1734_, v___x_1733_);
lean_dec(v___x_1734_);
v___x_1785_ = l_Lean_SourceInfo_fromRef(v_a_1727_, v___x_1783_);
v___x_1786_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1787_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1785_, 3);
v___x_1788_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1785_);
lean_ctor_set(v___x_1788_, 1, v___x_1787_);
v___x_1789_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1790_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1785_);
lean_ctor_set(v___x_1790_, 1, v___x_1789_);
v___x_1791_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1792_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1785_);
lean_ctor_set(v___x_1792_, 1, v___x_1791_);
v___x_1793_ = l_Lean_Syntax_node5(v___x_1785_, v___x_1786_, v___x_1788_, v___x_1740_, v___x_1790_, v___x_1784_, v___x_1792_);
v___x_1794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1793_);
lean_ctor_set(v___x_1794_, 1, v_a_1728_);
return v___x_1794_;
}
else
{
lean_object* v___x_1795_; lean_object* v___x_1796_; uint8_t v___x_1797_; 
v___x_1795_ = l_Lean_Syntax_getArg(v___x_1781_, v___x_1739_);
v___x_1796_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__6));
lean_inc(v___x_1795_);
v___x_1797_ = l_Lean_Syntax_isOfKind(v___x_1795_, v___x_1796_);
if (v___x_1797_ == 0)
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
lean_dec(v___x_1795_);
lean_dec(v___x_1781_);
v___x_1798_ = l_Lean_Syntax_getArg(v___x_1734_, v___x_1733_);
lean_dec(v___x_1734_);
v___x_1799_ = l_Lean_SourceInfo_fromRef(v_a_1727_, v___x_1797_);
v___x_1800_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1801_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1799_, 3);
v___x_1802_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1799_);
lean_ctor_set(v___x_1802_, 1, v___x_1801_);
v___x_1803_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1804_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1799_);
lean_ctor_set(v___x_1804_, 1, v___x_1803_);
v___x_1805_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1806_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1799_);
lean_ctor_set(v___x_1806_, 1, v___x_1805_);
v___x_1807_ = l_Lean_Syntax_node5(v___x_1799_, v___x_1800_, v___x_1802_, v___x_1740_, v___x_1804_, v___x_1798_, v___x_1806_);
v___x_1808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1807_);
lean_ctor_set(v___x_1808_, 1, v_a_1728_);
return v___x_1808_;
}
else
{
lean_object* v___x_1809_; lean_object* v___x_1810_; uint8_t v___x_1811_; 
v___x_1809_ = l_Lean_Syntax_getArg(v___x_1795_, v___x_1739_);
v___x_1810_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__8));
lean_inc(v___x_1809_);
v___x_1811_ = l_Lean_Syntax_isOfKind(v___x_1809_, v___x_1810_);
if (v___x_1811_ == 0)
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
lean_dec(v___x_1809_);
lean_dec(v___x_1795_);
lean_dec(v___x_1781_);
v___x_1812_ = l_Lean_Syntax_getArg(v___x_1734_, v___x_1733_);
lean_dec(v___x_1734_);
v___x_1813_ = l_Lean_SourceInfo_fromRef(v_a_1727_, v___x_1811_);
v___x_1814_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1815_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1813_, 3);
v___x_1816_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1813_);
lean_ctor_set(v___x_1816_, 1, v___x_1815_);
v___x_1817_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1818_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1813_);
lean_ctor_set(v___x_1818_, 1, v___x_1817_);
v___x_1819_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1820_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1813_);
lean_ctor_set(v___x_1820_, 1, v___x_1819_);
v___x_1821_ = l_Lean_Syntax_node5(v___x_1813_, v___x_1814_, v___x_1816_, v___x_1740_, v___x_1818_, v___x_1812_, v___x_1820_);
v___x_1822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1821_);
lean_ctor_set(v___x_1822_, 1, v_a_1728_);
return v___x_1822_;
}
else
{
lean_object* v___x_1823_; lean_object* v___x_1824_; uint8_t v___x_1825_; 
v___x_1823_ = l_Lean_Syntax_getArg(v___x_1809_, v___x_1739_);
v___x_1824_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__10));
v___x_1825_ = l_Lean_Syntax_matchesIdent(v___x_1823_, v___x_1824_);
lean_dec(v___x_1823_);
if (v___x_1825_ == 0)
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
lean_dec(v___x_1809_);
lean_dec(v___x_1795_);
lean_dec(v___x_1781_);
v___x_1826_ = l_Lean_Syntax_getArg(v___x_1734_, v___x_1733_);
lean_dec(v___x_1734_);
v___x_1827_ = l_Lean_SourceInfo_fromRef(v_a_1727_, v___x_1825_);
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
v___x_1835_ = l_Lean_Syntax_node5(v___x_1827_, v___x_1828_, v___x_1830_, v___x_1740_, v___x_1832_, v___x_1826_, v___x_1834_);
v___x_1836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1835_);
lean_ctor_set(v___x_1836_, 1, v_a_1728_);
return v___x_1836_;
}
else
{
lean_object* v___x_1837_; uint8_t v___x_1838_; 
v___x_1837_ = l_Lean_Syntax_getArg(v___x_1809_, v___x_1733_);
lean_dec(v___x_1809_);
v___x_1838_ = l_Lean_Syntax_matchesNull(v___x_1837_, v___x_1739_);
if (v___x_1838_ == 0)
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
lean_dec(v___x_1795_);
lean_dec(v___x_1781_);
v___x_1839_ = l_Lean_Syntax_getArg(v___x_1734_, v___x_1733_);
lean_dec(v___x_1734_);
v___x_1840_ = l_Lean_SourceInfo_fromRef(v_a_1727_, v___x_1838_);
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
v___x_1848_ = l_Lean_Syntax_node5(v___x_1840_, v___x_1841_, v___x_1843_, v___x_1740_, v___x_1845_, v___x_1839_, v___x_1847_);
v___x_1849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1848_);
lean_ctor_set(v___x_1849_, 1, v_a_1728_);
return v___x_1849_;
}
else
{
lean_object* v___x_1850_; lean_object* v___x_1851_; uint8_t v___x_1852_; 
v___x_1850_ = l_Lean_Syntax_getArg(v___x_1795_, v___x_1733_);
lean_dec(v___x_1795_);
v___x_1851_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_1850_);
v___x_1852_ = l_Lean_Syntax_matchesNull(v___x_1850_, v___x_1851_);
if (v___x_1852_ == 0)
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
lean_dec(v___x_1850_);
lean_dec(v___x_1781_);
v___x_1853_ = l_Lean_Syntax_getArg(v___x_1734_, v___x_1733_);
lean_dec(v___x_1734_);
v___x_1854_ = l_Lean_SourceInfo_fromRef(v_a_1727_, v___x_1852_);
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
v___x_1862_ = l_Lean_Syntax_node5(v___x_1854_, v___x_1855_, v___x_1857_, v___x_1740_, v___x_1859_, v___x_1853_, v___x_1861_);
v___x_1863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1862_);
lean_ctor_set(v___x_1863_, 1, v_a_1728_);
return v___x_1863_;
}
else
{
lean_object* v___x_1864_; uint8_t v___x_1865_; 
v___x_1864_ = l_Lean_Syntax_getArg(v___x_1850_, v___x_1739_);
v___x_1865_ = l_Lean_Syntax_matchesNull(v___x_1864_, v___x_1739_);
if (v___x_1865_ == 0)
{
lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
lean_dec(v___x_1850_);
lean_dec(v___x_1781_);
v___x_1866_ = l_Lean_Syntax_getArg(v___x_1734_, v___x_1733_);
lean_dec(v___x_1734_);
v___x_1867_ = l_Lean_SourceInfo_fromRef(v_a_1727_, v___x_1865_);
v___x_1868_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1869_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1867_, 3);
v___x_1870_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1867_);
lean_ctor_set(v___x_1870_, 1, v___x_1869_);
v___x_1871_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1872_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1867_);
lean_ctor_set(v___x_1872_, 1, v___x_1871_);
v___x_1873_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1874_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1867_);
lean_ctor_set(v___x_1874_, 1, v___x_1873_);
v___x_1875_ = l_Lean_Syntax_node5(v___x_1867_, v___x_1868_, v___x_1870_, v___x_1740_, v___x_1872_, v___x_1866_, v___x_1874_);
v___x_1876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1875_);
lean_ctor_set(v___x_1876_, 1, v_a_1728_);
return v___x_1876_;
}
else
{
lean_object* v___x_1877_; uint8_t v___x_1878_; 
v___x_1877_ = l_Lean_Syntax_getArg(v___x_1850_, v___x_1733_);
v___x_1878_ = l_Lean_Syntax_matchesNull(v___x_1877_, v___x_1739_);
if (v___x_1878_ == 0)
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
lean_dec(v___x_1850_);
lean_dec(v___x_1781_);
v___x_1879_ = l_Lean_Syntax_getArg(v___x_1734_, v___x_1733_);
lean_dec(v___x_1734_);
v___x_1880_ = l_Lean_SourceInfo_fromRef(v_a_1727_, v___x_1878_);
v___x_1881_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1882_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1880_, 3);
v___x_1883_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1880_);
lean_ctor_set(v___x_1883_, 1, v___x_1882_);
v___x_1884_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1885_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1880_);
lean_ctor_set(v___x_1885_, 1, v___x_1884_);
v___x_1886_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1887_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1887_, 0, v___x_1880_);
lean_ctor_set(v___x_1887_, 1, v___x_1886_);
v___x_1888_ = l_Lean_Syntax_node5(v___x_1880_, v___x_1881_, v___x_1883_, v___x_1740_, v___x_1885_, v___x_1879_, v___x_1887_);
v___x_1889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1888_);
lean_ctor_set(v___x_1889_, 1, v_a_1728_);
return v___x_1889_;
}
else
{
lean_object* v___x_1890_; lean_object* v___x_1891_; uint8_t v___x_1892_; 
v___x_1890_ = l_Lean_Syntax_getArg(v___x_1850_, v___x_1735_);
lean_dec(v___x_1850_);
v___x_1891_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__12));
lean_inc(v___x_1890_);
v___x_1892_ = l_Lean_Syntax_isOfKind(v___x_1890_, v___x_1891_);
if (v___x_1892_ == 0)
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
lean_dec(v___x_1890_);
lean_dec(v___x_1781_);
v___x_1893_ = l_Lean_Syntax_getArg(v___x_1734_, v___x_1733_);
lean_dec(v___x_1734_);
v___x_1894_ = l_Lean_SourceInfo_fromRef(v_a_1727_, v___x_1892_);
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
v___x_1902_ = l_Lean_Syntax_node5(v___x_1894_, v___x_1895_, v___x_1897_, v___x_1740_, v___x_1899_, v___x_1893_, v___x_1901_);
v___x_1903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1902_);
lean_ctor_set(v___x_1903_, 1, v_a_1728_);
return v___x_1903_;
}
else
{
lean_object* v___x_1904_; uint8_t v___x_1905_; 
v___x_1904_ = l_Lean_Syntax_getArg(v___x_1890_, v___x_1733_);
v___x_1905_ = l_Lean_Syntax_matchesNull(v___x_1904_, v___x_1739_);
if (v___x_1905_ == 0)
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
lean_dec(v___x_1890_);
lean_dec(v___x_1781_);
v___x_1906_ = l_Lean_Syntax_getArg(v___x_1734_, v___x_1733_);
lean_dec(v___x_1734_);
v___x_1907_ = l_Lean_SourceInfo_fromRef(v_a_1727_, v___x_1905_);
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
v___x_1915_ = l_Lean_Syntax_node5(v___x_1907_, v___x_1908_, v___x_1910_, v___x_1740_, v___x_1912_, v___x_1906_, v___x_1914_);
v___x_1916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1915_);
lean_ctor_set(v___x_1916_, 1, v_a_1728_);
return v___x_1916_;
}
else
{
lean_object* v___x_1917_; uint8_t v___x_1918_; 
v___x_1917_ = l_Lean_Syntax_getArg(v___x_1781_, v___x_1735_);
lean_inc(v___x_1917_);
v___x_1918_ = l_Lean_Syntax_isOfKind(v___x_1917_, v___x_1796_);
if (v___x_1918_ == 0)
{
lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
lean_dec(v___x_1917_);
lean_dec(v___x_1890_);
lean_dec(v___x_1781_);
v___x_1919_ = l_Lean_Syntax_getArg(v___x_1734_, v___x_1733_);
lean_dec(v___x_1734_);
v___x_1920_ = l_Lean_SourceInfo_fromRef(v_a_1727_, v___x_1918_);
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
v___x_1928_ = l_Lean_Syntax_node5(v___x_1920_, v___x_1921_, v___x_1923_, v___x_1740_, v___x_1925_, v___x_1919_, v___x_1927_);
v___x_1929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1928_);
lean_ctor_set(v___x_1929_, 1, v_a_1728_);
return v___x_1929_;
}
else
{
lean_object* v___x_1930_; uint8_t v___x_1931_; 
v___x_1930_ = l_Lean_Syntax_getArg(v___x_1917_, v___x_1739_);
lean_inc(v___x_1930_);
v___x_1931_ = l_Lean_Syntax_isOfKind(v___x_1930_, v___x_1810_);
if (v___x_1931_ == 0)
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
lean_dec(v___x_1930_);
lean_dec(v___x_1917_);
lean_dec(v___x_1890_);
lean_dec(v___x_1781_);
v___x_1932_ = l_Lean_Syntax_getArg(v___x_1734_, v___x_1733_);
lean_dec(v___x_1734_);
v___x_1933_ = l_Lean_SourceInfo_fromRef(v_a_1727_, v___x_1931_);
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
v___x_1941_ = l_Lean_Syntax_node5(v___x_1933_, v___x_1934_, v___x_1936_, v___x_1740_, v___x_1938_, v___x_1932_, v___x_1940_);
v___x_1942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1941_);
lean_ctor_set(v___x_1942_, 1, v_a_1728_);
return v___x_1942_;
}
else
{
lean_object* v___x_1943_; lean_object* v___x_1944_; uint8_t v___x_1945_; 
v___x_1943_ = l_Lean_Syntax_getArg(v___x_1930_, v___x_1739_);
v___x_1944_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__14));
v___x_1945_ = l_Lean_Syntax_matchesIdent(v___x_1943_, v___x_1944_);
lean_dec(v___x_1943_);
if (v___x_1945_ == 0)
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; 
lean_dec(v___x_1930_);
lean_dec(v___x_1917_);
lean_dec(v___x_1890_);
lean_dec(v___x_1781_);
v___x_1946_ = l_Lean_Syntax_getArg(v___x_1734_, v___x_1733_);
lean_dec(v___x_1734_);
v___x_1947_ = l_Lean_SourceInfo_fromRef(v_a_1727_, v___x_1945_);
v___x_1948_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1949_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1947_, 3);
v___x_1950_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1947_);
lean_ctor_set(v___x_1950_, 1, v___x_1949_);
v___x_1951_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1952_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1947_);
lean_ctor_set(v___x_1952_, 1, v___x_1951_);
v___x_1953_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1954_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1947_);
lean_ctor_set(v___x_1954_, 1, v___x_1953_);
v___x_1955_ = l_Lean_Syntax_node5(v___x_1947_, v___x_1948_, v___x_1950_, v___x_1740_, v___x_1952_, v___x_1946_, v___x_1954_);
v___x_1956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1956_, 0, v___x_1955_);
lean_ctor_set(v___x_1956_, 1, v_a_1728_);
return v___x_1956_;
}
else
{
lean_object* v___x_1957_; uint8_t v___x_1958_; 
v___x_1957_ = l_Lean_Syntax_getArg(v___x_1930_, v___x_1733_);
lean_dec(v___x_1930_);
v___x_1958_ = l_Lean_Syntax_matchesNull(v___x_1957_, v___x_1739_);
if (v___x_1958_ == 0)
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
lean_dec(v___x_1917_);
lean_dec(v___x_1890_);
lean_dec(v___x_1781_);
v___x_1959_ = l_Lean_Syntax_getArg(v___x_1734_, v___x_1733_);
lean_dec(v___x_1734_);
v___x_1960_ = l_Lean_SourceInfo_fromRef(v_a_1727_, v___x_1958_);
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
v___x_1968_ = l_Lean_Syntax_node5(v___x_1960_, v___x_1961_, v___x_1963_, v___x_1740_, v___x_1965_, v___x_1959_, v___x_1967_);
v___x_1969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1968_);
lean_ctor_set(v___x_1969_, 1, v_a_1728_);
return v___x_1969_;
}
else
{
lean_object* v___x_1970_; uint8_t v___x_1971_; 
v___x_1970_ = l_Lean_Syntax_getArg(v___x_1917_, v___x_1733_);
lean_dec(v___x_1917_);
lean_inc(v___x_1970_);
v___x_1971_ = l_Lean_Syntax_matchesNull(v___x_1970_, v___x_1851_);
if (v___x_1971_ == 0)
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; 
lean_dec(v___x_1970_);
lean_dec(v___x_1890_);
lean_dec(v___x_1781_);
v___x_1972_ = l_Lean_Syntax_getArg(v___x_1734_, v___x_1733_);
lean_dec(v___x_1734_);
v___x_1973_ = l_Lean_SourceInfo_fromRef(v_a_1727_, v___x_1971_);
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
v___x_1981_ = l_Lean_Syntax_node5(v___x_1973_, v___x_1974_, v___x_1976_, v___x_1740_, v___x_1978_, v___x_1972_, v___x_1980_);
v___x_1982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1981_);
lean_ctor_set(v___x_1982_, 1, v_a_1728_);
return v___x_1982_;
}
else
{
lean_object* v___x_1983_; uint8_t v___x_1984_; 
v___x_1983_ = l_Lean_Syntax_getArg(v___x_1970_, v___x_1739_);
v___x_1984_ = l_Lean_Syntax_matchesNull(v___x_1983_, v___x_1739_);
if (v___x_1984_ == 0)
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
lean_dec(v___x_1970_);
lean_dec(v___x_1890_);
lean_dec(v___x_1781_);
v___x_1985_ = l_Lean_Syntax_getArg(v___x_1734_, v___x_1733_);
lean_dec(v___x_1734_);
v___x_1986_ = l_Lean_SourceInfo_fromRef(v_a_1727_, v___x_1984_);
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
v___x_1994_ = l_Lean_Syntax_node5(v___x_1986_, v___x_1987_, v___x_1989_, v___x_1740_, v___x_1991_, v___x_1985_, v___x_1993_);
v___x_1995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1994_);
lean_ctor_set(v___x_1995_, 1, v_a_1728_);
return v___x_1995_;
}
else
{
lean_object* v___x_1996_; uint8_t v___x_1997_; 
v___x_1996_ = l_Lean_Syntax_getArg(v___x_1970_, v___x_1733_);
v___x_1997_ = l_Lean_Syntax_matchesNull(v___x_1996_, v___x_1739_);
if (v___x_1997_ == 0)
{
lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
lean_dec(v___x_1970_);
lean_dec(v___x_1890_);
lean_dec(v___x_1781_);
v___x_1998_ = l_Lean_Syntax_getArg(v___x_1734_, v___x_1733_);
lean_dec(v___x_1734_);
v___x_1999_ = l_Lean_SourceInfo_fromRef(v_a_1727_, v___x_1997_);
v___x_2000_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2001_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1999_, 3);
v___x_2002_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2002_, 0, v___x_1999_);
lean_ctor_set(v___x_2002_, 1, v___x_2001_);
v___x_2003_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2004_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2004_, 0, v___x_1999_);
lean_ctor_set(v___x_2004_, 1, v___x_2003_);
v___x_2005_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2006_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2006_, 0, v___x_1999_);
lean_ctor_set(v___x_2006_, 1, v___x_2005_);
v___x_2007_ = l_Lean_Syntax_node5(v___x_1999_, v___x_2000_, v___x_2002_, v___x_1740_, v___x_2004_, v___x_1998_, v___x_2006_);
v___x_2008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2008_, 0, v___x_2007_);
lean_ctor_set(v___x_2008_, 1, v_a_1728_);
return v___x_2008_;
}
else
{
lean_object* v___x_2009_; uint8_t v___x_2010_; 
v___x_2009_ = l_Lean_Syntax_getArg(v___x_1970_, v___x_1735_);
lean_dec(v___x_1970_);
lean_inc(v___x_2009_);
v___x_2010_ = l_Lean_Syntax_isOfKind(v___x_2009_, v___x_1891_);
if (v___x_2010_ == 0)
{
lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
lean_dec(v___x_2009_);
lean_dec(v___x_1890_);
lean_dec(v___x_1781_);
v___x_2011_ = l_Lean_Syntax_getArg(v___x_1734_, v___x_1733_);
lean_dec(v___x_1734_);
v___x_2012_ = l_Lean_SourceInfo_fromRef(v_a_1727_, v___x_2010_);
v___x_2013_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2014_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2012_, 3);
v___x_2015_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2015_, 0, v___x_2012_);
lean_ctor_set(v___x_2015_, 1, v___x_2014_);
v___x_2016_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2017_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2012_);
lean_ctor_set(v___x_2017_, 1, v___x_2016_);
v___x_2018_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2019_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2012_);
lean_ctor_set(v___x_2019_, 1, v___x_2018_);
v___x_2020_ = l_Lean_Syntax_node5(v___x_2012_, v___x_2013_, v___x_2015_, v___x_1740_, v___x_2017_, v___x_2011_, v___x_2019_);
v___x_2021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2020_);
lean_ctor_set(v___x_2021_, 1, v_a_1728_);
return v___x_2021_;
}
else
{
lean_object* v___x_2022_; uint8_t v___x_2023_; 
v___x_2022_ = l_Lean_Syntax_getArg(v___x_2009_, v___x_1733_);
v___x_2023_ = l_Lean_Syntax_matchesNull(v___x_2022_, v___x_1739_);
if (v___x_2023_ == 0)
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
lean_dec(v___x_2009_);
lean_dec(v___x_1890_);
lean_dec(v___x_1781_);
v___x_2024_ = l_Lean_Syntax_getArg(v___x_1734_, v___x_1733_);
lean_dec(v___x_1734_);
v___x_2025_ = l_Lean_SourceInfo_fromRef(v_a_1727_, v___x_2023_);
v___x_2026_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2027_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2025_, 3);
v___x_2028_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2025_);
lean_ctor_set(v___x_2028_, 1, v___x_2027_);
v___x_2029_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2030_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2025_);
lean_ctor_set(v___x_2030_, 1, v___x_2029_);
v___x_2031_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2032_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2025_);
lean_ctor_set(v___x_2032_, 1, v___x_2031_);
v___x_2033_ = l_Lean_Syntax_node5(v___x_2025_, v___x_2026_, v___x_2028_, v___x_1740_, v___x_2030_, v___x_2024_, v___x_2032_);
v___x_2034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2033_);
lean_ctor_set(v___x_2034_, 1, v_a_1728_);
return v___x_2034_;
}
else
{
lean_object* v___x_2035_; lean_object* v___x_2036_; uint8_t v___x_2037_; 
v___x_2035_ = lean_unsigned_to_nat(4u);
v___x_2036_ = l_Lean_Syntax_getArg(v___x_1781_, v___x_2035_);
lean_dec(v___x_1781_);
lean_inc(v___x_2036_);
v___x_2037_ = l_Lean_Syntax_isOfKind(v___x_2036_, v___x_1796_);
if (v___x_2037_ == 0)
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; 
lean_dec(v___x_2036_);
lean_dec(v___x_2009_);
lean_dec(v___x_1890_);
v___x_2038_ = l_Lean_Syntax_getArg(v___x_1734_, v___x_1733_);
lean_dec(v___x_1734_);
v___x_2039_ = l_Lean_SourceInfo_fromRef(v_a_1727_, v___x_2037_);
v___x_2040_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2041_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2039_, 3);
v___x_2042_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2039_);
lean_ctor_set(v___x_2042_, 1, v___x_2041_);
v___x_2043_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2044_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2039_);
lean_ctor_set(v___x_2044_, 1, v___x_2043_);
v___x_2045_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2046_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2039_);
lean_ctor_set(v___x_2046_, 1, v___x_2045_);
v___x_2047_ = l_Lean_Syntax_node5(v___x_2039_, v___x_2040_, v___x_2042_, v___x_1740_, v___x_2044_, v___x_2038_, v___x_2046_);
v___x_2048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2047_);
lean_ctor_set(v___x_2048_, 1, v_a_1728_);
return v___x_2048_;
}
else
{
lean_object* v___x_2049_; uint8_t v___x_2050_; 
v___x_2049_ = l_Lean_Syntax_getArg(v___x_2036_, v___x_1739_);
lean_inc(v___x_2049_);
v___x_2050_ = l_Lean_Syntax_isOfKind(v___x_2049_, v___x_1810_);
if (v___x_2050_ == 0)
{
lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
lean_dec(v___x_2049_);
lean_dec(v___x_2036_);
lean_dec(v___x_2009_);
lean_dec(v___x_1890_);
v___x_2051_ = l_Lean_Syntax_getArg(v___x_1734_, v___x_1733_);
lean_dec(v___x_1734_);
v___x_2052_ = l_Lean_SourceInfo_fromRef(v_a_1727_, v___x_2050_);
v___x_2053_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2054_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2052_, 3);
v___x_2055_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2052_);
lean_ctor_set(v___x_2055_, 1, v___x_2054_);
v___x_2056_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2057_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2057_, 0, v___x_2052_);
lean_ctor_set(v___x_2057_, 1, v___x_2056_);
v___x_2058_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2059_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2052_);
lean_ctor_set(v___x_2059_, 1, v___x_2058_);
v___x_2060_ = l_Lean_Syntax_node5(v___x_2052_, v___x_2053_, v___x_2055_, v___x_1740_, v___x_2057_, v___x_2051_, v___x_2059_);
v___x_2061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2060_);
lean_ctor_set(v___x_2061_, 1, v_a_1728_);
return v___x_2061_;
}
else
{
lean_object* v___x_2062_; lean_object* v___x_2063_; uint8_t v___x_2064_; 
v___x_2062_ = l_Lean_Syntax_getArg(v___x_2049_, v___x_1739_);
v___x_2063_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__16));
v___x_2064_ = l_Lean_Syntax_matchesIdent(v___x_2062_, v___x_2063_);
lean_dec(v___x_2062_);
if (v___x_2064_ == 0)
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
lean_dec(v___x_2049_);
lean_dec(v___x_2036_);
lean_dec(v___x_2009_);
lean_dec(v___x_1890_);
v___x_2065_ = l_Lean_Syntax_getArg(v___x_1734_, v___x_1733_);
lean_dec(v___x_1734_);
v___x_2066_ = l_Lean_SourceInfo_fromRef(v_a_1727_, v___x_2064_);
v___x_2067_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2068_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2066_, 3);
v___x_2069_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2066_);
lean_ctor_set(v___x_2069_, 1, v___x_2068_);
v___x_2070_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2071_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2066_);
lean_ctor_set(v___x_2071_, 1, v___x_2070_);
v___x_2072_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2073_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2066_);
lean_ctor_set(v___x_2073_, 1, v___x_2072_);
v___x_2074_ = l_Lean_Syntax_node5(v___x_2066_, v___x_2067_, v___x_2069_, v___x_1740_, v___x_2071_, v___x_2065_, v___x_2073_);
v___x_2075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2074_);
lean_ctor_set(v___x_2075_, 1, v_a_1728_);
return v___x_2075_;
}
else
{
lean_object* v___x_2076_; uint8_t v___x_2077_; 
v___x_2076_ = l_Lean_Syntax_getArg(v___x_2049_, v___x_1733_);
lean_dec(v___x_2049_);
v___x_2077_ = l_Lean_Syntax_matchesNull(v___x_2076_, v___x_1739_);
if (v___x_2077_ == 0)
{
lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
lean_dec(v___x_2036_);
lean_dec(v___x_2009_);
lean_dec(v___x_1890_);
v___x_2078_ = l_Lean_Syntax_getArg(v___x_1734_, v___x_1733_);
lean_dec(v___x_1734_);
v___x_2079_ = l_Lean_SourceInfo_fromRef(v_a_1727_, v___x_2077_);
v___x_2080_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2081_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2079_, 3);
v___x_2082_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2079_);
lean_ctor_set(v___x_2082_, 1, v___x_2081_);
v___x_2083_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2084_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2079_);
lean_ctor_set(v___x_2084_, 1, v___x_2083_);
v___x_2085_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2086_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2079_);
lean_ctor_set(v___x_2086_, 1, v___x_2085_);
v___x_2087_ = l_Lean_Syntax_node5(v___x_2079_, v___x_2080_, v___x_2082_, v___x_1740_, v___x_2084_, v___x_2078_, v___x_2086_);
v___x_2088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2087_);
lean_ctor_set(v___x_2088_, 1, v_a_1728_);
return v___x_2088_;
}
else
{
lean_object* v___x_2089_; uint8_t v___x_2090_; 
v___x_2089_ = l_Lean_Syntax_getArg(v___x_2036_, v___x_1733_);
lean_dec(v___x_2036_);
lean_inc(v___x_2089_);
v___x_2090_ = l_Lean_Syntax_matchesNull(v___x_2089_, v___x_1851_);
if (v___x_2090_ == 0)
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
lean_dec(v___x_2089_);
lean_dec(v___x_2009_);
lean_dec(v___x_1890_);
v___x_2091_ = l_Lean_Syntax_getArg(v___x_1734_, v___x_1733_);
lean_dec(v___x_1734_);
v___x_2092_ = l_Lean_SourceInfo_fromRef(v_a_1727_, v___x_2090_);
v___x_2093_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2094_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2092_, 3);
v___x_2095_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2092_);
lean_ctor_set(v___x_2095_, 1, v___x_2094_);
v___x_2096_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2097_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2092_);
lean_ctor_set(v___x_2097_, 1, v___x_2096_);
v___x_2098_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2099_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2092_);
lean_ctor_set(v___x_2099_, 1, v___x_2098_);
v___x_2100_ = l_Lean_Syntax_node5(v___x_2092_, v___x_2093_, v___x_2095_, v___x_1740_, v___x_2097_, v___x_2091_, v___x_2099_);
v___x_2101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2100_);
lean_ctor_set(v___x_2101_, 1, v_a_1728_);
return v___x_2101_;
}
else
{
lean_object* v___x_2102_; uint8_t v___x_2103_; 
v___x_2102_ = l_Lean_Syntax_getArg(v___x_2089_, v___x_1739_);
v___x_2103_ = l_Lean_Syntax_matchesNull(v___x_2102_, v___x_1739_);
if (v___x_2103_ == 0)
{
lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
lean_dec(v___x_2089_);
lean_dec(v___x_2009_);
lean_dec(v___x_1890_);
v___x_2104_ = l_Lean_Syntax_getArg(v___x_1734_, v___x_1733_);
lean_dec(v___x_1734_);
v___x_2105_ = l_Lean_SourceInfo_fromRef(v_a_1727_, v___x_2103_);
v___x_2106_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2107_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2105_, 3);
v___x_2108_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2105_);
lean_ctor_set(v___x_2108_, 1, v___x_2107_);
v___x_2109_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2110_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2105_);
lean_ctor_set(v___x_2110_, 1, v___x_2109_);
v___x_2111_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2112_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2105_);
lean_ctor_set(v___x_2112_, 1, v___x_2111_);
v___x_2113_ = l_Lean_Syntax_node5(v___x_2105_, v___x_2106_, v___x_2108_, v___x_1740_, v___x_2110_, v___x_2104_, v___x_2112_);
v___x_2114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2113_);
lean_ctor_set(v___x_2114_, 1, v_a_1728_);
return v___x_2114_;
}
else
{
lean_object* v___x_2115_; uint8_t v___x_2116_; 
v___x_2115_ = l_Lean_Syntax_getArg(v___x_2089_, v___x_1733_);
v___x_2116_ = l_Lean_Syntax_matchesNull(v___x_2115_, v___x_1739_);
if (v___x_2116_ == 0)
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
lean_dec(v___x_2089_);
lean_dec(v___x_2009_);
lean_dec(v___x_1890_);
v___x_2117_ = l_Lean_Syntax_getArg(v___x_1734_, v___x_1733_);
lean_dec(v___x_1734_);
v___x_2118_ = l_Lean_SourceInfo_fromRef(v_a_1727_, v___x_2116_);
v___x_2119_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2120_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2118_, 3);
v___x_2121_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2118_);
lean_ctor_set(v___x_2121_, 1, v___x_2120_);
v___x_2122_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2123_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2118_);
lean_ctor_set(v___x_2123_, 1, v___x_2122_);
v___x_2124_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2125_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2118_);
lean_ctor_set(v___x_2125_, 1, v___x_2124_);
v___x_2126_ = l_Lean_Syntax_node5(v___x_2118_, v___x_2119_, v___x_2121_, v___x_1740_, v___x_2123_, v___x_2117_, v___x_2125_);
v___x_2127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
lean_ctor_set(v___x_2127_, 1, v_a_1728_);
return v___x_2127_;
}
else
{
lean_object* v___x_2128_; uint8_t v___x_2129_; 
v___x_2128_ = l_Lean_Syntax_getArg(v___x_2089_, v___x_1735_);
lean_dec(v___x_2089_);
lean_inc(v___x_2128_);
v___x_2129_ = l_Lean_Syntax_isOfKind(v___x_2128_, v___x_1891_);
if (v___x_2129_ == 0)
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
lean_dec(v___x_2128_);
lean_dec(v___x_2009_);
lean_dec(v___x_1890_);
v___x_2130_ = l_Lean_Syntax_getArg(v___x_1734_, v___x_1733_);
lean_dec(v___x_1734_);
v___x_2131_ = l_Lean_SourceInfo_fromRef(v_a_1727_, v___x_2129_);
v___x_2132_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2133_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2131_, 3);
v___x_2134_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2131_);
lean_ctor_set(v___x_2134_, 1, v___x_2133_);
v___x_2135_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2136_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2131_);
lean_ctor_set(v___x_2136_, 1, v___x_2135_);
v___x_2137_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2138_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2138_, 0, v___x_2131_);
lean_ctor_set(v___x_2138_, 1, v___x_2137_);
v___x_2139_ = l_Lean_Syntax_node5(v___x_2131_, v___x_2132_, v___x_2134_, v___x_1740_, v___x_2136_, v___x_2130_, v___x_2138_);
v___x_2140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2139_);
lean_ctor_set(v___x_2140_, 1, v_a_1728_);
return v___x_2140_;
}
else
{
lean_object* v___x_2141_; uint8_t v___x_2142_; 
v___x_2141_ = l_Lean_Syntax_getArg(v___x_2128_, v___x_1733_);
v___x_2142_ = l_Lean_Syntax_matchesNull(v___x_2141_, v___x_1739_);
if (v___x_2142_ == 0)
{
lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
lean_dec(v___x_2128_);
lean_dec(v___x_2009_);
lean_dec(v___x_1890_);
v___x_2143_ = l_Lean_Syntax_getArg(v___x_1734_, v___x_1733_);
lean_dec(v___x_1734_);
v___x_2144_ = l_Lean_SourceInfo_fromRef(v_a_1727_, v___x_2142_);
v___x_2145_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2146_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2144_, 3);
v___x_2147_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2144_);
lean_ctor_set(v___x_2147_, 1, v___x_2146_);
v___x_2148_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2149_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2144_);
lean_ctor_set(v___x_2149_, 1, v___x_2148_);
v___x_2150_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2151_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2144_);
lean_ctor_set(v___x_2151_, 1, v___x_2150_);
v___x_2152_ = l_Lean_Syntax_node5(v___x_2144_, v___x_2145_, v___x_2147_, v___x_1740_, v___x_2149_, v___x_2143_, v___x_2151_);
v___x_2153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2152_);
lean_ctor_set(v___x_2153_, 1, v_a_1728_);
return v___x_2153_;
}
else
{
lean_object* v___x_2154_; lean_object* v___x_2155_; uint8_t v___x_2156_; 
v___x_2154_ = l_Lean_Syntax_getArg(v___x_1740_, v___x_1851_);
v___x_2155_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__18));
lean_inc(v___x_2154_);
v___x_2156_ = l_Lean_Syntax_isOfKind(v___x_2154_, v___x_2155_);
if (v___x_2156_ == 0)
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
lean_dec(v___x_2154_);
lean_dec(v___x_2128_);
lean_dec(v___x_2009_);
lean_dec(v___x_1890_);
v___x_2157_ = l_Lean_Syntax_getArg(v___x_1734_, v___x_1733_);
lean_dec(v___x_1734_);
v___x_2158_ = l_Lean_SourceInfo_fromRef(v_a_1727_, v___x_2156_);
v___x_2159_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2160_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2158_, 3);
v___x_2161_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2158_);
lean_ctor_set(v___x_2161_, 1, v___x_2160_);
v___x_2162_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2163_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2158_);
lean_ctor_set(v___x_2163_, 1, v___x_2162_);
v___x_2164_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2165_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2158_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
v___x_2166_ = l_Lean_Syntax_node5(v___x_2158_, v___x_2159_, v___x_2161_, v___x_1740_, v___x_2163_, v___x_2157_, v___x_2165_);
v___x_2167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2167_, 0, v___x_2166_);
lean_ctor_set(v___x_2167_, 1, v_a_1728_);
return v___x_2167_;
}
else
{
lean_object* v___x_2168_; uint8_t v___x_2169_; 
v___x_2168_ = l_Lean_Syntax_getArg(v___x_2154_, v___x_1739_);
lean_dec(v___x_2154_);
v___x_2169_ = l_Lean_Syntax_matchesNull(v___x_2168_, v___x_1739_);
if (v___x_2169_ == 0)
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
lean_dec(v___x_2128_);
lean_dec(v___x_2009_);
lean_dec(v___x_1890_);
v___x_2170_ = l_Lean_Syntax_getArg(v___x_1734_, v___x_1733_);
lean_dec(v___x_1734_);
v___x_2171_ = l_Lean_SourceInfo_fromRef(v_a_1727_, v___x_2169_);
v___x_2172_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2173_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2171_, 3);
v___x_2174_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2171_);
lean_ctor_set(v___x_2174_, 1, v___x_2173_);
v___x_2175_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2176_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2171_);
lean_ctor_set(v___x_2176_, 1, v___x_2175_);
v___x_2177_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2178_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2178_, 0, v___x_2171_);
lean_ctor_set(v___x_2178_, 1, v___x_2177_);
v___x_2179_ = l_Lean_Syntax_node5(v___x_2171_, v___x_2172_, v___x_2174_, v___x_1740_, v___x_2176_, v___x_2170_, v___x_2178_);
v___x_2180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2179_);
lean_ctor_set(v___x_2180_, 1, v_a_1728_);
return v___x_2180_;
}
else
{
lean_object* v___x_2181_; uint8_t v___x_2182_; 
v___x_2181_ = l_Lean_Syntax_getArg(v___x_1740_, v___x_2035_);
v___x_2182_ = l_Lean_Syntax_matchesNull(v___x_2181_, v___x_1739_);
if (v___x_2182_ == 0)
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
lean_dec(v___x_2128_);
lean_dec(v___x_2009_);
lean_dec(v___x_1890_);
v___x_2183_ = l_Lean_Syntax_getArg(v___x_1734_, v___x_1733_);
lean_dec(v___x_1734_);
v___x_2184_ = l_Lean_SourceInfo_fromRef(v_a_1727_, v___x_2182_);
v___x_2185_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2186_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2184_, 3);
v___x_2187_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2187_, 0, v___x_2184_);
lean_ctor_set(v___x_2187_, 1, v___x_2186_);
v___x_2188_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2189_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2184_);
lean_ctor_set(v___x_2189_, 1, v___x_2188_);
v___x_2190_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2191_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2184_);
lean_ctor_set(v___x_2191_, 1, v___x_2190_);
v___x_2192_ = l_Lean_Syntax_node5(v___x_2184_, v___x_2185_, v___x_2187_, v___x_1740_, v___x_2189_, v___x_2183_, v___x_2191_);
v___x_2193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2192_);
lean_ctor_set(v___x_2193_, 1, v_a_1728_);
return v___x_2193_;
}
else
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; uint8_t v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
lean_dec(v___x_1740_);
v___x_2194_ = l_Lean_Syntax_getArg(v___x_1890_, v___x_1735_);
lean_dec(v___x_1890_);
v___x_2195_ = l_Lean_Syntax_getArg(v___x_2009_, v___x_1735_);
lean_dec(v___x_2009_);
v___x_2196_ = l_Lean_Syntax_getArg(v___x_2128_, v___x_1735_);
lean_dec(v___x_2128_);
v___x_2197_ = l_Lean_Syntax_getArg(v___x_1734_, v___x_1733_);
lean_dec(v___x_1734_);
v___x_2198_ = 0;
v___x_2199_ = l_Lean_SourceInfo_fromRef(v_a_1727_, v___x_2198_);
v___x_2200_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__1));
v___x_2201_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2199_, 7);
v___x_2202_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2199_);
lean_ctor_set(v___x_2202_, 1, v___x_2201_);
v___x_2203_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2204_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2199_);
lean_ctor_set(v___x_2204_, 1, v___x_2203_);
v___x_2205_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__20));
v___x_2206_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__21));
v___x_2207_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2199_);
lean_ctor_set(v___x_2207_, 1, v___x_2206_);
v___x_2208_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__9));
lean_inc_ref_n(v___x_2204_, 2);
v___x_2209_ = l_Lean_Syntax_node3(v___x_2199_, v___x_2208_, v___x_2195_, v___x_2204_, v___x_2196_);
v___x_2210_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__22));
v___x_2211_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2199_);
lean_ctor_set(v___x_2211_, 1, v___x_2210_);
v___x_2212_ = l_Lean_Syntax_node3(v___x_2199_, v___x_2205_, v___x_2207_, v___x_2209_, v___x_2211_);
v___x_2213_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2214_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2199_);
lean_ctor_set(v___x_2214_, 1, v___x_2213_);
v___x_2215_ = l_Lean_Syntax_node7(v___x_2199_, v___x_2200_, v___x_2202_, v___x_2194_, v___x_2204_, v___x_2212_, v___x_2204_, v___x_2197_, v___x_2214_);
v___x_2216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2215_);
lean_ctor_set(v___x_2216_, 1, v_a_1728_);
return v___x_2216_;
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_unexpandDenote___boxed(lean_object* v_x_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_){
_start:
{
lean_object* v_res_2220_; 
v_res_2220_ = l_Std_Sat_AIG_unexpandDenote(v_x_2217_, v_a_2218_, v_a_2219_);
lean_dec(v_a_2218_);
return v_res_2220_;
}
}
uint8_t l_Std_Sat_AIG_isConstant___redArg(lean_object* v_aig_2221_, lean_object* v_ref_2222_, uint8_t v_b_2223_){
_start:
{
lean_object* v_gate_2224_; uint8_t v_invert_2225_; lean_object* v_decls_2226_; lean_object* v_decl_2227_; 
v_gate_2224_ = lean_ctor_get(v_ref_2222_, 0);
v_invert_2225_ = lean_ctor_get_uint8(v_ref_2222_, sizeof(void*)*1);
v_decls_2226_ = lean_ctor_get(v_aig_2221_, 0);
v_decl_2227_ = lean_array_fget_borrowed(v_decls_2226_, v_gate_2224_);
if (lean_obj_tag(v_decl_2227_) == 0)
{
if (v_b_2223_ == 0)
{
if (v_invert_2225_ == 0)
{
uint8_t v___x_2228_; 
v___x_2228_ = 1;
return v___x_2228_;
}
else
{
return v_b_2223_;
}
}
else
{
return v_invert_2225_;
}
}
else
{
uint8_t v___x_2229_; 
v___x_2229_ = 0;
return v___x_2229_;
}
}
}
LEAN_EXPORT void l_Std_Sat_AIG_isConstant___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_aig_2221_ = stack[0].m_obj;
lean_object* v_ref_2222_ = stack[1].m_obj;
uint8_t v_b_2223_ = stack[2].m_num;
uint8_t v_res_2230_;
v_res_2230_ = l_Std_Sat_AIG_isConstant___redArg(v_aig_2221_, v_ref_2222_, v_b_2223_);
stack->m_num = v_res_2230_;
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_isConstant___redArg___boxed(lean_object* v_aig_2231_, lean_object* v_ref_2232_, lean_object* v_b_2233_){
_start:
{
uint8_t v_b_boxed_2234_; uint8_t v_res_2235_; lean_object* v_r_2236_; 
v_b_boxed_2234_ = lean_unbox(v_b_2233_);
v_res_2235_ = l_Std_Sat_AIG_isConstant___redArg(v_aig_2231_, v_ref_2232_, v_b_boxed_2234_);
lean_dec_ref(v_ref_2232_);
lean_dec_ref(v_aig_2231_);
v_r_2236_ = lean_box(v_res_2235_);
return v_r_2236_;
}
}
uint8_t l_Std_Sat_AIG_isConstant(lean_object* v_00_u03b1_2237_, lean_object* v_inst_2238_, lean_object* v_inst_2239_, lean_object* v_aig_2240_, lean_object* v_ref_2241_, uint8_t v_b_2242_){
_start:
{
uint8_t v___x_2243_; 
v___x_2243_ = l_Std_Sat_AIG_isConstant___redArg(v_aig_2240_, v_ref_2241_, v_b_2242_);
return v___x_2243_;
}
}
LEAN_EXPORT void l_Std_Sat_AIG_isConstant_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2238_ = stack[1].m_obj;
lean_object* v_inst_2239_ = stack[2].m_obj;
lean_object* v_aig_2240_ = stack[3].m_obj;
lean_object* v_ref_2241_ = stack[4].m_obj;
uint8_t v_b_2242_ = stack[5].m_num;
uint8_t v_res_2244_;
v_res_2244_ = l_Std_Sat_AIG_isConstant(lean_box(0), v_inst_2238_, v_inst_2239_, v_aig_2240_, v_ref_2241_, v_b_2242_);
stack->m_num = v_res_2244_;
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_isConstant___boxed(lean_object* v_00_u03b1_2245_, lean_object* v_inst_2246_, lean_object* v_inst_2247_, lean_object* v_aig_2248_, lean_object* v_ref_2249_, lean_object* v_b_2250_){
_start:
{
uint8_t v_b_boxed_2251_; uint8_t v_res_2252_; lean_object* v_r_2253_; 
v_b_boxed_2251_ = lean_unbox(v_b_2250_);
v_res_2252_ = l_Std_Sat_AIG_isConstant(v_00_u03b1_2245_, v_inst_2246_, v_inst_2247_, v_aig_2248_, v_ref_2249_, v_b_boxed_2251_);
lean_dec_ref(v_ref_2249_);
lean_dec_ref(v_aig_2248_);
lean_dec_ref(v_inst_2247_);
lean_dec_ref(v_inst_2246_);
v_r_2253_ = lean_box(v_res_2252_);
return v_r_2253_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___redArg(lean_object* v_aig_2254_, lean_object* v_ref_2255_){
_start:
{
lean_object* v_gate_2256_; uint8_t v_invert_2257_; lean_object* v_decls_2258_; lean_object* v_decl_2259_; 
v_gate_2256_ = lean_ctor_get(v_ref_2255_, 0);
v_invert_2257_ = lean_ctor_get_uint8(v_ref_2255_, sizeof(void*)*1);
v_decls_2258_ = lean_ctor_get(v_aig_2254_, 0);
v_decl_2259_ = lean_array_fget_borrowed(v_decls_2258_, v_gate_2256_);
if (lean_obj_tag(v_decl_2259_) == 0)
{
lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2260_ = lean_box(v_invert_2257_);
v___x_2261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2260_);
return v___x_2261_;
}
else
{
lean_object* v___x_2262_; 
v___x_2262_ = lean_box(0);
return v___x_2262_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___redArg___boxed(lean_object* v_aig_2263_, lean_object* v_ref_2264_){
_start:
{
lean_object* v_res_2265_; 
v_res_2265_ = l_Std_Sat_AIG_getConstant___redArg(v_aig_2263_, v_ref_2264_);
lean_dec_ref(v_ref_2264_);
lean_dec_ref(v_aig_2263_);
return v_res_2265_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant(lean_object* v_00_u03b1_2266_, lean_object* v_inst_2267_, lean_object* v_inst_2268_, lean_object* v_aig_2269_, lean_object* v_ref_2270_){
_start:
{
lean_object* v___x_2271_; 
v___x_2271_ = l_Std_Sat_AIG_getConstant___redArg(v_aig_2269_, v_ref_2270_);
return v___x_2271_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___boxed(lean_object* v_00_u03b1_2272_, lean_object* v_inst_2273_, lean_object* v_inst_2274_, lean_object* v_aig_2275_, lean_object* v_ref_2276_){
_start:
{
lean_object* v_res_2277_; 
v_res_2277_ = l_Std_Sat_AIG_getConstant(v_00_u03b1_2272_, v_inst_2273_, v_inst_2274_, v_aig_2275_, v_ref_2276_);
lean_dec_ref(v_ref_2276_);
lean_dec_ref(v_aig_2275_);
lean_dec_ref(v_inst_2274_);
lean_dec_ref(v_inst_2273_);
return v_res_2277_;
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
