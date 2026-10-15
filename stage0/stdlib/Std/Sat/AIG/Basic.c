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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_ctorIdx___impl___redArg(lean_object* v_x_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = lean_obj_tag_nat(v_x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_ctorIdx___impl___redArg___boxed(lean_object* v_x_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Std_Sat_AIG_Decl_ctorIdx___impl___redArg(v_x_111_);
lean_dec(v_x_111_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_ctorIdx___impl(lean_object* v_00_u03b1_113_, lean_object* v_x_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = lean_obj_tag_nat(v_x_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_ctorIdx___impl___boxed(lean_object* v_00_u03b1_116_, lean_object* v_x_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Std_Sat_AIG_Decl_ctorIdx___impl(v_00_u03b1_116_, v_x_117_);
lean_dec(v_x_117_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_ctorElim___redArg(lean_object* v_t_119_, lean_object* v_k_120_){
_start:
{
switch(lean_obj_tag(v_t_119_))
{
case 0:
{
return v_k_120_;
}
case 1:
{
lean_object* v_idx_121_; lean_object* v___x_122_; 
v_idx_121_ = lean_ctor_get(v_t_119_, 0);
lean_inc(v_idx_121_);
lean_dec_ref_known(v_t_119_, 1);
v___x_122_ = lean_apply_1(v_k_120_, v_idx_121_);
return v___x_122_;
}
default: 
{
lean_object* v_l_123_; lean_object* v_r_124_; lean_object* v___x_125_; 
v_l_123_ = lean_ctor_get(v_t_119_, 0);
lean_inc(v_l_123_);
v_r_124_ = lean_ctor_get(v_t_119_, 1);
lean_inc(v_r_124_);
lean_dec_ref_known(v_t_119_, 2);
v___x_125_ = lean_apply_2(v_k_120_, v_l_123_, v_r_124_);
return v___x_125_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_ctorElim(lean_object* v_00_u03b1_126_, lean_object* v_motive_127_, lean_object* v_ctorIdx_128_, lean_object* v_t_129_, lean_object* v_h_130_, lean_object* v_k_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = l_Std_Sat_AIG_Decl_ctorElim___redArg(v_t_129_, v_k_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_ctorElim___boxed(lean_object* v_00_u03b1_133_, lean_object* v_motive_134_, lean_object* v_ctorIdx_135_, lean_object* v_t_136_, lean_object* v_h_137_, lean_object* v_k_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Std_Sat_AIG_Decl_ctorElim(v_00_u03b1_133_, v_motive_134_, v_ctorIdx_135_, v_t_136_, v_h_137_, v_k_138_);
lean_dec(v_ctorIdx_135_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_false_elim___redArg(lean_object* v_t_140_, lean_object* v_false_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = l_Std_Sat_AIG_Decl_ctorElim___redArg(v_t_140_, v_false_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_false_elim(lean_object* v_00_u03b1_143_, lean_object* v_motive_144_, lean_object* v_t_145_, lean_object* v_h_146_, lean_object* v_false_147_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Std_Sat_AIG_Decl_ctorElim___redArg(v_t_145_, v_false_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_atom_elim___redArg(lean_object* v_t_149_, lean_object* v_atom_150_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = l_Std_Sat_AIG_Decl_ctorElim___redArg(v_t_149_, v_atom_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_atom_elim(lean_object* v_00_u03b1_152_, lean_object* v_motive_153_, lean_object* v_t_154_, lean_object* v_h_155_, lean_object* v_atom_156_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l_Std_Sat_AIG_Decl_ctorElim___redArg(v_t_154_, v_atom_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_gate_elim___redArg(lean_object* v_t_158_, lean_object* v_gate_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l_Std_Sat_AIG_Decl_ctorElim___redArg(v_t_158_, v_gate_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_gate_elim(lean_object* v_00_u03b1_161_, lean_object* v_motive_162_, lean_object* v_t_163_, lean_object* v_h_164_, lean_object* v_gate_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = l_Std_Sat_AIG_Decl_ctorElim___redArg(v_t_163_, v_gate_165_);
return v___x_166_;
}
}
LEAN_EXPORT uint64_t l_Std_Sat_AIG_instHashableDecl_hash___redArg(lean_object* v_inst_167_, lean_object* v_x_168_){
_start:
{
switch(lean_obj_tag(v_x_168_))
{
case 0:
{
uint64_t v___x_169_; 
lean_dec_ref(v_inst_167_);
v___x_169_ = 0ULL;
return v___x_169_;
}
case 1:
{
lean_object* v_idx_170_; uint64_t v___x_171_; lean_object* v___x_172_; uint64_t v___x_173_; uint64_t v___x_174_; 
v_idx_170_ = lean_ctor_get(v_x_168_, 0);
lean_inc(v_idx_170_);
lean_dec_ref_known(v_x_168_, 1);
v___x_171_ = 1ULL;
v___x_172_ = lean_apply_1(v_inst_167_, v_idx_170_);
v___x_173_ = lean_unbox_uint64(v___x_172_);
lean_dec_ref(v___x_172_);
v___x_174_ = lean_uint64_mix_hash(v___x_171_, v___x_173_);
return v___x_174_;
}
default: 
{
lean_object* v_l_175_; lean_object* v_r_176_; uint64_t v___x_177_; uint64_t v___x_178_; uint64_t v___x_179_; uint64_t v___x_180_; uint64_t v___x_181_; 
lean_dec_ref(v_inst_167_);
v_l_175_ = lean_ctor_get(v_x_168_, 0);
lean_inc(v_l_175_);
v_r_176_ = lean_ctor_get(v_x_168_, 1);
lean_inc(v_r_176_);
lean_dec_ref_known(v_x_168_, 2);
v___x_177_ = 2ULL;
v___x_178_ = l_Std_Sat_AIG_instHashableFanin_hash(v_l_175_);
lean_dec(v_l_175_);
v___x_179_ = lean_uint64_mix_hash(v___x_177_, v___x_178_);
v___x_180_ = l_Std_Sat_AIG_instHashableFanin_hash(v_r_176_);
lean_dec(v_r_176_);
v___x_181_ = lean_uint64_mix_hash(v___x_179_, v___x_180_);
return v___x_181_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableDecl_hash___redArg___boxed(lean_object* v_inst_182_, lean_object* v_x_183_){
_start:
{
uint64_t v_res_184_; lean_object* v_r_185_; 
v_res_184_ = l_Std_Sat_AIG_instHashableDecl_hash___redArg(v_inst_182_, v_x_183_);
v_r_185_ = lean_box_uint64(v_res_184_);
return v_r_185_;
}
}
LEAN_EXPORT uint64_t l_Std_Sat_AIG_instHashableDecl_hash(lean_object* v_00_u03b1_186_, lean_object* v_inst_187_, lean_object* v_x_188_){
_start:
{
uint64_t v___x_189_; 
v___x_189_ = l_Std_Sat_AIG_instHashableDecl_hash___redArg(v_inst_187_, v_x_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableDecl_hash___boxed(lean_object* v_00_u03b1_190_, lean_object* v_inst_191_, lean_object* v_x_192_){
_start:
{
uint64_t v_res_193_; lean_object* v_r_194_; 
v_res_193_ = l_Std_Sat_AIG_instHashableDecl_hash(v_00_u03b1_190_, v_inst_191_, v_x_192_);
v_r_194_ = lean_box_uint64(v_res_193_);
return v_r_194_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableDecl___redArg(lean_object* v_inst_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_196_, 0, lean_box(0));
lean_closure_set(v___x_196_, 1, v_inst_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableDecl(lean_object* v_00_u03b1_197_, lean_object* v_inst_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_199_, 0, lean_box(0));
lean_closure_set(v___x_199_, 1, v_inst_198_);
return v___x_199_;
}
}
static lean_object* _init_l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = lean_unsigned_to_nat(2u);
v___x_204_ = lean_nat_to_int(v___x_203_);
return v___x_204_;
}
}
static lean_object* _init_l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3(void){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = lean_unsigned_to_nat(1u);
v___x_206_ = lean_nat_to_int(v___x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprDecl_repr___redArg(lean_object* v_inst_219_, lean_object* v_x_220_, lean_object* v_prec_221_){
_start:
{
lean_object* v___y_223_; 
switch(lean_obj_tag(v_x_220_))
{
case 0:
{
lean_object* v___x_229_; uint8_t v___x_230_; 
lean_dec_ref(v_inst_219_);
v___x_229_ = lean_unsigned_to_nat(1024u);
v___x_230_ = lean_nat_dec_le(v___x_229_, v_prec_221_);
if (v___x_230_ == 0)
{
lean_object* v___x_231_; 
v___x_231_ = lean_obj_once(&l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2, &l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2_once, _init_l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2);
v___y_223_ = v___x_231_;
goto v___jp_222_;
}
else
{
lean_object* v___x_232_; 
v___x_232_ = lean_obj_once(&l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3, &l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3_once, _init_l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3);
v___y_223_ = v___x_232_;
goto v___jp_222_;
}
}
case 1:
{
lean_object* v_idx_233_; lean_object* v___y_235_; lean_object* v___x_244_; uint8_t v___x_245_; 
v_idx_233_ = lean_ctor_get(v_x_220_, 0);
lean_inc(v_idx_233_);
lean_dec_ref_known(v_x_220_, 1);
v___x_244_ = lean_unsigned_to_nat(1024u);
v___x_245_ = lean_nat_dec_le(v___x_244_, v_prec_221_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; 
v___x_246_ = lean_obj_once(&l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2, &l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2_once, _init_l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2);
v___y_235_ = v___x_246_;
goto v___jp_234_;
}
else
{
lean_object* v___x_247_; 
v___x_247_ = lean_obj_once(&l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3, &l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3_once, _init_l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3);
v___y_235_ = v___x_247_;
goto v___jp_234_;
}
v___jp_234_:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; uint8_t v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_236_ = ((lean_object*)(l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__6));
v___x_237_ = lean_unsigned_to_nat(1024u);
v___x_238_ = lean_apply_2(v_inst_219_, v_idx_233_, v___x_237_);
v___x_239_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_236_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
lean_inc(v___y_235_);
v___x_240_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_240_, 0, v___y_235_);
lean_ctor_set(v___x_240_, 1, v___x_239_);
v___x_241_ = 0;
v___x_242_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_242_, 0, v___x_240_);
lean_ctor_set_uint8(v___x_242_, sizeof(void*)*1, v___x_241_);
v___x_243_ = l_Repr_addAppParen(v___x_242_, v_prec_221_);
return v___x_243_;
}
}
default: 
{
lean_object* v_l_248_; lean_object* v_r_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_272_; 
lean_dec_ref(v_inst_219_);
v_l_248_ = lean_ctor_get(v_x_220_, 0);
v_r_249_ = lean_ctor_get(v_x_220_, 1);
v_isSharedCheck_272_ = !lean_is_exclusive(v_x_220_);
if (v_isSharedCheck_272_ == 0)
{
v___x_251_ = v_x_220_;
v_isShared_252_ = v_isSharedCheck_272_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_r_249_);
lean_inc(v_l_248_);
lean_dec(v_x_220_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_272_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___y_254_; lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_268_ = lean_unsigned_to_nat(1024u);
v___x_269_ = lean_nat_dec_le(v___x_268_, v_prec_221_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; 
v___x_270_ = lean_obj_once(&l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2, &l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2_once, _init_l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2);
v___y_254_ = v___x_270_;
goto v___jp_253_;
}
else
{
lean_object* v___x_271_; 
v___x_271_ = lean_obj_once(&l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3, &l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3_once, _init_l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3);
v___y_254_ = v___x_271_;
goto v___jp_253_;
}
v___jp_253_:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_259_; 
v___x_255_ = lean_box(1);
v___x_256_ = ((lean_object*)(l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__9));
v___x_257_ = l_Std_Sat_AIG_instReprFanin_repr___redArg(v_l_248_);
if (v_isShared_252_ == 0)
{
lean_ctor_set_tag(v___x_251_, 5);
lean_ctor_set(v___x_251_, 1, v___x_257_);
lean_ctor_set(v___x_251_, 0, v___x_256_);
v___x_259_ = v___x_251_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v___x_256_);
lean_ctor_set(v_reuseFailAlloc_267_, 1, v___x_257_);
v___x_259_ = v_reuseFailAlloc_267_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
lean_ctor_set(v___x_260_, 1, v___x_255_);
v___x_261_ = l_Std_Sat_AIG_instReprFanin_repr___redArg(v_r_249_);
v___x_262_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_260_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
lean_inc(v___y_254_);
v___x_263_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_263_, 0, v___y_254_);
lean_ctor_set(v___x_263_, 1, v___x_262_);
v___x_264_ = 0;
v___x_265_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_265_, 0, v___x_263_);
lean_ctor_set_uint8(v___x_265_, sizeof(void*)*1, v___x_264_);
v___x_266_ = l_Repr_addAppParen(v___x_265_, v_prec_221_);
return v___x_266_;
}
}
}
}
}
v___jp_222_:
{
lean_object* v___x_224_; lean_object* v___x_225_; uint8_t v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_224_ = ((lean_object*)(l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__1));
lean_inc(v___y_223_);
v___x_225_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_225_, 0, v___y_223_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
v___x_226_ = 0;
v___x_227_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_227_, 0, v___x_225_);
lean_ctor_set_uint8(v___x_227_, sizeof(void*)*1, v___x_226_);
v___x_228_ = l_Repr_addAppParen(v___x_227_, v_prec_221_);
return v___x_228_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprDecl_repr___redArg___boxed(lean_object* v_inst_273_, lean_object* v_x_274_, lean_object* v_prec_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Std_Sat_AIG_instReprDecl_repr___redArg(v_inst_273_, v_x_274_, v_prec_275_);
lean_dec(v_prec_275_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprDecl_repr(lean_object* v_00_u03b1_277_, lean_object* v_inst_278_, lean_object* v_x_279_, lean_object* v_prec_280_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = l_Std_Sat_AIG_instReprDecl_repr___redArg(v_inst_278_, v_x_279_, v_prec_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprDecl_repr___boxed(lean_object* v_00_u03b1_282_, lean_object* v_inst_283_, lean_object* v_x_284_, lean_object* v_prec_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Std_Sat_AIG_instReprDecl_repr(v_00_u03b1_282_, v_inst_283_, v_x_284_, v_prec_285_);
lean_dec(v_prec_285_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprDecl___redArg(lean_object* v_inst_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instReprDecl_repr___boxed), 4, 2);
lean_closure_set(v___x_288_, 0, lean_box(0));
lean_closure_set(v___x_288_, 1, v_inst_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instReprDecl(lean_object* v_00_u03b1_289_, lean_object* v_inst_290_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instReprDecl_repr___boxed), 4, 2);
lean_closure_set(v___x_291_, 0, lean_box(0));
lean_closure_set(v___x_291_, 1, v_inst_290_);
return v___x_291_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(lean_object* v_inst_292_, lean_object* v_x_293_, lean_object* v_x_294_){
_start:
{
switch(lean_obj_tag(v_x_293_))
{
case 0:
{
lean_dec_ref(v_inst_292_);
if (lean_obj_tag(v_x_294_) == 0)
{
uint8_t v___x_295_; 
v___x_295_ = 1;
return v___x_295_;
}
else
{
uint8_t v___x_296_; 
lean_dec(v_x_294_);
v___x_296_ = 0;
return v___x_296_;
}
}
case 1:
{
if (lean_obj_tag(v_x_294_) == 1)
{
lean_object* v_idx_297_; lean_object* v_idx_298_; lean_object* v___x_299_; uint8_t v___x_300_; 
v_idx_297_ = lean_ctor_get(v_x_293_, 0);
lean_inc(v_idx_297_);
lean_dec_ref_known(v_x_293_, 1);
v_idx_298_ = lean_ctor_get(v_x_294_, 0);
lean_inc(v_idx_298_);
lean_dec_ref_known(v_x_294_, 1);
v___x_299_ = lean_apply_2(v_inst_292_, v_idx_297_, v_idx_298_);
v___x_300_ = lean_unbox(v___x_299_);
return v___x_300_;
}
else
{
uint8_t v___x_301_; 
lean_dec_ref_known(v_x_293_, 1);
lean_dec(v_x_294_);
lean_dec_ref(v_inst_292_);
v___x_301_ = 0;
return v___x_301_;
}
}
default: 
{
lean_dec_ref(v_inst_292_);
if (lean_obj_tag(v_x_294_) == 2)
{
lean_object* v_l_302_; lean_object* v_r_303_; lean_object* v_l_304_; lean_object* v_r_305_; uint8_t v___x_306_; 
v_l_302_ = lean_ctor_get(v_x_293_, 0);
lean_inc(v_l_302_);
v_r_303_ = lean_ctor_get(v_x_293_, 1);
lean_inc(v_r_303_);
lean_dec_ref_known(v_x_293_, 2);
v_l_304_ = lean_ctor_get(v_x_294_, 0);
lean_inc(v_l_304_);
v_r_305_ = lean_ctor_get(v_x_294_, 1);
lean_inc(v_r_305_);
lean_dec_ref_known(v_x_294_, 2);
v___x_306_ = lean_nat_dec_eq(v_l_302_, v_l_304_);
lean_dec(v_l_304_);
lean_dec(v_l_302_);
if (v___x_306_ == 0)
{
lean_dec(v_r_305_);
lean_dec(v_r_303_);
return v___x_306_;
}
else
{
uint8_t v___x_307_; 
v___x_307_ = lean_nat_dec_eq(v_r_303_, v_r_305_);
lean_dec(v_r_305_);
lean_dec(v_r_303_);
return v___x_307_;
}
}
else
{
uint8_t v___x_308_; 
lean_dec_ref_known(v_x_293_, 2);
lean_dec(v_x_294_);
v___x_308_ = 0;
return v___x_308_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg___boxed(lean_object* v_inst_309_, lean_object* v_x_310_, lean_object* v_x_311_){
_start:
{
uint8_t v_res_312_; lean_object* v_r_313_; 
v_res_312_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v_inst_309_, v_x_310_, v_x_311_);
v_r_313_ = lean_box(v_res_312_);
return v_r_313_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_instDecidableEqDecl_decEq(lean_object* v_00_u03b1_314_, lean_object* v_inst_315_, lean_object* v_x_316_, lean_object* v_x_317_){
_start:
{
uint8_t v___x_318_; 
v___x_318_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v_inst_315_, v_x_316_, v_x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instDecidableEqDecl_decEq___boxed(lean_object* v_00_u03b1_319_, lean_object* v_inst_320_, lean_object* v_x_321_, lean_object* v_x_322_){
_start:
{
uint8_t v_res_323_; lean_object* v_r_324_; 
v_res_323_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq(v_00_u03b1_319_, v_inst_320_, v_x_321_, v_x_322_);
v_r_324_ = lean_box(v_res_323_);
return v_r_324_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_instDecidableEqDecl___redArg(lean_object* v_inst_325_, lean_object* v_x_326_, lean_object* v_x_327_){
_start:
{
uint8_t v___x_328_; 
v___x_328_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v_inst_325_, v_x_326_, v_x_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instDecidableEqDecl___redArg___boxed(lean_object* v_inst_329_, lean_object* v_x_330_, lean_object* v_x_331_){
_start:
{
uint8_t v_res_332_; lean_object* v_r_333_; 
v_res_332_ = l_Std_Sat_AIG_instDecidableEqDecl___redArg(v_inst_329_, v_x_330_, v_x_331_);
v_r_333_ = lean_box(v_res_332_);
return v_r_333_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_instDecidableEqDecl(lean_object* v_00_u03b1_334_, lean_object* v_inst_335_, lean_object* v_x_336_, lean_object* v_x_337_){
_start:
{
uint8_t v___x_338_; 
v___x_338_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v_inst_335_, v_x_336_, v_x_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instDecidableEqDecl___boxed(lean_object* v_00_u03b1_339_, lean_object* v_inst_340_, lean_object* v_x_341_, lean_object* v_x_342_){
_start:
{
uint8_t v_res_343_; lean_object* v_r_344_; 
v_res_343_ = l_Std_Sat_AIG_instDecidableEqDecl(v_00_u03b1_339_, v_inst_340_, v_x_341_, v_x_342_);
v_r_344_ = lean_box(v_res_343_);
return v_r_344_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instInhabitedDecl_default___redArg(){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = lean_box(0);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instInhabitedDecl_default___redArg___boxed(lean_object* v___dummy_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Std_Sat_AIG_instInhabitedDecl_default___redArg();
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instInhabitedDecl_default(lean_object* v_00_u03b1_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = lean_box(0);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instInhabitedDecl___redArg(){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = lean_box(0);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instInhabitedDecl___redArg___boxed(lean_object* v___dummy_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Std_Sat_AIG_instInhabitedDecl___redArg();
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instInhabitedDecl(lean_object* v_a_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = lean_box(0);
return v___x_356_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__12(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__10));
v___x_384_ = l_Lean_mkAtom(v___x_383_);
return v___x_384_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__13(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_385_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__12, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__12_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__12);
v___x_386_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__5));
v___x_387_ = lean_array_push(v___x_386_, v___x_385_);
return v___x_387_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__17(void){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_398_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__16));
v___x_399_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__5));
v___x_400_ = lean_array_push(v___x_399_, v___x_398_);
return v___x_400_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__18(void){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_401_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__17, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__17_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__17);
v___x_402_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__15));
v___x_403_ = lean_box(2);
v___x_404_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
lean_ctor_set(v___x_404_, 1, v___x_402_);
lean_ctor_set(v___x_404_, 2, v___x_401_);
return v___x_404_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__19(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_405_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__18, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__18_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__18);
v___x_406_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__13, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__13_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__13);
v___x_407_ = lean_array_push(v___x_406_, v___x_405_);
return v___x_407_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__20(void){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_408_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__16));
v___x_409_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__19, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__19_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__19);
v___x_410_ = lean_array_push(v___x_409_, v___x_408_);
return v___x_410_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__21(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_411_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__16));
v___x_412_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__20, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__20_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__20);
v___x_413_ = lean_array_push(v___x_412_, v___x_411_);
return v___x_413_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__22(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_414_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__16));
v___x_415_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__21, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__21_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__21);
v___x_416_ = lean_array_push(v___x_415_, v___x_414_);
return v___x_416_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__23(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_417_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__16));
v___x_418_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__22, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__22_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__22);
v___x_419_ = lean_array_push(v___x_418_, v___x_417_);
return v___x_419_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__24(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_420_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__23, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__23_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__23);
v___x_421_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__11));
v___x_422_ = lean_box(2);
v___x_423_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
lean_ctor_set(v___x_423_, 1, v___x_421_);
lean_ctor_set(v___x_423_, 2, v___x_420_);
return v___x_423_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__25(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_424_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__24, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__24_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__24);
v___x_425_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__5));
v___x_426_ = lean_array_push(v___x_425_, v___x_424_);
return v___x_426_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__26(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_427_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__25, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__25_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__25);
v___x_428_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__9));
v___x_429_ = lean_box(2);
v___x_430_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
lean_ctor_set(v___x_430_, 1, v___x_428_);
lean_ctor_set(v___x_430_, 2, v___x_427_);
return v___x_430_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__27(void){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_431_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__26, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__26_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__26);
v___x_432_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__5));
v___x_433_ = lean_array_push(v___x_432_, v___x_431_);
return v___x_433_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__28(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_434_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__27, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__27_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__27);
v___x_435_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__7));
v___x_436_ = lean_box(2);
v___x_437_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
lean_ctor_set(v___x_437_, 1, v___x_435_);
lean_ctor_set(v___x_437_, 2, v___x_434_);
return v___x_437_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__29(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_438_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__28, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__28_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__28);
v___x_439_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__5));
v___x_440_ = lean_array_push(v___x_439_, v___x_438_);
return v___x_440_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__30(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_441_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__29, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__29_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__29);
v___x_442_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__4));
v___x_443_ = lean_box(2);
v___x_444_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
lean_ctor_set(v___x_444_, 1, v___x_442_);
lean_ctor_set(v___x_444_, 2, v___x_441_);
return v___x_444_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___auto__1(void){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___auto__1___closed__30, &l_Std_Sat_AIG_Cache_empty___auto__1___closed__30_once, _init_l_Std_Sat_AIG_Cache_empty___auto__1___closed__30);
return v___x_445_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___redArg___closed__0(void){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_446_ = lean_box(0);
v___x_447_ = lean_unsigned_to_nat(16u);
v___x_448_ = lean_mk_array(v___x_447_, v___x_446_);
return v___x_448_;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___redArg___closed__1(void){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_449_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___redArg___closed__0, &l_Std_Sat_AIG_Cache_empty___redArg___closed__0_once, _init_l_Std_Sat_AIG_Cache_empty___redArg___closed__0);
v___x_450_ = lean_unsigned_to_nat(0u);
v___x_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_451_, 0, v___x_450_);
lean_ctor_set(v___x_451_, 1, v___x_449_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_empty___redArg(){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___redArg___closed__1, &l_Std_Sat_AIG_Cache_empty___redArg___closed__1_once, _init_l_Std_Sat_AIG_Cache_empty___redArg___closed__1);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_empty___redArg___boxed(lean_object* v___dummy_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Std_Sat_AIG_Cache_empty___redArg();
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_empty(lean_object* v_00_u03b1_456_, lean_object* v_inst_457_, lean_object* v_inst_458_, lean_object* v_decls_459_, lean_object* v_hatoms_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___redArg___closed__1, &l_Std_Sat_AIG_Cache_empty___redArg___closed__1_once, _init_l_Std_Sat_AIG_Cache_empty___redArg___closed__1);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_empty___boxed(lean_object* v_00_u03b1_462_, lean_object* v_inst_463_, lean_object* v_inst_464_, lean_object* v_decls_465_, lean_object* v_hatoms_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Std_Sat_AIG_Cache_empty(v_00_u03b1_462_, v_inst_463_, v_inst_464_, v_decls_465_, v_hatoms_466_);
lean_dec_ref(v_decls_465_);
lean_dec_ref(v_inst_464_);
lean_dec_ref(v_inst_463_);
return v_res_467_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_Cache_insert___redArg___lam__0(lean_object* v_inst_468_, lean_object* v_a_469_, lean_object* v_b_470_){
_start:
{
uint8_t v___x_471_; 
v___x_471_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v_inst_468_, v_a_469_, v_b_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed(lean_object* v_inst_472_, lean_object* v_a_473_, lean_object* v_b_474_){
_start:
{
uint8_t v_res_475_; lean_object* v_r_476_; 
v_res_475_ = l_Std_Sat_AIG_Cache_insert___redArg___lam__0(v_inst_472_, v_a_473_, v_b_474_);
v_r_476_ = lean_box(v_res_475_);
return v_r_476_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___redArg(lean_object* v_inst_477_, lean_object* v_inst_478_, lean_object* v_decls_479_, lean_object* v_cache_480_, lean_object* v_decl_481_){
_start:
{
lean_object* v___f_482_; lean_object* v___x_483_; lean_object* v___f_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___f_482_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_482_, 0, v_inst_478_);
v___x_483_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_483_, 0, lean_box(0));
lean_closure_set(v___x_483_, 1, v_inst_477_);
v___f_484_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_484_, 0, v___f_482_);
v___x_485_ = lean_array_get_size(v_decls_479_);
v___x_486_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_484_, v___x_483_, v_cache_480_, v_decl_481_, v___x_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___redArg___boxed(lean_object* v_inst_487_, lean_object* v_inst_488_, lean_object* v_decls_489_, lean_object* v_cache_490_, lean_object* v_decl_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Std_Sat_AIG_Cache_insert___redArg(v_inst_487_, v_inst_488_, v_decls_489_, v_cache_490_, v_decl_491_);
lean_dec_ref(v_decls_489_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert(lean_object* v_00_u03b1_493_, lean_object* v_inst_494_, lean_object* v_inst_495_, lean_object* v_decls_496_, lean_object* v_cache_497_, lean_object* v_decl_498_, lean_object* v_hmiss_499_){
_start:
{
lean_object* v___f_500_; lean_object* v___x_501_; lean_object* v___f_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___f_500_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_500_, 0, v_inst_495_);
v___x_501_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_501_, 0, lean_box(0));
lean_closure_set(v___x_501_, 1, v_inst_494_);
v___f_502_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_502_, 0, v___f_500_);
v___x_503_ = lean_array_get_size(v_decls_496_);
v___x_504_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_502_, v___x_501_, v_cache_497_, v_decl_498_, v___x_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___boxed(lean_object* v_00_u03b1_505_, lean_object* v_inst_506_, lean_object* v_inst_507_, lean_object* v_decls_508_, lean_object* v_cache_509_, lean_object* v_decl_510_, lean_object* v_hmiss_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Std_Sat_AIG_Cache_insert(v_00_u03b1_505_, v_inst_506_, v_inst_507_, v_decls_508_, v_cache_509_, v_decl_510_, v_hmiss_511_);
lean_dec_ref(v_decls_508_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f___redArg(lean_object* v_inst_513_, lean_object* v_inst_514_, lean_object* v_cache_515_, lean_object* v_decl_516_){
_start:
{
lean_object* v___f_517_; lean_object* v___x_518_; lean_object* v___f_519_; lean_object* v___x_520_; 
v___f_517_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_517_, 0, v_inst_514_);
v___x_518_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_518_, 0, lean_box(0));
lean_closure_set(v___x_518_, 1, v_inst_513_);
v___f_519_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_519_, 0, v___f_517_);
v___x_520_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_519_, v___x_518_, v_cache_515_, v_decl_516_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v___x_521_; 
v___x_521_ = lean_box(0);
return v___x_521_;
}
else
{
lean_object* v_val_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_529_; 
v_val_522_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_529_ == 0)
{
v___x_524_ = v___x_520_;
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_val_522_);
lean_dec(v___x_520_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_527_; 
if (v_isShared_525_ == 0)
{
v___x_527_ = v___x_524_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_val_522_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f___redArg___boxed(lean_object* v_inst_530_, lean_object* v_inst_531_, lean_object* v_cache_532_, lean_object* v_decl_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Std_Sat_AIG_Cache_get_x3f___redArg(v_inst_530_, v_inst_531_, v_cache_532_, v_decl_533_);
lean_dec_ref(v_cache_532_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f(lean_object* v_00_u03b1_535_, lean_object* v_inst_536_, lean_object* v_inst_537_, lean_object* v_decls_538_, lean_object* v_cache_539_, lean_object* v_decl_540_){
_start:
{
lean_object* v___f_541_; lean_object* v___x_542_; lean_object* v___f_543_; lean_object* v___x_544_; 
v___f_541_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_541_, 0, v_inst_537_);
v___x_542_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_542_, 0, lean_box(0));
lean_closure_set(v___x_542_, 1, v_inst_536_);
v___f_543_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_543_, 0, v___f_541_);
v___x_544_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_543_, v___x_542_, v_cache_539_, v_decl_540_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v___x_545_; 
v___x_545_ = lean_box(0);
return v___x_545_;
}
else
{
lean_object* v_val_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_553_; 
v_val_546_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_553_ == 0)
{
v___x_548_ = v___x_544_;
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_val_546_);
lean_dec(v___x_544_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_551_; 
if (v_isShared_549_ == 0)
{
v___x_551_ = v___x_548_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_val_546_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f___boxed(lean_object* v_00_u03b1_554_, lean_object* v_inst_555_, lean_object* v_inst_556_, lean_object* v_decls_557_, lean_object* v_cache_558_, lean_object* v_decl_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Std_Sat_AIG_Cache_get_x3f(v_00_u03b1_554_, v_inst_555_, v_inst_556_, v_decls_557_, v_cache_558_, v_decl_559_);
lean_dec_ref(v_cache_558_);
lean_dec_ref(v_decls_557_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_Cache_get_x3f_match__1_splitter___redArg(lean_object* v_x_561_, lean_object* v_h__1_562_, lean_object* v_h__2_563_){
_start:
{
if (lean_obj_tag(v_x_561_) == 0)
{
lean_object* v___x_564_; 
lean_dec(v_h__1_562_);
v___x_564_ = lean_apply_1(v_h__2_563_, lean_box(0));
return v___x_564_;
}
else
{
lean_object* v_val_565_; lean_object* v___x_566_; 
lean_dec(v_h__2_563_);
v_val_565_ = lean_ctor_get(v_x_561_, 0);
lean_inc(v_val_565_);
lean_dec_ref_known(v_x_561_, 1);
v___x_566_ = lean_apply_2(v_h__1_562_, v_val_565_, lean_box(0));
return v___x_566_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_Cache_get_x3f_match__1_splitter(lean_object* v_motive_567_, lean_object* v_x_568_, lean_object* v_h__1_569_, lean_object* v_h__2_570_){
_start:
{
if (lean_obj_tag(v_x_568_) == 0)
{
lean_object* v___x_571_; 
lean_dec(v_h__1_569_);
v___x_571_ = lean_apply_1(v_h__2_570_, lean_box(0));
return v___x_571_;
}
else
{
lean_object* v_val_572_; lean_object* v___x_573_; 
lean_dec(v_h__2_570_);
v_val_572_ = lean_ctor_get(v_x_568_, 0);
lean_inc(v_val_572_);
lean_dec_ref_known(v_x_568_, 1);
v___x_573_ = lean_apply_2(v_h__1_569_, v_val_572_, lean_box(0));
return v___x_573_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_ofAtoms_go___redArg(lean_object* v_inst_574_, lean_object* v_inst_575_, lean_object* v_decls_576_, lean_object* v_idx_577_, lean_object* v_map_578_){
_start:
{
lean_object* v___x_579_; uint8_t v___x_580_; 
v___x_579_ = lean_array_get_size(v_decls_576_);
v___x_580_ = lean_nat_dec_lt(v_idx_577_, v___x_579_);
if (v___x_580_ == 0)
{
lean_dec(v_idx_577_);
lean_dec_ref(v_inst_575_);
lean_dec_ref(v_inst_574_);
return v_map_578_;
}
else
{
lean_object* v___x_581_; 
v___x_581_ = lean_array_fget_borrowed(v_decls_576_, v_idx_577_);
if (lean_obj_tag(v___x_581_) == 1)
{
lean_object* v___f_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___f_586_; lean_object* v___x_587_; 
lean_inc_ref(v_inst_575_);
v___f_582_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_582_, 0, v_inst_575_);
lean_inc_ref(v_inst_574_);
v___x_583_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_583_, 0, lean_box(0));
lean_closure_set(v___x_583_, 1, v_inst_574_);
v___x_584_ = lean_unsigned_to_nat(1u);
v___x_585_ = lean_nat_add(v_idx_577_, v___x_584_);
v___f_586_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_586_, 0, v___f_582_);
lean_inc_ref(v___x_581_);
v___x_587_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_586_, v___x_583_, v_map_578_, v___x_581_, v_idx_577_);
v_idx_577_ = v___x_585_;
v_map_578_ = v___x_587_;
goto _start;
}
else
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = lean_unsigned_to_nat(1u);
v___x_590_ = lean_nat_add(v_idx_577_, v___x_589_);
lean_dec(v_idx_577_);
v_idx_577_ = v___x_590_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_ofAtoms_go___redArg___boxed(lean_object* v_inst_592_, lean_object* v_inst_593_, lean_object* v_decls_594_, lean_object* v_idx_595_, lean_object* v_map_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Std_Sat_AIG_Cache_ofAtoms_go___redArg(v_inst_592_, v_inst_593_, v_decls_594_, v_idx_595_, v_map_596_);
lean_dec_ref(v_decls_594_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_ofAtoms_go(lean_object* v_00_u03b1_598_, lean_object* v_inst_599_, lean_object* v_inst_600_, lean_object* v_decls_601_, lean_object* v_huniq_602_, lean_object* v_idx_603_, lean_object* v_map_604_, lean_object* v_hsound_605_, lean_object* v_hcomp_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Std_Sat_AIG_Cache_ofAtoms_go___redArg(v_inst_599_, v_inst_600_, v_decls_601_, v_idx_603_, v_map_604_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_ofAtoms_go___boxed(lean_object* v_00_u03b1_608_, lean_object* v_inst_609_, lean_object* v_inst_610_, lean_object* v_decls_611_, lean_object* v_huniq_612_, lean_object* v_idx_613_, lean_object* v_map_614_, lean_object* v_hsound_615_, lean_object* v_hcomp_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Std_Sat_AIG_Cache_ofAtoms_go(v_00_u03b1_608_, v_inst_609_, v_inst_610_, v_decls_611_, v_huniq_612_, v_idx_613_, v_map_614_, v_hsound_615_, v_hcomp_616_);
lean_dec_ref(v_decls_611_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_Cache_ofAtoms_go_match__1_splitter___redArg(lean_object* v_x_618_, lean_object* v_h__1_619_, lean_object* v_h__2_620_, lean_object* v_h__3_621_){
_start:
{
switch(lean_obj_tag(v_x_618_))
{
case 0:
{
lean_object* v___x_622_; 
lean_dec(v_h__3_621_);
lean_dec(v_h__1_619_);
v___x_622_ = lean_apply_1(v_h__2_620_, lean_box(0));
return v___x_622_;
}
case 1:
{
lean_object* v_idx_623_; lean_object* v___x_624_; 
lean_dec(v_h__3_621_);
lean_dec(v_h__2_620_);
v_idx_623_ = lean_ctor_get(v_x_618_, 0);
lean_inc(v_idx_623_);
lean_dec_ref_known(v_x_618_, 1);
v___x_624_ = lean_apply_2(v_h__1_619_, v_idx_623_, lean_box(0));
return v___x_624_;
}
default: 
{
lean_object* v_l_625_; lean_object* v_r_626_; lean_object* v___x_627_; 
lean_dec(v_h__2_620_);
lean_dec(v_h__1_619_);
v_l_625_ = lean_ctor_get(v_x_618_, 0);
lean_inc(v_l_625_);
v_r_626_ = lean_ctor_get(v_x_618_, 1);
lean_inc(v_r_626_);
lean_dec_ref_known(v_x_618_, 2);
v___x_627_ = lean_apply_3(v_h__3_621_, v_l_625_, v_r_626_, lean_box(0));
return v___x_627_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_Cache_ofAtoms_go_match__1_splitter(lean_object* v_00_u03b1_628_, lean_object* v_motive_629_, lean_object* v_x_630_, lean_object* v_h__1_631_, lean_object* v_h__2_632_, lean_object* v_h__3_633_){
_start:
{
switch(lean_obj_tag(v_x_630_))
{
case 0:
{
lean_object* v___x_634_; 
lean_dec(v_h__3_633_);
lean_dec(v_h__1_631_);
v___x_634_ = lean_apply_1(v_h__2_632_, lean_box(0));
return v___x_634_;
}
case 1:
{
lean_object* v_idx_635_; lean_object* v___x_636_; 
lean_dec(v_h__3_633_);
lean_dec(v_h__2_632_);
v_idx_635_ = lean_ctor_get(v_x_630_, 0);
lean_inc(v_idx_635_);
lean_dec_ref_known(v_x_630_, 1);
v___x_636_ = lean_apply_2(v_h__1_631_, v_idx_635_, lean_box(0));
return v___x_636_;
}
default: 
{
lean_object* v_l_637_; lean_object* v_r_638_; lean_object* v___x_639_; 
lean_dec(v_h__2_632_);
lean_dec(v_h__1_631_);
v_l_637_ = lean_ctor_get(v_x_630_, 0);
lean_inc(v_l_637_);
v_r_638_ = lean_ctor_get(v_x_630_, 1);
lean_inc(v_r_638_);
lean_dec_ref_known(v_x_630_, 2);
v___x_639_ = lean_apply_3(v_h__3_633_, v_l_637_, v_r_638_, lean_box(0));
return v___x_639_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_ofAtoms___redArg(lean_object* v_inst_640_, lean_object* v_inst_641_, lean_object* v_decls_642_){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_643_ = lean_unsigned_to_nat(0u);
v___x_644_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___redArg___closed__1, &l_Std_Sat_AIG_Cache_empty___redArg___closed__1_once, _init_l_Std_Sat_AIG_Cache_empty___redArg___closed__1);
v___x_645_ = l_Std_Sat_AIG_Cache_ofAtoms_go___redArg(v_inst_640_, v_inst_641_, v_decls_642_, v___x_643_, v___x_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_ofAtoms___redArg___boxed(lean_object* v_inst_646_, lean_object* v_inst_647_, lean_object* v_decls_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_Std_Sat_AIG_Cache_ofAtoms___redArg(v_inst_646_, v_inst_647_, v_decls_648_);
lean_dec_ref(v_decls_648_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_ofAtoms(lean_object* v_00_u03b1_650_, lean_object* v_inst_651_, lean_object* v_inst_652_, lean_object* v_decls_653_, lean_object* v_huniq_654_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_Std_Sat_AIG_Cache_ofAtoms___redArg(v_inst_651_, v_inst_652_, v_decls_653_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_ofAtoms___boxed(lean_object* v_00_u03b1_656_, lean_object* v_inst_657_, lean_object* v_inst_658_, lean_object* v_decls_659_, lean_object* v_huniq_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Std_Sat_AIG_Cache_ofAtoms(v_00_u03b1_656_, v_inst_657_, v_inst_658_, v_decls_659_, v_huniq_660_);
lean_dec_ref(v_decls_659_);
return v_res_661_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___redArg___closed__1(void){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_666_ = lean_obj_once(&l_Std_Sat_AIG_Cache_empty___redArg___closed__1, &l_Std_Sat_AIG_Cache_empty___redArg___closed__1_once, _init_l_Std_Sat_AIG_Cache_empty___redArg___closed__1);
v___x_667_ = ((lean_object*)(l_Std_Sat_AIG_empty___redArg___closed__0));
v___x_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
lean_ctor_set(v___x_668_, 1, v___x_666_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_empty___redArg(){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = lean_obj_once(&l_Std_Sat_AIG_empty___redArg___closed__1, &l_Std_Sat_AIG_empty___redArg___closed__1_once, _init_l_Std_Sat_AIG_empty___redArg___closed__1);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_empty___redArg___boxed(lean_object* v___dummy_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Std_Sat_AIG_empty___redArg();
return v_res_672_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___closed__0(void){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = l_Std_Sat_AIG_empty___redArg();
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_empty(lean_object* v_00_u03b1_674_, lean_object* v_inst_675_, lean_object* v_inst_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = lean_obj_once(&l_Std_Sat_AIG_empty___closed__0, &l_Std_Sat_AIG_empty___closed__0_once, _init_l_Std_Sat_AIG_empty___closed__0);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_empty___boxed(lean_object* v_00_u03b1_678_, lean_object* v_inst_679_, lean_object* v_inst_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Std_Sat_AIG_empty(v_00_u03b1_678_, v_inst_679_, v_inst_680_);
lean_dec_ref(v_inst_680_);
lean_dec_ref(v_inst_679_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instMembership___redArg(){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = lean_box(0);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instMembership___redArg___boxed(lean_object* v___dummy_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Std_Sat_AIG_instMembership___redArg();
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instMembership(lean_object* v_00_u03b1_686_, lean_object* v_inst_687_, lean_object* v_inst_688_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = lean_box(0);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instMembership___boxed(lean_object* v_00_u03b1_690_, lean_object* v_inst_691_, lean_object* v_inst_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Std_Sat_AIG_instMembership(v_00_u03b1_690_, v_inst_691_, v_inst_692_);
lean_dec_ref(v_inst_692_);
lean_dec_ref(v_inst_691_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_cast___redArg(lean_object* v_ref_694_){
_start:
{
lean_object* v_gate_695_; uint8_t v_invert_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
v_gate_695_ = lean_ctor_get(v_ref_694_, 0);
v_invert_696_ = lean_ctor_get_uint8(v_ref_694_, sizeof(void*)*1);
v_isSharedCheck_703_ = !lean_is_exclusive(v_ref_694_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v_ref_694_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_gate_695_);
lean_dec(v_ref_694_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_gate_695_);
lean_ctor_set_uint8(v_reuseFailAlloc_702_, sizeof(void*)*1, v_invert_696_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_cast(lean_object* v_00_u03b1_704_, lean_object* v_inst_705_, lean_object* v_inst_706_, lean_object* v_aig1_707_, lean_object* v_aig2_708_, lean_object* v_ref_709_, lean_object* v_h_710_){
_start:
{
lean_object* v_gate_711_; uint8_t v_invert_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
v_gate_711_ = lean_ctor_get(v_ref_709_, 0);
v_invert_712_ = lean_ctor_get_uint8(v_ref_709_, sizeof(void*)*1);
v_isSharedCheck_719_ = !lean_is_exclusive(v_ref_709_);
if (v_isSharedCheck_719_ == 0)
{
v___x_714_ = v_ref_709_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_gate_711_);
lean_dec(v_ref_709_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_gate_711_);
lean_ctor_set_uint8(v_reuseFailAlloc_718_, sizeof(void*)*1, v_invert_712_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_cast___boxed(lean_object* v_00_u03b1_720_, lean_object* v_inst_721_, lean_object* v_inst_722_, lean_object* v_aig1_723_, lean_object* v_aig2_724_, lean_object* v_ref_725_, lean_object* v_h_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Std_Sat_AIG_Ref_cast(v_00_u03b1_720_, v_inst_721_, v_inst_722_, v_aig1_723_, v_aig2_724_, v_ref_725_, v_h_726_);
lean_dec_ref(v_aig2_724_);
lean_dec_ref(v_aig1_723_);
lean_dec_ref(v_inst_722_);
lean_dec_ref(v_inst_721_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_flip___redArg(lean_object* v_ref_728_, uint8_t v_inv_729_){
_start:
{
lean_object* v_gate_730_; uint8_t v_invert_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_743_; 
v_gate_730_ = lean_ctor_get(v_ref_728_, 0);
v_invert_731_ = lean_ctor_get_uint8(v_ref_728_, sizeof(void*)*1);
v_isSharedCheck_743_ = !lean_is_exclusive(v_ref_728_);
if (v_isSharedCheck_743_ == 0)
{
v___x_733_ = v_ref_728_;
v_isShared_734_ = v_isSharedCheck_743_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_gate_730_);
lean_dec(v_ref_728_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_743_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
if (v_invert_731_ == 0)
{
if (v_inv_729_ == 0)
{
lean_del_object(v___x_733_);
goto v___jp_740_;
}
else
{
goto v___jp_735_;
}
}
else
{
if (v_inv_729_ == 0)
{
goto v___jp_735_;
}
else
{
lean_del_object(v___x_733_);
goto v___jp_740_;
}
}
v___jp_735_:
{
uint8_t v___x_736_; lean_object* v___x_738_; 
v___x_736_ = 1;
if (v_isShared_734_ == 0)
{
v___x_738_ = v___x_733_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_gate_730_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
lean_ctor_set_uint8(v___x_738_, sizeof(void*)*1, v___x_736_);
return v___x_738_;
}
}
v___jp_740_:
{
uint8_t v___x_741_; lean_object* v___x_742_; 
v___x_741_ = 0;
v___x_742_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_742_, 0, v_gate_730_);
lean_ctor_set_uint8(v___x_742_, sizeof(void*)*1, v___x_741_);
return v___x_742_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_flip___redArg___boxed(lean_object* v_ref_744_, lean_object* v_inv_745_){
_start:
{
uint8_t v_inv_boxed_746_; lean_object* v_res_747_; 
v_inv_boxed_746_ = lean_unbox(v_inv_745_);
v_res_747_ = l_Std_Sat_AIG_Ref_flip___redArg(v_ref_744_, v_inv_boxed_746_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_flip(lean_object* v_00_u03b1_748_, lean_object* v_inst_749_, lean_object* v_inst_750_, lean_object* v_aig_751_, lean_object* v_ref_752_, uint8_t v_inv_753_){
_start:
{
lean_object* v_gate_754_; uint8_t v_invert_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_767_; 
v_gate_754_ = lean_ctor_get(v_ref_752_, 0);
v_invert_755_ = lean_ctor_get_uint8(v_ref_752_, sizeof(void*)*1);
v_isSharedCheck_767_ = !lean_is_exclusive(v_ref_752_);
if (v_isSharedCheck_767_ == 0)
{
v___x_757_ = v_ref_752_;
v_isShared_758_ = v_isSharedCheck_767_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_gate_754_);
lean_dec(v_ref_752_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_767_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
if (v_invert_755_ == 0)
{
if (v_inv_753_ == 0)
{
lean_del_object(v___x_757_);
goto v___jp_764_;
}
else
{
goto v___jp_759_;
}
}
else
{
if (v_inv_753_ == 0)
{
goto v___jp_759_;
}
else
{
lean_del_object(v___x_757_);
goto v___jp_764_;
}
}
v___jp_759_:
{
uint8_t v___x_760_; lean_object* v___x_762_; 
v___x_760_ = 1;
if (v_isShared_758_ == 0)
{
v___x_762_ = v___x_757_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_gate_754_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
lean_ctor_set_uint8(v___x_762_, sizeof(void*)*1, v___x_760_);
return v___x_762_;
}
}
v___jp_764_:
{
uint8_t v___x_765_; lean_object* v___x_766_; 
v___x_765_ = 0;
v___x_766_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_766_, 0, v_gate_754_);
lean_ctor_set_uint8(v___x_766_, sizeof(void*)*1, v___x_765_);
return v___x_766_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_flip___boxed(lean_object* v_00_u03b1_768_, lean_object* v_inst_769_, lean_object* v_inst_770_, lean_object* v_aig_771_, lean_object* v_ref_772_, lean_object* v_inv_773_){
_start:
{
uint8_t v_inv_boxed_774_; lean_object* v_res_775_; 
v_inv_boxed_774_ = lean_unbox(v_inv_773_);
v_res_775_ = l_Std_Sat_AIG_Ref_flip(v_00_u03b1_768_, v_inst_769_, v_inst_770_, v_aig_771_, v_ref_772_, v_inv_boxed_774_);
lean_dec_ref(v_aig_771_);
lean_dec_ref(v_inst_770_);
lean_dec_ref(v_inst_769_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_not___redArg(lean_object* v_ref_776_){
_start:
{
uint8_t v_invert_777_; 
v_invert_777_ = lean_ctor_get_uint8(v_ref_776_, sizeof(void*)*1);
if (v_invert_777_ == 0)
{
lean_object* v_gate_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_786_; 
v_gate_778_ = lean_ctor_get(v_ref_776_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v_ref_776_);
if (v_isSharedCheck_786_ == 0)
{
v___x_780_ = v_ref_776_;
v_isShared_781_ = v_isSharedCheck_786_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_gate_778_);
lean_dec(v_ref_776_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_786_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
uint8_t v___x_782_; lean_object* v___x_784_; 
v___x_782_ = 1;
if (v_isShared_781_ == 0)
{
v___x_784_ = v___x_780_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_gate_778_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
lean_ctor_set_uint8(v___x_784_, sizeof(void*)*1, v___x_782_);
return v___x_784_;
}
}
}
else
{
lean_object* v_gate_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_795_; 
v_gate_787_ = lean_ctor_get(v_ref_776_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v_ref_776_);
if (v_isSharedCheck_795_ == 0)
{
v___x_789_ = v_ref_776_;
v_isShared_790_ = v_isSharedCheck_795_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_gate_787_);
lean_dec(v_ref_776_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_795_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
uint8_t v___x_791_; lean_object* v___x_793_; 
v___x_791_ = 0;
if (v_isShared_790_ == 0)
{
v___x_793_ = v___x_789_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_gate_787_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
lean_ctor_set_uint8(v___x_793_, sizeof(void*)*1, v___x_791_);
return v___x_793_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_not(lean_object* v_00_u03b1_796_, lean_object* v_inst_797_, lean_object* v_inst_798_, lean_object* v_aig_799_, lean_object* v_ref_800_){
_start:
{
uint8_t v_invert_801_; 
v_invert_801_ = lean_ctor_get_uint8(v_ref_800_, sizeof(void*)*1);
if (v_invert_801_ == 0)
{
lean_object* v_gate_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_810_; 
v_gate_802_ = lean_ctor_get(v_ref_800_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v_ref_800_);
if (v_isSharedCheck_810_ == 0)
{
v___x_804_ = v_ref_800_;
v_isShared_805_ = v_isSharedCheck_810_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_gate_802_);
lean_dec(v_ref_800_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_810_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
uint8_t v___x_806_; lean_object* v___x_808_; 
v___x_806_ = 1;
if (v_isShared_805_ == 0)
{
v___x_808_ = v___x_804_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_gate_802_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
lean_ctor_set_uint8(v___x_808_, sizeof(void*)*1, v___x_806_);
return v___x_808_;
}
}
}
else
{
lean_object* v_gate_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_819_; 
v_gate_811_ = lean_ctor_get(v_ref_800_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v_ref_800_);
if (v_isSharedCheck_819_ == 0)
{
v___x_813_ = v_ref_800_;
v_isShared_814_ = v_isSharedCheck_819_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_gate_811_);
lean_dec(v_ref_800_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_819_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
uint8_t v___x_815_; lean_object* v___x_817_; 
v___x_815_ = 0;
if (v_isShared_814_ == 0)
{
v___x_817_ = v___x_813_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_gate_811_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
lean_ctor_set_uint8(v___x_817_, sizeof(void*)*1, v___x_815_);
return v___x_817_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Ref_not___boxed(lean_object* v_00_u03b1_820_, lean_object* v_inst_821_, lean_object* v_inst_822_, lean_object* v_aig_823_, lean_object* v_ref_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Std_Sat_AIG_Ref_not(v_00_u03b1_820_, v_inst_821_, v_inst_822_, v_aig_823_, v_ref_824_);
lean_dec_ref(v_aig_823_);
lean_dec_ref(v_inst_822_);
lean_dec_ref(v_inst_821_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_cast___redArg(lean_object* v_input_826_){
_start:
{
lean_object* v_lhs_827_; lean_object* v_rhs_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_853_; 
v_lhs_827_ = lean_ctor_get(v_input_826_, 0);
v_rhs_828_ = lean_ctor_get(v_input_826_, 1);
v_isSharedCheck_853_ = !lean_is_exclusive(v_input_826_);
if (v_isSharedCheck_853_ == 0)
{
v___x_830_ = v_input_826_;
v_isShared_831_ = v_isSharedCheck_853_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_rhs_828_);
lean_inc(v_lhs_827_);
lean_dec(v_input_826_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_853_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v_gate_832_; uint8_t v_invert_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_852_; 
v_gate_832_ = lean_ctor_get(v_lhs_827_, 0);
v_invert_833_ = lean_ctor_get_uint8(v_lhs_827_, sizeof(void*)*1);
v_isSharedCheck_852_ = !lean_is_exclusive(v_lhs_827_);
if (v_isSharedCheck_852_ == 0)
{
v___x_835_ = v_lhs_827_;
v_isShared_836_ = v_isSharedCheck_852_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_gate_832_);
lean_dec(v_lhs_827_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_852_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v_gate_837_; uint8_t v_invert_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_851_; 
v_gate_837_ = lean_ctor_get(v_rhs_828_, 0);
v_invert_838_ = lean_ctor_get_uint8(v_rhs_828_, sizeof(void*)*1);
v_isSharedCheck_851_ = !lean_is_exclusive(v_rhs_828_);
if (v_isSharedCheck_851_ == 0)
{
v___x_840_ = v_rhs_828_;
v_isShared_841_ = v_isSharedCheck_851_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_gate_837_);
lean_dec(v_rhs_828_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_851_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_843_; 
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 0, v_gate_832_);
v___x_843_ = v___x_840_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_gate_832_);
v___x_843_ = v_reuseFailAlloc_850_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
lean_object* v___x_845_; 
lean_ctor_set_uint8(v___x_843_, sizeof(void*)*1, v_invert_833_);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 0, v_gate_837_);
v___x_845_ = v___x_835_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_gate_837_);
v___x_845_ = v_reuseFailAlloc_849_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
lean_object* v___x_847_; 
lean_ctor_set_uint8(v___x_845_, sizeof(void*)*1, v_invert_838_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 1, v___x_845_);
lean_ctor_set(v___x_830_, 0, v___x_843_);
v___x_847_ = v___x_830_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_843_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v___x_845_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_cast(lean_object* v_00_u03b1_854_, lean_object* v_inst_855_, lean_object* v_inst_856_, lean_object* v_aig1_857_, lean_object* v_aig2_858_, lean_object* v_input_859_, lean_object* v_h_860_){
_start:
{
lean_object* v_lhs_861_; lean_object* v_rhs_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_887_; 
v_lhs_861_ = lean_ctor_get(v_input_859_, 0);
v_rhs_862_ = lean_ctor_get(v_input_859_, 1);
v_isSharedCheck_887_ = !lean_is_exclusive(v_input_859_);
if (v_isSharedCheck_887_ == 0)
{
v___x_864_ = v_input_859_;
v_isShared_865_ = v_isSharedCheck_887_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_rhs_862_);
lean_inc(v_lhs_861_);
lean_dec(v_input_859_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_887_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v_gate_866_; uint8_t v_invert_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_886_; 
v_gate_866_ = lean_ctor_get(v_lhs_861_, 0);
v_invert_867_ = lean_ctor_get_uint8(v_lhs_861_, sizeof(void*)*1);
v_isSharedCheck_886_ = !lean_is_exclusive(v_lhs_861_);
if (v_isSharedCheck_886_ == 0)
{
v___x_869_ = v_lhs_861_;
v_isShared_870_ = v_isSharedCheck_886_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_gate_866_);
lean_dec(v_lhs_861_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_886_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v_gate_871_; uint8_t v_invert_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_885_; 
v_gate_871_ = lean_ctor_get(v_rhs_862_, 0);
v_invert_872_ = lean_ctor_get_uint8(v_rhs_862_, sizeof(void*)*1);
v_isSharedCheck_885_ = !lean_is_exclusive(v_rhs_862_);
if (v_isSharedCheck_885_ == 0)
{
v___x_874_ = v_rhs_862_;
v_isShared_875_ = v_isSharedCheck_885_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_gate_871_);
lean_dec(v_rhs_862_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_885_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 0, v_gate_866_);
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_gate_866_);
v___x_877_ = v_reuseFailAlloc_884_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
lean_object* v___x_879_; 
lean_ctor_set_uint8(v___x_877_, sizeof(void*)*1, v_invert_867_);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v_gate_871_);
v___x_879_ = v___x_869_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_gate_871_);
v___x_879_ = v_reuseFailAlloc_883_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
lean_object* v___x_881_; 
lean_ctor_set_uint8(v___x_879_, sizeof(void*)*1, v_invert_872_);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 1, v___x_879_);
lean_ctor_set(v___x_864_, 0, v___x_877_);
v___x_881_ = v___x_864_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_877_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v___x_879_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_cast___boxed(lean_object* v_00_u03b1_888_, lean_object* v_inst_889_, lean_object* v_inst_890_, lean_object* v_aig1_891_, lean_object* v_aig2_892_, lean_object* v_input_893_, lean_object* v_h_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Std_Sat_AIG_BinaryInput_cast(v_00_u03b1_888_, v_inst_889_, v_inst_890_, v_aig1_891_, v_aig2_892_, v_input_893_, v_h_894_);
lean_dec_ref(v_aig2_892_);
lean_dec_ref(v_aig1_891_);
lean_dec_ref(v_inst_890_);
lean_dec_ref(v_inst_889_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_invert___redArg(lean_object* v_input_896_, uint8_t v_linv_897_, uint8_t v_rinv_898_){
_start:
{
lean_object* v___y_900_; lean_object* v___y_901_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v_lhs_911_; lean_object* v_rhs_912_; lean_object* v___y_914_; lean_object* v_gate_920_; uint8_t v_invert_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_933_; 
v_lhs_911_ = lean_ctor_get(v_input_896_, 0);
lean_inc_ref(v_lhs_911_);
v_rhs_912_ = lean_ctor_get(v_input_896_, 1);
lean_inc_ref(v_rhs_912_);
lean_dec_ref(v_input_896_);
v_gate_920_ = lean_ctor_get(v_lhs_911_, 0);
v_invert_921_ = lean_ctor_get_uint8(v_lhs_911_, sizeof(void*)*1);
v_isSharedCheck_933_ = !lean_is_exclusive(v_lhs_911_);
if (v_isSharedCheck_933_ == 0)
{
v___x_923_ = v_lhs_911_;
v_isShared_924_ = v_isSharedCheck_933_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_gate_920_);
lean_dec(v_lhs_911_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_933_;
goto v_resetjp_922_;
}
v___jp_899_:
{
uint8_t v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_902_ = 0;
v___x_903_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_903_, 0, v___y_901_);
lean_ctor_set_uint8(v___x_903_, sizeof(void*)*1, v___x_902_);
v___x_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_904_, 0, v___y_900_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
return v___x_904_;
}
v___jp_905_:
{
uint8_t v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_908_ = 1;
v___x_909_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_909_, 0, v___y_907_);
lean_ctor_set_uint8(v___x_909_, sizeof(void*)*1, v___x_908_);
v___x_910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_910_, 0, v___y_906_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
return v___x_910_;
}
v___jp_913_:
{
uint8_t v_invert_915_; 
v_invert_915_ = lean_ctor_get_uint8(v_rhs_912_, sizeof(void*)*1);
if (v_invert_915_ == 0)
{
if (v_rinv_898_ == 0)
{
lean_object* v_gate_916_; 
v_gate_916_ = lean_ctor_get(v_rhs_912_, 0);
lean_inc(v_gate_916_);
lean_dec_ref(v_rhs_912_);
v___y_900_ = v___y_914_;
v___y_901_ = v_gate_916_;
goto v___jp_899_;
}
else
{
lean_object* v_gate_917_; 
v_gate_917_ = lean_ctor_get(v_rhs_912_, 0);
lean_inc(v_gate_917_);
lean_dec_ref(v_rhs_912_);
v___y_906_ = v___y_914_;
v___y_907_ = v_gate_917_;
goto v___jp_905_;
}
}
else
{
if (v_rinv_898_ == 0)
{
lean_object* v_gate_918_; 
v_gate_918_ = lean_ctor_get(v_rhs_912_, 0);
lean_inc(v_gate_918_);
lean_dec_ref(v_rhs_912_);
v___y_906_ = v___y_914_;
v___y_907_ = v_gate_918_;
goto v___jp_905_;
}
else
{
lean_object* v_gate_919_; 
v_gate_919_ = lean_ctor_get(v_rhs_912_, 0);
lean_inc(v_gate_919_);
lean_dec_ref(v_rhs_912_);
v___y_900_ = v___y_914_;
v___y_901_ = v_gate_919_;
goto v___jp_899_;
}
}
}
v_resetjp_922_:
{
if (v_invert_921_ == 0)
{
if (v_linv_897_ == 0)
{
lean_del_object(v___x_923_);
goto v___jp_930_;
}
else
{
goto v___jp_925_;
}
}
else
{
if (v_linv_897_ == 0)
{
goto v___jp_925_;
}
else
{
lean_del_object(v___x_923_);
goto v___jp_930_;
}
}
v___jp_925_:
{
uint8_t v___x_926_; lean_object* v___x_928_; 
v___x_926_ = 1;
if (v_isShared_924_ == 0)
{
v___x_928_ = v___x_923_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_gate_920_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
lean_ctor_set_uint8(v___x_928_, sizeof(void*)*1, v___x_926_);
v___y_914_ = v___x_928_;
goto v___jp_913_;
}
}
v___jp_930_:
{
uint8_t v___x_931_; lean_object* v___x_932_; 
v___x_931_ = 0;
v___x_932_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_932_, 0, v_gate_920_);
lean_ctor_set_uint8(v___x_932_, sizeof(void*)*1, v___x_931_);
v___y_914_ = v___x_932_;
goto v___jp_913_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_invert___redArg___boxed(lean_object* v_input_934_, lean_object* v_linv_935_, lean_object* v_rinv_936_){
_start:
{
uint8_t v_linv_boxed_937_; uint8_t v_rinv_boxed_938_; lean_object* v_res_939_; 
v_linv_boxed_937_ = lean_unbox(v_linv_935_);
v_rinv_boxed_938_ = lean_unbox(v_rinv_936_);
v_res_939_ = l_Std_Sat_AIG_BinaryInput_invert___redArg(v_input_934_, v_linv_boxed_937_, v_rinv_boxed_938_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_invert(lean_object* v_00_u03b1_940_, lean_object* v_inst_941_, lean_object* v_inst_942_, lean_object* v_aig_943_, lean_object* v_input_944_, uint8_t v_linv_945_, uint8_t v_rinv_946_){
_start:
{
lean_object* v___y_948_; lean_object* v___y_949_; lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v_lhs_959_; lean_object* v_rhs_960_; lean_object* v___y_962_; lean_object* v_gate_968_; uint8_t v_invert_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_981_; 
v_lhs_959_ = lean_ctor_get(v_input_944_, 0);
lean_inc_ref(v_lhs_959_);
v_rhs_960_ = lean_ctor_get(v_input_944_, 1);
lean_inc_ref(v_rhs_960_);
lean_dec_ref(v_input_944_);
v_gate_968_ = lean_ctor_get(v_lhs_959_, 0);
v_invert_969_ = lean_ctor_get_uint8(v_lhs_959_, sizeof(void*)*1);
v_isSharedCheck_981_ = !lean_is_exclusive(v_lhs_959_);
if (v_isSharedCheck_981_ == 0)
{
v___x_971_ = v_lhs_959_;
v_isShared_972_ = v_isSharedCheck_981_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_gate_968_);
lean_dec(v_lhs_959_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_981_;
goto v_resetjp_970_;
}
v___jp_947_:
{
uint8_t v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_950_ = 0;
v___x_951_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_951_, 0, v___y_949_);
lean_ctor_set_uint8(v___x_951_, sizeof(void*)*1, v___x_950_);
v___x_952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_952_, 0, v___y_948_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
return v___x_952_;
}
v___jp_953_:
{
uint8_t v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_956_ = 1;
v___x_957_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_957_, 0, v___y_955_);
lean_ctor_set_uint8(v___x_957_, sizeof(void*)*1, v___x_956_);
v___x_958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_958_, 0, v___y_954_);
lean_ctor_set(v___x_958_, 1, v___x_957_);
return v___x_958_;
}
v___jp_961_:
{
uint8_t v_invert_963_; 
v_invert_963_ = lean_ctor_get_uint8(v_rhs_960_, sizeof(void*)*1);
if (v_invert_963_ == 0)
{
if (v_rinv_946_ == 0)
{
lean_object* v_gate_964_; 
v_gate_964_ = lean_ctor_get(v_rhs_960_, 0);
lean_inc(v_gate_964_);
lean_dec_ref(v_rhs_960_);
v___y_948_ = v___y_962_;
v___y_949_ = v_gate_964_;
goto v___jp_947_;
}
else
{
lean_object* v_gate_965_; 
v_gate_965_ = lean_ctor_get(v_rhs_960_, 0);
lean_inc(v_gate_965_);
lean_dec_ref(v_rhs_960_);
v___y_954_ = v___y_962_;
v___y_955_ = v_gate_965_;
goto v___jp_953_;
}
}
else
{
if (v_rinv_946_ == 0)
{
lean_object* v_gate_966_; 
v_gate_966_ = lean_ctor_get(v_rhs_960_, 0);
lean_inc(v_gate_966_);
lean_dec_ref(v_rhs_960_);
v___y_954_ = v___y_962_;
v___y_955_ = v_gate_966_;
goto v___jp_953_;
}
else
{
lean_object* v_gate_967_; 
v_gate_967_ = lean_ctor_get(v_rhs_960_, 0);
lean_inc(v_gate_967_);
lean_dec_ref(v_rhs_960_);
v___y_948_ = v___y_962_;
v___y_949_ = v_gate_967_;
goto v___jp_947_;
}
}
}
v_resetjp_970_:
{
if (v_invert_969_ == 0)
{
if (v_linv_945_ == 0)
{
lean_del_object(v___x_971_);
goto v___jp_978_;
}
else
{
goto v___jp_973_;
}
}
else
{
if (v_linv_945_ == 0)
{
goto v___jp_973_;
}
else
{
lean_del_object(v___x_971_);
goto v___jp_978_;
}
}
v___jp_973_:
{
uint8_t v___x_974_; lean_object* v___x_976_; 
v___x_974_ = 1;
if (v_isShared_972_ == 0)
{
v___x_976_ = v___x_971_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_gate_968_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
lean_ctor_set_uint8(v___x_976_, sizeof(void*)*1, v___x_974_);
v___y_962_ = v___x_976_;
goto v___jp_961_;
}
}
v___jp_978_:
{
uint8_t v___x_979_; lean_object* v___x_980_; 
v___x_979_ = 0;
v___x_980_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_980_, 0, v_gate_968_);
lean_ctor_set_uint8(v___x_980_, sizeof(void*)*1, v___x_979_);
v___y_962_ = v___x_980_;
goto v___jp_961_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_invert___boxed(lean_object* v_00_u03b1_982_, lean_object* v_inst_983_, lean_object* v_inst_984_, lean_object* v_aig_985_, lean_object* v_input_986_, lean_object* v_linv_987_, lean_object* v_rinv_988_){
_start:
{
uint8_t v_linv_boxed_989_; uint8_t v_rinv_boxed_990_; lean_object* v_res_991_; 
v_linv_boxed_989_ = lean_unbox(v_linv_987_);
v_rinv_boxed_990_ = lean_unbox(v_rinv_988_);
v_res_991_ = l_Std_Sat_AIG_BinaryInput_invert(v_00_u03b1_982_, v_inst_983_, v_inst_984_, v_aig_985_, v_input_986_, v_linv_boxed_989_, v_rinv_boxed_990_);
lean_dec_ref(v_aig_985_);
lean_dec_ref(v_inst_984_);
lean_dec_ref(v_inst_983_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_TernaryInput_cast___redArg(lean_object* v_input_992_){
_start:
{
lean_object* v_discr_993_; lean_object* v_lhs_994_; lean_object* v_rhs_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1029_; 
v_discr_993_ = lean_ctor_get(v_input_992_, 0);
v_lhs_994_ = lean_ctor_get(v_input_992_, 1);
v_rhs_995_ = lean_ctor_get(v_input_992_, 2);
v_isSharedCheck_1029_ = !lean_is_exclusive(v_input_992_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_997_ = v_input_992_;
v_isShared_998_ = v_isSharedCheck_1029_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_rhs_995_);
lean_inc(v_lhs_994_);
lean_inc(v_discr_993_);
lean_dec(v_input_992_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1029_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v_gate_999_; uint8_t v_invert_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1028_; 
v_gate_999_ = lean_ctor_get(v_discr_993_, 0);
v_invert_1000_ = lean_ctor_get_uint8(v_discr_993_, sizeof(void*)*1);
v_isSharedCheck_1028_ = !lean_is_exclusive(v_discr_993_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1002_ = v_discr_993_;
v_isShared_1003_ = v_isSharedCheck_1028_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_gate_999_);
lean_dec(v_discr_993_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1028_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v_gate_1004_; uint8_t v_invert_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1027_; 
v_gate_1004_ = lean_ctor_get(v_lhs_994_, 0);
v_invert_1005_ = lean_ctor_get_uint8(v_lhs_994_, sizeof(void*)*1);
v_isSharedCheck_1027_ = !lean_is_exclusive(v_lhs_994_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1007_ = v_lhs_994_;
v_isShared_1008_ = v_isSharedCheck_1027_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_gate_1004_);
lean_dec(v_lhs_994_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1027_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v_gate_1009_; uint8_t v_invert_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1026_; 
v_gate_1009_ = lean_ctor_get(v_rhs_995_, 0);
v_invert_1010_ = lean_ctor_get_uint8(v_rhs_995_, sizeof(void*)*1);
v_isSharedCheck_1026_ = !lean_is_exclusive(v_rhs_995_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1012_ = v_rhs_995_;
v_isShared_1013_ = v_isSharedCheck_1026_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_gate_1009_);
lean_dec(v_rhs_995_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1026_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 0, v_gate_999_);
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_gate_999_);
v___x_1015_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
lean_object* v___x_1017_; 
lean_ctor_set_uint8(v___x_1015_, sizeof(void*)*1, v_invert_1000_);
if (v_isShared_1008_ == 0)
{
v___x_1017_ = v___x_1007_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_gate_1004_);
lean_ctor_set_uint8(v_reuseFailAlloc_1024_, sizeof(void*)*1, v_invert_1005_);
v___x_1017_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
lean_object* v___x_1019_; 
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 0, v_gate_1009_);
v___x_1019_ = v___x_1002_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_gate_1009_);
v___x_1019_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
lean_object* v___x_1021_; 
lean_ctor_set_uint8(v___x_1019_, sizeof(void*)*1, v_invert_1010_);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 2, v___x_1019_);
lean_ctor_set(v___x_997_, 1, v___x_1017_);
lean_ctor_set(v___x_997_, 0, v___x_1015_);
v___x_1021_ = v___x_997_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v___x_1015_);
lean_ctor_set(v_reuseFailAlloc_1022_, 1, v___x_1017_);
lean_ctor_set(v_reuseFailAlloc_1022_, 2, v___x_1019_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_TernaryInput_cast(lean_object* v_00_u03b1_1030_, lean_object* v_inst_1031_, lean_object* v_inst_1032_, lean_object* v_aig1_1033_, lean_object* v_aig2_1034_, lean_object* v_input_1035_, lean_object* v_h_1036_){
_start:
{
lean_object* v_discr_1037_; lean_object* v_lhs_1038_; lean_object* v_rhs_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1073_; 
v_discr_1037_ = lean_ctor_get(v_input_1035_, 0);
v_lhs_1038_ = lean_ctor_get(v_input_1035_, 1);
v_rhs_1039_ = lean_ctor_get(v_input_1035_, 2);
v_isSharedCheck_1073_ = !lean_is_exclusive(v_input_1035_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1041_ = v_input_1035_;
v_isShared_1042_ = v_isSharedCheck_1073_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_rhs_1039_);
lean_inc(v_lhs_1038_);
lean_inc(v_discr_1037_);
lean_dec(v_input_1035_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1073_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v_gate_1043_; uint8_t v_invert_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1072_; 
v_gate_1043_ = lean_ctor_get(v_discr_1037_, 0);
v_invert_1044_ = lean_ctor_get_uint8(v_discr_1037_, sizeof(void*)*1);
v_isSharedCheck_1072_ = !lean_is_exclusive(v_discr_1037_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1046_ = v_discr_1037_;
v_isShared_1047_ = v_isSharedCheck_1072_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_gate_1043_);
lean_dec(v_discr_1037_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1072_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v_gate_1048_; uint8_t v_invert_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1071_; 
v_gate_1048_ = lean_ctor_get(v_lhs_1038_, 0);
v_invert_1049_ = lean_ctor_get_uint8(v_lhs_1038_, sizeof(void*)*1);
v_isSharedCheck_1071_ = !lean_is_exclusive(v_lhs_1038_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1051_ = v_lhs_1038_;
v_isShared_1052_ = v_isSharedCheck_1071_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_gate_1048_);
lean_dec(v_lhs_1038_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1071_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v_gate_1053_; uint8_t v_invert_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1070_; 
v_gate_1053_ = lean_ctor_get(v_rhs_1039_, 0);
v_invert_1054_ = lean_ctor_get_uint8(v_rhs_1039_, sizeof(void*)*1);
v_isSharedCheck_1070_ = !lean_is_exclusive(v_rhs_1039_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1056_ = v_rhs_1039_;
v_isShared_1057_ = v_isSharedCheck_1070_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_gate_1053_);
lean_dec(v_rhs_1039_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1070_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1059_; 
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 0, v_gate_1043_);
v___x_1059_ = v___x_1056_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_gate_1043_);
v___x_1059_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
lean_object* v___x_1061_; 
lean_ctor_set_uint8(v___x_1059_, sizeof(void*)*1, v_invert_1044_);
if (v_isShared_1052_ == 0)
{
v___x_1061_ = v___x_1051_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_gate_1048_);
lean_ctor_set_uint8(v_reuseFailAlloc_1068_, sizeof(void*)*1, v_invert_1049_);
v___x_1061_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
lean_object* v___x_1063_; 
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 0, v_gate_1053_);
v___x_1063_ = v___x_1046_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_gate_1053_);
v___x_1063_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
lean_object* v___x_1065_; 
lean_ctor_set_uint8(v___x_1063_, sizeof(void*)*1, v_invert_1054_);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 2, v___x_1063_);
lean_ctor_set(v___x_1041_, 1, v___x_1061_);
lean_ctor_set(v___x_1041_, 0, v___x_1059_);
v___x_1065_ = v___x_1041_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v___x_1059_);
lean_ctor_set(v_reuseFailAlloc_1066_, 1, v___x_1061_);
lean_ctor_set(v_reuseFailAlloc_1066_, 2, v___x_1063_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_TernaryInput_cast___boxed(lean_object* v_00_u03b1_1074_, lean_object* v_inst_1075_, lean_object* v_inst_1076_, lean_object* v_aig1_1077_, lean_object* v_aig2_1078_, lean_object* v_input_1079_, lean_object* v_h_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Std_Sat_AIG_TernaryInput_cast(v_00_u03b1_1074_, v_inst_1075_, v_inst_1076_, v_aig1_1077_, v_aig2_1078_, v_input_1079_, v_h_1080_);
lean_dec_ref(v_aig2_1078_);
lean_dec_ref(v_aig1_1077_);
lean_dec_ref(v_inst_1076_);
lean_dec_ref(v_inst_1075_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_invEdgeStyle(uint8_t v_isInv_1084_){
_start:
{
if (v_isInv_1084_ == 0)
{
lean_object* v___x_1085_; 
v___x_1085_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_invEdgeStyle___closed__0));
return v___x_1085_;
}
else
{
lean_object* v___x_1086_; 
v___x_1086_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_invEdgeStyle___closed__1));
return v___x_1086_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_invEdgeStyle___boxed(lean_object* v_isInv_1087_){
_start:
{
uint8_t v_isInv_boxed_1088_; lean_object* v_res_1089_; 
v_isInv_boxed_1088_ = lean_unbox(v_isInv_1087_);
v_res_1089_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v_isInv_boxed_1088_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___redArg(lean_object* v_acc_1094_, lean_object* v_decls_1095_, lean_object* v_idx_1096_, lean_object* v_a_1097_){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___f_1100_; lean_object* v___f_1101_; uint8_t v___x_1102_; 
v___x_1098_ = lean_array_get_size(v_decls_1095_);
v___x_1099_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_1099_, 0, v___x_1098_);
v___f_1100_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1100_, 0, v___x_1099_);
v___f_1101_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___redArg___closed__0));
lean_inc(v_idx_1096_);
lean_inc_ref(v___f_1100_);
v___x_1102_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1100_, v___f_1101_, v_a_1097_, v_idx_1096_);
if (v___x_1102_ == 0)
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1103_ = lean_box(0);
lean_inc(v_idx_1096_);
v___x_1104_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___f_1100_, v___f_1101_, v_a_1097_, v_idx_1096_, v___x_1103_);
v___x_1105_ = lean_array_fget_borrowed(v_decls_1095_, v_idx_1096_);
if (lean_obj_tag(v___x_1105_) == 2)
{
lean_object* v_l_1106_; lean_object* v_r_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; uint8_t v___y_1111_; lean_object* v___y_1112_; uint8_t v___y_1113_; uint8_t v___y_1137_; lean_object* v___x_1143_; lean_object* v___x_1144_; uint8_t v___x_1145_; 
v_l_1106_ = lean_ctor_get(v___x_1105_, 0);
v_r_1107_ = lean_ctor_get(v___x_1105_, 1);
v___x_1108_ = lean_unsigned_to_nat(1u);
v___x_1109_ = lean_nat_shiftr(v_l_1106_, v___x_1108_);
v___x_1143_ = lean_nat_land(v___x_1108_, v_l_1106_);
v___x_1144_ = lean_unsigned_to_nat(0u);
v___x_1145_ = lean_nat_dec_eq(v___x_1143_, v___x_1144_);
lean_dec(v___x_1143_);
if (v___x_1145_ == 0)
{
uint8_t v___x_1146_; 
v___x_1146_ = 1;
v___y_1137_ = v___x_1146_;
goto v___jp_1136_;
}
else
{
v___y_1137_ = v___x_1102_;
goto v___jp_1136_;
}
v___jp_1110_:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v_fst_1133_; lean_object* v_snd_1134_; 
v___x_1114_ = l_Nat_reprFast(v_idx_1096_);
v___x_1115_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___redArg___closed__1));
lean_inc_ref(v___x_1114_);
v___x_1116_ = lean_string_append(v___x_1114_, v___x_1115_);
lean_inc(v___x_1109_);
v___x_1117_ = l_Nat_reprFast(v___x_1109_);
v___x_1118_ = lean_string_append(v___x_1116_, v___x_1117_);
lean_dec_ref(v___x_1117_);
v___x_1119_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_1111_);
v___x_1120_ = lean_string_append(v___x_1118_, v___x_1119_);
lean_dec_ref(v___x_1119_);
v___x_1121_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___redArg___closed__2));
v___x_1122_ = lean_string_append(v___x_1120_, v___x_1121_);
v___x_1123_ = lean_string_append(v___x_1122_, v___x_1114_);
lean_dec_ref(v___x_1114_);
v___x_1124_ = lean_string_append(v___x_1123_, v___x_1115_);
lean_inc(v___y_1112_);
v___x_1125_ = l_Nat_reprFast(v___y_1112_);
v___x_1126_ = lean_string_append(v___x_1124_, v___x_1125_);
lean_dec_ref(v___x_1125_);
v___x_1127_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_1113_);
v___x_1128_ = lean_string_append(v___x_1126_, v___x_1127_);
lean_dec_ref(v___x_1127_);
v___x_1129_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___redArg___closed__3));
v___x_1130_ = lean_string_append(v___x_1128_, v___x_1129_);
v___x_1131_ = lean_string_append(v_acc_1094_, v___x_1130_);
lean_dec_ref(v___x_1130_);
v___x_1132_ = l_Std_Sat_AIG_toGraphviz_go___redArg(v___x_1131_, v_decls_1095_, v___x_1109_, v___x_1104_);
v_fst_1133_ = lean_ctor_get(v___x_1132_, 0);
lean_inc(v_fst_1133_);
v_snd_1134_ = lean_ctor_get(v___x_1132_, 1);
lean_inc(v_snd_1134_);
lean_dec_ref(v___x_1132_);
v_acc_1094_ = v_fst_1133_;
v_idx_1096_ = v___y_1112_;
v_a_1097_ = v_snd_1134_;
goto _start;
}
v___jp_1136_:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; uint8_t v___x_1141_; 
v___x_1138_ = lean_nat_shiftr(v_r_1107_, v___x_1108_);
v___x_1139_ = lean_nat_land(v___x_1108_, v_r_1107_);
v___x_1140_ = lean_unsigned_to_nat(0u);
v___x_1141_ = lean_nat_dec_eq(v___x_1139_, v___x_1140_);
lean_dec(v___x_1139_);
if (v___x_1141_ == 0)
{
uint8_t v___x_1142_; 
v___x_1142_ = 1;
v___y_1111_ = v___y_1137_;
v___y_1112_ = v___x_1138_;
v___y_1113_ = v___x_1142_;
goto v___jp_1110_;
}
else
{
v___y_1111_ = v___y_1137_;
v___y_1112_ = v___x_1138_;
v___y_1113_ = v___x_1102_;
goto v___jp_1110_;
}
}
}
else
{
lean_object* v___x_1147_; 
lean_dec(v_idx_1096_);
v___x_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1147_, 0, v_acc_1094_);
lean_ctor_set(v___x_1147_, 1, v___x_1104_);
return v___x_1147_;
}
}
else
{
lean_object* v___x_1148_; 
lean_dec_ref(v___f_1100_);
lean_dec(v_idx_1096_);
v___x_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1148_, 0, v_acc_1094_);
lean_ctor_set(v___x_1148_, 1, v_a_1097_);
return v___x_1148_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___redArg___boxed(lean_object* v_acc_1149_, lean_object* v_decls_1150_, lean_object* v_idx_1151_, lean_object* v_a_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Std_Sat_AIG_toGraphviz_go___redArg(v_acc_1149_, v_decls_1150_, v_idx_1151_, v_a_1152_);
lean_dec_ref(v_decls_1150_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go(lean_object* v_00_u03b1_1154_, lean_object* v_inst_1155_, lean_object* v_inst_1156_, lean_object* v_inst_1157_, lean_object* v_acc_1158_, lean_object* v_decls_1159_, lean_object* v_hinv_1160_, lean_object* v_idx_1161_, lean_object* v_hidx_1162_, lean_object* v_a_1163_){
_start:
{
lean_object* v___x_1164_; 
v___x_1164_ = l_Std_Sat_AIG_toGraphviz_go___redArg(v_acc_1158_, v_decls_1159_, v_idx_1161_, v_a_1163_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___boxed(lean_object* v_00_u03b1_1165_, lean_object* v_inst_1166_, lean_object* v_inst_1167_, lean_object* v_inst_1168_, lean_object* v_acc_1169_, lean_object* v_decls_1170_, lean_object* v_hinv_1171_, lean_object* v_idx_1172_, lean_object* v_hidx_1173_, lean_object* v_a_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Std_Sat_AIG_toGraphviz_go(v_00_u03b1_1165_, v_inst_1166_, v_inst_1167_, v_inst_1168_, v_acc_1169_, v_decls_1170_, v_hinv_1171_, v_idx_1172_, v_hidx_1173_, v_a_1174_);
lean_dec_ref(v_decls_1170_);
lean_dec_ref(v_inst_1168_);
lean_dec_ref(v_inst_1167_);
lean_dec_ref(v_inst_1166_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter___redArg(lean_object* v_x_1176_, lean_object* v_h__1_1177_, lean_object* v_h__2_1178_, lean_object* v_h__3_1179_){
_start:
{
switch(lean_obj_tag(v_x_1176_))
{
case 0:
{
lean_object* v___x_1180_; 
lean_dec(v_h__3_1179_);
lean_dec(v_h__2_1178_);
v___x_1180_ = lean_apply_1(v_h__1_1177_, lean_box(0));
return v___x_1180_;
}
case 1:
{
lean_object* v_idx_1181_; lean_object* v___x_1182_; 
lean_dec(v_h__3_1179_);
lean_dec(v_h__1_1177_);
v_idx_1181_ = lean_ctor_get(v_x_1176_, 0);
lean_inc(v_idx_1181_);
lean_dec_ref_known(v_x_1176_, 1);
v___x_1182_ = lean_apply_2(v_h__2_1178_, v_idx_1181_, lean_box(0));
return v___x_1182_;
}
default: 
{
lean_object* v_l_1183_; lean_object* v_r_1184_; lean_object* v___x_1185_; 
lean_dec(v_h__2_1178_);
lean_dec(v_h__1_1177_);
v_l_1183_ = lean_ctor_get(v_x_1176_, 0);
lean_inc(v_l_1183_);
v_r_1184_ = lean_ctor_get(v_x_1176_, 1);
lean_inc(v_r_1184_);
lean_dec_ref_known(v_x_1176_, 2);
v___x_1185_ = lean_apply_3(v_h__3_1179_, v_l_1183_, v_r_1184_, lean_box(0));
return v___x_1185_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter(lean_object* v_00_u03b1_1186_, lean_object* v_motive_1187_, lean_object* v_x_1188_, lean_object* v_h__1_1189_, lean_object* v_h__2_1190_, lean_object* v_h__3_1191_){
_start:
{
switch(lean_obj_tag(v_x_1188_))
{
case 0:
{
lean_object* v___x_1192_; 
lean_dec(v_h__3_1191_);
lean_dec(v_h__2_1190_);
v___x_1192_ = lean_apply_1(v_h__1_1189_, lean_box(0));
return v___x_1192_;
}
case 1:
{
lean_object* v_idx_1193_; lean_object* v___x_1194_; 
lean_dec(v_h__3_1191_);
lean_dec(v_h__1_1189_);
v_idx_1193_ = lean_ctor_get(v_x_1188_, 0);
lean_inc(v_idx_1193_);
lean_dec_ref_known(v_x_1188_, 1);
v___x_1194_ = lean_apply_2(v_h__2_1190_, v_idx_1193_, lean_box(0));
return v___x_1194_;
}
default: 
{
lean_object* v_l_1195_; lean_object* v_r_1196_; lean_object* v___x_1197_; 
lean_dec(v_h__2_1190_);
lean_dec(v_h__1_1189_);
v_l_1195_ = lean_ctor_get(v_x_1188_, 0);
lean_inc(v_l_1195_);
v_r_1196_ = lean_ctor_get(v_x_1188_, 1);
lean_inc(v_r_1196_);
lean_dec_ref_known(v_x_1188_, 2);
v___x_1197_ = lean_apply_3(v_h__3_1191_, v_l_1195_, v_r_1196_, lean_box(0));
return v___x_1197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg(lean_object* v_inst_1203_, lean_object* v_decls_1204_, lean_object* v_idx_1205_){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = lean_array_fget_borrowed(v_decls_1204_, v_idx_1205_);
switch(lean_obj_tag(v___x_1206_))
{
case 0:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
lean_dec_ref(v_inst_1203_);
v___x_1207_ = l_Nat_reprFast(v_idx_1205_);
v___x_1208_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__0));
v___x_1209_ = lean_string_append(v___x_1207_, v___x_1208_);
v___x_1210_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__1));
v___x_1211_ = lean_string_append(v___x_1209_, v___x_1210_);
v___x_1212_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__2));
v___x_1213_ = lean_string_append(v___x_1211_, v___x_1212_);
return v___x_1213_;
}
case 1:
{
lean_object* v_idx_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v_idx_1214_ = lean_ctor_get(v___x_1206_, 0);
v___x_1215_ = l_Nat_reprFast(v_idx_1205_);
v___x_1216_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__0));
v___x_1217_ = lean_string_append(v___x_1215_, v___x_1216_);
lean_inc(v_idx_1214_);
v___x_1218_ = lean_apply_1(v_inst_1203_, v_idx_1214_);
v___x_1219_ = lean_string_append(v___x_1217_, v___x_1218_);
lean_dec_ref(v___x_1218_);
v___x_1220_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__3));
v___x_1221_ = lean_string_append(v___x_1219_, v___x_1220_);
return v___x_1221_;
}
default: 
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
lean_dec_ref(v_inst_1203_);
v___x_1222_ = l_Nat_reprFast(v_idx_1205_);
v___x_1223_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__0));
lean_inc_ref(v___x_1222_);
v___x_1224_ = lean_string_append(v___x_1222_, v___x_1223_);
v___x_1225_ = lean_string_append(v___x_1224_, v___x_1222_);
lean_dec_ref(v___x_1222_);
v___x_1226_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__4));
v___x_1227_ = lean_string_append(v___x_1225_, v___x_1226_);
return v___x_1227_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___boxed(lean_object* v_inst_1228_, lean_object* v_decls_1229_, lean_object* v_idx_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg(v_inst_1228_, v_decls_1229_, v_idx_1230_);
lean_dec_ref(v_decls_1229_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString(lean_object* v_00_u03b1_1232_, lean_object* v_inst_1233_, lean_object* v_inst_1234_, lean_object* v_inst_1235_, lean_object* v_decls_1236_, lean_object* v_idx_1237_){
_start:
{
lean_object* v___x_1238_; 
v___x_1238_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg(v_inst_1234_, v_decls_1236_, v_idx_1237_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___boxed(lean_object* v_00_u03b1_1239_, lean_object* v_inst_1240_, lean_object* v_inst_1241_, lean_object* v_inst_1242_, lean_object* v_decls_1243_, lean_object* v_idx_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString(v_00_u03b1_1239_, v_inst_1240_, v_inst_1241_, v_inst_1242_, v_decls_1243_, v_idx_1244_);
lean_dec_ref(v_decls_1243_);
lean_dec_ref(v_inst_1242_);
lean_dec_ref(v_inst_1240_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___redArg___lam__0(lean_object* v_inst_1246_, lean_object* v_decls_1247_, lean_object* v_x1_1248_, lean_object* v_x2_1249_, lean_object* v_x3_1250_){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg(v_inst_1246_, v_decls_1247_, v_x2_1249_);
v___x_1252_ = lean_string_append(v_x1_1248_, v___x_1251_);
lean_dec_ref(v___x_1251_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___redArg___lam__0___boxed(lean_object* v_inst_1253_, lean_object* v_decls_1254_, lean_object* v_x1_1255_, lean_object* v_x2_1256_, lean_object* v_x3_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_Std_Sat_AIG_toGraphviz___redArg___lam__0(v_inst_1253_, v_decls_1254_, v_x1_1255_, v_x2_1256_, v_x3_1257_);
lean_dec_ref(v_decls_1254_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___redArg___lam__1(lean_object* v___x_1259_, lean_object* v___f_1260_, lean_object* v_acc_1261_, lean_object* v_l_1262_){
_start:
{
lean_object* v___x_1263_; 
v___x_1263_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1259_, v___f_1260_, v_acc_1261_, v_l_1262_);
return v___x_1263_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___redArg___closed__1(void){
_start:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1265_ = lean_box(0);
v___x_1266_ = lean_unsigned_to_nat(16u);
v___x_1267_ = lean_mk_array(v___x_1266_, v___x_1265_);
return v___x_1267_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___redArg___closed__2(void){
_start:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1268_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___redArg___closed__1, &l_Std_Sat_AIG_toGraphviz___redArg___closed__1_once, _init_l_Std_Sat_AIG_toGraphviz___redArg___closed__1);
v___x_1269_ = lean_unsigned_to_nat(0u);
v___x_1270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1269_);
lean_ctor_set(v___x_1270_, 1, v___x_1268_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___redArg(lean_object* v_inst_1292_, lean_object* v_entry_1293_){
_start:
{
lean_object* v_aig_1294_; lean_object* v_ref_1295_; lean_object* v_decls_1296_; lean_object* v_gate_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v_fst_1302_; lean_object* v_snd_1303_; lean_object* v___y_1305_; lean_object* v___x_1311_; lean_object* v_buckets_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; 
v_aig_1294_ = lean_ctor_get(v_entry_1293_, 0);
lean_inc_ref(v_aig_1294_);
v_ref_1295_ = lean_ctor_get(v_entry_1293_, 1);
lean_inc_ref(v_ref_1295_);
lean_dec_ref(v_entry_1293_);
v_decls_1296_ = lean_ctor_get(v_aig_1294_, 0);
lean_inc_ref(v_decls_1296_);
lean_dec_ref(v_aig_1294_);
v_gate_1297_ = lean_ctor_get(v_ref_1295_, 0);
lean_inc(v_gate_1297_);
lean_dec_ref(v_ref_1295_);
v___x_1298_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___redArg___closed__0));
v___x_1299_ = lean_unsigned_to_nat(0u);
v___x_1300_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___redArg___closed__2, &l_Std_Sat_AIG_toGraphviz___redArg___closed__2_once, _init_l_Std_Sat_AIG_toGraphviz___redArg___closed__2);
v___x_1301_ = l_Std_Sat_AIG_toGraphviz_go___redArg(v___x_1298_, v_decls_1296_, v_gate_1297_, v___x_1300_);
v_fst_1302_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_fst_1302_);
v_snd_1303_ = lean_ctor_get(v___x_1301_, 1);
lean_inc(v_snd_1303_);
lean_dec_ref(v___x_1301_);
v___x_1311_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___redArg___closed__14));
v_buckets_1312_ = lean_ctor_get(v_snd_1303_, 1);
lean_inc_ref(v_buckets_1312_);
lean_dec(v_snd_1303_);
v___x_1313_ = lean_array_get_size(v_buckets_1312_);
v___x_1314_ = lean_nat_dec_lt(v___x_1299_, v___x_1313_);
if (v___x_1314_ == 0)
{
lean_dec_ref(v_buckets_1312_);
lean_dec_ref(v_decls_1296_);
lean_dec_ref(v_inst_1292_);
v___y_1305_ = v___x_1298_;
goto v___jp_1304_;
}
else
{
lean_object* v___f_1315_; lean_object* v___f_1316_; size_t v___x_1317_; size_t v___x_1318_; lean_object* v___x_1319_; 
v___f_1315_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_toGraphviz___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1315_, 0, v_inst_1292_);
lean_closure_set(v___f_1315_, 1, v_decls_1296_);
v___f_1316_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_toGraphviz___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1316_, 0, v___x_1311_);
lean_closure_set(v___f_1316_, 1, v___f_1315_);
v___x_1317_ = ((size_t)0ULL);
v___x_1318_ = lean_usize_of_nat(v___x_1313_);
v___x_1319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1311_, v___f_1316_, v_buckets_1312_, v___x_1317_, v___x_1318_, v___x_1298_);
v___y_1305_ = v___x_1319_;
goto v___jp_1304_;
}
v___jp_1304_:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1306_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___redArg___closed__3));
v___x_1307_ = lean_string_append(v___x_1306_, v___y_1305_);
lean_dec_ref(v___y_1305_);
v___x_1308_ = lean_string_append(v___x_1307_, v_fst_1302_);
lean_dec(v_fst_1302_);
v___x_1309_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___redArg___closed__4));
v___x_1310_ = lean_string_append(v___x_1308_, v___x_1309_);
return v___x_1310_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz(lean_object* v_00_u03b1_1320_, lean_object* v_inst_1321_, lean_object* v_inst_1322_, lean_object* v_inst_1323_, lean_object* v_entry_1324_){
_start:
{
lean_object* v___x_1325_; 
v___x_1325_ = l_Std_Sat_AIG_toGraphviz___redArg(v_inst_1322_, v_entry_1324_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___boxed(lean_object* v_00_u03b1_1326_, lean_object* v_inst_1327_, lean_object* v_inst_1328_, lean_object* v_inst_1329_, lean_object* v_entry_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_Std_Sat_AIG_toGraphviz(v_00_u03b1_1326_, v_inst_1327_, v_inst_1328_, v_inst_1329_, v_entry_1330_);
lean_dec_ref(v_inst_1329_);
lean_dec_ref(v_inst_1327_);
return v_res_1331_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote_go___redArg(lean_object* v_x_1332_, lean_object* v_decls_1333_, lean_object* v_assign_1334_){
_start:
{
uint8_t v___y_1336_; uint8_t v___y_1337_; lean_object* v___x_1339_; 
v___x_1339_ = lean_array_fget_borrowed(v_decls_1333_, v_x_1332_);
switch(lean_obj_tag(v___x_1339_))
{
case 0:
{
uint8_t v___x_1340_; 
lean_dec_ref(v_assign_1334_);
v___x_1340_ = 0;
return v___x_1340_;
}
case 1:
{
lean_object* v_idx_1341_; lean_object* v___x_1342_; uint8_t v___x_1343_; 
v_idx_1341_ = lean_ctor_get(v___x_1339_, 0);
lean_inc(v_idx_1341_);
v___x_1342_ = lean_apply_1(v_assign_1334_, v_idx_1341_);
v___x_1343_ = lean_unbox(v___x_1342_);
return v___x_1343_;
}
default: 
{
lean_object* v_l_1344_; lean_object* v_r_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; uint8_t v_lval_1348_; lean_object* v___x_1349_; uint8_t v_rval_1350_; uint8_t v___y_1352_; uint8_t v___y_1357_; lean_object* v___x_1359_; lean_object* v___x_1360_; uint8_t v___x_1361_; 
v_l_1344_ = lean_ctor_get(v___x_1339_, 0);
v_r_1345_ = lean_ctor_get(v___x_1339_, 1);
v___x_1346_ = lean_unsigned_to_nat(1u);
v___x_1347_ = lean_nat_shiftr(v_l_1344_, v___x_1346_);
lean_inc_ref(v_assign_1334_);
v_lval_1348_ = l_Std_Sat_AIG_denote_go___redArg(v___x_1347_, v_decls_1333_, v_assign_1334_);
lean_dec(v___x_1347_);
v___x_1349_ = lean_nat_shiftr(v_r_1345_, v___x_1346_);
v_rval_1350_ = l_Std_Sat_AIG_denote_go___redArg(v___x_1349_, v_decls_1333_, v_assign_1334_);
lean_dec(v___x_1349_);
v___x_1359_ = lean_nat_land(v___x_1346_, v_l_1344_);
v___x_1360_ = lean_unsigned_to_nat(0u);
v___x_1361_ = lean_nat_dec_eq(v___x_1359_, v___x_1360_);
lean_dec(v___x_1359_);
if (v___x_1361_ == 0)
{
v___y_1357_ = v_lval_1348_;
goto v___jp_1356_;
}
else
{
if (v_lval_1348_ == 0)
{
v___y_1357_ = v___x_1361_;
goto v___jp_1356_;
}
else
{
uint8_t v___x_1362_; 
v___x_1362_ = 0;
v___y_1352_ = v___x_1362_;
goto v___jp_1351_;
}
}
v___jp_1351_:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; uint8_t v___x_1355_; 
v___x_1353_ = lean_nat_land(v___x_1346_, v_r_1345_);
v___x_1354_ = lean_unsigned_to_nat(0u);
v___x_1355_ = lean_nat_dec_eq(v___x_1353_, v___x_1354_);
lean_dec(v___x_1353_);
if (v___x_1355_ == 0)
{
v___y_1336_ = v___y_1352_;
v___y_1337_ = v_rval_1350_;
goto v___jp_1335_;
}
else
{
if (v_rval_1350_ == 0)
{
v___y_1336_ = v___y_1352_;
v___y_1337_ = v___x_1355_;
goto v___jp_1335_;
}
else
{
return v_rval_1350_;
}
}
}
v___jp_1356_:
{
if (v___y_1357_ == 0)
{
v___y_1352_ = v___y_1357_;
goto v___jp_1351_;
}
else
{
uint8_t v___x_1358_; 
v___x_1358_ = 0;
return v___x_1358_;
}
}
}
}
v___jp_1335_:
{
if (v___y_1337_ == 0)
{
uint8_t v___x_1338_; 
v___x_1338_ = 1;
return v___x_1338_;
}
else
{
return v___y_1336_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote_go___redArg___boxed(lean_object* v_x_1363_, lean_object* v_decls_1364_, lean_object* v_assign_1365_){
_start:
{
uint8_t v_res_1366_; lean_object* v_r_1367_; 
v_res_1366_ = l_Std_Sat_AIG_denote_go___redArg(v_x_1363_, v_decls_1364_, v_assign_1365_);
lean_dec_ref(v_decls_1364_);
lean_dec(v_x_1363_);
v_r_1367_ = lean_box(v_res_1366_);
return v_r_1367_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote_go(lean_object* v_00_u03b1_1368_, lean_object* v_x_1369_, lean_object* v_decls_1370_, lean_object* v_assign_1371_, lean_object* v_h1_1372_, lean_object* v_h2_1373_){
_start:
{
uint8_t v___x_1374_; 
v___x_1374_ = l_Std_Sat_AIG_denote_go___redArg(v_x_1369_, v_decls_1370_, v_assign_1371_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote_go___boxed(lean_object* v_00_u03b1_1375_, lean_object* v_x_1376_, lean_object* v_decls_1377_, lean_object* v_assign_1378_, lean_object* v_h1_1379_, lean_object* v_h2_1380_){
_start:
{
uint8_t v_res_1381_; lean_object* v_r_1382_; 
v_res_1381_ = l_Std_Sat_AIG_denote_go(v_00_u03b1_1375_, v_x_1376_, v_decls_1377_, v_assign_1378_, v_h1_1379_, v_h2_1380_);
lean_dec_ref(v_decls_1377_);
lean_dec(v_x_1376_);
v_r_1382_ = lean_box(v_res_1381_);
return v_r_1382_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote___redArg(lean_object* v_assign_1383_, lean_object* v_entry_1384_){
_start:
{
lean_object* v_ref_1385_; lean_object* v_aig_1386_; lean_object* v_gate_1387_; uint8_t v_invert_1388_; lean_object* v_decls_1389_; uint8_t v___x_1390_; 
v_ref_1385_ = lean_ctor_get(v_entry_1384_, 1);
v_aig_1386_ = lean_ctor_get(v_entry_1384_, 0);
v_gate_1387_ = lean_ctor_get(v_ref_1385_, 0);
v_invert_1388_ = lean_ctor_get_uint8(v_ref_1385_, sizeof(void*)*1);
v_decls_1389_ = lean_ctor_get(v_aig_1386_, 0);
v___x_1390_ = l_Std_Sat_AIG_denote_go___redArg(v_gate_1387_, v_decls_1389_, v_assign_1383_);
if (v_invert_1388_ == 0)
{
return v___x_1390_;
}
else
{
if (v___x_1390_ == 0)
{
return v_invert_1388_;
}
else
{
uint8_t v___x_1391_; 
v___x_1391_ = 0;
return v___x_1391_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote___redArg___boxed(lean_object* v_assign_1392_, lean_object* v_entry_1393_){
_start:
{
uint8_t v_res_1394_; lean_object* v_r_1395_; 
v_res_1394_ = l_Std_Sat_AIG_denote___redArg(v_assign_1392_, v_entry_1393_);
lean_dec_ref(v_entry_1393_);
v_r_1395_ = lean_box(v_res_1394_);
return v_r_1395_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote(lean_object* v_00_u03b1_1396_, lean_object* v_inst_1397_, lean_object* v_inst_1398_, lean_object* v_assign_1399_, lean_object* v_entry_1400_){
_start:
{
uint8_t v___x_1401_; 
v___x_1401_ = l_Std_Sat_AIG_denote___redArg(v_assign_1399_, v_entry_1400_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote___boxed(lean_object* v_00_u03b1_1402_, lean_object* v_inst_1403_, lean_object* v_inst_1404_, lean_object* v_assign_1405_, lean_object* v_entry_1406_){
_start:
{
uint8_t v_res_1407_; lean_object* v_r_1408_; 
v_res_1407_ = l_Std_Sat_AIG_denote(v_00_u03b1_1402_, v_inst_1403_, v_inst_1404_, v_assign_1405_, v_entry_1406_);
lean_dec_ref(v_entry_1406_);
lean_dec_ref(v_inst_1404_);
lean_dec_ref(v_inst_1403_);
v_r_1408_ = lean_box(v_res_1407_);
return v_r_1408_;
}
}
static lean_object* _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4(void){
_start:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1488_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__3));
v___x_1489_ = l_String_toRawSubstring_x27(v___x_1488_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1(lean_object* v_x_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_){
_start:
{
lean_object* v___x_1511_; uint8_t v___x_1512_; 
v___x_1511_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
lean_inc(v_x_1508_);
v___x_1512_ = l_Lean_Syntax_isOfKind(v_x_1508_, v___x_1511_);
if (v___x_1512_ == 0)
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
lean_dec(v_x_1508_);
v___x_1513_ = lean_box(1);
v___x_1514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1513_);
lean_ctor_set(v___x_1514_, 1, v_a_1510_);
return v___x_1514_;
}
else
{
lean_object* v_quotContext_1515_; lean_object* v_currMacroScope_1516_; lean_object* v_ref_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; uint8_t v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v_quotContext_1515_ = lean_ctor_get(v_a_1509_, 1);
v_currMacroScope_1516_ = lean_ctor_get(v_a_1509_, 2);
v_ref_1517_ = lean_ctor_get(v_a_1509_, 5);
v___x_1518_ = lean_unsigned_to_nat(1u);
v___x_1519_ = l_Lean_Syntax_getArg(v_x_1508_, v___x_1518_);
v___x_1520_ = lean_unsigned_to_nat(3u);
v___x_1521_ = l_Lean_Syntax_getArg(v_x_1508_, v___x_1520_);
lean_dec(v_x_1508_);
v___x_1522_ = 0;
v___x_1523_ = l_Lean_SourceInfo_fromRef(v_ref_1517_, v___x_1522_);
v___x_1524_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2));
v___x_1525_ = lean_obj_once(&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4, &l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4_once, _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4);
v___x_1526_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__5));
lean_inc(v_currMacroScope_1516_);
lean_inc(v_quotContext_1515_);
v___x_1527_ = l_Lean_addMacroScope(v_quotContext_1515_, v___x_1526_, v_currMacroScope_1516_);
v___x_1528_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__10));
lean_inc_n(v___x_1523_, 2);
v___x_1529_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1523_);
lean_ctor_set(v___x_1529_, 1, v___x_1525_);
lean_ctor_set(v___x_1529_, 2, v___x_1527_);
lean_ctor_set(v___x_1529_, 3, v___x_1528_);
v___x_1530_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__9));
v___x_1531_ = l_Lean_Syntax_node2(v___x_1523_, v___x_1530_, v___x_1521_, v___x_1519_);
v___x_1532_ = l_Lean_Syntax_node2(v___x_1523_, v___x_1524_, v___x_1529_, v___x_1531_);
v___x_1533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1532_);
lean_ctor_set(v___x_1533_, 1, v_a_1510_);
return v___x_1533_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___boxed(lean_object* v_x_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_){
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1(v_x_1534_, v_a_1535_, v_a_1536_);
lean_dec_ref(v_a_1535_);
return v_res_1537_;
}
}
static lean_object* _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__7(void){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1554_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___redArg___closed__0));
v___x_1555_ = l_String_toRawSubstring_x27(v___x_1554_);
return v___x_1555_;
}
}
static lean_object* _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__12(void){
_start:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1566_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__11));
v___x_1567_ = l_String_toRawSubstring_x27(v___x_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1(lean_object* v_x_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_){
_start:
{
lean_object* v___x_1594_; uint8_t v___x_1595_; 
v___x_1594_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__1));
lean_inc(v_x_1591_);
v___x_1595_ = l_Lean_Syntax_isOfKind(v_x_1591_, v___x_1594_);
if (v___x_1595_ == 0)
{
lean_object* v___x_1596_; lean_object* v___x_1597_; 
lean_dec(v_x_1591_);
v___x_1596_ = lean_box(1);
v___x_1597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1596_);
lean_ctor_set(v___x_1597_, 1, v_a_1593_);
return v___x_1597_;
}
else
{
lean_object* v_quotContext_1598_; lean_object* v_currMacroScope_1599_; lean_object* v_ref_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; uint8_t v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
v_quotContext_1598_ = lean_ctor_get(v_a_1592_, 1);
v_currMacroScope_1599_ = lean_ctor_get(v_a_1592_, 2);
v_ref_1600_ = lean_ctor_get(v_a_1592_, 5);
v___x_1601_ = lean_unsigned_to_nat(1u);
v___x_1602_ = l_Lean_Syntax_getArg(v_x_1591_, v___x_1601_);
v___x_1603_ = lean_unsigned_to_nat(3u);
v___x_1604_ = l_Lean_Syntax_getArg(v_x_1591_, v___x_1603_);
v___x_1605_ = lean_unsigned_to_nat(5u);
v___x_1606_ = l_Lean_Syntax_getArg(v_x_1591_, v___x_1605_);
lean_dec(v_x_1591_);
v___x_1607_ = 0;
v___x_1608_ = l_Lean_SourceInfo_fromRef(v_ref_1600_, v___x_1607_);
v___x_1609_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2));
v___x_1610_ = lean_obj_once(&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4, &l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4_once, _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4);
v___x_1611_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__5));
lean_inc_n(v_currMacroScope_1599_, 3);
lean_inc_n(v_quotContext_1598_, 3);
v___x_1612_ = l_Lean_addMacroScope(v_quotContext_1598_, v___x_1611_, v_currMacroScope_1599_);
v___x_1613_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__10));
lean_inc_n(v___x_1608_, 11);
v___x_1614_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1608_);
lean_ctor_set(v___x_1614_, 1, v___x_1610_);
lean_ctor_set(v___x_1614_, 2, v___x_1612_);
lean_ctor_set(v___x_1614_, 3, v___x_1613_);
v___x_1615_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__9));
v___x_1616_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__1));
v___x_1617_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__3));
v___x_1618_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__4));
v___x_1619_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1608_);
lean_ctor_set(v___x_1619_, 1, v___x_1618_);
v___x_1620_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__6));
v___x_1621_ = lean_obj_once(&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__7, &l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__7_once, _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__7);
v___x_1622_ = lean_box(0);
v___x_1623_ = l_Lean_addMacroScope(v_quotContext_1598_, v___x_1622_, v_currMacroScope_1599_);
v___x_1624_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__10));
v___x_1625_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1608_);
lean_ctor_set(v___x_1625_, 1, v___x_1621_);
lean_ctor_set(v___x_1625_, 2, v___x_1623_);
lean_ctor_set(v___x_1625_, 3, v___x_1624_);
v___x_1626_ = l_Lean_Syntax_node1(v___x_1608_, v___x_1620_, v___x_1625_);
v___x_1627_ = l_Lean_Syntax_node2(v___x_1608_, v___x_1617_, v___x_1619_, v___x_1626_);
v___x_1628_ = lean_obj_once(&l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__12, &l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__12_once, _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__12);
v___x_1629_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__15));
v___x_1630_ = l_Lean_addMacroScope(v_quotContext_1598_, v___x_1629_, v_currMacroScope_1599_);
v___x_1631_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__20));
v___x_1632_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1608_);
lean_ctor_set(v___x_1632_, 1, v___x_1628_);
lean_ctor_set(v___x_1632_, 2, v___x_1630_);
lean_ctor_set(v___x_1632_, 3, v___x_1631_);
v___x_1633_ = l_Lean_Syntax_node2(v___x_1608_, v___x_1615_, v___x_1602_, v___x_1604_);
v___x_1634_ = l_Lean_Syntax_node2(v___x_1608_, v___x_1609_, v___x_1632_, v___x_1633_);
v___x_1635_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__21));
v___x_1636_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1608_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
v___x_1637_ = l_Lean_Syntax_node3(v___x_1608_, v___x_1616_, v___x_1627_, v___x_1634_, v___x_1636_);
v___x_1638_ = l_Lean_Syntax_node2(v___x_1608_, v___x_1615_, v___x_1606_, v___x_1637_);
v___x_1639_ = l_Lean_Syntax_node2(v___x_1608_, v___x_1609_, v___x_1614_, v___x_1638_);
v___x_1640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1639_);
lean_ctor_set(v___x_1640_, 1, v_a_1593_);
return v___x_1640_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___boxed(lean_object* v_x_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1(v_x_1641_, v_a_1642_, v_a_1643_);
lean_dec_ref(v_a_1642_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_unexpandDenote(lean_object* v_x_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_){
_start:
{
lean_object* v___x_1702_; uint8_t v___x_1703_; 
v___x_1702_ = ((lean_object*)(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2));
lean_inc(v_x_1699_);
v___x_1703_ = l_Lean_Syntax_isOfKind(v_x_1699_, v___x_1702_);
if (v___x_1703_ == 0)
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
lean_dec(v_x_1699_);
v___x_1704_ = lean_box(0);
v___x_1705_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1704_);
lean_ctor_set(v___x_1705_, 1, v_a_1701_);
return v___x_1705_;
}
else
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; uint8_t v___x_1709_; 
v___x_1706_ = lean_unsigned_to_nat(1u);
v___x_1707_ = l_Lean_Syntax_getArg(v_x_1699_, v___x_1706_);
lean_dec(v_x_1699_);
v___x_1708_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1707_);
v___x_1709_ = l_Lean_Syntax_matchesNull(v___x_1707_, v___x_1708_);
if (v___x_1709_ == 0)
{
lean_object* v___x_1710_; lean_object* v___x_1711_; 
lean_dec(v___x_1707_);
v___x_1710_ = lean_box(0);
v___x_1711_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1710_);
lean_ctor_set(v___x_1711_, 1, v_a_1701_);
return v___x_1711_;
}
else
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; uint8_t v___x_1715_; 
v___x_1712_ = lean_unsigned_to_nat(0u);
v___x_1713_ = l_Lean_Syntax_getArg(v___x_1707_, v___x_1712_);
v___x_1714_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__1));
lean_inc(v___x_1713_);
v___x_1715_ = l_Lean_Syntax_isOfKind(v___x_1713_, v___x_1714_);
if (v___x_1715_ == 0)
{
lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1716_ = l_Lean_Syntax_getArg(v___x_1707_, v___x_1706_);
lean_dec(v___x_1707_);
v___x_1717_ = l_Lean_SourceInfo_fromRef(v_a_1700_, v___x_1715_);
v___x_1718_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1719_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1717_, 3);
v___x_1720_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1720_, 0, v___x_1717_);
lean_ctor_set(v___x_1720_, 1, v___x_1719_);
v___x_1721_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1722_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1717_);
lean_ctor_set(v___x_1722_, 1, v___x_1721_);
v___x_1723_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1724_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1717_);
lean_ctor_set(v___x_1724_, 1, v___x_1723_);
v___x_1725_ = l_Lean_Syntax_node5(v___x_1717_, v___x_1718_, v___x_1720_, v___x_1713_, v___x_1722_, v___x_1716_, v___x_1724_);
v___x_1726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1725_);
lean_ctor_set(v___x_1726_, 1, v_a_1701_);
return v___x_1726_;
}
else
{
lean_object* v___x_1727_; uint8_t v___x_1728_; 
v___x_1727_ = l_Lean_Syntax_getArg(v___x_1713_, v___x_1706_);
v___x_1728_ = l_Lean_Syntax_matchesNull(v___x_1727_, v___x_1712_);
if (v___x_1728_ == 0)
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1729_ = l_Lean_Syntax_getArg(v___x_1707_, v___x_1706_);
lean_dec(v___x_1707_);
v___x_1730_ = l_Lean_SourceInfo_fromRef(v_a_1700_, v___x_1728_);
v___x_1731_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1732_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1730_, 3);
v___x_1733_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1730_);
lean_ctor_set(v___x_1733_, 1, v___x_1732_);
v___x_1734_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1735_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1730_);
lean_ctor_set(v___x_1735_, 1, v___x_1734_);
v___x_1736_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1737_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1730_);
lean_ctor_set(v___x_1737_, 1, v___x_1736_);
v___x_1738_ = l_Lean_Syntax_node5(v___x_1730_, v___x_1731_, v___x_1733_, v___x_1713_, v___x_1735_, v___x_1729_, v___x_1737_);
v___x_1739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1738_);
lean_ctor_set(v___x_1739_, 1, v_a_1701_);
return v___x_1739_;
}
else
{
lean_object* v___x_1740_; lean_object* v___x_1741_; uint8_t v___x_1742_; 
v___x_1740_ = l_Lean_Syntax_getArg(v___x_1713_, v___x_1708_);
v___x_1741_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__4));
lean_inc(v___x_1740_);
v___x_1742_ = l_Lean_Syntax_isOfKind(v___x_1740_, v___x_1741_);
if (v___x_1742_ == 0)
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
lean_dec(v___x_1740_);
v___x_1743_ = l_Lean_Syntax_getArg(v___x_1707_, v___x_1706_);
lean_dec(v___x_1707_);
v___x_1744_ = l_Lean_SourceInfo_fromRef(v_a_1700_, v___x_1742_);
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
v___x_1752_ = l_Lean_Syntax_node5(v___x_1744_, v___x_1745_, v___x_1747_, v___x_1713_, v___x_1749_, v___x_1743_, v___x_1751_);
v___x_1753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1752_);
lean_ctor_set(v___x_1753_, 1, v_a_1701_);
return v___x_1753_;
}
else
{
lean_object* v___x_1754_; lean_object* v___x_1755_; uint8_t v___x_1756_; 
v___x_1754_ = l_Lean_Syntax_getArg(v___x_1740_, v___x_1712_);
lean_dec(v___x_1740_);
v___x_1755_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_1754_);
v___x_1756_ = l_Lean_Syntax_matchesNull(v___x_1754_, v___x_1755_);
if (v___x_1756_ == 0)
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; 
lean_dec(v___x_1754_);
v___x_1757_ = l_Lean_Syntax_getArg(v___x_1707_, v___x_1706_);
lean_dec(v___x_1707_);
v___x_1758_ = l_Lean_SourceInfo_fromRef(v_a_1700_, v___x_1756_);
v___x_1759_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1760_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1758_, 3);
v___x_1761_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1758_);
lean_ctor_set(v___x_1761_, 1, v___x_1760_);
v___x_1762_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1763_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1758_);
lean_ctor_set(v___x_1763_, 1, v___x_1762_);
v___x_1764_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1765_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1758_);
lean_ctor_set(v___x_1765_, 1, v___x_1764_);
v___x_1766_ = l_Lean_Syntax_node5(v___x_1758_, v___x_1759_, v___x_1761_, v___x_1713_, v___x_1763_, v___x_1757_, v___x_1765_);
v___x_1767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1766_);
lean_ctor_set(v___x_1767_, 1, v_a_1701_);
return v___x_1767_;
}
else
{
lean_object* v___x_1768_; lean_object* v___x_1769_; uint8_t v___x_1770_; 
v___x_1768_ = l_Lean_Syntax_getArg(v___x_1754_, v___x_1712_);
v___x_1769_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__6));
lean_inc(v___x_1768_);
v___x_1770_ = l_Lean_Syntax_isOfKind(v___x_1768_, v___x_1769_);
if (v___x_1770_ == 0)
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
lean_dec(v___x_1768_);
lean_dec(v___x_1754_);
v___x_1771_ = l_Lean_Syntax_getArg(v___x_1707_, v___x_1706_);
lean_dec(v___x_1707_);
v___x_1772_ = l_Lean_SourceInfo_fromRef(v_a_1700_, v___x_1770_);
v___x_1773_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1774_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1772_, 3);
v___x_1775_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1772_);
lean_ctor_set(v___x_1775_, 1, v___x_1774_);
v___x_1776_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1777_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1772_);
lean_ctor_set(v___x_1777_, 1, v___x_1776_);
v___x_1778_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1779_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1772_);
lean_ctor_set(v___x_1779_, 1, v___x_1778_);
v___x_1780_ = l_Lean_Syntax_node5(v___x_1772_, v___x_1773_, v___x_1775_, v___x_1713_, v___x_1777_, v___x_1771_, v___x_1779_);
v___x_1781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1780_);
lean_ctor_set(v___x_1781_, 1, v_a_1701_);
return v___x_1781_;
}
else
{
lean_object* v___x_1782_; lean_object* v___x_1783_; uint8_t v___x_1784_; 
v___x_1782_ = l_Lean_Syntax_getArg(v___x_1768_, v___x_1712_);
v___x_1783_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__8));
lean_inc(v___x_1782_);
v___x_1784_ = l_Lean_Syntax_isOfKind(v___x_1782_, v___x_1783_);
if (v___x_1784_ == 0)
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
lean_dec(v___x_1782_);
lean_dec(v___x_1768_);
lean_dec(v___x_1754_);
v___x_1785_ = l_Lean_Syntax_getArg(v___x_1707_, v___x_1706_);
lean_dec(v___x_1707_);
v___x_1786_ = l_Lean_SourceInfo_fromRef(v_a_1700_, v___x_1784_);
v___x_1787_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1788_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1786_, 3);
v___x_1789_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1786_);
lean_ctor_set(v___x_1789_, 1, v___x_1788_);
v___x_1790_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1791_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1786_);
lean_ctor_set(v___x_1791_, 1, v___x_1790_);
v___x_1792_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1793_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1786_);
lean_ctor_set(v___x_1793_, 1, v___x_1792_);
v___x_1794_ = l_Lean_Syntax_node5(v___x_1786_, v___x_1787_, v___x_1789_, v___x_1713_, v___x_1791_, v___x_1785_, v___x_1793_);
v___x_1795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1794_);
lean_ctor_set(v___x_1795_, 1, v_a_1701_);
return v___x_1795_;
}
else
{
lean_object* v___x_1796_; lean_object* v___x_1797_; uint8_t v___x_1798_; 
v___x_1796_ = l_Lean_Syntax_getArg(v___x_1782_, v___x_1712_);
v___x_1797_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__10));
v___x_1798_ = l_Lean_Syntax_matchesIdent(v___x_1796_, v___x_1797_);
lean_dec(v___x_1796_);
if (v___x_1798_ == 0)
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
lean_dec(v___x_1782_);
lean_dec(v___x_1768_);
lean_dec(v___x_1754_);
v___x_1799_ = l_Lean_Syntax_getArg(v___x_1707_, v___x_1706_);
lean_dec(v___x_1707_);
v___x_1800_ = l_Lean_SourceInfo_fromRef(v_a_1700_, v___x_1798_);
v___x_1801_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1802_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1800_, 3);
v___x_1803_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1800_);
lean_ctor_set(v___x_1803_, 1, v___x_1802_);
v___x_1804_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1805_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1800_);
lean_ctor_set(v___x_1805_, 1, v___x_1804_);
v___x_1806_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1807_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1800_);
lean_ctor_set(v___x_1807_, 1, v___x_1806_);
v___x_1808_ = l_Lean_Syntax_node5(v___x_1800_, v___x_1801_, v___x_1803_, v___x_1713_, v___x_1805_, v___x_1799_, v___x_1807_);
v___x_1809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1808_);
lean_ctor_set(v___x_1809_, 1, v_a_1701_);
return v___x_1809_;
}
else
{
lean_object* v___x_1810_; uint8_t v___x_1811_; 
v___x_1810_ = l_Lean_Syntax_getArg(v___x_1782_, v___x_1706_);
lean_dec(v___x_1782_);
v___x_1811_ = l_Lean_Syntax_matchesNull(v___x_1810_, v___x_1712_);
if (v___x_1811_ == 0)
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
lean_dec(v___x_1768_);
lean_dec(v___x_1754_);
v___x_1812_ = l_Lean_Syntax_getArg(v___x_1707_, v___x_1706_);
lean_dec(v___x_1707_);
v___x_1813_ = l_Lean_SourceInfo_fromRef(v_a_1700_, v___x_1811_);
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
v___x_1821_ = l_Lean_Syntax_node5(v___x_1813_, v___x_1814_, v___x_1816_, v___x_1713_, v___x_1818_, v___x_1812_, v___x_1820_);
v___x_1822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1821_);
lean_ctor_set(v___x_1822_, 1, v_a_1701_);
return v___x_1822_;
}
else
{
lean_object* v___x_1823_; lean_object* v___x_1824_; uint8_t v___x_1825_; 
v___x_1823_ = l_Lean_Syntax_getArg(v___x_1768_, v___x_1706_);
lean_dec(v___x_1768_);
v___x_1824_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_1823_);
v___x_1825_ = l_Lean_Syntax_matchesNull(v___x_1823_, v___x_1824_);
if (v___x_1825_ == 0)
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
lean_dec(v___x_1823_);
lean_dec(v___x_1754_);
v___x_1826_ = l_Lean_Syntax_getArg(v___x_1707_, v___x_1706_);
lean_dec(v___x_1707_);
v___x_1827_ = l_Lean_SourceInfo_fromRef(v_a_1700_, v___x_1825_);
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
v___x_1835_ = l_Lean_Syntax_node5(v___x_1827_, v___x_1828_, v___x_1830_, v___x_1713_, v___x_1832_, v___x_1826_, v___x_1834_);
v___x_1836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1835_);
lean_ctor_set(v___x_1836_, 1, v_a_1701_);
return v___x_1836_;
}
else
{
lean_object* v___x_1837_; uint8_t v___x_1838_; 
v___x_1837_ = l_Lean_Syntax_getArg(v___x_1823_, v___x_1712_);
v___x_1838_ = l_Lean_Syntax_matchesNull(v___x_1837_, v___x_1712_);
if (v___x_1838_ == 0)
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
lean_dec(v___x_1823_);
lean_dec(v___x_1754_);
v___x_1839_ = l_Lean_Syntax_getArg(v___x_1707_, v___x_1706_);
lean_dec(v___x_1707_);
v___x_1840_ = l_Lean_SourceInfo_fromRef(v_a_1700_, v___x_1838_);
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
v___x_1848_ = l_Lean_Syntax_node5(v___x_1840_, v___x_1841_, v___x_1843_, v___x_1713_, v___x_1845_, v___x_1839_, v___x_1847_);
v___x_1849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1848_);
lean_ctor_set(v___x_1849_, 1, v_a_1701_);
return v___x_1849_;
}
else
{
lean_object* v___x_1850_; uint8_t v___x_1851_; 
v___x_1850_ = l_Lean_Syntax_getArg(v___x_1823_, v___x_1706_);
v___x_1851_ = l_Lean_Syntax_matchesNull(v___x_1850_, v___x_1712_);
if (v___x_1851_ == 0)
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
lean_dec(v___x_1823_);
lean_dec(v___x_1754_);
v___x_1852_ = l_Lean_Syntax_getArg(v___x_1707_, v___x_1706_);
lean_dec(v___x_1707_);
v___x_1853_ = l_Lean_SourceInfo_fromRef(v_a_1700_, v___x_1851_);
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
v___x_1861_ = l_Lean_Syntax_node5(v___x_1853_, v___x_1854_, v___x_1856_, v___x_1713_, v___x_1858_, v___x_1852_, v___x_1860_);
v___x_1862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1861_);
lean_ctor_set(v___x_1862_, 1, v_a_1701_);
return v___x_1862_;
}
else
{
lean_object* v___x_1863_; lean_object* v___x_1864_; uint8_t v___x_1865_; 
v___x_1863_ = l_Lean_Syntax_getArg(v___x_1823_, v___x_1708_);
lean_dec(v___x_1823_);
v___x_1864_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__12));
lean_inc(v___x_1863_);
v___x_1865_ = l_Lean_Syntax_isOfKind(v___x_1863_, v___x_1864_);
if (v___x_1865_ == 0)
{
lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
lean_dec(v___x_1863_);
lean_dec(v___x_1754_);
v___x_1866_ = l_Lean_Syntax_getArg(v___x_1707_, v___x_1706_);
lean_dec(v___x_1707_);
v___x_1867_ = l_Lean_SourceInfo_fromRef(v_a_1700_, v___x_1865_);
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
v___x_1875_ = l_Lean_Syntax_node5(v___x_1867_, v___x_1868_, v___x_1870_, v___x_1713_, v___x_1872_, v___x_1866_, v___x_1874_);
v___x_1876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1875_);
lean_ctor_set(v___x_1876_, 1, v_a_1701_);
return v___x_1876_;
}
else
{
lean_object* v___x_1877_; uint8_t v___x_1878_; 
v___x_1877_ = l_Lean_Syntax_getArg(v___x_1863_, v___x_1706_);
v___x_1878_ = l_Lean_Syntax_matchesNull(v___x_1877_, v___x_1712_);
if (v___x_1878_ == 0)
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
lean_dec(v___x_1863_);
lean_dec(v___x_1754_);
v___x_1879_ = l_Lean_Syntax_getArg(v___x_1707_, v___x_1706_);
lean_dec(v___x_1707_);
v___x_1880_ = l_Lean_SourceInfo_fromRef(v_a_1700_, v___x_1878_);
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
v___x_1888_ = l_Lean_Syntax_node5(v___x_1880_, v___x_1881_, v___x_1883_, v___x_1713_, v___x_1885_, v___x_1879_, v___x_1887_);
v___x_1889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1888_);
lean_ctor_set(v___x_1889_, 1, v_a_1701_);
return v___x_1889_;
}
else
{
lean_object* v___x_1890_; uint8_t v___x_1891_; 
v___x_1890_ = l_Lean_Syntax_getArg(v___x_1754_, v___x_1708_);
lean_inc(v___x_1890_);
v___x_1891_ = l_Lean_Syntax_isOfKind(v___x_1890_, v___x_1769_);
if (v___x_1891_ == 0)
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
lean_dec(v___x_1890_);
lean_dec(v___x_1863_);
lean_dec(v___x_1754_);
v___x_1892_ = l_Lean_Syntax_getArg(v___x_1707_, v___x_1706_);
lean_dec(v___x_1707_);
v___x_1893_ = l_Lean_SourceInfo_fromRef(v_a_1700_, v___x_1891_);
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
v___x_1901_ = l_Lean_Syntax_node5(v___x_1893_, v___x_1894_, v___x_1896_, v___x_1713_, v___x_1898_, v___x_1892_, v___x_1900_);
v___x_1902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1901_);
lean_ctor_set(v___x_1902_, 1, v_a_1701_);
return v___x_1902_;
}
else
{
lean_object* v___x_1903_; uint8_t v___x_1904_; 
v___x_1903_ = l_Lean_Syntax_getArg(v___x_1890_, v___x_1712_);
lean_inc(v___x_1903_);
v___x_1904_ = l_Lean_Syntax_isOfKind(v___x_1903_, v___x_1783_);
if (v___x_1904_ == 0)
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
lean_dec(v___x_1903_);
lean_dec(v___x_1890_);
lean_dec(v___x_1863_);
lean_dec(v___x_1754_);
v___x_1905_ = l_Lean_Syntax_getArg(v___x_1707_, v___x_1706_);
lean_dec(v___x_1707_);
v___x_1906_ = l_Lean_SourceInfo_fromRef(v_a_1700_, v___x_1904_);
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
v___x_1914_ = l_Lean_Syntax_node5(v___x_1906_, v___x_1907_, v___x_1909_, v___x_1713_, v___x_1911_, v___x_1905_, v___x_1913_);
v___x_1915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1914_);
lean_ctor_set(v___x_1915_, 1, v_a_1701_);
return v___x_1915_;
}
else
{
lean_object* v___x_1916_; lean_object* v___x_1917_; uint8_t v___x_1918_; 
v___x_1916_ = l_Lean_Syntax_getArg(v___x_1903_, v___x_1712_);
v___x_1917_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__14));
v___x_1918_ = l_Lean_Syntax_matchesIdent(v___x_1916_, v___x_1917_);
lean_dec(v___x_1916_);
if (v___x_1918_ == 0)
{
lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
lean_dec(v___x_1903_);
lean_dec(v___x_1890_);
lean_dec(v___x_1863_);
lean_dec(v___x_1754_);
v___x_1919_ = l_Lean_Syntax_getArg(v___x_1707_, v___x_1706_);
lean_dec(v___x_1707_);
v___x_1920_ = l_Lean_SourceInfo_fromRef(v_a_1700_, v___x_1918_);
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
v___x_1928_ = l_Lean_Syntax_node5(v___x_1920_, v___x_1921_, v___x_1923_, v___x_1713_, v___x_1925_, v___x_1919_, v___x_1927_);
v___x_1929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1928_);
lean_ctor_set(v___x_1929_, 1, v_a_1701_);
return v___x_1929_;
}
else
{
lean_object* v___x_1930_; uint8_t v___x_1931_; 
v___x_1930_ = l_Lean_Syntax_getArg(v___x_1903_, v___x_1706_);
lean_dec(v___x_1903_);
v___x_1931_ = l_Lean_Syntax_matchesNull(v___x_1930_, v___x_1712_);
if (v___x_1931_ == 0)
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
lean_dec(v___x_1890_);
lean_dec(v___x_1863_);
lean_dec(v___x_1754_);
v___x_1932_ = l_Lean_Syntax_getArg(v___x_1707_, v___x_1706_);
lean_dec(v___x_1707_);
v___x_1933_ = l_Lean_SourceInfo_fromRef(v_a_1700_, v___x_1931_);
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
v___x_1941_ = l_Lean_Syntax_node5(v___x_1933_, v___x_1934_, v___x_1936_, v___x_1713_, v___x_1938_, v___x_1932_, v___x_1940_);
v___x_1942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1941_);
lean_ctor_set(v___x_1942_, 1, v_a_1701_);
return v___x_1942_;
}
else
{
lean_object* v___x_1943_; uint8_t v___x_1944_; 
v___x_1943_ = l_Lean_Syntax_getArg(v___x_1890_, v___x_1706_);
lean_dec(v___x_1890_);
lean_inc(v___x_1943_);
v___x_1944_ = l_Lean_Syntax_matchesNull(v___x_1943_, v___x_1824_);
if (v___x_1944_ == 0)
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
lean_dec(v___x_1943_);
lean_dec(v___x_1863_);
lean_dec(v___x_1754_);
v___x_1945_ = l_Lean_Syntax_getArg(v___x_1707_, v___x_1706_);
lean_dec(v___x_1707_);
v___x_1946_ = l_Lean_SourceInfo_fromRef(v_a_1700_, v___x_1944_);
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
v___x_1954_ = l_Lean_Syntax_node5(v___x_1946_, v___x_1947_, v___x_1949_, v___x_1713_, v___x_1951_, v___x_1945_, v___x_1953_);
v___x_1955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1954_);
lean_ctor_set(v___x_1955_, 1, v_a_1701_);
return v___x_1955_;
}
else
{
lean_object* v___x_1956_; uint8_t v___x_1957_; 
v___x_1956_ = l_Lean_Syntax_getArg(v___x_1943_, v___x_1712_);
v___x_1957_ = l_Lean_Syntax_matchesNull(v___x_1956_, v___x_1712_);
if (v___x_1957_ == 0)
{
lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
lean_dec(v___x_1943_);
lean_dec(v___x_1863_);
lean_dec(v___x_1754_);
v___x_1958_ = l_Lean_Syntax_getArg(v___x_1707_, v___x_1706_);
lean_dec(v___x_1707_);
v___x_1959_ = l_Lean_SourceInfo_fromRef(v_a_1700_, v___x_1957_);
v___x_1960_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1961_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1959_, 3);
v___x_1962_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1959_);
lean_ctor_set(v___x_1962_, 1, v___x_1961_);
v___x_1963_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1964_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1959_);
lean_ctor_set(v___x_1964_, 1, v___x_1963_);
v___x_1965_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1966_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1959_);
lean_ctor_set(v___x_1966_, 1, v___x_1965_);
v___x_1967_ = l_Lean_Syntax_node5(v___x_1959_, v___x_1960_, v___x_1962_, v___x_1713_, v___x_1964_, v___x_1958_, v___x_1966_);
v___x_1968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1967_);
lean_ctor_set(v___x_1968_, 1, v_a_1701_);
return v___x_1968_;
}
else
{
lean_object* v___x_1969_; uint8_t v___x_1970_; 
v___x_1969_ = l_Lean_Syntax_getArg(v___x_1943_, v___x_1706_);
v___x_1970_ = l_Lean_Syntax_matchesNull(v___x_1969_, v___x_1712_);
if (v___x_1970_ == 0)
{
lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
lean_dec(v___x_1943_);
lean_dec(v___x_1863_);
lean_dec(v___x_1754_);
v___x_1971_ = l_Lean_Syntax_getArg(v___x_1707_, v___x_1706_);
lean_dec(v___x_1707_);
v___x_1972_ = l_Lean_SourceInfo_fromRef(v_a_1700_, v___x_1970_);
v___x_1973_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1974_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1972_, 3);
v___x_1975_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1972_);
lean_ctor_set(v___x_1975_, 1, v___x_1974_);
v___x_1976_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1977_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1972_);
lean_ctor_set(v___x_1977_, 1, v___x_1976_);
v___x_1978_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1979_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1972_);
lean_ctor_set(v___x_1979_, 1, v___x_1978_);
v___x_1980_ = l_Lean_Syntax_node5(v___x_1972_, v___x_1973_, v___x_1975_, v___x_1713_, v___x_1977_, v___x_1971_, v___x_1979_);
v___x_1981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1980_);
lean_ctor_set(v___x_1981_, 1, v_a_1701_);
return v___x_1981_;
}
else
{
lean_object* v___x_1982_; uint8_t v___x_1983_; 
v___x_1982_ = l_Lean_Syntax_getArg(v___x_1943_, v___x_1708_);
lean_dec(v___x_1943_);
lean_inc(v___x_1982_);
v___x_1983_ = l_Lean_Syntax_isOfKind(v___x_1982_, v___x_1864_);
if (v___x_1983_ == 0)
{
lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
lean_dec(v___x_1982_);
lean_dec(v___x_1863_);
lean_dec(v___x_1754_);
v___x_1984_ = l_Lean_Syntax_getArg(v___x_1707_, v___x_1706_);
lean_dec(v___x_1707_);
v___x_1985_ = l_Lean_SourceInfo_fromRef(v_a_1700_, v___x_1983_);
v___x_1986_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_1987_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1985_, 3);
v___x_1988_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1985_);
lean_ctor_set(v___x_1988_, 1, v___x_1987_);
v___x_1989_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_1990_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1985_);
lean_ctor_set(v___x_1990_, 1, v___x_1989_);
v___x_1991_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_1992_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1985_);
lean_ctor_set(v___x_1992_, 1, v___x_1991_);
v___x_1993_ = l_Lean_Syntax_node5(v___x_1985_, v___x_1986_, v___x_1988_, v___x_1713_, v___x_1990_, v___x_1984_, v___x_1992_);
v___x_1994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1993_);
lean_ctor_set(v___x_1994_, 1, v_a_1701_);
return v___x_1994_;
}
else
{
lean_object* v___x_1995_; uint8_t v___x_1996_; 
v___x_1995_ = l_Lean_Syntax_getArg(v___x_1982_, v___x_1706_);
v___x_1996_ = l_Lean_Syntax_matchesNull(v___x_1995_, v___x_1712_);
if (v___x_1996_ == 0)
{
lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; 
lean_dec(v___x_1982_);
lean_dec(v___x_1863_);
lean_dec(v___x_1754_);
v___x_1997_ = l_Lean_Syntax_getArg(v___x_1707_, v___x_1706_);
lean_dec(v___x_1707_);
v___x_1998_ = l_Lean_SourceInfo_fromRef(v_a_1700_, v___x_1996_);
v___x_1999_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2000_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_1998_, 3);
v___x_2001_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2001_, 0, v___x_1998_);
lean_ctor_set(v___x_2001_, 1, v___x_2000_);
v___x_2002_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2003_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2003_, 0, v___x_1998_);
lean_ctor_set(v___x_2003_, 1, v___x_2002_);
v___x_2004_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2005_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2005_, 0, v___x_1998_);
lean_ctor_set(v___x_2005_, 1, v___x_2004_);
v___x_2006_ = l_Lean_Syntax_node5(v___x_1998_, v___x_1999_, v___x_2001_, v___x_1713_, v___x_2003_, v___x_1997_, v___x_2005_);
v___x_2007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2006_);
lean_ctor_set(v___x_2007_, 1, v_a_1701_);
return v___x_2007_;
}
else
{
lean_object* v___x_2008_; lean_object* v___x_2009_; uint8_t v___x_2010_; 
v___x_2008_ = lean_unsigned_to_nat(4u);
v___x_2009_ = l_Lean_Syntax_getArg(v___x_1754_, v___x_2008_);
lean_dec(v___x_1754_);
lean_inc(v___x_2009_);
v___x_2010_ = l_Lean_Syntax_isOfKind(v___x_2009_, v___x_1769_);
if (v___x_2010_ == 0)
{
lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
lean_dec(v___x_2009_);
lean_dec(v___x_1982_);
lean_dec(v___x_1863_);
v___x_2011_ = l_Lean_Syntax_getArg(v___x_1707_, v___x_1706_);
lean_dec(v___x_1707_);
v___x_2012_ = l_Lean_SourceInfo_fromRef(v_a_1700_, v___x_2010_);
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
v___x_2020_ = l_Lean_Syntax_node5(v___x_2012_, v___x_2013_, v___x_2015_, v___x_1713_, v___x_2017_, v___x_2011_, v___x_2019_);
v___x_2021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2020_);
lean_ctor_set(v___x_2021_, 1, v_a_1701_);
return v___x_2021_;
}
else
{
lean_object* v___x_2022_; uint8_t v___x_2023_; 
v___x_2022_ = l_Lean_Syntax_getArg(v___x_2009_, v___x_1712_);
lean_inc(v___x_2022_);
v___x_2023_ = l_Lean_Syntax_isOfKind(v___x_2022_, v___x_1783_);
if (v___x_2023_ == 0)
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
lean_dec(v___x_2022_);
lean_dec(v___x_2009_);
lean_dec(v___x_1982_);
lean_dec(v___x_1863_);
v___x_2024_ = l_Lean_Syntax_getArg(v___x_1707_, v___x_1706_);
lean_dec(v___x_1707_);
v___x_2025_ = l_Lean_SourceInfo_fromRef(v_a_1700_, v___x_2023_);
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
v___x_2033_ = l_Lean_Syntax_node5(v___x_2025_, v___x_2026_, v___x_2028_, v___x_1713_, v___x_2030_, v___x_2024_, v___x_2032_);
v___x_2034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2033_);
lean_ctor_set(v___x_2034_, 1, v_a_1701_);
return v___x_2034_;
}
else
{
lean_object* v___x_2035_; lean_object* v___x_2036_; uint8_t v___x_2037_; 
v___x_2035_ = l_Lean_Syntax_getArg(v___x_2022_, v___x_1712_);
v___x_2036_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__16));
v___x_2037_ = l_Lean_Syntax_matchesIdent(v___x_2035_, v___x_2036_);
lean_dec(v___x_2035_);
if (v___x_2037_ == 0)
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; 
lean_dec(v___x_2022_);
lean_dec(v___x_2009_);
lean_dec(v___x_1982_);
lean_dec(v___x_1863_);
v___x_2038_ = l_Lean_Syntax_getArg(v___x_1707_, v___x_1706_);
lean_dec(v___x_1707_);
v___x_2039_ = l_Lean_SourceInfo_fromRef(v_a_1700_, v___x_2037_);
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
v___x_2047_ = l_Lean_Syntax_node5(v___x_2039_, v___x_2040_, v___x_2042_, v___x_1713_, v___x_2044_, v___x_2038_, v___x_2046_);
v___x_2048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2047_);
lean_ctor_set(v___x_2048_, 1, v_a_1701_);
return v___x_2048_;
}
else
{
lean_object* v___x_2049_; uint8_t v___x_2050_; 
v___x_2049_ = l_Lean_Syntax_getArg(v___x_2022_, v___x_1706_);
lean_dec(v___x_2022_);
v___x_2050_ = l_Lean_Syntax_matchesNull(v___x_2049_, v___x_1712_);
if (v___x_2050_ == 0)
{
lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
lean_dec(v___x_2009_);
lean_dec(v___x_1982_);
lean_dec(v___x_1863_);
v___x_2051_ = l_Lean_Syntax_getArg(v___x_1707_, v___x_1706_);
lean_dec(v___x_1707_);
v___x_2052_ = l_Lean_SourceInfo_fromRef(v_a_1700_, v___x_2050_);
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
v___x_2060_ = l_Lean_Syntax_node5(v___x_2052_, v___x_2053_, v___x_2055_, v___x_1713_, v___x_2057_, v___x_2051_, v___x_2059_);
v___x_2061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2060_);
lean_ctor_set(v___x_2061_, 1, v_a_1701_);
return v___x_2061_;
}
else
{
lean_object* v___x_2062_; uint8_t v___x_2063_; 
v___x_2062_ = l_Lean_Syntax_getArg(v___x_2009_, v___x_1706_);
lean_dec(v___x_2009_);
lean_inc(v___x_2062_);
v___x_2063_ = l_Lean_Syntax_matchesNull(v___x_2062_, v___x_1824_);
if (v___x_2063_ == 0)
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; 
lean_dec(v___x_2062_);
lean_dec(v___x_1982_);
lean_dec(v___x_1863_);
v___x_2064_ = l_Lean_Syntax_getArg(v___x_1707_, v___x_1706_);
lean_dec(v___x_1707_);
v___x_2065_ = l_Lean_SourceInfo_fromRef(v_a_1700_, v___x_2063_);
v___x_2066_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2067_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2065_, 3);
v___x_2068_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2065_);
lean_ctor_set(v___x_2068_, 1, v___x_2067_);
v___x_2069_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2070_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2065_);
lean_ctor_set(v___x_2070_, 1, v___x_2069_);
v___x_2071_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2072_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2065_);
lean_ctor_set(v___x_2072_, 1, v___x_2071_);
v___x_2073_ = l_Lean_Syntax_node5(v___x_2065_, v___x_2066_, v___x_2068_, v___x_1713_, v___x_2070_, v___x_2064_, v___x_2072_);
v___x_2074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2073_);
lean_ctor_set(v___x_2074_, 1, v_a_1701_);
return v___x_2074_;
}
else
{
lean_object* v___x_2075_; uint8_t v___x_2076_; 
v___x_2075_ = l_Lean_Syntax_getArg(v___x_2062_, v___x_1712_);
v___x_2076_ = l_Lean_Syntax_matchesNull(v___x_2075_, v___x_1712_);
if (v___x_2076_ == 0)
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
lean_dec(v___x_2062_);
lean_dec(v___x_1982_);
lean_dec(v___x_1863_);
v___x_2077_ = l_Lean_Syntax_getArg(v___x_1707_, v___x_1706_);
lean_dec(v___x_1707_);
v___x_2078_ = l_Lean_SourceInfo_fromRef(v_a_1700_, v___x_2076_);
v___x_2079_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2080_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2078_, 3);
v___x_2081_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2078_);
lean_ctor_set(v___x_2081_, 1, v___x_2080_);
v___x_2082_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2083_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2078_);
lean_ctor_set(v___x_2083_, 1, v___x_2082_);
v___x_2084_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2085_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2078_);
lean_ctor_set(v___x_2085_, 1, v___x_2084_);
v___x_2086_ = l_Lean_Syntax_node5(v___x_2078_, v___x_2079_, v___x_2081_, v___x_1713_, v___x_2083_, v___x_2077_, v___x_2085_);
v___x_2087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2086_);
lean_ctor_set(v___x_2087_, 1, v_a_1701_);
return v___x_2087_;
}
else
{
lean_object* v___x_2088_; uint8_t v___x_2089_; 
v___x_2088_ = l_Lean_Syntax_getArg(v___x_2062_, v___x_1706_);
v___x_2089_ = l_Lean_Syntax_matchesNull(v___x_2088_, v___x_1712_);
if (v___x_2089_ == 0)
{
lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
lean_dec(v___x_2062_);
lean_dec(v___x_1982_);
lean_dec(v___x_1863_);
v___x_2090_ = l_Lean_Syntax_getArg(v___x_1707_, v___x_1706_);
lean_dec(v___x_1707_);
v___x_2091_ = l_Lean_SourceInfo_fromRef(v_a_1700_, v___x_2089_);
v___x_2092_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2093_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2091_, 3);
v___x_2094_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2091_);
lean_ctor_set(v___x_2094_, 1, v___x_2093_);
v___x_2095_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2096_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2091_);
lean_ctor_set(v___x_2096_, 1, v___x_2095_);
v___x_2097_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2098_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2091_);
lean_ctor_set(v___x_2098_, 1, v___x_2097_);
v___x_2099_ = l_Lean_Syntax_node5(v___x_2091_, v___x_2092_, v___x_2094_, v___x_1713_, v___x_2096_, v___x_2090_, v___x_2098_);
v___x_2100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2099_);
lean_ctor_set(v___x_2100_, 1, v_a_1701_);
return v___x_2100_;
}
else
{
lean_object* v___x_2101_; uint8_t v___x_2102_; 
v___x_2101_ = l_Lean_Syntax_getArg(v___x_2062_, v___x_1708_);
lean_dec(v___x_2062_);
lean_inc(v___x_2101_);
v___x_2102_ = l_Lean_Syntax_isOfKind(v___x_2101_, v___x_1864_);
if (v___x_2102_ == 0)
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
lean_dec(v___x_2101_);
lean_dec(v___x_1982_);
lean_dec(v___x_1863_);
v___x_2103_ = l_Lean_Syntax_getArg(v___x_1707_, v___x_1706_);
lean_dec(v___x_1707_);
v___x_2104_ = l_Lean_SourceInfo_fromRef(v_a_1700_, v___x_2102_);
v___x_2105_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2106_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2104_, 3);
v___x_2107_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2104_);
lean_ctor_set(v___x_2107_, 1, v___x_2106_);
v___x_2108_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2109_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2104_);
lean_ctor_set(v___x_2109_, 1, v___x_2108_);
v___x_2110_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2111_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2104_);
lean_ctor_set(v___x_2111_, 1, v___x_2110_);
v___x_2112_ = l_Lean_Syntax_node5(v___x_2104_, v___x_2105_, v___x_2107_, v___x_1713_, v___x_2109_, v___x_2103_, v___x_2111_);
v___x_2113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2112_);
lean_ctor_set(v___x_2113_, 1, v_a_1701_);
return v___x_2113_;
}
else
{
lean_object* v___x_2114_; uint8_t v___x_2115_; 
v___x_2114_ = l_Lean_Syntax_getArg(v___x_2101_, v___x_1706_);
v___x_2115_ = l_Lean_Syntax_matchesNull(v___x_2114_, v___x_1712_);
if (v___x_2115_ == 0)
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
lean_dec(v___x_2101_);
lean_dec(v___x_1982_);
lean_dec(v___x_1863_);
v___x_2116_ = l_Lean_Syntax_getArg(v___x_1707_, v___x_1706_);
lean_dec(v___x_1707_);
v___x_2117_ = l_Lean_SourceInfo_fromRef(v_a_1700_, v___x_2115_);
v___x_2118_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2119_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2117_, 3);
v___x_2120_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2117_);
lean_ctor_set(v___x_2120_, 1, v___x_2119_);
v___x_2121_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2122_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2117_);
lean_ctor_set(v___x_2122_, 1, v___x_2121_);
v___x_2123_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2124_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2117_);
lean_ctor_set(v___x_2124_, 1, v___x_2123_);
v___x_2125_ = l_Lean_Syntax_node5(v___x_2117_, v___x_2118_, v___x_2120_, v___x_1713_, v___x_2122_, v___x_2116_, v___x_2124_);
v___x_2126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2125_);
lean_ctor_set(v___x_2126_, 1, v_a_1701_);
return v___x_2126_;
}
else
{
lean_object* v___x_2127_; lean_object* v___x_2128_; uint8_t v___x_2129_; 
v___x_2127_ = l_Lean_Syntax_getArg(v___x_1713_, v___x_1824_);
v___x_2128_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__18));
lean_inc(v___x_2127_);
v___x_2129_ = l_Lean_Syntax_isOfKind(v___x_2127_, v___x_2128_);
if (v___x_2129_ == 0)
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
lean_dec(v___x_2127_);
lean_dec(v___x_2101_);
lean_dec(v___x_1982_);
lean_dec(v___x_1863_);
v___x_2130_ = l_Lean_Syntax_getArg(v___x_1707_, v___x_1706_);
lean_dec(v___x_1707_);
v___x_2131_ = l_Lean_SourceInfo_fromRef(v_a_1700_, v___x_2129_);
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
v___x_2139_ = l_Lean_Syntax_node5(v___x_2131_, v___x_2132_, v___x_2134_, v___x_1713_, v___x_2136_, v___x_2130_, v___x_2138_);
v___x_2140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2139_);
lean_ctor_set(v___x_2140_, 1, v_a_1701_);
return v___x_2140_;
}
else
{
lean_object* v___x_2141_; uint8_t v___x_2142_; 
v___x_2141_ = l_Lean_Syntax_getArg(v___x_2127_, v___x_1712_);
lean_dec(v___x_2127_);
v___x_2142_ = l_Lean_Syntax_matchesNull(v___x_2141_, v___x_1712_);
if (v___x_2142_ == 0)
{
lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
lean_dec(v___x_2101_);
lean_dec(v___x_1982_);
lean_dec(v___x_1863_);
v___x_2143_ = l_Lean_Syntax_getArg(v___x_1707_, v___x_1706_);
lean_dec(v___x_1707_);
v___x_2144_ = l_Lean_SourceInfo_fromRef(v_a_1700_, v___x_2142_);
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
v___x_2152_ = l_Lean_Syntax_node5(v___x_2144_, v___x_2145_, v___x_2147_, v___x_1713_, v___x_2149_, v___x_2143_, v___x_2151_);
v___x_2153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2152_);
lean_ctor_set(v___x_2153_, 1, v_a_1701_);
return v___x_2153_;
}
else
{
lean_object* v___x_2154_; uint8_t v___x_2155_; 
v___x_2154_ = l_Lean_Syntax_getArg(v___x_1713_, v___x_2008_);
v___x_2155_ = l_Lean_Syntax_matchesNull(v___x_2154_, v___x_1712_);
if (v___x_2155_ == 0)
{
lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
lean_dec(v___x_2101_);
lean_dec(v___x_1982_);
lean_dec(v___x_1863_);
v___x_2156_ = l_Lean_Syntax_getArg(v___x_1707_, v___x_1706_);
lean_dec(v___x_1707_);
v___x_2157_ = l_Lean_SourceInfo_fromRef(v_a_1700_, v___x_2155_);
v___x_2158_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4));
v___x_2159_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2157_, 3);
v___x_2160_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2157_);
lean_ctor_set(v___x_2160_, 1, v___x_2159_);
v___x_2161_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2162_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2157_);
lean_ctor_set(v___x_2162_, 1, v___x_2161_);
v___x_2163_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2164_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2157_);
lean_ctor_set(v___x_2164_, 1, v___x_2163_);
v___x_2165_ = l_Lean_Syntax_node5(v___x_2157_, v___x_2158_, v___x_2160_, v___x_1713_, v___x_2162_, v___x_2156_, v___x_2164_);
v___x_2166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2165_);
lean_ctor_set(v___x_2166_, 1, v_a_1701_);
return v___x_2166_;
}
else
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; uint8_t v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
lean_dec(v___x_1713_);
v___x_2167_ = l_Lean_Syntax_getArg(v___x_1863_, v___x_1708_);
lean_dec(v___x_1863_);
v___x_2168_ = l_Lean_Syntax_getArg(v___x_1982_, v___x_1708_);
lean_dec(v___x_1982_);
v___x_2169_ = l_Lean_Syntax_getArg(v___x_2101_, v___x_1708_);
lean_dec(v___x_2101_);
v___x_2170_ = l_Lean_Syntax_getArg(v___x_1707_, v___x_1706_);
lean_dec(v___x_1707_);
v___x_2171_ = 0;
v___x_2172_ = l_Lean_SourceInfo_fromRef(v_a_1700_, v___x_2171_);
v___x_2173_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__1));
v___x_2174_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7));
lean_inc_n(v___x_2172_, 7);
v___x_2175_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2175_, 0, v___x_2172_);
lean_ctor_set(v___x_2175_, 1, v___x_2174_);
v___x_2176_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__2));
v___x_2177_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2172_);
lean_ctor_set(v___x_2177_, 1, v___x_2176_);
v___x_2178_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__20));
v___x_2179_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__21));
v___x_2180_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2172_);
lean_ctor_set(v___x_2180_, 1, v___x_2179_);
v___x_2181_ = ((lean_object*)(l_Std_Sat_AIG_Cache_empty___auto__1___closed__9));
lean_inc_ref_n(v___x_2177_, 2);
v___x_2182_ = l_Lean_Syntax_node3(v___x_2172_, v___x_2181_, v___x_2168_, v___x_2177_, v___x_2169_);
v___x_2183_ = ((lean_object*)(l_Std_Sat_AIG_unexpandDenote___closed__22));
v___x_2184_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2172_);
lean_ctor_set(v___x_2184_, 1, v___x_2183_);
v___x_2185_ = l_Lean_Syntax_node3(v___x_2172_, v___x_2178_, v___x_2180_, v___x_2182_, v___x_2184_);
v___x_2186_ = ((lean_object*)(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17));
v___x_2187_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2187_, 0, v___x_2172_);
lean_ctor_set(v___x_2187_, 1, v___x_2186_);
v___x_2188_ = l_Lean_Syntax_node7(v___x_2172_, v___x_2173_, v___x_2175_, v___x_2167_, v___x_2177_, v___x_2185_, v___x_2177_, v___x_2170_, v___x_2187_);
v___x_2189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2188_);
lean_ctor_set(v___x_2189_, 1, v_a_1701_);
return v___x_2189_;
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_unexpandDenote___boxed(lean_object* v_x_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_){
_start:
{
lean_object* v_res_2193_; 
v_res_2193_ = l_Std_Sat_AIG_unexpandDenote(v_x_2190_, v_a_2191_, v_a_2192_);
lean_dec(v_a_2191_);
return v_res_2193_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_isConstant___redArg(lean_object* v_aig_2194_, lean_object* v_ref_2195_, uint8_t v_b_2196_){
_start:
{
lean_object* v_gate_2197_; uint8_t v_invert_2198_; lean_object* v_decls_2199_; lean_object* v_decl_2200_; 
v_gate_2197_ = lean_ctor_get(v_ref_2195_, 0);
v_invert_2198_ = lean_ctor_get_uint8(v_ref_2195_, sizeof(void*)*1);
v_decls_2199_ = lean_ctor_get(v_aig_2194_, 0);
v_decl_2200_ = lean_array_fget_borrowed(v_decls_2199_, v_gate_2197_);
if (lean_obj_tag(v_decl_2200_) == 0)
{
if (v_b_2196_ == 0)
{
if (v_invert_2198_ == 0)
{
uint8_t v___x_2201_; 
v___x_2201_ = 1;
return v___x_2201_;
}
else
{
return v_b_2196_;
}
}
else
{
return v_invert_2198_;
}
}
else
{
uint8_t v___x_2202_; 
v___x_2202_ = 0;
return v___x_2202_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_isConstant___redArg___boxed(lean_object* v_aig_2203_, lean_object* v_ref_2204_, lean_object* v_b_2205_){
_start:
{
uint8_t v_b_boxed_2206_; uint8_t v_res_2207_; lean_object* v_r_2208_; 
v_b_boxed_2206_ = lean_unbox(v_b_2205_);
v_res_2207_ = l_Std_Sat_AIG_isConstant___redArg(v_aig_2203_, v_ref_2204_, v_b_boxed_2206_);
lean_dec_ref(v_ref_2204_);
lean_dec_ref(v_aig_2203_);
v_r_2208_ = lean_box(v_res_2207_);
return v_r_2208_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_isConstant(lean_object* v_00_u03b1_2209_, lean_object* v_inst_2210_, lean_object* v_inst_2211_, lean_object* v_aig_2212_, lean_object* v_ref_2213_, uint8_t v_b_2214_){
_start:
{
uint8_t v___x_2215_; 
v___x_2215_ = l_Std_Sat_AIG_isConstant___redArg(v_aig_2212_, v_ref_2213_, v_b_2214_);
return v___x_2215_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_isConstant___boxed(lean_object* v_00_u03b1_2216_, lean_object* v_inst_2217_, lean_object* v_inst_2218_, lean_object* v_aig_2219_, lean_object* v_ref_2220_, lean_object* v_b_2221_){
_start:
{
uint8_t v_b_boxed_2222_; uint8_t v_res_2223_; lean_object* v_r_2224_; 
v_b_boxed_2222_ = lean_unbox(v_b_2221_);
v_res_2223_ = l_Std_Sat_AIG_isConstant(v_00_u03b1_2216_, v_inst_2217_, v_inst_2218_, v_aig_2219_, v_ref_2220_, v_b_boxed_2222_);
lean_dec_ref(v_ref_2220_);
lean_dec_ref(v_aig_2219_);
lean_dec_ref(v_inst_2218_);
lean_dec_ref(v_inst_2217_);
v_r_2224_ = lean_box(v_res_2223_);
return v_r_2224_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___redArg(lean_object* v_aig_2225_, lean_object* v_ref_2226_){
_start:
{
lean_object* v_gate_2227_; uint8_t v_invert_2228_; lean_object* v_decls_2229_; lean_object* v_decl_2230_; 
v_gate_2227_ = lean_ctor_get(v_ref_2226_, 0);
v_invert_2228_ = lean_ctor_get_uint8(v_ref_2226_, sizeof(void*)*1);
v_decls_2229_ = lean_ctor_get(v_aig_2225_, 0);
v_decl_2230_ = lean_array_fget_borrowed(v_decls_2229_, v_gate_2227_);
if (lean_obj_tag(v_decl_2230_) == 0)
{
lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2231_ = lean_box(v_invert_2228_);
v___x_2232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2231_);
return v___x_2232_;
}
else
{
lean_object* v___x_2233_; 
v___x_2233_ = lean_box(0);
return v___x_2233_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___redArg___boxed(lean_object* v_aig_2234_, lean_object* v_ref_2235_){
_start:
{
lean_object* v_res_2236_; 
v_res_2236_ = l_Std_Sat_AIG_getConstant___redArg(v_aig_2234_, v_ref_2235_);
lean_dec_ref(v_ref_2235_);
lean_dec_ref(v_aig_2234_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant(lean_object* v_00_u03b1_2237_, lean_object* v_inst_2238_, lean_object* v_inst_2239_, lean_object* v_aig_2240_, lean_object* v_ref_2241_){
_start:
{
lean_object* v___x_2242_; 
v___x_2242_ = l_Std_Sat_AIG_getConstant___redArg(v_aig_2240_, v_ref_2241_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___boxed(lean_object* v_00_u03b1_2243_, lean_object* v_inst_2244_, lean_object* v_inst_2245_, lean_object* v_aig_2246_, lean_object* v_ref_2247_){
_start:
{
lean_object* v_res_2248_; 
v_res_2248_ = l_Std_Sat_AIG_getConstant(v_00_u03b1_2243_, v_inst_2244_, v_inst_2245_, v_aig_2246_, v_ref_2247_);
lean_dec_ref(v_ref_2247_);
lean_dec_ref(v_aig_2246_);
lean_dec_ref(v_inst_2245_);
lean_dec_ref(v_inst_2244_);
return v_res_2248_;
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
