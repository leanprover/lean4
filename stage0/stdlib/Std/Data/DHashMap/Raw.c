// Lean compiler output
// Module: Std.Data.DHashMap.Raw
// Imports: public import Init.Data.LawfulHashable public import Std.Data.DHashMap.Internal.Defs import all Std.Data.DHashMap.Internal.Defs
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instForInOfForIn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mark_linear(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Sigma_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_emptyWithCapacity___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_emptyWithCapacity___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_emptyWithCapacity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_emptyWithCapacity___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Raw_instEmptyCollection___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Raw_instEmptyCollection___closed__0;
static lean_once_cell_t l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Raw_instEmptyCollection___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instEmptyCollection(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInhabited(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_markLinear___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_markLinear(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DHashMap_Raw_term___x7em___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Std_DHashMap_Raw_term___x7em___00__closed__0 = (const lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__0_value;
static const lean_string_object l_Std_DHashMap_Raw_term___x7em___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "DHashMap"};
static const lean_object* l_Std_DHashMap_Raw_term___x7em___00__closed__1 = (const lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__1_value;
static const lean_string_object l_Std_DHashMap_Raw_term___x7em___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Raw"};
static const lean_object* l_Std_DHashMap_Raw_term___x7em___00__closed__2 = (const lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__2_value;
static const lean_string_object l_Std_DHashMap_Raw_term___x7em___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_~m_"};
static const lean_object* l_Std_DHashMap_Raw_term___x7em___00__closed__3 = (const lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__3_value;
static const lean_ctor_object l_Std_DHashMap_Raw_term___x7em___00__closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_DHashMap_Raw_term___x7em___00__closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__4_value_aux_0),((lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(251, 125, 75, 48, 212, 67, 75, 250)}};
static const lean_ctor_object l_Std_DHashMap_Raw_term___x7em___00__closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__4_value_aux_1),((lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(4, 208, 171, 151, 52, 103, 172, 57)}};
static const lean_ctor_object l_Std_DHashMap_Raw_term___x7em___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__4_value_aux_2),((lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__3_value),LEAN_SCALAR_PTR_LITERAL(66, 56, 12, 237, 152, 116, 148, 199)}};
static const lean_object* l_Std_DHashMap_Raw_term___x7em___00__closed__4 = (const lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__4_value;
static const lean_string_object l_Std_DHashMap_Raw_term___x7em___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Std_DHashMap_Raw_term___x7em___00__closed__5 = (const lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__5_value;
static const lean_ctor_object l_Std_DHashMap_Raw_term___x7em___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__5_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Std_DHashMap_Raw_term___x7em___00__closed__6 = (const lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__6_value;
static const lean_string_object l_Std_DHashMap_Raw_term___x7em___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " ~m "};
static const lean_object* l_Std_DHashMap_Raw_term___x7em___00__closed__7 = (const lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__7_value;
static const lean_ctor_object l_Std_DHashMap_Raw_term___x7em___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__7_value)}};
static const lean_object* l_Std_DHashMap_Raw_term___x7em___00__closed__8 = (const lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__8_value;
static const lean_string_object l_Std_DHashMap_Raw_term___x7em___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Std_DHashMap_Raw_term___x7em___00__closed__9 = (const lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__9_value;
static const lean_ctor_object l_Std_DHashMap_Raw_term___x7em___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__9_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Std_DHashMap_Raw_term___x7em___00__closed__10 = (const lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__10_value;
static const lean_ctor_object l_Std_DHashMap_Raw_term___x7em___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__10_value),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l_Std_DHashMap_Raw_term___x7em___00__closed__11 = (const lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__11_value;
static const lean_ctor_object l_Std_DHashMap_Raw_term___x7em___00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__6_value),((lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__8_value),((lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__11_value)}};
static const lean_object* l_Std_DHashMap_Raw_term___x7em___00__closed__12 = (const lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__12_value;
static const lean_ctor_object l_Std_DHashMap_Raw_term___x7em___00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__4_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__12_value)}};
static const lean_object* l_Std_DHashMap_Raw_term___x7em___00__closed__13 = (const lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__13_value;
LEAN_EXPORT const lean_object* l_Std_DHashMap_Raw_term___x7em__ = (const lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__13_value;
static const lean_string_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__0 = (const lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__0_value;
static const lean_string_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__1 = (const lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__1_value;
static const lean_string_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__2 = (const lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__2_value;
static const lean_string_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__3 = (const lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__3_value;
static const lean_ctor_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4_value_aux_0),((lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4_value_aux_1),((lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4_value_aux_2),((lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4 = (const lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4_value;
static const lean_string_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Raw.Equiv"};
static const lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__5 = (const lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__5_value;
static lean_once_cell_t l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__6;
static const lean_string_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Equiv"};
static const lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__7 = (const lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__7_value;
static const lean_ctor_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(196, 77, 10, 233, 67, 27, 127, 47)}};
static const lean_ctor_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__8_value_aux_0),((lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(235, 138, 4, 70, 137, 129, 138, 224)}};
static const lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__8 = (const lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__8_value;
static const lean_ctor_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9_value_aux_0),((lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(251, 125, 75, 48, 212, 67, 75, 250)}};
static const lean_ctor_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9_value_aux_1),((lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(4, 208, 171, 151, 52, 103, 172, 57)}};
static const lean_ctor_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9_value_aux_2),((lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(43, 81, 159, 136, 76, 18, 51, 116)}};
static const lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9 = (const lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9_value;
static const lean_ctor_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__10 = (const lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__10_value;
static const lean_ctor_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9_value)}};
static const lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__11 = (const lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__11_value;
static const lean_ctor_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__12 = (const lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__12_value;
static const lean_ctor_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__10_value),((lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__12_value)}};
static const lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__13 = (const lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__13_value;
static const lean_string_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__14 = (const lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__14_value;
static const lean_ctor_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__15 = (const lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__15_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___closed__0 = (const lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___closed__0_value;
static const lean_ctor_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___closed__1 = (const lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0;
static lean_once_cell_t l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insertIfNew(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_containsThenInsert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_containsThenInsert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getThenInsertIfNew_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getThenInsertIfNew_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_containsThenInsertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_containsThenInsertIfNew(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_contains___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instMembershipOfBEqOfHashable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instMembershipOfBEqOfHashable___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instDecidableMem___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_instDecidableMem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instDecidableMem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getThenInsertIfNew_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getThenInsertIfNew_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKeyD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKeyD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKeyD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntryD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntryD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntryD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntryD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_isEmpty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_isEmpty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_modify(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_modify(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_alter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_alter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRevM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRevM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRev___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__0_value;
static const lean_closure_object l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__1 = (const lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__1_value;
static const lean_closure_object l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__2 = (const lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__2_value;
static const lean_closure_object l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__3 = (const lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__3_value;
static const lean_closure_object l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__4 = (const lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__4_value;
static const lean_closure_object l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__5 = (const lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__5_value;
static const lean_closure_object l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__6 = (const lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__6_value;
static const lean_ctor_object l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__0_value),((lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__1_value)}};
static const lean_object* l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__7 = (const lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__7_value;
static const lean_ctor_object l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__7_value),((lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__2_value),((lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__3_value),((lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__4_value),((lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__5_value)}};
static const lean_object* l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__8 = (const lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__8_value;
static const lean_ctor_object l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__8_value),((lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__6_value)}};
static const lean_object* l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9 = (const lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRev___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRev(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRev___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRev(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forMUncurried___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forMUncurried(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forInUncurried___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forInUncurried(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_filterMap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_filterMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_filter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toArray___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DHashMap_Raw_toArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_toArray___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_toArray___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Raw_toArray___redArg___closed__0_value;
static const lean_closure_object l_Std_DHashMap_Raw_toArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_toArray___redArg___lam__1, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value),((lean_object*)&l_Std_DHashMap_Raw_toArray___redArg___closed__0_value)} };
static const lean_object* l_Std_DHashMap_Raw_toArray___redArg___closed__1 = (const lean_object*)&l_Std_DHashMap_Raw_toArray___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toArray___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DHashMap_Raw_Const_toArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_Const_toArray___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_Const_toArray___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Raw_Const_toArray___redArg___closed__0_value;
static const lean_closure_object l_Std_DHashMap_Raw_Const_toArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_Const_toArray___redArg___lam__1, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value),((lean_object*)&l_Std_DHashMap_Raw_Const_toArray___redArg___closed__0_value)} };
static const lean_object* l_Std_DHashMap_Raw_Const_toArray___redArg___closed__1 = (const lean_object*)&l_Std_DHashMap_Raw_Const_toArray___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keysArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keysArray___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keysArray___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DHashMap_Raw_keysArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_keysArray___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_keysArray___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Raw_keysArray___redArg___closed__0_value;
static const lean_closure_object l_Std_DHashMap_Raw_keysArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_keysArray___redArg___lam__1, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value),((lean_object*)&l_Std_DHashMap_Raw_keysArray___redArg___closed__0_value)} };
static const lean_object* l_Std_DHashMap_Raw_keysArray___redArg___closed__1 = (const lean_object*)&l_Std_DHashMap_Raw_keysArray___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keysArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keysArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_union___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_union___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DHashMap_Raw_union___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value)} };
static const lean_object* l_Std_DHashMap_Raw_union___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Raw_union___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_union___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_union(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instUnionOfBEqOfHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instUnionOfBEqOfHashable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_inter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_inter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInterOfBEqOfHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInterOfBEqOfHashable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_beq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_beq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instBEqOfHashableOfLawfulBEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instBEqOfHashableOfLawfulBEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_Const_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_beq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_Const_beq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_diff___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_diff___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_diff___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_diff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instSDiffOfBEqOfHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instSDiffOfBEqOfHashable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_values___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_values___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_values___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DHashMap_Raw_values___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_values___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_values___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Raw_values___redArg___closed__0_value;
static const lean_closure_object l_Std_DHashMap_Raw_values___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_values___redArg___lam__1, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value),((lean_object*)&l_Std_DHashMap_Raw_values___redArg___closed__0_value)} };
static const lean_object* l_Std_DHashMap_Raw_values___redArg___closed__1 = (const lean_object*)&l_Std_DHashMap_Raw_values___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_values___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_values(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_valuesArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_valuesArray___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DHashMap_Raw_valuesArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_valuesArray___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_valuesArray___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Raw_valuesArray___redArg___closed__0_value;
static const lean_closure_object l_Std_DHashMap_Raw_valuesArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_keysArray___redArg___lam__1, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value),((lean_object*)&l_Std_DHashMap_Raw_valuesArray___redArg___closed__0_value)} };
static const lean_object* l_Std_DHashMap_Raw_valuesArray___redArg___closed__1 = (const lean_object*)&l_Std_DHashMap_Raw_valuesArray___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_valuesArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_valuesArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insertMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_eraseManyEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_eraseManyEntries(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_insertMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_insertManyIfNewUnit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_insertManyIfNewUnit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value)} };
static const lean_object* l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__0_value;
static const lean_closure_object l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instForInOfForIn_x27___redArg___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__0_value)} };
static const lean_object* l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1 = (const lean_object*)&l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_unitOfArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_unitOfArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_numBuckets___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_numBuckets___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_numBuckets(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_numBuckets___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toList___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toList___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DHashMap_Raw_toList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_toList___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_toList___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Raw_toList___redArg___closed__0_value;
static const lean_closure_object l_Std_DHashMap_Raw_toList___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_toList___redArg___lam__1, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value),((lean_object*)&l_Std_DHashMap_Raw_toList___redArg___closed__0_value)} };
static const lean_object* l_Std_DHashMap_Raw_toList___redArg___closed__1 = (const lean_object*)&l_Std_DHashMap_Raw_toList___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toList___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toList___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DHashMap_Raw_Const_toList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_Const_toList___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_Const_toList___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Raw_Const_toList___redArg___closed__0_value;
static const lean_closure_object l_Std_DHashMap_Raw_Const_toList___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_Const_toList___redArg___lam__1, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value),((lean_object*)&l_Std_DHashMap_Raw_Const_toList___redArg___closed__0_value)} };
static const lean_object* l_Std_DHashMap_Raw_Const_toList___redArg___closed__1 = (const lean_object*)&l_Std_DHashMap_Raw_Const_toList___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toList(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DHashMap_Raw_instRepr___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Std.DHashMap.Raw.ofList "};
static const lean_object* l_Std_DHashMap_Raw_instRepr___redArg___lam__2___closed__0 = (const lean_object*)&l_Std_DHashMap_Raw_instRepr___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_Std_DHashMap_Raw_instRepr___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_instRepr___redArg___lam__2___closed__0_value)}};
static const lean_object* l_Std_DHashMap_Raw_instRepr___redArg___lam__2___closed__1 = (const lean_object*)&l_Std_DHashMap_Raw_instRepr___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instRepr___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instRepr___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instRepr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instRepr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keys___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keys___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DHashMap_Raw_keys___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_keys___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_keys___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Raw_keys___redArg___closed__0_value;
static const lean_closure_object l_Std_DHashMap_Raw_keys___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_values___redArg___lam__1, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value),((lean_object*)&l_Std_DHashMap_Raw_keys___redArg___closed__0_value)} };
static const lean_object* l_Std_DHashMap_Raw_keys___redArg___closed__1 = (const lean_object*)&l_Std_DHashMap_Raw_keys___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keys___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keys(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DHashMap_Raw_ofList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value)} };
static const lean_object* l_Std_DHashMap_Raw_ofList___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Raw_ofList___redArg___closed__0_value;
static const lean_closure_object l_Std_DHashMap_Raw_ofList___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instForInOfForIn_x27___redArg___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_ofList___redArg___closed__0_value)} };
static const lean_object* l_Std_DHashMap_Raw_ofList___redArg___closed__1 = (const lean_object*)&l_Std_DHashMap_Raw_ofList___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_ofList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_ofList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_ofArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_ofArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_ofList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_ofList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_ofArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_ofArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_unitOfList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_unitOfList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_emptyWithCapacity___redArg(lean_object* v_capacity_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_2_ = lean_unsigned_to_nat(0u);
v___x_3_ = lean_unsigned_to_nat(4u);
v___x_4_ = lean_nat_mul(v_capacity_1_, v___x_3_);
v___x_5_ = lean_unsigned_to_nat(3u);
v___x_6_ = lean_nat_div(v___x_4_, v___x_5_);
lean_dec(v___x_4_);
v___x_7_ = l_Nat_nextPowerOfTwo(v___x_6_);
lean_dec(v___x_6_);
v___x_8_ = lean_box(0);
v___x_9_ = lean_mk_array(v___x_7_, v___x_8_);
v___x_10_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_10_, 0, v___x_2_);
lean_ctor_set(v___x_10_, 1, v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_emptyWithCapacity___redArg___boxed(lean_object* v_capacity_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Std_DHashMap_Raw_emptyWithCapacity___redArg(v_capacity_11_);
lean_dec(v_capacity_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_emptyWithCapacity(lean_object* v_00_u03b1_13_, lean_object* v_00_u03b2_14_, lean_object* v_capacity_15_){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_16_ = lean_unsigned_to_nat(0u);
v___x_17_ = lean_unsigned_to_nat(4u);
v___x_18_ = lean_nat_mul(v_capacity_15_, v___x_17_);
v___x_19_ = lean_unsigned_to_nat(3u);
v___x_20_ = lean_nat_div(v___x_18_, v___x_19_);
lean_dec(v___x_18_);
v___x_21_ = l_Nat_nextPowerOfTwo(v___x_20_);
lean_dec(v___x_20_);
v___x_22_ = lean_box(0);
v___x_23_ = lean_mk_array(v___x_21_, v___x_22_);
v___x_24_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_24_, 0, v___x_16_);
lean_ctor_set(v___x_24_, 1, v___x_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_emptyWithCapacity___boxed(lean_object* v_00_u03b1_25_, lean_object* v_00_u03b2_26_, lean_object* v_capacity_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Std_DHashMap_Raw_emptyWithCapacity(v_00_u03b1_25_, v_00_u03b2_26_, v_capacity_27_);
lean_dec(v_capacity_27_);
return v_res_28_;
}
}
static lean_object* _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__0(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = lean_box(0);
v___x_30_ = lean_unsigned_to_nat(16u);
v___x_31_ = lean_mk_array(v___x_30_, v___x_29_);
return v___x_31_;
}
}
static lean_object* _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1(void){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_32_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__0, &l_Std_DHashMap_Raw_instEmptyCollection___closed__0_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__0);
v___x_33_ = lean_unsigned_to_nat(0u);
v___x_34_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_34_, 0, v___x_33_);
lean_ctor_set(v___x_34_, 1, v___x_32_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instEmptyCollection(lean_object* v_00_u03b1_35_, lean_object* v_00_u03b2_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInhabited(lean_object* v_00_u03b1_38_, lean_object* v_00_u03b2_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_markLinear___redArg(lean_object* v_m_41_){
_start:
{
lean_object* v_size_42_; lean_object* v_buckets_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_51_; 
v_size_42_ = lean_ctor_get(v_m_41_, 0);
v_buckets_43_ = lean_ctor_get(v_m_41_, 1);
v_isSharedCheck_51_ = !lean_is_exclusive(v_m_41_);
if (v_isSharedCheck_51_ == 0)
{
v___x_45_ = v_m_41_;
v_isShared_46_ = v_isSharedCheck_51_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_buckets_43_);
lean_inc(v_size_42_);
lean_dec(v_m_41_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_51_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
lean_object* v___x_47_; lean_object* v___x_49_; 
v___x_47_ = lean_array_mark_linear(v_buckets_43_);
if (v_isShared_46_ == 0)
{
lean_ctor_set(v___x_45_, 1, v___x_47_);
v___x_49_ = v___x_45_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v_size_42_);
lean_ctor_set(v_reuseFailAlloc_50_, 1, v___x_47_);
v___x_49_ = v_reuseFailAlloc_50_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
return v___x_49_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_markLinear(lean_object* v_00_u03b1_52_, lean_object* v_00_u03b2_53_, lean_object* v_m_54_){
_start:
{
lean_object* v_size_55_; lean_object* v_buckets_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_64_; 
v_size_55_ = lean_ctor_get(v_m_54_, 0);
v_buckets_56_ = lean_ctor_get(v_m_54_, 1);
v_isSharedCheck_64_ = !lean_is_exclusive(v_m_54_);
if (v_isSharedCheck_64_ == 0)
{
v___x_58_ = v_m_54_;
v_isShared_59_ = v_isSharedCheck_64_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_buckets_56_);
lean_inc(v_size_55_);
lean_dec(v_m_54_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_64_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_60_; lean_object* v___x_62_; 
v___x_60_ = lean_array_mark_linear(v_buckets_56_);
if (v_isShared_59_ == 0)
{
lean_ctor_set(v___x_58_, 1, v___x_60_);
v___x_62_ = v___x_58_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v_size_55_);
lean_ctor_set(v_reuseFailAlloc_63_, 1, v___x_60_);
v___x_62_ = v_reuseFailAlloc_63_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
return v___x_62_;
}
}
}
}
static lean_object* _init_l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__6(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = ((lean_object*)(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__5));
v___x_106_ = l_String_toRawSubstring_x27(v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1(lean_object* v_x_130_, lean_object* v_a_131_, lean_object* v_a_132_){
_start:
{
lean_object* v___x_133_; uint8_t v___x_134_; 
v___x_133_ = ((lean_object*)(l_Std_DHashMap_Raw_term___x7em___00__closed__4));
lean_inc(v_x_130_);
v___x_134_ = l_Lean_Syntax_isOfKind(v_x_130_, v___x_133_);
if (v___x_134_ == 0)
{
lean_object* v___x_135_; lean_object* v___x_136_; 
lean_dec(v_x_130_);
v___x_135_ = lean_box(1);
v___x_136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_136_, 0, v___x_135_);
lean_ctor_set(v___x_136_, 1, v_a_132_);
return v___x_136_;
}
else
{
lean_object* v_quotContext_137_; lean_object* v_currMacroScope_138_; lean_object* v_ref_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; uint8_t v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v_quotContext_137_ = lean_ctor_get(v_a_131_, 1);
v_currMacroScope_138_ = lean_ctor_get(v_a_131_, 2);
v_ref_139_ = lean_ctor_get(v_a_131_, 5);
v___x_140_ = lean_unsigned_to_nat(0u);
v___x_141_ = l_Lean_Syntax_getArg(v_x_130_, v___x_140_);
v___x_142_ = lean_unsigned_to_nat(2u);
v___x_143_ = l_Lean_Syntax_getArg(v_x_130_, v___x_142_);
lean_dec(v_x_130_);
v___x_144_ = 0;
v___x_145_ = l_Lean_SourceInfo_fromRef(v_ref_139_, v___x_144_);
v___x_146_ = ((lean_object*)(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4));
v___x_147_ = lean_obj_once(&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__6, &l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__6_once, _init_l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__6);
v___x_148_ = ((lean_object*)(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__8));
lean_inc(v_currMacroScope_138_);
lean_inc(v_quotContext_137_);
v___x_149_ = l_Lean_addMacroScope(v_quotContext_137_, v___x_148_, v_currMacroScope_138_);
v___x_150_ = ((lean_object*)(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__13));
lean_inc_n(v___x_145_, 2);
v___x_151_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_151_, 0, v___x_145_);
lean_ctor_set(v___x_151_, 1, v___x_147_);
lean_ctor_set(v___x_151_, 2, v___x_149_);
lean_ctor_set(v___x_151_, 3, v___x_150_);
v___x_152_ = ((lean_object*)(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__15));
v___x_153_ = l_Lean_Syntax_node2(v___x_145_, v___x_152_, v___x_141_, v___x_143_);
v___x_154_ = l_Lean_Syntax_node2(v___x_145_, v___x_146_, v___x_151_, v___x_153_);
v___x_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
lean_ctor_set(v___x_155_, 1, v_a_132_);
return v___x_155_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___boxed(lean_object* v_x_156_, lean_object* v_a_157_, lean_object* v_a_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1(v_x_156_, v_a_157_, v_a_158_);
lean_dec_ref(v_a_157_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1(lean_object* v_x_163_, lean_object* v_a_164_, lean_object* v_a_165_){
_start:
{
lean_object* v___x_166_; uint8_t v___x_167_; 
v___x_166_ = ((lean_object*)(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4));
lean_inc(v_x_163_);
v___x_167_ = l_Lean_Syntax_isOfKind(v_x_163_, v___x_166_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; lean_object* v___x_169_; 
lean_dec(v_x_163_);
v___x_168_ = lean_box(0);
v___x_169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
lean_ctor_set(v___x_169_, 1, v_a_165_);
return v___x_169_;
}
else
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_170_ = lean_unsigned_to_nat(0u);
v___x_171_ = l_Lean_Syntax_getArg(v_x_163_, v___x_170_);
v___x_172_ = ((lean_object*)(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___closed__1));
lean_inc(v___x_171_);
v___x_173_ = l_Lean_Syntax_isOfKind(v___x_171_, v___x_172_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; lean_object* v___x_175_; 
lean_dec(v___x_171_);
lean_dec(v_x_163_);
v___x_174_ = lean_box(0);
v___x_175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
lean_ctor_set(v___x_175_, 1, v_a_165_);
return v___x_175_;
}
else
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; uint8_t v___x_179_; 
v___x_176_ = lean_unsigned_to_nat(1u);
v___x_177_ = l_Lean_Syntax_getArg(v_x_163_, v___x_176_);
lean_dec(v_x_163_);
v___x_178_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_177_);
v___x_179_ = l_Lean_Syntax_matchesNull(v___x_177_, v___x_178_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; lean_object* v___x_181_; 
lean_dec(v___x_177_);
lean_dec(v___x_171_);
v___x_180_ = lean_box(0);
v___x_181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set(v___x_181_, 1, v_a_165_);
return v___x_181_;
}
else
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v_ref_184_; uint8_t v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_182_ = l_Lean_Syntax_getArg(v___x_177_, v___x_170_);
v___x_183_ = l_Lean_Syntax_getArg(v___x_177_, v___x_176_);
lean_dec(v___x_177_);
v_ref_184_ = l_Lean_replaceRef(v___x_171_, v_a_164_);
lean_dec(v___x_171_);
v___x_185_ = 0;
v___x_186_ = l_Lean_SourceInfo_fromRef(v_ref_184_, v___x_185_);
lean_dec(v_ref_184_);
v___x_187_ = ((lean_object*)(l_Std_DHashMap_Raw_term___x7em___00__closed__4));
v___x_188_ = ((lean_object*)(l_Std_DHashMap_Raw_term___x7em___00__closed__7));
lean_inc(v___x_186_);
v___x_189_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_186_);
lean_ctor_set(v___x_189_, 1, v___x_188_);
v___x_190_ = l_Lean_Syntax_node3(v___x_186_, v___x_187_, v___x_182_, v___x_189_, v___x_183_);
v___x_191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
lean_ctor_set(v___x_191_, 1, v_a_165_);
return v___x_191_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___boxed(lean_object* v_x_192_, lean_object* v_a_193_, lean_object* v_a_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1(v_x_192_, v_a_193_, v_a_194_);
lean_dec(v_a_193_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insert___redArg(lean_object* v_inst_196_, lean_object* v_inst_197_, lean_object* v_m_198_, lean_object* v_a_199_, lean_object* v_b_200_){
_start:
{
lean_object* v_buckets_201_; lean_object* v___x_202_; lean_object* v___x_203_; uint8_t v___x_204_; 
v_buckets_201_ = lean_ctor_get(v_m_198_, 1);
v___x_202_ = lean_unsigned_to_nat(0u);
v___x_203_ = lean_array_get_size(v_buckets_201_);
v___x_204_ = lean_nat_dec_lt(v___x_202_, v___x_203_);
if (v___x_204_ == 0)
{
lean_dec(v_b_200_);
lean_dec(v_a_199_);
lean_dec_ref(v_inst_197_);
lean_dec_ref(v_inst_196_);
return v_m_198_;
}
else
{
lean_object* v___x_205_; 
v___x_205_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_196_, v_inst_197_, v_m_198_, v_a_199_, v_b_200_);
return v___x_205_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insert(lean_object* v_00_u03b1_206_, lean_object* v_00_u03b2_207_, lean_object* v_inst_208_, lean_object* v_inst_209_, lean_object* v_m_210_, lean_object* v_a_211_, lean_object* v_b_212_){
_start:
{
lean_object* v_buckets_213_; lean_object* v___x_214_; lean_object* v___x_215_; uint8_t v___x_216_; 
v_buckets_213_ = lean_ctor_get(v_m_210_, 1);
v___x_214_ = lean_unsigned_to_nat(0u);
v___x_215_ = lean_array_get_size(v_buckets_213_);
v___x_216_ = lean_nat_dec_lt(v___x_214_, v___x_215_);
if (v___x_216_ == 0)
{
lean_dec(v_b_212_);
lean_dec(v_a_211_);
lean_dec_ref(v_inst_209_);
lean_dec_ref(v_inst_208_);
return v_m_210_;
}
else
{
lean_object* v___x_217_; 
v___x_217_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_208_, v_inst_209_, v_m_210_, v_a_211_, v_b_212_);
return v___x_217_;
}
}
}
static lean_object* _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__0, &l_Std_DHashMap_Raw_instEmptyCollection___closed__0_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__0);
v___x_219_ = lean_array_get_size(v___x_218_);
return v___x_219_;
}
}
static uint8_t _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; uint8_t v___x_222_; 
v___x_220_ = lean_obj_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0);
v___x_221_ = lean_unsigned_to_nat(0u);
v___x_222_ = lean_nat_dec_lt(v___x_221_, v___x_220_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0(lean_object* v_inst_223_, lean_object* v_inst_224_, lean_object* v_x_225_){
_start:
{
lean_object* v_fst_226_; lean_object* v_snd_227_; lean_object* v___x_228_; uint8_t v___x_229_; 
v_fst_226_ = lean_ctor_get(v_x_225_, 0);
lean_inc(v_fst_226_);
v_snd_227_ = lean_ctor_get(v_x_225_, 1);
lean_inc(v_snd_227_);
lean_dec_ref(v_x_225_);
v___x_228_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
v___x_229_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_229_ == 0)
{
lean_dec(v_snd_227_);
lean_dec(v_fst_226_);
lean_dec_ref(v_inst_224_);
lean_dec_ref(v_inst_223_);
return v___x_228_;
}
else
{
lean_object* v___x_230_; 
v___x_230_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_223_, v_inst_224_, v___x_228_, v_fst_226_, v_snd_227_);
return v___x_230_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg(lean_object* v_inst_231_, lean_object* v_inst_232_){
_start:
{
lean_object* v___f_233_; 
v___f_233_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_233_, 0, v_inst_231_);
lean_closure_set(v___f_233_, 1, v_inst_232_);
return v___f_233_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable(lean_object* v_00_u03b1_234_, lean_object* v_00_u03b2_235_, lean_object* v_inst_236_, lean_object* v_inst_237_){
_start:
{
lean_object* v___f_238_; 
v___f_238_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_238_, 0, v_inst_236_);
lean_closure_set(v___f_238_, 1, v_inst_237_);
return v___f_238_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable___redArg___lam__0(lean_object* v_inst_239_, lean_object* v_inst_240_, lean_object* v_x_241_, lean_object* v_s_242_){
_start:
{
lean_object* v_fst_243_; lean_object* v_snd_244_; lean_object* v_buckets_245_; lean_object* v___x_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v_fst_243_ = lean_ctor_get(v_x_241_, 0);
lean_inc(v_fst_243_);
v_snd_244_ = lean_ctor_get(v_x_241_, 1);
lean_inc(v_snd_244_);
lean_dec_ref(v_x_241_);
v_buckets_245_ = lean_ctor_get(v_s_242_, 1);
v___x_246_ = lean_unsigned_to_nat(0u);
v___x_247_ = lean_array_get_size(v_buckets_245_);
v___x_248_ = lean_nat_dec_lt(v___x_246_, v___x_247_);
if (v___x_248_ == 0)
{
lean_dec(v_snd_244_);
lean_dec(v_fst_243_);
lean_dec_ref(v_inst_240_);
lean_dec_ref(v_inst_239_);
return v_s_242_;
}
else
{
lean_object* v___x_249_; 
v___x_249_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_239_, v_inst_240_, v_s_242_, v_fst_243_, v_snd_244_);
return v___x_249_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable___redArg(lean_object* v_inst_250_, lean_object* v_inst_251_){
_start:
{
lean_object* v___f_252_; 
v___f_252_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_252_, 0, v_inst_250_);
lean_closure_set(v___f_252_, 1, v_inst_251_);
return v___f_252_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable(lean_object* v_00_u03b1_253_, lean_object* v_00_u03b2_254_, lean_object* v_inst_255_, lean_object* v_inst_256_){
_start:
{
lean_object* v___f_257_; 
v___f_257_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_257_, 0, v_inst_255_);
lean_closure_set(v___f_257_, 1, v_inst_256_);
return v___f_257_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insertIfNew___redArg(lean_object* v_inst_258_, lean_object* v_inst_259_, lean_object* v_m_260_, lean_object* v_a_261_, lean_object* v_b_262_){
_start:
{
lean_object* v_buckets_263_; lean_object* v___x_264_; lean_object* v___x_265_; uint8_t v___x_266_; 
v_buckets_263_ = lean_ctor_get(v_m_260_, 1);
v___x_264_ = lean_unsigned_to_nat(0u);
v___x_265_ = lean_array_get_size(v_buckets_263_);
v___x_266_ = lean_nat_dec_lt(v___x_264_, v___x_265_);
if (v___x_266_ == 0)
{
lean_dec(v_b_262_);
lean_dec(v_a_261_);
lean_dec_ref(v_inst_259_);
lean_dec_ref(v_inst_258_);
return v_m_260_;
}
else
{
lean_object* v___x_267_; 
v___x_267_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_258_, v_inst_259_, v_m_260_, v_a_261_, v_b_262_);
return v___x_267_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insertIfNew(lean_object* v_00_u03b1_268_, lean_object* v_00_u03b2_269_, lean_object* v_inst_270_, lean_object* v_inst_271_, lean_object* v_m_272_, lean_object* v_a_273_, lean_object* v_b_274_){
_start:
{
lean_object* v_buckets_275_; lean_object* v___x_276_; lean_object* v___x_277_; uint8_t v___x_278_; 
v_buckets_275_ = lean_ctor_get(v_m_272_, 1);
v___x_276_ = lean_unsigned_to_nat(0u);
v___x_277_ = lean_array_get_size(v_buckets_275_);
v___x_278_ = lean_nat_dec_lt(v___x_276_, v___x_277_);
if (v___x_278_ == 0)
{
lean_dec(v_b_274_);
lean_dec(v_a_273_);
lean_dec_ref(v_inst_271_);
lean_dec_ref(v_inst_270_);
return v_m_272_;
}
else
{
lean_object* v___x_279_; 
v___x_279_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_270_, v_inst_271_, v_m_272_, v_a_273_, v_b_274_);
return v___x_279_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_containsThenInsert___redArg(lean_object* v_inst_280_, lean_object* v_inst_281_, lean_object* v_m_282_, lean_object* v_a_283_, lean_object* v_b_284_){
_start:
{
lean_object* v_size_285_; lean_object* v_buckets_286_; lean_object* v___x_287_; lean_object* v___x_288_; uint8_t v___x_289_; 
v_size_285_ = lean_ctor_get(v_m_282_, 0);
v_buckets_286_ = lean_ctor_get(v_m_282_, 1);
v___x_287_ = lean_unsigned_to_nat(0u);
v___x_288_ = lean_array_get_size(v_buckets_286_);
v___x_289_ = lean_nat_dec_lt(v___x_287_, v___x_288_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; lean_object* v___x_291_; 
lean_dec(v_b_284_);
lean_dec(v_a_283_);
lean_dec_ref(v_inst_281_);
lean_dec_ref(v_inst_280_);
v___x_290_ = lean_box(v___x_289_);
v___x_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
lean_ctor_set(v___x_291_, 1, v_m_282_);
return v___x_291_;
}
else
{
lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_341_; 
lean_inc_ref(v_buckets_286_);
lean_inc(v_size_285_);
v_isSharedCheck_341_ = !lean_is_exclusive(v_m_282_);
if (v_isSharedCheck_341_ == 0)
{
lean_object* v_unused_342_; lean_object* v_unused_343_; 
v_unused_342_ = lean_ctor_get(v_m_282_, 1);
lean_dec(v_unused_342_);
v_unused_343_ = lean_ctor_get(v_m_282_, 0);
lean_dec(v_unused_343_);
v___x_293_ = v_m_282_;
v_isShared_294_ = v_isSharedCheck_341_;
goto v_resetjp_292_;
}
else
{
lean_dec(v_m_282_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_341_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_295_; uint64_t v___x_296_; uint64_t v___x_297_; uint64_t v___x_298_; uint64_t v___x_299_; uint64_t v_fold_300_; uint64_t v___x_301_; uint64_t v___x_302_; uint64_t v___x_303_; size_t v___x_304_; size_t v___x_305_; size_t v___x_306_; size_t v___x_307_; size_t v___x_308_; lean_object* v_bkt_309_; uint8_t v___x_310_; 
lean_inc_ref(v_inst_281_);
lean_inc_n(v_a_283_, 2);
v___x_295_ = lean_apply_1(v_inst_281_, v_a_283_);
v___x_296_ = 32ULL;
v___x_297_ = lean_unbox_uint64(v___x_295_);
v___x_298_ = lean_uint64_shift_right(v___x_297_, v___x_296_);
v___x_299_ = lean_unbox_uint64(v___x_295_);
lean_dec_ref(v___x_295_);
v_fold_300_ = lean_uint64_xor(v___x_299_, v___x_298_);
v___x_301_ = 16ULL;
v___x_302_ = lean_uint64_shift_right(v_fold_300_, v___x_301_);
v___x_303_ = lean_uint64_xor(v_fold_300_, v___x_302_);
v___x_304_ = lean_uint64_to_usize(v___x_303_);
v___x_305_ = lean_usize_of_nat(v___x_288_);
v___x_306_ = ((size_t)1ULL);
v___x_307_ = lean_usize_sub(v___x_305_, v___x_306_);
v___x_308_ = lean_usize_land(v___x_304_, v___x_307_);
v_bkt_309_ = lean_array_uget_borrowed(v_buckets_286_, v___x_308_);
lean_inc(v_bkt_309_);
lean_inc_ref(v_inst_280_);
v___x_310_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_280_, v_a_283_, v_bkt_309_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; lean_object* v_size_x27_312_; lean_object* v___x_313_; lean_object* v_buckets_x27_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; uint8_t v___x_320_; 
lean_dec_ref(v_inst_280_);
v___x_311_ = lean_unsigned_to_nat(1u);
v_size_x27_312_ = lean_nat_add(v_size_285_, v___x_311_);
lean_dec(v_size_285_);
lean_inc(v_bkt_309_);
v___x_313_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_313_, 0, v_a_283_);
lean_ctor_set(v___x_313_, 1, v_b_284_);
lean_ctor_set(v___x_313_, 2, v_bkt_309_);
v_buckets_x27_314_ = lean_array_uset(v_buckets_286_, v___x_308_, v___x_313_);
v___x_315_ = lean_unsigned_to_nat(4u);
v___x_316_ = lean_nat_mul(v_size_x27_312_, v___x_315_);
v___x_317_ = lean_unsigned_to_nat(3u);
v___x_318_ = lean_nat_div(v___x_316_, v___x_317_);
lean_dec(v___x_316_);
v___x_319_ = lean_array_get_size(v_buckets_x27_314_);
v___x_320_ = lean_nat_dec_le(v___x_318_, v___x_319_);
lean_dec(v___x_318_);
if (v___x_320_ == 0)
{
lean_object* v_val_321_; lean_object* v___x_323_; 
v_val_321_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_281_, v_buckets_x27_314_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 1, v_val_321_);
lean_ctor_set(v___x_293_, 0, v_size_x27_312_);
v___x_323_ = v___x_293_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_size_x27_312_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_val_321_);
v___x_323_ = v_reuseFailAlloc_326_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = lean_box(v___x_310_);
v___x_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
lean_ctor_set(v___x_325_, 1, v___x_323_);
return v___x_325_;
}
}
else
{
lean_object* v___x_328_; 
lean_dec_ref(v_inst_281_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 1, v_buckets_x27_314_);
lean_ctor_set(v___x_293_, 0, v_size_x27_312_);
v___x_328_ = v___x_293_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_size_x27_312_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v_buckets_x27_314_);
v___x_328_ = v_reuseFailAlloc_331_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = lean_box(v___x_310_);
v___x_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
lean_ctor_set(v___x_330_, 1, v___x_328_);
return v___x_330_;
}
}
}
else
{
lean_object* v___x_332_; lean_object* v_buckets_x27_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_337_; 
lean_inc(v_bkt_309_);
lean_dec_ref(v_inst_281_);
v___x_332_ = lean_box(0);
v_buckets_x27_333_ = lean_array_uset(v_buckets_286_, v___x_308_, v___x_332_);
v___x_334_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_inst_280_, v_a_283_, v_b_284_, v_bkt_309_);
v___x_335_ = lean_array_uset(v_buckets_x27_333_, v___x_308_, v___x_334_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 1, v___x_335_);
v___x_337_ = v___x_293_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_size_285_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v___x_335_);
v___x_337_ = v_reuseFailAlloc_340_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = lean_box(v___x_310_);
v___x_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
lean_ctor_set(v___x_339_, 1, v___x_337_);
return v___x_339_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_containsThenInsert(lean_object* v_00_u03b1_344_, lean_object* v_00_u03b2_345_, lean_object* v_inst_346_, lean_object* v_inst_347_, lean_object* v_m_348_, lean_object* v_a_349_, lean_object* v_b_350_){
_start:
{
lean_object* v_size_351_; lean_object* v_buckets_352_; lean_object* v___x_353_; lean_object* v___x_354_; uint8_t v___x_355_; 
v_size_351_ = lean_ctor_get(v_m_348_, 0);
v_buckets_352_ = lean_ctor_get(v_m_348_, 1);
v___x_353_ = lean_unsigned_to_nat(0u);
v___x_354_ = lean_array_get_size(v_buckets_352_);
v___x_355_ = lean_nat_dec_lt(v___x_353_, v___x_354_);
if (v___x_355_ == 0)
{
lean_object* v___x_356_; lean_object* v___x_357_; 
lean_dec(v_b_350_);
lean_dec(v_a_349_);
lean_dec_ref(v_inst_347_);
lean_dec_ref(v_inst_346_);
v___x_356_ = lean_box(v___x_355_);
v___x_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
lean_ctor_set(v___x_357_, 1, v_m_348_);
return v___x_357_;
}
else
{
lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_407_; 
lean_inc_ref(v_buckets_352_);
lean_inc(v_size_351_);
v_isSharedCheck_407_ = !lean_is_exclusive(v_m_348_);
if (v_isSharedCheck_407_ == 0)
{
lean_object* v_unused_408_; lean_object* v_unused_409_; 
v_unused_408_ = lean_ctor_get(v_m_348_, 1);
lean_dec(v_unused_408_);
v_unused_409_ = lean_ctor_get(v_m_348_, 0);
lean_dec(v_unused_409_);
v___x_359_ = v_m_348_;
v_isShared_360_ = v_isSharedCheck_407_;
goto v_resetjp_358_;
}
else
{
lean_dec(v_m_348_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_407_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_361_; uint64_t v___x_362_; uint64_t v___x_363_; uint64_t v___x_364_; uint64_t v___x_365_; uint64_t v_fold_366_; uint64_t v___x_367_; uint64_t v___x_368_; uint64_t v___x_369_; size_t v___x_370_; size_t v___x_371_; size_t v___x_372_; size_t v___x_373_; size_t v___x_374_; lean_object* v_bkt_375_; uint8_t v___x_376_; 
lean_inc_ref(v_inst_347_);
lean_inc_n(v_a_349_, 2);
v___x_361_ = lean_apply_1(v_inst_347_, v_a_349_);
v___x_362_ = 32ULL;
v___x_363_ = lean_unbox_uint64(v___x_361_);
v___x_364_ = lean_uint64_shift_right(v___x_363_, v___x_362_);
v___x_365_ = lean_unbox_uint64(v___x_361_);
lean_dec_ref(v___x_361_);
v_fold_366_ = lean_uint64_xor(v___x_365_, v___x_364_);
v___x_367_ = 16ULL;
v___x_368_ = lean_uint64_shift_right(v_fold_366_, v___x_367_);
v___x_369_ = lean_uint64_xor(v_fold_366_, v___x_368_);
v___x_370_ = lean_uint64_to_usize(v___x_369_);
v___x_371_ = lean_usize_of_nat(v___x_354_);
v___x_372_ = ((size_t)1ULL);
v___x_373_ = lean_usize_sub(v___x_371_, v___x_372_);
v___x_374_ = lean_usize_land(v___x_370_, v___x_373_);
v_bkt_375_ = lean_array_uget_borrowed(v_buckets_352_, v___x_374_);
lean_inc(v_bkt_375_);
lean_inc_ref(v_inst_346_);
v___x_376_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_346_, v_a_349_, v_bkt_375_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; lean_object* v_size_x27_378_; lean_object* v___x_379_; lean_object* v_buckets_x27_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; uint8_t v___x_386_; 
lean_dec_ref(v_inst_346_);
v___x_377_ = lean_unsigned_to_nat(1u);
v_size_x27_378_ = lean_nat_add(v_size_351_, v___x_377_);
lean_dec(v_size_351_);
lean_inc(v_bkt_375_);
v___x_379_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_379_, 0, v_a_349_);
lean_ctor_set(v___x_379_, 1, v_b_350_);
lean_ctor_set(v___x_379_, 2, v_bkt_375_);
v_buckets_x27_380_ = lean_array_uset(v_buckets_352_, v___x_374_, v___x_379_);
v___x_381_ = lean_unsigned_to_nat(4u);
v___x_382_ = lean_nat_mul(v_size_x27_378_, v___x_381_);
v___x_383_ = lean_unsigned_to_nat(3u);
v___x_384_ = lean_nat_div(v___x_382_, v___x_383_);
lean_dec(v___x_382_);
v___x_385_ = lean_array_get_size(v_buckets_x27_380_);
v___x_386_ = lean_nat_dec_le(v___x_384_, v___x_385_);
lean_dec(v___x_384_);
if (v___x_386_ == 0)
{
lean_object* v_val_387_; lean_object* v___x_389_; 
v_val_387_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_347_, v_buckets_x27_380_);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 1, v_val_387_);
lean_ctor_set(v___x_359_, 0, v_size_x27_378_);
v___x_389_ = v___x_359_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_size_x27_378_);
lean_ctor_set(v_reuseFailAlloc_392_, 1, v_val_387_);
v___x_389_ = v_reuseFailAlloc_392_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = lean_box(v___x_376_);
v___x_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
lean_ctor_set(v___x_391_, 1, v___x_389_);
return v___x_391_;
}
}
else
{
lean_object* v___x_394_; 
lean_dec_ref(v_inst_347_);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 1, v_buckets_x27_380_);
lean_ctor_set(v___x_359_, 0, v_size_x27_378_);
v___x_394_ = v___x_359_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_size_x27_378_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v_buckets_x27_380_);
v___x_394_ = v_reuseFailAlloc_397_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = lean_box(v___x_376_);
v___x_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
lean_ctor_set(v___x_396_, 1, v___x_394_);
return v___x_396_;
}
}
}
else
{
lean_object* v___x_398_; lean_object* v_buckets_x27_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_403_; 
lean_inc(v_bkt_375_);
lean_dec_ref(v_inst_347_);
v___x_398_ = lean_box(0);
v_buckets_x27_399_ = lean_array_uset(v_buckets_352_, v___x_374_, v___x_398_);
v___x_400_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_inst_346_, v_a_349_, v_b_350_, v_bkt_375_);
v___x_401_ = lean_array_uset(v_buckets_x27_399_, v___x_374_, v___x_400_);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 1, v___x_401_);
v___x_403_ = v___x_359_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_size_351_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v___x_401_);
v___x_403_ = v_reuseFailAlloc_406_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = lean_box(v___x_376_);
v___x_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v___x_403_);
return v___x_405_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getThenInsertIfNew_x3f___redArg(lean_object* v_inst_410_, lean_object* v_inst_411_, lean_object* v_m_412_, lean_object* v_a_413_, lean_object* v_b_414_){
_start:
{
lean_object* v_size_415_; lean_object* v_buckets_416_; lean_object* v___x_417_; lean_object* v___x_418_; uint8_t v___x_419_; 
v_size_415_ = lean_ctor_get(v_m_412_, 0);
v_buckets_416_ = lean_ctor_get(v_m_412_, 1);
v___x_417_ = lean_unsigned_to_nat(0u);
v___x_418_ = lean_array_get_size(v_buckets_416_);
v___x_419_ = lean_nat_dec_lt(v___x_417_, v___x_418_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; lean_object* v___x_421_; 
lean_dec(v_b_414_);
lean_dec(v_a_413_);
lean_dec_ref(v_inst_411_);
lean_dec_ref(v_inst_410_);
v___x_420_ = lean_box(0);
v___x_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
lean_ctor_set(v___x_421_, 1, v_m_412_);
return v___x_421_;
}
else
{
lean_object* v___x_422_; uint64_t v___x_423_; uint64_t v___x_424_; uint64_t v___x_425_; uint64_t v___x_426_; uint64_t v_fold_427_; uint64_t v___x_428_; uint64_t v___x_429_; uint64_t v___x_430_; size_t v___x_431_; size_t v___x_432_; size_t v___x_433_; size_t v___x_434_; size_t v___x_435_; lean_object* v_bkt_436_; lean_object* v___x_437_; 
lean_inc_ref(v_inst_411_);
lean_inc_n(v_a_413_, 2);
v___x_422_ = lean_apply_1(v_inst_411_, v_a_413_);
v___x_423_ = 32ULL;
v___x_424_ = lean_unbox_uint64(v___x_422_);
v___x_425_ = lean_uint64_shift_right(v___x_424_, v___x_423_);
v___x_426_ = lean_unbox_uint64(v___x_422_);
lean_dec_ref(v___x_422_);
v_fold_427_ = lean_uint64_xor(v___x_426_, v___x_425_);
v___x_428_ = 16ULL;
v___x_429_ = lean_uint64_shift_right(v_fold_427_, v___x_428_);
v___x_430_ = lean_uint64_xor(v_fold_427_, v___x_429_);
v___x_431_ = lean_uint64_to_usize(v___x_430_);
v___x_432_ = lean_usize_of_nat(v___x_418_);
v___x_433_ = ((size_t)1ULL);
v___x_434_ = lean_usize_sub(v___x_432_, v___x_433_);
v___x_435_ = lean_usize_land(v___x_431_, v___x_434_);
v_bkt_436_ = lean_array_uget_borrowed(v_buckets_416_, v___x_435_);
lean_inc(v_bkt_436_);
v___x_437_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(v_inst_410_, v_a_413_, v_bkt_436_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_460_; 
lean_inc_ref(v_buckets_416_);
lean_inc(v_size_415_);
v_isSharedCheck_460_ = !lean_is_exclusive(v_m_412_);
if (v_isSharedCheck_460_ == 0)
{
lean_object* v_unused_461_; lean_object* v_unused_462_; 
v_unused_461_ = lean_ctor_get(v_m_412_, 1);
lean_dec(v_unused_461_);
v_unused_462_ = lean_ctor_get(v_m_412_, 0);
lean_dec(v_unused_462_);
v___x_439_ = v_m_412_;
v_isShared_440_ = v_isSharedCheck_460_;
goto v_resetjp_438_;
}
else
{
lean_dec(v_m_412_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_460_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; lean_object* v_size_x27_442_; lean_object* v___x_443_; lean_object* v_buckets_x27_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; uint8_t v___x_450_; 
v___x_441_ = lean_unsigned_to_nat(1u);
v_size_x27_442_ = lean_nat_add(v_size_415_, v___x_441_);
lean_dec(v_size_415_);
lean_inc(v_bkt_436_);
v___x_443_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_443_, 0, v_a_413_);
lean_ctor_set(v___x_443_, 1, v_b_414_);
lean_ctor_set(v___x_443_, 2, v_bkt_436_);
v_buckets_x27_444_ = lean_array_uset(v_buckets_416_, v___x_435_, v___x_443_);
v___x_445_ = lean_unsigned_to_nat(4u);
v___x_446_ = lean_nat_mul(v_size_x27_442_, v___x_445_);
v___x_447_ = lean_unsigned_to_nat(3u);
v___x_448_ = lean_nat_div(v___x_446_, v___x_447_);
lean_dec(v___x_446_);
v___x_449_ = lean_array_get_size(v_buckets_x27_444_);
v___x_450_ = lean_nat_dec_le(v___x_448_, v___x_449_);
lean_dec(v___x_448_);
if (v___x_450_ == 0)
{
lean_object* v_val_451_; lean_object* v___x_453_; 
v_val_451_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_411_, v_buckets_x27_444_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 1, v_val_451_);
lean_ctor_set(v___x_439_, 0, v_size_x27_442_);
v___x_453_ = v___x_439_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_size_x27_442_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_val_451_);
v___x_453_ = v_reuseFailAlloc_455_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
lean_object* v___x_454_; 
v___x_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_437_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
return v___x_454_;
}
}
else
{
lean_object* v___x_457_; 
lean_dec_ref(v_inst_411_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 1, v_buckets_x27_444_);
lean_ctor_set(v___x_439_, 0, v_size_x27_442_);
v___x_457_ = v___x_439_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_size_x27_442_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v_buckets_x27_444_);
v___x_457_ = v_reuseFailAlloc_459_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
lean_object* v___x_458_; 
v___x_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_437_);
lean_ctor_set(v___x_458_, 1, v___x_457_);
return v___x_458_;
}
}
}
}
else
{
lean_object* v___x_463_; 
lean_dec(v_b_414_);
lean_dec(v_a_413_);
lean_dec_ref(v_inst_411_);
v___x_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_437_);
lean_ctor_set(v___x_463_, 1, v_m_412_);
return v___x_463_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_464_, lean_object* v_00_u03b2_465_, lean_object* v_inst_466_, lean_object* v_inst_467_, lean_object* v_inst_468_, lean_object* v_m_469_, lean_object* v_a_470_, lean_object* v_b_471_){
_start:
{
lean_object* v_size_472_; lean_object* v_buckets_473_; lean_object* v___x_474_; lean_object* v___x_475_; uint8_t v___x_476_; 
v_size_472_ = lean_ctor_get(v_m_469_, 0);
v_buckets_473_ = lean_ctor_get(v_m_469_, 1);
v___x_474_ = lean_unsigned_to_nat(0u);
v___x_475_ = lean_array_get_size(v_buckets_473_);
v___x_476_ = lean_nat_dec_lt(v___x_474_, v___x_475_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; lean_object* v___x_478_; 
lean_dec(v_b_471_);
lean_dec(v_a_470_);
lean_dec_ref(v_inst_467_);
lean_dec_ref(v_inst_466_);
v___x_477_ = lean_box(0);
v___x_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
lean_ctor_set(v___x_478_, 1, v_m_469_);
return v___x_478_;
}
else
{
lean_object* v___x_479_; uint64_t v___x_480_; uint64_t v___x_481_; uint64_t v___x_482_; uint64_t v___x_483_; uint64_t v_fold_484_; uint64_t v___x_485_; uint64_t v___x_486_; uint64_t v___x_487_; size_t v___x_488_; size_t v___x_489_; size_t v___x_490_; size_t v___x_491_; size_t v___x_492_; lean_object* v_bkt_493_; lean_object* v___x_494_; 
lean_inc_ref(v_inst_467_);
lean_inc_n(v_a_470_, 2);
v___x_479_ = lean_apply_1(v_inst_467_, v_a_470_);
v___x_480_ = 32ULL;
v___x_481_ = lean_unbox_uint64(v___x_479_);
v___x_482_ = lean_uint64_shift_right(v___x_481_, v___x_480_);
v___x_483_ = lean_unbox_uint64(v___x_479_);
lean_dec_ref(v___x_479_);
v_fold_484_ = lean_uint64_xor(v___x_483_, v___x_482_);
v___x_485_ = 16ULL;
v___x_486_ = lean_uint64_shift_right(v_fold_484_, v___x_485_);
v___x_487_ = lean_uint64_xor(v_fold_484_, v___x_486_);
v___x_488_ = lean_uint64_to_usize(v___x_487_);
v___x_489_ = lean_usize_of_nat(v___x_475_);
v___x_490_ = ((size_t)1ULL);
v___x_491_ = lean_usize_sub(v___x_489_, v___x_490_);
v___x_492_ = lean_usize_land(v___x_488_, v___x_491_);
v_bkt_493_ = lean_array_uget_borrowed(v_buckets_473_, v___x_492_);
lean_inc(v_bkt_493_);
v___x_494_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(v_inst_466_, v_a_470_, v_bkt_493_);
if (lean_obj_tag(v___x_494_) == 0)
{
lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_517_; 
lean_inc_ref(v_buckets_473_);
lean_inc(v_size_472_);
v_isSharedCheck_517_ = !lean_is_exclusive(v_m_469_);
if (v_isSharedCheck_517_ == 0)
{
lean_object* v_unused_518_; lean_object* v_unused_519_; 
v_unused_518_ = lean_ctor_get(v_m_469_, 1);
lean_dec(v_unused_518_);
v_unused_519_ = lean_ctor_get(v_m_469_, 0);
lean_dec(v_unused_519_);
v___x_496_ = v_m_469_;
v_isShared_497_ = v_isSharedCheck_517_;
goto v_resetjp_495_;
}
else
{
lean_dec(v_m_469_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_517_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_498_; lean_object* v_size_x27_499_; lean_object* v___x_500_; lean_object* v_buckets_x27_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_498_ = lean_unsigned_to_nat(1u);
v_size_x27_499_ = lean_nat_add(v_size_472_, v___x_498_);
lean_dec(v_size_472_);
lean_inc(v_bkt_493_);
v___x_500_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_500_, 0, v_a_470_);
lean_ctor_set(v___x_500_, 1, v_b_471_);
lean_ctor_set(v___x_500_, 2, v_bkt_493_);
v_buckets_x27_501_ = lean_array_uset(v_buckets_473_, v___x_492_, v___x_500_);
v___x_502_ = lean_unsigned_to_nat(4u);
v___x_503_ = lean_nat_mul(v_size_x27_499_, v___x_502_);
v___x_504_ = lean_unsigned_to_nat(3u);
v___x_505_ = lean_nat_div(v___x_503_, v___x_504_);
lean_dec(v___x_503_);
v___x_506_ = lean_array_get_size(v_buckets_x27_501_);
v___x_507_ = lean_nat_dec_le(v___x_505_, v___x_506_);
lean_dec(v___x_505_);
if (v___x_507_ == 0)
{
lean_object* v_val_508_; lean_object* v___x_510_; 
v_val_508_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_467_, v_buckets_x27_501_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 1, v_val_508_);
lean_ctor_set(v___x_496_, 0, v_size_x27_499_);
v___x_510_ = v___x_496_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_size_x27_499_);
lean_ctor_set(v_reuseFailAlloc_512_, 1, v_val_508_);
v___x_510_ = v_reuseFailAlloc_512_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
lean_object* v___x_511_; 
v___x_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_511_, 0, v___x_494_);
lean_ctor_set(v___x_511_, 1, v___x_510_);
return v___x_511_;
}
}
else
{
lean_object* v___x_514_; 
lean_dec_ref(v_inst_467_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 1, v_buckets_x27_501_);
lean_ctor_set(v___x_496_, 0, v_size_x27_499_);
v___x_514_ = v___x_496_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_size_x27_499_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v_buckets_x27_501_);
v___x_514_ = v_reuseFailAlloc_516_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
lean_object* v___x_515_; 
v___x_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_515_, 0, v___x_494_);
lean_ctor_set(v___x_515_, 1, v___x_514_);
return v___x_515_;
}
}
}
}
else
{
lean_object* v___x_520_; 
lean_dec(v_b_471_);
lean_dec(v_a_470_);
lean_dec_ref(v_inst_467_);
v___x_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_494_);
lean_ctor_set(v___x_520_, 1, v_m_469_);
return v___x_520_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_containsThenInsertIfNew___redArg(lean_object* v_inst_521_, lean_object* v_inst_522_, lean_object* v_m_523_, lean_object* v_a_524_, lean_object* v_b_525_){
_start:
{
lean_object* v_size_526_; lean_object* v_buckets_527_; lean_object* v___x_528_; lean_object* v___x_529_; uint8_t v___x_530_; 
v_size_526_ = lean_ctor_get(v_m_523_, 0);
v_buckets_527_ = lean_ctor_get(v_m_523_, 1);
v___x_528_ = lean_unsigned_to_nat(0u);
v___x_529_ = lean_array_get_size(v_buckets_527_);
v___x_530_ = lean_nat_dec_lt(v___x_528_, v___x_529_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; lean_object* v___x_532_; 
lean_dec(v_b_525_);
lean_dec(v_a_524_);
lean_dec_ref(v_inst_522_);
lean_dec_ref(v_inst_521_);
v___x_531_ = lean_box(v___x_530_);
v___x_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
lean_ctor_set(v___x_532_, 1, v_m_523_);
return v___x_532_;
}
else
{
lean_object* v___x_533_; uint64_t v___x_534_; uint64_t v___x_535_; uint64_t v___x_536_; uint64_t v___x_537_; uint64_t v_fold_538_; uint64_t v___x_539_; uint64_t v___x_540_; uint64_t v___x_541_; size_t v___x_542_; size_t v___x_543_; size_t v___x_544_; size_t v___x_545_; size_t v___x_546_; lean_object* v_bkt_547_; uint8_t v___x_548_; 
lean_inc_ref(v_inst_522_);
lean_inc_n(v_a_524_, 2);
v___x_533_ = lean_apply_1(v_inst_522_, v_a_524_);
v___x_534_ = 32ULL;
v___x_535_ = lean_unbox_uint64(v___x_533_);
v___x_536_ = lean_uint64_shift_right(v___x_535_, v___x_534_);
v___x_537_ = lean_unbox_uint64(v___x_533_);
lean_dec_ref(v___x_533_);
v_fold_538_ = lean_uint64_xor(v___x_537_, v___x_536_);
v___x_539_ = 16ULL;
v___x_540_ = lean_uint64_shift_right(v_fold_538_, v___x_539_);
v___x_541_ = lean_uint64_xor(v_fold_538_, v___x_540_);
v___x_542_ = lean_uint64_to_usize(v___x_541_);
v___x_543_ = lean_usize_of_nat(v___x_529_);
v___x_544_ = ((size_t)1ULL);
v___x_545_ = lean_usize_sub(v___x_543_, v___x_544_);
v___x_546_ = lean_usize_land(v___x_542_, v___x_545_);
v_bkt_547_ = lean_array_uget_borrowed(v_buckets_527_, v___x_546_);
lean_inc(v_bkt_547_);
v___x_548_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_521_, v_a_524_, v_bkt_547_);
if (v___x_548_ == 0)
{
lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_573_; 
lean_inc_ref(v_buckets_527_);
lean_inc(v_size_526_);
v_isSharedCheck_573_ = !lean_is_exclusive(v_m_523_);
if (v_isSharedCheck_573_ == 0)
{
lean_object* v_unused_574_; lean_object* v_unused_575_; 
v_unused_574_ = lean_ctor_get(v_m_523_, 1);
lean_dec(v_unused_574_);
v_unused_575_ = lean_ctor_get(v_m_523_, 0);
lean_dec(v_unused_575_);
v___x_550_ = v_m_523_;
v_isShared_551_ = v_isSharedCheck_573_;
goto v_resetjp_549_;
}
else
{
lean_dec(v_m_523_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_573_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_552_; lean_object* v_size_x27_553_; lean_object* v___x_554_; lean_object* v_buckets_x27_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; uint8_t v___x_561_; 
v___x_552_ = lean_unsigned_to_nat(1u);
v_size_x27_553_ = lean_nat_add(v_size_526_, v___x_552_);
lean_dec(v_size_526_);
lean_inc(v_bkt_547_);
v___x_554_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_554_, 0, v_a_524_);
lean_ctor_set(v___x_554_, 1, v_b_525_);
lean_ctor_set(v___x_554_, 2, v_bkt_547_);
v_buckets_x27_555_ = lean_array_uset(v_buckets_527_, v___x_546_, v___x_554_);
v___x_556_ = lean_unsigned_to_nat(4u);
v___x_557_ = lean_nat_mul(v_size_x27_553_, v___x_556_);
v___x_558_ = lean_unsigned_to_nat(3u);
v___x_559_ = lean_nat_div(v___x_557_, v___x_558_);
lean_dec(v___x_557_);
v___x_560_ = lean_array_get_size(v_buckets_x27_555_);
v___x_561_ = lean_nat_dec_le(v___x_559_, v___x_560_);
lean_dec(v___x_559_);
if (v___x_561_ == 0)
{
lean_object* v_val_562_; lean_object* v___x_564_; 
v_val_562_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_522_, v_buckets_x27_555_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 1, v_val_562_);
lean_ctor_set(v___x_550_, 0, v_size_x27_553_);
v___x_564_ = v___x_550_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_size_x27_553_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v_val_562_);
v___x_564_ = v_reuseFailAlloc_567_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = lean_box(v___x_548_);
v___x_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
lean_ctor_set(v___x_566_, 1, v___x_564_);
return v___x_566_;
}
}
else
{
lean_object* v___x_569_; 
lean_dec_ref(v_inst_522_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 1, v_buckets_x27_555_);
lean_ctor_set(v___x_550_, 0, v_size_x27_553_);
v___x_569_ = v___x_550_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_size_x27_553_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_buckets_x27_555_);
v___x_569_ = v_reuseFailAlloc_572_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = lean_box(v___x_548_);
v___x_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
lean_ctor_set(v___x_571_, 1, v___x_569_);
return v___x_571_;
}
}
}
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; 
lean_dec(v_b_525_);
lean_dec(v_a_524_);
lean_dec_ref(v_inst_522_);
v___x_576_ = lean_box(v___x_548_);
v___x_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
lean_ctor_set(v___x_577_, 1, v_m_523_);
return v___x_577_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_containsThenInsertIfNew(lean_object* v_00_u03b1_578_, lean_object* v_00_u03b2_579_, lean_object* v_inst_580_, lean_object* v_inst_581_, lean_object* v_m_582_, lean_object* v_a_583_, lean_object* v_b_584_){
_start:
{
lean_object* v_size_585_; lean_object* v_buckets_586_; lean_object* v___x_587_; lean_object* v___x_588_; uint8_t v___x_589_; 
v_size_585_ = lean_ctor_get(v_m_582_, 0);
v_buckets_586_ = lean_ctor_get(v_m_582_, 1);
v___x_587_ = lean_unsigned_to_nat(0u);
v___x_588_ = lean_array_get_size(v_buckets_586_);
v___x_589_ = lean_nat_dec_lt(v___x_587_, v___x_588_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; lean_object* v___x_591_; 
lean_dec(v_b_584_);
lean_dec(v_a_583_);
lean_dec_ref(v_inst_581_);
lean_dec_ref(v_inst_580_);
v___x_590_ = lean_box(v___x_589_);
v___x_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_590_);
lean_ctor_set(v___x_591_, 1, v_m_582_);
return v___x_591_;
}
else
{
lean_object* v___x_592_; uint64_t v___x_593_; uint64_t v___x_594_; uint64_t v___x_595_; uint64_t v___x_596_; uint64_t v_fold_597_; uint64_t v___x_598_; uint64_t v___x_599_; uint64_t v___x_600_; size_t v___x_601_; size_t v___x_602_; size_t v___x_603_; size_t v___x_604_; size_t v___x_605_; lean_object* v_bkt_606_; uint8_t v___x_607_; 
lean_inc_ref(v_inst_581_);
lean_inc_n(v_a_583_, 2);
v___x_592_ = lean_apply_1(v_inst_581_, v_a_583_);
v___x_593_ = 32ULL;
v___x_594_ = lean_unbox_uint64(v___x_592_);
v___x_595_ = lean_uint64_shift_right(v___x_594_, v___x_593_);
v___x_596_ = lean_unbox_uint64(v___x_592_);
lean_dec_ref(v___x_592_);
v_fold_597_ = lean_uint64_xor(v___x_596_, v___x_595_);
v___x_598_ = 16ULL;
v___x_599_ = lean_uint64_shift_right(v_fold_597_, v___x_598_);
v___x_600_ = lean_uint64_xor(v_fold_597_, v___x_599_);
v___x_601_ = lean_uint64_to_usize(v___x_600_);
v___x_602_ = lean_usize_of_nat(v___x_588_);
v___x_603_ = ((size_t)1ULL);
v___x_604_ = lean_usize_sub(v___x_602_, v___x_603_);
v___x_605_ = lean_usize_land(v___x_601_, v___x_604_);
v_bkt_606_ = lean_array_uget_borrowed(v_buckets_586_, v___x_605_);
lean_inc(v_bkt_606_);
v___x_607_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_580_, v_a_583_, v_bkt_606_);
if (v___x_607_ == 0)
{
lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_632_; 
lean_inc_ref(v_buckets_586_);
lean_inc(v_size_585_);
v_isSharedCheck_632_ = !lean_is_exclusive(v_m_582_);
if (v_isSharedCheck_632_ == 0)
{
lean_object* v_unused_633_; lean_object* v_unused_634_; 
v_unused_633_ = lean_ctor_get(v_m_582_, 1);
lean_dec(v_unused_633_);
v_unused_634_ = lean_ctor_get(v_m_582_, 0);
lean_dec(v_unused_634_);
v___x_609_ = v_m_582_;
v_isShared_610_ = v_isSharedCheck_632_;
goto v_resetjp_608_;
}
else
{
lean_dec(v_m_582_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_632_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; lean_object* v_size_x27_612_; lean_object* v___x_613_; lean_object* v_buckets_x27_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_611_ = lean_unsigned_to_nat(1u);
v_size_x27_612_ = lean_nat_add(v_size_585_, v___x_611_);
lean_dec(v_size_585_);
lean_inc(v_bkt_606_);
v___x_613_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_613_, 0, v_a_583_);
lean_ctor_set(v___x_613_, 1, v_b_584_);
lean_ctor_set(v___x_613_, 2, v_bkt_606_);
v_buckets_x27_614_ = lean_array_uset(v_buckets_586_, v___x_605_, v___x_613_);
v___x_615_ = lean_unsigned_to_nat(4u);
v___x_616_ = lean_nat_mul(v_size_x27_612_, v___x_615_);
v___x_617_ = lean_unsigned_to_nat(3u);
v___x_618_ = lean_nat_div(v___x_616_, v___x_617_);
lean_dec(v___x_616_);
v___x_619_ = lean_array_get_size(v_buckets_x27_614_);
v___x_620_ = lean_nat_dec_le(v___x_618_, v___x_619_);
lean_dec(v___x_618_);
if (v___x_620_ == 0)
{
lean_object* v_val_621_; lean_object* v___x_623_; 
v_val_621_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_581_, v_buckets_x27_614_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 1, v_val_621_);
lean_ctor_set(v___x_609_, 0, v_size_x27_612_);
v___x_623_ = v___x_609_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_size_x27_612_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_val_621_);
v___x_623_ = v_reuseFailAlloc_626_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = lean_box(v___x_607_);
v___x_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
lean_ctor_set(v___x_625_, 1, v___x_623_);
return v___x_625_;
}
}
else
{
lean_object* v___x_628_; 
lean_dec_ref(v_inst_581_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 1, v_buckets_x27_614_);
lean_ctor_set(v___x_609_, 0, v_size_x27_612_);
v___x_628_ = v___x_609_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_size_x27_612_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v_buckets_x27_614_);
v___x_628_ = v_reuseFailAlloc_631_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = lean_box(v___x_607_);
v___x_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
lean_ctor_set(v___x_630_, 1, v___x_628_);
return v___x_630_;
}
}
}
}
else
{
lean_object* v___x_635_; lean_object* v___x_636_; 
lean_dec(v_b_584_);
lean_dec(v_a_583_);
lean_dec_ref(v_inst_581_);
v___x_635_ = lean_box(v___x_607_);
v___x_636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
lean_ctor_set(v___x_636_, 1, v_m_582_);
return v___x_636_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x3f___redArg(lean_object* v_inst_637_, lean_object* v_inst_638_, lean_object* v_m_639_, lean_object* v_a_640_){
_start:
{
lean_object* v_buckets_641_; lean_object* v___x_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
v_buckets_641_ = lean_ctor_get(v_m_639_, 1);
v___x_642_ = lean_unsigned_to_nat(0u);
v___x_643_ = lean_array_get_size(v_buckets_641_);
v___x_644_ = lean_nat_dec_lt(v___x_642_, v___x_643_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; 
lean_dec(v_a_640_);
lean_dec_ref(v_inst_638_);
lean_dec_ref(v_inst_637_);
v___x_645_ = lean_box(0);
return v___x_645_;
}
else
{
lean_object* v___x_646_; 
v___x_646_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(v_inst_637_, v_inst_638_, v_m_639_, v_a_640_);
return v___x_646_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x3f___redArg___boxed(lean_object* v_inst_647_, lean_object* v_inst_648_, lean_object* v_m_649_, lean_object* v_a_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Std_DHashMap_Raw_get_x3f___redArg(v_inst_647_, v_inst_648_, v_m_649_, v_a_650_);
lean_dec_ref(v_m_649_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x3f(lean_object* v_00_u03b1_652_, lean_object* v_00_u03b2_653_, lean_object* v_inst_654_, lean_object* v_inst_655_, lean_object* v_inst_656_, lean_object* v_m_657_, lean_object* v_a_658_){
_start:
{
lean_object* v_buckets_659_; lean_object* v___x_660_; lean_object* v___x_661_; uint8_t v___x_662_; 
v_buckets_659_ = lean_ctor_get(v_m_657_, 1);
v___x_660_ = lean_unsigned_to_nat(0u);
v___x_661_ = lean_array_get_size(v_buckets_659_);
v___x_662_ = lean_nat_dec_lt(v___x_660_, v___x_661_);
if (v___x_662_ == 0)
{
lean_object* v___x_663_; 
lean_dec(v_a_658_);
lean_dec_ref(v_inst_656_);
lean_dec_ref(v_inst_654_);
v___x_663_ = lean_box(0);
return v___x_663_;
}
else
{
lean_object* v___x_664_; 
v___x_664_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(v_inst_654_, v_inst_656_, v_m_657_, v_a_658_);
return v___x_664_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x3f___boxed(lean_object* v_00_u03b1_665_, lean_object* v_00_u03b2_666_, lean_object* v_inst_667_, lean_object* v_inst_668_, lean_object* v_inst_669_, lean_object* v_m_670_, lean_object* v_a_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Std_DHashMap_Raw_get_x3f(v_00_u03b1_665_, v_00_u03b2_666_, v_inst_667_, v_inst_668_, v_inst_669_, v_m_670_, v_a_671_);
lean_dec_ref(v_m_670_);
return v_res_672_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_contains___redArg(lean_object* v_inst_673_, lean_object* v_inst_674_, lean_object* v_m_675_, lean_object* v_a_676_){
_start:
{
lean_object* v_buckets_677_; lean_object* v___x_678_; lean_object* v___x_679_; uint8_t v___x_680_; 
v_buckets_677_ = lean_ctor_get(v_m_675_, 1);
v___x_678_ = lean_unsigned_to_nat(0u);
v___x_679_ = lean_array_get_size(v_buckets_677_);
v___x_680_ = lean_nat_dec_lt(v___x_678_, v___x_679_);
if (v___x_680_ == 0)
{
lean_dec(v_a_676_);
lean_dec_ref(v_inst_674_);
lean_dec_ref(v_inst_673_);
return v___x_680_;
}
else
{
uint8_t v___x_681_; 
v___x_681_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_673_, v_inst_674_, v_m_675_, v_a_676_);
return v___x_681_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_contains___redArg___boxed(lean_object* v_inst_682_, lean_object* v_inst_683_, lean_object* v_m_684_, lean_object* v_a_685_){
_start:
{
uint8_t v_res_686_; lean_object* v_r_687_; 
v_res_686_ = l_Std_DHashMap_Raw_contains___redArg(v_inst_682_, v_inst_683_, v_m_684_, v_a_685_);
lean_dec_ref(v_m_684_);
v_r_687_ = lean_box(v_res_686_);
return v_r_687_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_contains(lean_object* v_00_u03b1_688_, lean_object* v_00_u03b2_689_, lean_object* v_inst_690_, lean_object* v_inst_691_, lean_object* v_m_692_, lean_object* v_a_693_){
_start:
{
lean_object* v_buckets_694_; lean_object* v___x_695_; lean_object* v___x_696_; uint8_t v___x_697_; 
v_buckets_694_ = lean_ctor_get(v_m_692_, 1);
v___x_695_ = lean_unsigned_to_nat(0u);
v___x_696_ = lean_array_get_size(v_buckets_694_);
v___x_697_ = lean_nat_dec_lt(v___x_695_, v___x_696_);
if (v___x_697_ == 0)
{
lean_dec(v_a_693_);
lean_dec_ref(v_inst_691_);
lean_dec_ref(v_inst_690_);
return v___x_697_;
}
else
{
uint8_t v___x_698_; 
v___x_698_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_690_, v_inst_691_, v_m_692_, v_a_693_);
return v___x_698_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_contains___boxed(lean_object* v_00_u03b1_699_, lean_object* v_00_u03b2_700_, lean_object* v_inst_701_, lean_object* v_inst_702_, lean_object* v_m_703_, lean_object* v_a_704_){
_start:
{
uint8_t v_res_705_; lean_object* v_r_706_; 
v_res_705_ = l_Std_DHashMap_Raw_contains(v_00_u03b1_699_, v_00_u03b2_700_, v_inst_701_, v_inst_702_, v_m_703_, v_a_704_);
lean_dec_ref(v_m_703_);
v_r_706_ = lean_box(v_res_705_);
return v_r_706_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instMembershipOfBEqOfHashable(lean_object* v_00_u03b1_707_, lean_object* v_00_u03b2_708_, lean_object* v_inst_709_, lean_object* v_inst_710_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = lean_box(0);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instMembershipOfBEqOfHashable___boxed(lean_object* v_00_u03b1_712_, lean_object* v_00_u03b2_713_, lean_object* v_inst_714_, lean_object* v_inst_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Std_DHashMap_Raw_instMembershipOfBEqOfHashable(v_00_u03b1_712_, v_00_u03b2_713_, v_inst_714_, v_inst_715_);
lean_dec_ref(v_inst_715_);
lean_dec_ref(v_inst_714_);
return v_res_716_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_instDecidableMem___redArg(lean_object* v_inst_717_, lean_object* v_inst_718_, lean_object* v_m_719_, lean_object* v_a_720_){
_start:
{
lean_object* v_buckets_721_; lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v_buckets_721_ = lean_ctor_get(v_m_719_, 1);
v___x_722_ = lean_unsigned_to_nat(0u);
v___x_723_ = lean_array_get_size(v_buckets_721_);
v___x_724_ = lean_nat_dec_lt(v___x_722_, v___x_723_);
if (v___x_724_ == 0)
{
lean_dec(v_a_720_);
lean_dec_ref(v_inst_718_);
lean_dec_ref(v_inst_717_);
return v___x_724_;
}
else
{
uint8_t v___x_725_; 
v___x_725_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_717_, v_inst_718_, v_m_719_, v_a_720_);
return v___x_725_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instDecidableMem___redArg___boxed(lean_object* v_inst_726_, lean_object* v_inst_727_, lean_object* v_m_728_, lean_object* v_a_729_){
_start:
{
uint8_t v_res_730_; lean_object* v_r_731_; 
v_res_730_ = l_Std_DHashMap_Raw_instDecidableMem___redArg(v_inst_726_, v_inst_727_, v_m_728_, v_a_729_);
lean_dec_ref(v_m_728_);
v_r_731_ = lean_box(v_res_730_);
return v_r_731_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_instDecidableMem(lean_object* v_00_u03b1_732_, lean_object* v_00_u03b2_733_, lean_object* v_inst_734_, lean_object* v_inst_735_, lean_object* v_m_736_, lean_object* v_a_737_){
_start:
{
uint8_t v___x_738_; 
v___x_738_ = l_Std_DHashMap_Raw_instDecidableMem___redArg(v_inst_734_, v_inst_735_, v_m_736_, v_a_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instDecidableMem___boxed(lean_object* v_00_u03b1_739_, lean_object* v_00_u03b2_740_, lean_object* v_inst_741_, lean_object* v_inst_742_, lean_object* v_m_743_, lean_object* v_a_744_){
_start:
{
uint8_t v_res_745_; lean_object* v_r_746_; 
v_res_745_ = l_Std_DHashMap_Raw_instDecidableMem(v_00_u03b1_739_, v_00_u03b2_740_, v_inst_741_, v_inst_742_, v_m_743_, v_a_744_);
lean_dec_ref(v_m_743_);
v_r_746_ = lean_box(v_res_745_);
return v_r_746_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get___redArg(lean_object* v_inst_747_, lean_object* v_inst_748_, lean_object* v_m_749_, lean_object* v_a_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Std_DHashMap_Internal_Raw_u2080_get___redArg(v_inst_747_, v_inst_748_, v_m_749_, v_a_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get___redArg___boxed(lean_object* v_inst_752_, lean_object* v_inst_753_, lean_object* v_m_754_, lean_object* v_a_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Std_DHashMap_Raw_get___redArg(v_inst_752_, v_inst_753_, v_m_754_, v_a_755_);
lean_dec_ref(v_m_754_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get(lean_object* v_00_u03b1_757_, lean_object* v_00_u03b2_758_, lean_object* v_inst_759_, lean_object* v_inst_760_, lean_object* v_inst_761_, lean_object* v_m_762_, lean_object* v_a_763_, lean_object* v_h_764_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_Std_DHashMap_Internal_Raw_u2080_get___redArg(v_inst_759_, v_inst_760_, v_m_762_, v_a_763_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get___boxed(lean_object* v_00_u03b1_766_, lean_object* v_00_u03b2_767_, lean_object* v_inst_768_, lean_object* v_inst_769_, lean_object* v_inst_770_, lean_object* v_m_771_, lean_object* v_a_772_, lean_object* v_h_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Std_DHashMap_Raw_get(v_00_u03b1_766_, v_00_u03b2_767_, v_inst_768_, v_inst_769_, v_inst_770_, v_m_771_, v_a_772_, v_h_773_);
lean_dec_ref(v_m_771_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getD___redArg(lean_object* v_inst_775_, lean_object* v_inst_776_, lean_object* v_m_777_, lean_object* v_a_778_, lean_object* v_fallback_779_){
_start:
{
lean_object* v_buckets_780_; lean_object* v___x_781_; lean_object* v___x_782_; uint8_t v___x_783_; 
v_buckets_780_ = lean_ctor_get(v_m_777_, 1);
v___x_781_ = lean_unsigned_to_nat(0u);
v___x_782_ = lean_array_get_size(v_buckets_780_);
v___x_783_ = lean_nat_dec_lt(v___x_781_, v___x_782_);
if (v___x_783_ == 0)
{
lean_dec(v_a_778_);
lean_dec_ref(v_inst_776_);
lean_dec_ref(v_inst_775_);
lean_inc(v_fallback_779_);
return v_fallback_779_;
}
else
{
lean_object* v___x_784_; 
v___x_784_ = l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(v_inst_775_, v_inst_776_, v_m_777_, v_a_778_, v_fallback_779_);
return v___x_784_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getD___redArg___boxed(lean_object* v_inst_785_, lean_object* v_inst_786_, lean_object* v_m_787_, lean_object* v_a_788_, lean_object* v_fallback_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Std_DHashMap_Raw_getD___redArg(v_inst_785_, v_inst_786_, v_m_787_, v_a_788_, v_fallback_789_);
lean_dec(v_fallback_789_);
lean_dec_ref(v_m_787_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getD(lean_object* v_00_u03b1_791_, lean_object* v_00_u03b2_792_, lean_object* v_inst_793_, lean_object* v_inst_794_, lean_object* v_inst_795_, lean_object* v_m_796_, lean_object* v_a_797_, lean_object* v_fallback_798_){
_start:
{
lean_object* v_buckets_799_; lean_object* v___x_800_; lean_object* v___x_801_; uint8_t v___x_802_; 
v_buckets_799_ = lean_ctor_get(v_m_796_, 1);
v___x_800_ = lean_unsigned_to_nat(0u);
v___x_801_ = lean_array_get_size(v_buckets_799_);
v___x_802_ = lean_nat_dec_lt(v___x_800_, v___x_801_);
if (v___x_802_ == 0)
{
lean_dec(v_a_797_);
lean_dec_ref(v_inst_794_);
lean_dec_ref(v_inst_793_);
lean_inc(v_fallback_798_);
return v_fallback_798_;
}
else
{
lean_object* v___x_803_; 
v___x_803_ = l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(v_inst_793_, v_inst_794_, v_m_796_, v_a_797_, v_fallback_798_);
return v___x_803_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getD___boxed(lean_object* v_00_u03b1_804_, lean_object* v_00_u03b2_805_, lean_object* v_inst_806_, lean_object* v_inst_807_, lean_object* v_inst_808_, lean_object* v_m_809_, lean_object* v_a_810_, lean_object* v_fallback_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Std_DHashMap_Raw_getD(v_00_u03b1_804_, v_00_u03b2_805_, v_inst_806_, v_inst_807_, v_inst_808_, v_m_809_, v_a_810_, v_fallback_811_);
lean_dec(v_fallback_811_);
lean_dec_ref(v_m_809_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x21___redArg(lean_object* v_inst_813_, lean_object* v_inst_814_, lean_object* v_m_815_, lean_object* v_a_816_, lean_object* v_inst_817_){
_start:
{
lean_object* v_buckets_818_; lean_object* v___x_819_; lean_object* v___x_820_; uint8_t v___x_821_; 
v_buckets_818_ = lean_ctor_get(v_m_815_, 1);
v___x_819_ = lean_unsigned_to_nat(0u);
v___x_820_ = lean_array_get_size(v_buckets_818_);
v___x_821_ = lean_nat_dec_lt(v___x_819_, v___x_820_);
if (v___x_821_ == 0)
{
lean_dec(v_a_816_);
lean_dec_ref(v_inst_814_);
lean_dec_ref(v_inst_813_);
lean_inc(v_inst_817_);
return v_inst_817_;
}
else
{
lean_object* v___x_822_; 
v___x_822_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(v_inst_813_, v_inst_814_, v_m_815_, v_a_816_, v_inst_817_);
return v___x_822_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x21___redArg___boxed(lean_object* v_inst_823_, lean_object* v_inst_824_, lean_object* v_m_825_, lean_object* v_a_826_, lean_object* v_inst_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_Std_DHashMap_Raw_get_x21___redArg(v_inst_823_, v_inst_824_, v_m_825_, v_a_826_, v_inst_827_);
lean_dec(v_inst_827_);
lean_dec_ref(v_m_825_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x21(lean_object* v_00_u03b1_829_, lean_object* v_00_u03b2_830_, lean_object* v_inst_831_, lean_object* v_inst_832_, lean_object* v_inst_833_, lean_object* v_m_834_, lean_object* v_a_835_, lean_object* v_inst_836_){
_start:
{
lean_object* v_buckets_837_; lean_object* v___x_838_; lean_object* v___x_839_; uint8_t v___x_840_; 
v_buckets_837_ = lean_ctor_get(v_m_834_, 1);
v___x_838_ = lean_unsigned_to_nat(0u);
v___x_839_ = lean_array_get_size(v_buckets_837_);
v___x_840_ = lean_nat_dec_lt(v___x_838_, v___x_839_);
if (v___x_840_ == 0)
{
lean_dec(v_a_835_);
lean_dec_ref(v_inst_832_);
lean_dec_ref(v_inst_831_);
lean_inc(v_inst_836_);
return v_inst_836_;
}
else
{
lean_object* v___x_841_; 
v___x_841_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(v_inst_831_, v_inst_832_, v_m_834_, v_a_835_, v_inst_836_);
return v___x_841_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x21___boxed(lean_object* v_00_u03b1_842_, lean_object* v_00_u03b2_843_, lean_object* v_inst_844_, lean_object* v_inst_845_, lean_object* v_inst_846_, lean_object* v_m_847_, lean_object* v_a_848_, lean_object* v_inst_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Std_DHashMap_Raw_get_x21(v_00_u03b1_842_, v_00_u03b2_843_, v_inst_844_, v_inst_845_, v_inst_846_, v_m_847_, v_a_848_, v_inst_849_);
lean_dec(v_inst_849_);
lean_dec_ref(v_m_847_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_erase___redArg(lean_object* v_inst_851_, lean_object* v_inst_852_, lean_object* v_m_853_, lean_object* v_a_854_){
_start:
{
lean_object* v_buckets_855_; lean_object* v___x_856_; lean_object* v___x_857_; uint8_t v___x_858_; 
v_buckets_855_ = lean_ctor_get(v_m_853_, 1);
v___x_856_ = lean_unsigned_to_nat(0u);
v___x_857_ = lean_array_get_size(v_buckets_855_);
v___x_858_ = lean_nat_dec_lt(v___x_856_, v___x_857_);
if (v___x_858_ == 0)
{
lean_dec(v_a_854_);
lean_dec_ref(v_inst_852_);
lean_dec_ref(v_inst_851_);
return v_m_853_;
}
else
{
lean_object* v___x_859_; 
v___x_859_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_851_, v_inst_852_, v_m_853_, v_a_854_);
return v___x_859_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_erase(lean_object* v_00_u03b1_860_, lean_object* v_00_u03b2_861_, lean_object* v_inst_862_, lean_object* v_inst_863_, lean_object* v_m_864_, lean_object* v_a_865_){
_start:
{
lean_object* v_buckets_866_; lean_object* v___x_867_; lean_object* v___x_868_; uint8_t v___x_869_; 
v_buckets_866_ = lean_ctor_get(v_m_864_, 1);
v___x_867_ = lean_unsigned_to_nat(0u);
v___x_868_ = lean_array_get_size(v_buckets_866_);
v___x_869_ = lean_nat_dec_lt(v___x_867_, v___x_868_);
if (v___x_869_ == 0)
{
lean_dec(v_a_865_);
lean_dec_ref(v_inst_863_);
lean_dec_ref(v_inst_862_);
return v_m_864_;
}
else
{
lean_object* v___x_870_; 
v___x_870_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_862_, v_inst_863_, v_m_864_, v_a_865_);
return v___x_870_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x3f___redArg(lean_object* v_inst_871_, lean_object* v_inst_872_, lean_object* v_m_873_, lean_object* v_a_874_){
_start:
{
lean_object* v_buckets_875_; lean_object* v___x_876_; lean_object* v___x_877_; uint8_t v___x_878_; 
v_buckets_875_ = lean_ctor_get(v_m_873_, 1);
v___x_876_ = lean_unsigned_to_nat(0u);
v___x_877_ = lean_array_get_size(v_buckets_875_);
v___x_878_ = lean_nat_dec_lt(v___x_876_, v___x_877_);
if (v___x_878_ == 0)
{
lean_object* v___x_879_; 
lean_dec(v_a_874_);
lean_dec_ref(v_inst_872_);
lean_dec_ref(v_inst_871_);
v___x_879_ = lean_box(0);
return v___x_879_;
}
else
{
lean_object* v___x_880_; 
v___x_880_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_871_, v_inst_872_, v_m_873_, v_a_874_);
return v___x_880_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x3f___redArg___boxed(lean_object* v_inst_881_, lean_object* v_inst_882_, lean_object* v_m_883_, lean_object* v_a_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Std_DHashMap_Raw_Const_get_x3f___redArg(v_inst_881_, v_inst_882_, v_m_883_, v_a_884_);
lean_dec_ref(v_m_883_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x3f(lean_object* v_00_u03b1_886_, lean_object* v_00_u03b2_887_, lean_object* v_inst_888_, lean_object* v_inst_889_, lean_object* v_m_890_, lean_object* v_a_891_){
_start:
{
lean_object* v_buckets_892_; lean_object* v___x_893_; lean_object* v___x_894_; uint8_t v___x_895_; 
v_buckets_892_ = lean_ctor_get(v_m_890_, 1);
v___x_893_ = lean_unsigned_to_nat(0u);
v___x_894_ = lean_array_get_size(v_buckets_892_);
v___x_895_ = lean_nat_dec_lt(v___x_893_, v___x_894_);
if (v___x_895_ == 0)
{
lean_object* v___x_896_; 
lean_dec(v_a_891_);
lean_dec_ref(v_inst_889_);
lean_dec_ref(v_inst_888_);
v___x_896_ = lean_box(0);
return v___x_896_;
}
else
{
lean_object* v___x_897_; 
v___x_897_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_888_, v_inst_889_, v_m_890_, v_a_891_);
return v___x_897_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x3f___boxed(lean_object* v_00_u03b1_898_, lean_object* v_00_u03b2_899_, lean_object* v_inst_900_, lean_object* v_inst_901_, lean_object* v_m_902_, lean_object* v_a_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Std_DHashMap_Raw_Const_get_x3f(v_00_u03b1_898_, v_00_u03b2_899_, v_inst_900_, v_inst_901_, v_m_902_, v_a_903_);
lean_dec_ref(v_m_902_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get___redArg(lean_object* v_inst_905_, lean_object* v_inst_906_, lean_object* v_m_907_, lean_object* v_a_908_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_905_, v_inst_906_, v_m_907_, v_a_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get___redArg___boxed(lean_object* v_inst_910_, lean_object* v_inst_911_, lean_object* v_m_912_, lean_object* v_a_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Std_DHashMap_Raw_Const_get___redArg(v_inst_910_, v_inst_911_, v_m_912_, v_a_913_);
lean_dec_ref(v_m_912_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get(lean_object* v_00_u03b1_915_, lean_object* v_00_u03b2_916_, lean_object* v_inst_917_, lean_object* v_inst_918_, lean_object* v_m_919_, lean_object* v_a_920_, lean_object* v_h_921_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_917_, v_inst_918_, v_m_919_, v_a_920_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get___boxed(lean_object* v_00_u03b1_923_, lean_object* v_00_u03b2_924_, lean_object* v_inst_925_, lean_object* v_inst_926_, lean_object* v_m_927_, lean_object* v_a_928_, lean_object* v_h_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l_Std_DHashMap_Raw_Const_get(v_00_u03b1_923_, v_00_u03b2_924_, v_inst_925_, v_inst_926_, v_m_927_, v_a_928_, v_h_929_);
lean_dec_ref(v_m_927_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getD___redArg(lean_object* v_inst_931_, lean_object* v_inst_932_, lean_object* v_m_933_, lean_object* v_a_934_, lean_object* v_fallback_935_){
_start:
{
lean_object* v_buckets_936_; lean_object* v___x_937_; lean_object* v___x_938_; uint8_t v___x_939_; 
v_buckets_936_ = lean_ctor_get(v_m_933_, 1);
v___x_937_ = lean_unsigned_to_nat(0u);
v___x_938_ = lean_array_get_size(v_buckets_936_);
v___x_939_ = lean_nat_dec_lt(v___x_937_, v___x_938_);
if (v___x_939_ == 0)
{
lean_dec(v_a_934_);
lean_dec_ref(v_inst_932_);
lean_dec_ref(v_inst_931_);
lean_inc(v_fallback_935_);
return v_fallback_935_;
}
else
{
lean_object* v___x_940_; 
v___x_940_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_inst_931_, v_inst_932_, v_m_933_, v_a_934_, v_fallback_935_);
return v___x_940_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getD___redArg___boxed(lean_object* v_inst_941_, lean_object* v_inst_942_, lean_object* v_m_943_, lean_object* v_a_944_, lean_object* v_fallback_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l_Std_DHashMap_Raw_Const_getD___redArg(v_inst_941_, v_inst_942_, v_m_943_, v_a_944_, v_fallback_945_);
lean_dec(v_fallback_945_);
lean_dec_ref(v_m_943_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getD(lean_object* v_00_u03b1_947_, lean_object* v_00_u03b2_948_, lean_object* v_inst_949_, lean_object* v_inst_950_, lean_object* v_m_951_, lean_object* v_a_952_, lean_object* v_fallback_953_){
_start:
{
lean_object* v_buckets_954_; lean_object* v___x_955_; lean_object* v___x_956_; uint8_t v___x_957_; 
v_buckets_954_ = lean_ctor_get(v_m_951_, 1);
v___x_955_ = lean_unsigned_to_nat(0u);
v___x_956_ = lean_array_get_size(v_buckets_954_);
v___x_957_ = lean_nat_dec_lt(v___x_955_, v___x_956_);
if (v___x_957_ == 0)
{
lean_dec(v_a_952_);
lean_dec_ref(v_inst_950_);
lean_dec_ref(v_inst_949_);
lean_inc(v_fallback_953_);
return v_fallback_953_;
}
else
{
lean_object* v___x_958_; 
v___x_958_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_inst_949_, v_inst_950_, v_m_951_, v_a_952_, v_fallback_953_);
return v___x_958_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getD___boxed(lean_object* v_00_u03b1_959_, lean_object* v_00_u03b2_960_, lean_object* v_inst_961_, lean_object* v_inst_962_, lean_object* v_m_963_, lean_object* v_a_964_, lean_object* v_fallback_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Std_DHashMap_Raw_Const_getD(v_00_u03b1_959_, v_00_u03b2_960_, v_inst_961_, v_inst_962_, v_m_963_, v_a_964_, v_fallback_965_);
lean_dec(v_fallback_965_);
lean_dec_ref(v_m_963_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x21___redArg(lean_object* v_inst_967_, lean_object* v_inst_968_, lean_object* v_inst_969_, lean_object* v_m_970_, lean_object* v_a_971_){
_start:
{
lean_object* v_buckets_972_; lean_object* v___x_973_; lean_object* v___x_974_; uint8_t v___x_975_; 
v_buckets_972_ = lean_ctor_get(v_m_970_, 1);
v___x_973_ = lean_unsigned_to_nat(0u);
v___x_974_ = lean_array_get_size(v_buckets_972_);
v___x_975_ = lean_nat_dec_lt(v___x_973_, v___x_974_);
if (v___x_975_ == 0)
{
lean_dec(v_a_971_);
lean_dec_ref(v_inst_968_);
lean_dec_ref(v_inst_967_);
lean_inc(v_inst_969_);
return v_inst_969_;
}
else
{
lean_object* v___x_976_; 
v___x_976_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_967_, v_inst_968_, v_inst_969_, v_m_970_, v_a_971_);
return v___x_976_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x21___redArg___boxed(lean_object* v_inst_977_, lean_object* v_inst_978_, lean_object* v_inst_979_, lean_object* v_m_980_, lean_object* v_a_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Std_DHashMap_Raw_Const_get_x21___redArg(v_inst_977_, v_inst_978_, v_inst_979_, v_m_980_, v_a_981_);
lean_dec_ref(v_m_980_);
lean_dec(v_inst_979_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x21(lean_object* v_00_u03b1_983_, lean_object* v_00_u03b2_984_, lean_object* v_inst_985_, lean_object* v_inst_986_, lean_object* v_inst_987_, lean_object* v_m_988_, lean_object* v_a_989_){
_start:
{
lean_object* v_buckets_990_; lean_object* v___x_991_; lean_object* v___x_992_; uint8_t v___x_993_; 
v_buckets_990_ = lean_ctor_get(v_m_988_, 1);
v___x_991_ = lean_unsigned_to_nat(0u);
v___x_992_ = lean_array_get_size(v_buckets_990_);
v___x_993_ = lean_nat_dec_lt(v___x_991_, v___x_992_);
if (v___x_993_ == 0)
{
lean_dec(v_a_989_);
lean_dec_ref(v_inst_986_);
lean_dec_ref(v_inst_985_);
lean_inc(v_inst_987_);
return v_inst_987_;
}
else
{
lean_object* v___x_994_; 
v___x_994_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_985_, v_inst_986_, v_inst_987_, v_m_988_, v_a_989_);
return v___x_994_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x21___boxed(lean_object* v_00_u03b1_995_, lean_object* v_00_u03b2_996_, lean_object* v_inst_997_, lean_object* v_inst_998_, lean_object* v_inst_999_, lean_object* v_m_1000_, lean_object* v_a_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Std_DHashMap_Raw_Const_get_x21(v_00_u03b1_995_, v_00_u03b2_996_, v_inst_997_, v_inst_998_, v_inst_999_, v_m_1000_, v_a_1001_);
lean_dec_ref(v_m_1000_);
lean_dec(v_inst_999_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getThenInsertIfNew_x3f___redArg(lean_object* v_inst_1003_, lean_object* v_inst_1004_, lean_object* v_m_1005_, lean_object* v_a_1006_, lean_object* v_b_1007_){
_start:
{
lean_object* v_size_1008_; lean_object* v_buckets_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; uint8_t v___x_1012_; 
v_size_1008_ = lean_ctor_get(v_m_1005_, 0);
v_buckets_1009_ = lean_ctor_get(v_m_1005_, 1);
v___x_1010_ = lean_unsigned_to_nat(0u);
v___x_1011_ = lean_array_get_size(v_buckets_1009_);
v___x_1012_ = lean_nat_dec_lt(v___x_1010_, v___x_1011_);
if (v___x_1012_ == 0)
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
lean_dec(v_b_1007_);
lean_dec(v_a_1006_);
lean_dec_ref(v_inst_1004_);
lean_dec_ref(v_inst_1003_);
v___x_1013_ = lean_box(0);
v___x_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
lean_ctor_set(v___x_1014_, 1, v_m_1005_);
return v___x_1014_;
}
else
{
lean_object* v___x_1015_; uint64_t v___x_1016_; uint64_t v___x_1017_; uint64_t v___x_1018_; uint64_t v___x_1019_; uint64_t v_fold_1020_; uint64_t v___x_1021_; uint64_t v___x_1022_; uint64_t v___x_1023_; size_t v___x_1024_; size_t v___x_1025_; size_t v___x_1026_; size_t v___x_1027_; size_t v___x_1028_; lean_object* v_bkt_1029_; lean_object* v___x_1030_; 
lean_inc_ref(v_inst_1004_);
lean_inc_n(v_a_1006_, 2);
v___x_1015_ = lean_apply_1(v_inst_1004_, v_a_1006_);
v___x_1016_ = 32ULL;
v___x_1017_ = lean_unbox_uint64(v___x_1015_);
v___x_1018_ = lean_uint64_shift_right(v___x_1017_, v___x_1016_);
v___x_1019_ = lean_unbox_uint64(v___x_1015_);
lean_dec_ref(v___x_1015_);
v_fold_1020_ = lean_uint64_xor(v___x_1019_, v___x_1018_);
v___x_1021_ = 16ULL;
v___x_1022_ = lean_uint64_shift_right(v_fold_1020_, v___x_1021_);
v___x_1023_ = lean_uint64_xor(v_fold_1020_, v___x_1022_);
v___x_1024_ = lean_uint64_to_usize(v___x_1023_);
v___x_1025_ = lean_usize_of_nat(v___x_1011_);
v___x_1026_ = ((size_t)1ULL);
v___x_1027_ = lean_usize_sub(v___x_1025_, v___x_1026_);
v___x_1028_ = lean_usize_land(v___x_1024_, v___x_1027_);
v_bkt_1029_ = lean_array_uget_borrowed(v_buckets_1009_, v___x_1028_);
lean_inc(v_bkt_1029_);
v___x_1030_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_inst_1003_, v_a_1006_, v_bkt_1029_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1053_; 
lean_inc_ref(v_buckets_1009_);
lean_inc(v_size_1008_);
v_isSharedCheck_1053_ = !lean_is_exclusive(v_m_1005_);
if (v_isSharedCheck_1053_ == 0)
{
lean_object* v_unused_1054_; lean_object* v_unused_1055_; 
v_unused_1054_ = lean_ctor_get(v_m_1005_, 1);
lean_dec(v_unused_1054_);
v_unused_1055_ = lean_ctor_get(v_m_1005_, 0);
lean_dec(v_unused_1055_);
v___x_1032_ = v_m_1005_;
v_isShared_1033_ = v_isSharedCheck_1053_;
goto v_resetjp_1031_;
}
else
{
lean_dec(v_m_1005_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1053_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1034_; lean_object* v_size_x27_1035_; lean_object* v___x_1036_; lean_object* v_buckets_x27_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; uint8_t v___x_1043_; 
v___x_1034_ = lean_unsigned_to_nat(1u);
v_size_x27_1035_ = lean_nat_add(v_size_1008_, v___x_1034_);
lean_dec(v_size_1008_);
lean_inc(v_bkt_1029_);
v___x_1036_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1036_, 0, v_a_1006_);
lean_ctor_set(v___x_1036_, 1, v_b_1007_);
lean_ctor_set(v___x_1036_, 2, v_bkt_1029_);
v_buckets_x27_1037_ = lean_array_uset(v_buckets_1009_, v___x_1028_, v___x_1036_);
v___x_1038_ = lean_unsigned_to_nat(4u);
v___x_1039_ = lean_nat_mul(v_size_x27_1035_, v___x_1038_);
v___x_1040_ = lean_unsigned_to_nat(3u);
v___x_1041_ = lean_nat_div(v___x_1039_, v___x_1040_);
lean_dec(v___x_1039_);
v___x_1042_ = lean_array_get_size(v_buckets_x27_1037_);
v___x_1043_ = lean_nat_dec_le(v___x_1041_, v___x_1042_);
lean_dec(v___x_1041_);
if (v___x_1043_ == 0)
{
lean_object* v_val_1044_; lean_object* v___x_1046_; 
v_val_1044_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1004_, v_buckets_x27_1037_);
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 1, v_val_1044_);
lean_ctor_set(v___x_1032_, 0, v_size_x27_1035_);
v___x_1046_ = v___x_1032_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_size_x27_1035_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v_val_1044_);
v___x_1046_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
lean_object* v___x_1047_; 
v___x_1047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1030_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
return v___x_1047_;
}
}
else
{
lean_object* v___x_1050_; 
lean_dec_ref(v_inst_1004_);
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 1, v_buckets_x27_1037_);
lean_ctor_set(v___x_1032_, 0, v_size_x27_1035_);
v___x_1050_ = v___x_1032_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_size_x27_1035_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v_buckets_x27_1037_);
v___x_1050_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
lean_object* v___x_1051_; 
v___x_1051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1030_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
return v___x_1051_;
}
}
}
}
else
{
lean_object* v___x_1056_; 
lean_dec(v_b_1007_);
lean_dec(v_a_1006_);
lean_dec_ref(v_inst_1004_);
v___x_1056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1030_);
lean_ctor_set(v___x_1056_, 1, v_m_1005_);
return v___x_1056_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_1057_, lean_object* v_00_u03b2_1058_, lean_object* v_inst_1059_, lean_object* v_inst_1060_, lean_object* v_m_1061_, lean_object* v_a_1062_, lean_object* v_b_1063_){
_start:
{
lean_object* v_size_1064_; lean_object* v_buckets_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; uint8_t v___x_1068_; 
v_size_1064_ = lean_ctor_get(v_m_1061_, 0);
v_buckets_1065_ = lean_ctor_get(v_m_1061_, 1);
v___x_1066_ = lean_unsigned_to_nat(0u);
v___x_1067_ = lean_array_get_size(v_buckets_1065_);
v___x_1068_ = lean_nat_dec_lt(v___x_1066_, v___x_1067_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
lean_dec(v_b_1063_);
lean_dec(v_a_1062_);
lean_dec_ref(v_inst_1060_);
lean_dec_ref(v_inst_1059_);
v___x_1069_ = lean_box(0);
v___x_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
lean_ctor_set(v___x_1070_, 1, v_m_1061_);
return v___x_1070_;
}
else
{
lean_object* v___x_1071_; uint64_t v___x_1072_; uint64_t v___x_1073_; uint64_t v___x_1074_; uint64_t v___x_1075_; uint64_t v_fold_1076_; uint64_t v___x_1077_; uint64_t v___x_1078_; uint64_t v___x_1079_; size_t v___x_1080_; size_t v___x_1081_; size_t v___x_1082_; size_t v___x_1083_; size_t v___x_1084_; lean_object* v_bkt_1085_; lean_object* v___x_1086_; 
lean_inc_ref(v_inst_1060_);
lean_inc_n(v_a_1062_, 2);
v___x_1071_ = lean_apply_1(v_inst_1060_, v_a_1062_);
v___x_1072_ = 32ULL;
v___x_1073_ = lean_unbox_uint64(v___x_1071_);
v___x_1074_ = lean_uint64_shift_right(v___x_1073_, v___x_1072_);
v___x_1075_ = lean_unbox_uint64(v___x_1071_);
lean_dec_ref(v___x_1071_);
v_fold_1076_ = lean_uint64_xor(v___x_1075_, v___x_1074_);
v___x_1077_ = 16ULL;
v___x_1078_ = lean_uint64_shift_right(v_fold_1076_, v___x_1077_);
v___x_1079_ = lean_uint64_xor(v_fold_1076_, v___x_1078_);
v___x_1080_ = lean_uint64_to_usize(v___x_1079_);
v___x_1081_ = lean_usize_of_nat(v___x_1067_);
v___x_1082_ = ((size_t)1ULL);
v___x_1083_ = lean_usize_sub(v___x_1081_, v___x_1082_);
v___x_1084_ = lean_usize_land(v___x_1080_, v___x_1083_);
v_bkt_1085_ = lean_array_uget_borrowed(v_buckets_1065_, v___x_1084_);
lean_inc(v_bkt_1085_);
v___x_1086_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_inst_1059_, v_a_1062_, v_bkt_1085_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1109_; 
lean_inc_ref(v_buckets_1065_);
lean_inc(v_size_1064_);
v_isSharedCheck_1109_ = !lean_is_exclusive(v_m_1061_);
if (v_isSharedCheck_1109_ == 0)
{
lean_object* v_unused_1110_; lean_object* v_unused_1111_; 
v_unused_1110_ = lean_ctor_get(v_m_1061_, 1);
lean_dec(v_unused_1110_);
v_unused_1111_ = lean_ctor_get(v_m_1061_, 0);
lean_dec(v_unused_1111_);
v___x_1088_ = v_m_1061_;
v_isShared_1089_ = v_isSharedCheck_1109_;
goto v_resetjp_1087_;
}
else
{
lean_dec(v_m_1061_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1109_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1090_; lean_object* v_size_x27_1091_; lean_object* v___x_1092_; lean_object* v_buckets_x27_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; uint8_t v___x_1099_; 
v___x_1090_ = lean_unsigned_to_nat(1u);
v_size_x27_1091_ = lean_nat_add(v_size_1064_, v___x_1090_);
lean_dec(v_size_1064_);
lean_inc(v_bkt_1085_);
v___x_1092_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1092_, 0, v_a_1062_);
lean_ctor_set(v___x_1092_, 1, v_b_1063_);
lean_ctor_set(v___x_1092_, 2, v_bkt_1085_);
v_buckets_x27_1093_ = lean_array_uset(v_buckets_1065_, v___x_1084_, v___x_1092_);
v___x_1094_ = lean_unsigned_to_nat(4u);
v___x_1095_ = lean_nat_mul(v_size_x27_1091_, v___x_1094_);
v___x_1096_ = lean_unsigned_to_nat(3u);
v___x_1097_ = lean_nat_div(v___x_1095_, v___x_1096_);
lean_dec(v___x_1095_);
v___x_1098_ = lean_array_get_size(v_buckets_x27_1093_);
v___x_1099_ = lean_nat_dec_le(v___x_1097_, v___x_1098_);
lean_dec(v___x_1097_);
if (v___x_1099_ == 0)
{
lean_object* v_val_1100_; lean_object* v___x_1102_; 
v_val_1100_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1060_, v_buckets_x27_1093_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 1, v_val_1100_);
lean_ctor_set(v___x_1088_, 0, v_size_x27_1091_);
v___x_1102_ = v___x_1088_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_size_x27_1091_);
lean_ctor_set(v_reuseFailAlloc_1104_, 1, v_val_1100_);
v___x_1102_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
lean_object* v___x_1103_; 
v___x_1103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1086_);
lean_ctor_set(v___x_1103_, 1, v___x_1102_);
return v___x_1103_;
}
}
else
{
lean_object* v___x_1106_; 
lean_dec_ref(v_inst_1060_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 1, v_buckets_x27_1093_);
lean_ctor_set(v___x_1088_, 0, v_size_x27_1091_);
v___x_1106_ = v___x_1088_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_size_x27_1091_);
lean_ctor_set(v_reuseFailAlloc_1108_, 1, v_buckets_x27_1093_);
v___x_1106_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
lean_object* v___x_1107_; 
v___x_1107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1086_);
lean_ctor_set(v___x_1107_, 1, v___x_1106_);
return v___x_1107_;
}
}
}
}
else
{
lean_object* v___x_1112_; 
lean_dec(v_b_1063_);
lean_dec(v_a_1062_);
lean_dec_ref(v_inst_1060_);
v___x_1112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1086_);
lean_ctor_set(v___x_1112_, 1, v_m_1061_);
return v___x_1112_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x3f___redArg(lean_object* v_inst_1113_, lean_object* v_inst_1114_, lean_object* v_m_1115_, lean_object* v_a_1116_){
_start:
{
lean_object* v_buckets_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; uint8_t v___x_1120_; 
v_buckets_1117_ = lean_ctor_get(v_m_1115_, 1);
v___x_1118_ = lean_unsigned_to_nat(0u);
v___x_1119_ = lean_array_get_size(v_buckets_1117_);
v___x_1120_ = lean_nat_dec_lt(v___x_1118_, v___x_1119_);
if (v___x_1120_ == 0)
{
lean_object* v___x_1121_; 
lean_dec(v_a_1116_);
lean_dec_ref(v_inst_1114_);
lean_dec_ref(v_inst_1113_);
v___x_1121_ = lean_box(0);
return v___x_1121_;
}
else
{
lean_object* v___x_1122_; 
v___x_1122_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_1113_, v_inst_1114_, v_m_1115_, v_a_1116_);
return v___x_1122_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x3f___redArg___boxed(lean_object* v_inst_1123_, lean_object* v_inst_1124_, lean_object* v_m_1125_, lean_object* v_a_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Std_DHashMap_Raw_getKey_x3f___redArg(v_inst_1123_, v_inst_1124_, v_m_1125_, v_a_1126_);
lean_dec_ref(v_m_1125_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x3f(lean_object* v_00_u03b1_1128_, lean_object* v_00_u03b2_1129_, lean_object* v_inst_1130_, lean_object* v_inst_1131_, lean_object* v_m_1132_, lean_object* v_a_1133_){
_start:
{
lean_object* v_buckets_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; uint8_t v___x_1137_; 
v_buckets_1134_ = lean_ctor_get(v_m_1132_, 1);
v___x_1135_ = lean_unsigned_to_nat(0u);
v___x_1136_ = lean_array_get_size(v_buckets_1134_);
v___x_1137_ = lean_nat_dec_lt(v___x_1135_, v___x_1136_);
if (v___x_1137_ == 0)
{
lean_object* v___x_1138_; 
lean_dec(v_a_1133_);
lean_dec_ref(v_inst_1131_);
lean_dec_ref(v_inst_1130_);
v___x_1138_ = lean_box(0);
return v___x_1138_;
}
else
{
lean_object* v___x_1139_; 
v___x_1139_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_1130_, v_inst_1131_, v_m_1132_, v_a_1133_);
return v___x_1139_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x3f___boxed(lean_object* v_00_u03b1_1140_, lean_object* v_00_u03b2_1141_, lean_object* v_inst_1142_, lean_object* v_inst_1143_, lean_object* v_m_1144_, lean_object* v_a_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_Std_DHashMap_Raw_getKey_x3f(v_00_u03b1_1140_, v_00_u03b2_1141_, v_inst_1142_, v_inst_1143_, v_m_1144_, v_a_1145_);
lean_dec_ref(v_m_1144_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey___redArg(lean_object* v_inst_1147_, lean_object* v_inst_1148_, lean_object* v_m_1149_, lean_object* v_a_1150_){
_start:
{
lean_object* v___x_1151_; 
v___x_1151_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_1147_, v_inst_1148_, v_m_1149_, v_a_1150_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey___redArg___boxed(lean_object* v_inst_1152_, lean_object* v_inst_1153_, lean_object* v_m_1154_, lean_object* v_a_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Std_DHashMap_Raw_getKey___redArg(v_inst_1152_, v_inst_1153_, v_m_1154_, v_a_1155_);
lean_dec_ref(v_m_1154_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey(lean_object* v_00_u03b1_1157_, lean_object* v_00_u03b2_1158_, lean_object* v_inst_1159_, lean_object* v_inst_1160_, lean_object* v_m_1161_, lean_object* v_a_1162_, lean_object* v_h_1163_){
_start:
{
lean_object* v___x_1164_; 
v___x_1164_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_1159_, v_inst_1160_, v_m_1161_, v_a_1162_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey___boxed(lean_object* v_00_u03b1_1165_, lean_object* v_00_u03b2_1166_, lean_object* v_inst_1167_, lean_object* v_inst_1168_, lean_object* v_m_1169_, lean_object* v_a_1170_, lean_object* v_h_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Std_DHashMap_Raw_getKey(v_00_u03b1_1165_, v_00_u03b2_1166_, v_inst_1167_, v_inst_1168_, v_m_1169_, v_a_1170_, v_h_1171_);
lean_dec_ref(v_m_1169_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKeyD___redArg(lean_object* v_inst_1173_, lean_object* v_inst_1174_, lean_object* v_m_1175_, lean_object* v_a_1176_, lean_object* v_fallback_1177_){
_start:
{
lean_object* v_buckets_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; uint8_t v___x_1181_; 
v_buckets_1178_ = lean_ctor_get(v_m_1175_, 1);
v___x_1179_ = lean_unsigned_to_nat(0u);
v___x_1180_ = lean_array_get_size(v_buckets_1178_);
v___x_1181_ = lean_nat_dec_lt(v___x_1179_, v___x_1180_);
if (v___x_1181_ == 0)
{
lean_dec(v_a_1176_);
lean_dec_ref(v_inst_1174_);
lean_dec_ref(v_inst_1173_);
lean_inc(v_fallback_1177_);
return v_fallback_1177_;
}
else
{
lean_object* v___x_1182_; 
v___x_1182_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_1173_, v_inst_1174_, v_m_1175_, v_a_1176_, v_fallback_1177_);
return v___x_1182_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKeyD___redArg___boxed(lean_object* v_inst_1183_, lean_object* v_inst_1184_, lean_object* v_m_1185_, lean_object* v_a_1186_, lean_object* v_fallback_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Std_DHashMap_Raw_getKeyD___redArg(v_inst_1183_, v_inst_1184_, v_m_1185_, v_a_1186_, v_fallback_1187_);
lean_dec(v_fallback_1187_);
lean_dec_ref(v_m_1185_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKeyD(lean_object* v_00_u03b1_1189_, lean_object* v_00_u03b2_1190_, lean_object* v_inst_1191_, lean_object* v_inst_1192_, lean_object* v_m_1193_, lean_object* v_a_1194_, lean_object* v_fallback_1195_){
_start:
{
lean_object* v_buckets_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; uint8_t v___x_1199_; 
v_buckets_1196_ = lean_ctor_get(v_m_1193_, 1);
v___x_1197_ = lean_unsigned_to_nat(0u);
v___x_1198_ = lean_array_get_size(v_buckets_1196_);
v___x_1199_ = lean_nat_dec_lt(v___x_1197_, v___x_1198_);
if (v___x_1199_ == 0)
{
lean_dec(v_a_1194_);
lean_dec_ref(v_inst_1192_);
lean_dec_ref(v_inst_1191_);
lean_inc(v_fallback_1195_);
return v_fallback_1195_;
}
else
{
lean_object* v___x_1200_; 
v___x_1200_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_1191_, v_inst_1192_, v_m_1193_, v_a_1194_, v_fallback_1195_);
return v___x_1200_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKeyD___boxed(lean_object* v_00_u03b1_1201_, lean_object* v_00_u03b2_1202_, lean_object* v_inst_1203_, lean_object* v_inst_1204_, lean_object* v_m_1205_, lean_object* v_a_1206_, lean_object* v_fallback_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l_Std_DHashMap_Raw_getKeyD(v_00_u03b1_1201_, v_00_u03b2_1202_, v_inst_1203_, v_inst_1204_, v_m_1205_, v_a_1206_, v_fallback_1207_);
lean_dec(v_fallback_1207_);
lean_dec_ref(v_m_1205_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x21___redArg(lean_object* v_inst_1209_, lean_object* v_inst_1210_, lean_object* v_inst_1211_, lean_object* v_m_1212_, lean_object* v_a_1213_){
_start:
{
lean_object* v_buckets_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; uint8_t v___x_1217_; 
v_buckets_1214_ = lean_ctor_get(v_m_1212_, 1);
v___x_1215_ = lean_unsigned_to_nat(0u);
v___x_1216_ = lean_array_get_size(v_buckets_1214_);
v___x_1217_ = lean_nat_dec_lt(v___x_1215_, v___x_1216_);
if (v___x_1217_ == 0)
{
lean_dec(v_a_1213_);
lean_dec_ref(v_inst_1210_);
lean_dec_ref(v_inst_1209_);
lean_inc(v_inst_1211_);
return v_inst_1211_;
}
else
{
lean_object* v___x_1218_; 
v___x_1218_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_1209_, v_inst_1210_, v_inst_1211_, v_m_1212_, v_a_1213_);
return v___x_1218_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x21___redArg___boxed(lean_object* v_inst_1219_, lean_object* v_inst_1220_, lean_object* v_inst_1221_, lean_object* v_m_1222_, lean_object* v_a_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l_Std_DHashMap_Raw_getKey_x21___redArg(v_inst_1219_, v_inst_1220_, v_inst_1221_, v_m_1222_, v_a_1223_);
lean_dec_ref(v_m_1222_);
lean_dec(v_inst_1221_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x21(lean_object* v_00_u03b1_1225_, lean_object* v_00_u03b2_1226_, lean_object* v_inst_1227_, lean_object* v_inst_1228_, lean_object* v_inst_1229_, lean_object* v_m_1230_, lean_object* v_a_1231_){
_start:
{
lean_object* v_buckets_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; uint8_t v___x_1235_; 
v_buckets_1232_ = lean_ctor_get(v_m_1230_, 1);
v___x_1233_ = lean_unsigned_to_nat(0u);
v___x_1234_ = lean_array_get_size(v_buckets_1232_);
v___x_1235_ = lean_nat_dec_lt(v___x_1233_, v___x_1234_);
if (v___x_1235_ == 0)
{
lean_dec(v_a_1231_);
lean_dec_ref(v_inst_1228_);
lean_dec_ref(v_inst_1227_);
lean_inc(v_inst_1229_);
return v_inst_1229_;
}
else
{
lean_object* v___x_1236_; 
v___x_1236_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_1227_, v_inst_1228_, v_inst_1229_, v_m_1230_, v_a_1231_);
return v___x_1236_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x21___boxed(lean_object* v_00_u03b1_1237_, lean_object* v_00_u03b2_1238_, lean_object* v_inst_1239_, lean_object* v_inst_1240_, lean_object* v_inst_1241_, lean_object* v_m_1242_, lean_object* v_a_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_Std_DHashMap_Raw_getKey_x21(v_00_u03b1_1237_, v_00_u03b2_1238_, v_inst_1239_, v_inst_1240_, v_inst_1241_, v_m_1242_, v_a_1243_);
lean_dec_ref(v_m_1242_);
lean_dec(v_inst_1241_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x3f___redArg(lean_object* v_inst_1245_, lean_object* v_inst_1246_, lean_object* v_m_1247_, lean_object* v_a_1248_){
_start:
{
lean_object* v_buckets_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; uint8_t v___x_1252_; 
v_buckets_1249_ = lean_ctor_get(v_m_1247_, 1);
v___x_1250_ = lean_unsigned_to_nat(0u);
v___x_1251_ = lean_array_get_size(v_buckets_1249_);
v___x_1252_ = lean_nat_dec_lt(v___x_1250_, v___x_1251_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; 
lean_dec(v_a_1248_);
lean_dec_ref(v_inst_1246_);
lean_dec_ref(v_inst_1245_);
v___x_1253_ = lean_box(0);
return v___x_1253_;
}
else
{
lean_object* v___x_1254_; 
v___x_1254_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(v_inst_1245_, v_inst_1246_, v_m_1247_, v_a_1248_);
return v___x_1254_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x3f___redArg___boxed(lean_object* v_inst_1255_, lean_object* v_inst_1256_, lean_object* v_m_1257_, lean_object* v_a_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Std_DHashMap_Raw_getEntry_x3f___redArg(v_inst_1255_, v_inst_1256_, v_m_1257_, v_a_1258_);
lean_dec_ref(v_m_1257_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x3f(lean_object* v_00_u03b1_1260_, lean_object* v_00_u03b2_1261_, lean_object* v_inst_1262_, lean_object* v_inst_1263_, lean_object* v_m_1264_, lean_object* v_a_1265_){
_start:
{
lean_object* v_buckets_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; uint8_t v___x_1269_; 
v_buckets_1266_ = lean_ctor_get(v_m_1264_, 1);
v___x_1267_ = lean_unsigned_to_nat(0u);
v___x_1268_ = lean_array_get_size(v_buckets_1266_);
v___x_1269_ = lean_nat_dec_lt(v___x_1267_, v___x_1268_);
if (v___x_1269_ == 0)
{
lean_object* v___x_1270_; 
lean_dec(v_a_1265_);
lean_dec_ref(v_inst_1263_);
lean_dec_ref(v_inst_1262_);
v___x_1270_ = lean_box(0);
return v___x_1270_;
}
else
{
lean_object* v___x_1271_; 
v___x_1271_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(v_inst_1262_, v_inst_1263_, v_m_1264_, v_a_1265_);
return v___x_1271_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x3f___boxed(lean_object* v_00_u03b1_1272_, lean_object* v_00_u03b2_1273_, lean_object* v_inst_1274_, lean_object* v_inst_1275_, lean_object* v_m_1276_, lean_object* v_a_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_Std_DHashMap_Raw_getEntry_x3f(v_00_u03b1_1272_, v_00_u03b2_1273_, v_inst_1274_, v_inst_1275_, v_m_1276_, v_a_1277_);
lean_dec_ref(v_m_1276_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry___redArg(lean_object* v_inst_1279_, lean_object* v_inst_1280_, lean_object* v_m_1281_, lean_object* v_a_1282_){
_start:
{
lean_object* v___x_1283_; 
v___x_1283_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg(v_inst_1279_, v_inst_1280_, v_m_1281_, v_a_1282_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry___redArg___boxed(lean_object* v_inst_1284_, lean_object* v_inst_1285_, lean_object* v_m_1286_, lean_object* v_a_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_Std_DHashMap_Raw_getEntry___redArg(v_inst_1284_, v_inst_1285_, v_m_1286_, v_a_1287_);
lean_dec_ref(v_m_1286_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry(lean_object* v_00_u03b1_1289_, lean_object* v_00_u03b2_1290_, lean_object* v_inst_1291_, lean_object* v_inst_1292_, lean_object* v_m_1293_, lean_object* v_a_1294_, lean_object* v_h_1295_){
_start:
{
lean_object* v___x_1296_; 
v___x_1296_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg(v_inst_1291_, v_inst_1292_, v_m_1293_, v_a_1294_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry___boxed(lean_object* v_00_u03b1_1297_, lean_object* v_00_u03b2_1298_, lean_object* v_inst_1299_, lean_object* v_inst_1300_, lean_object* v_m_1301_, lean_object* v_a_1302_, lean_object* v_h_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Std_DHashMap_Raw_getEntry(v_00_u03b1_1297_, v_00_u03b2_1298_, v_inst_1299_, v_inst_1300_, v_m_1301_, v_a_1302_, v_h_1303_);
lean_dec_ref(v_m_1301_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntryD___redArg(lean_object* v_inst_1305_, lean_object* v_inst_1306_, lean_object* v_m_1307_, lean_object* v_a_1308_, lean_object* v_fallback_1309_){
_start:
{
lean_object* v_buckets_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; uint8_t v___x_1313_; 
v_buckets_1310_ = lean_ctor_get(v_m_1307_, 1);
v___x_1311_ = lean_unsigned_to_nat(0u);
v___x_1312_ = lean_array_get_size(v_buckets_1310_);
v___x_1313_ = lean_nat_dec_lt(v___x_1311_, v___x_1312_);
if (v___x_1313_ == 0)
{
lean_dec(v_a_1308_);
lean_dec_ref(v_inst_1306_);
lean_dec_ref(v_inst_1305_);
lean_inc_ref(v_fallback_1309_);
return v_fallback_1309_;
}
else
{
lean_object* v___x_1314_; 
v___x_1314_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD___redArg(v_inst_1305_, v_inst_1306_, v_m_1307_, v_a_1308_, v_fallback_1309_);
return v___x_1314_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntryD___redArg___boxed(lean_object* v_inst_1315_, lean_object* v_inst_1316_, lean_object* v_m_1317_, lean_object* v_a_1318_, lean_object* v_fallback_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_Std_DHashMap_Raw_getEntryD___redArg(v_inst_1315_, v_inst_1316_, v_m_1317_, v_a_1318_, v_fallback_1319_);
lean_dec_ref(v_fallback_1319_);
lean_dec_ref(v_m_1317_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntryD(lean_object* v_00_u03b1_1321_, lean_object* v_00_u03b2_1322_, lean_object* v_inst_1323_, lean_object* v_inst_1324_, lean_object* v_m_1325_, lean_object* v_a_1326_, lean_object* v_fallback_1327_){
_start:
{
lean_object* v_buckets_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; uint8_t v___x_1331_; 
v_buckets_1328_ = lean_ctor_get(v_m_1325_, 1);
v___x_1329_ = lean_unsigned_to_nat(0u);
v___x_1330_ = lean_array_get_size(v_buckets_1328_);
v___x_1331_ = lean_nat_dec_lt(v___x_1329_, v___x_1330_);
if (v___x_1331_ == 0)
{
lean_dec(v_a_1326_);
lean_dec_ref(v_inst_1324_);
lean_dec_ref(v_inst_1323_);
lean_inc_ref(v_fallback_1327_);
return v_fallback_1327_;
}
else
{
lean_object* v___x_1332_; 
v___x_1332_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD___redArg(v_inst_1323_, v_inst_1324_, v_m_1325_, v_a_1326_, v_fallback_1327_);
return v___x_1332_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntryD___boxed(lean_object* v_00_u03b1_1333_, lean_object* v_00_u03b2_1334_, lean_object* v_inst_1335_, lean_object* v_inst_1336_, lean_object* v_m_1337_, lean_object* v_a_1338_, lean_object* v_fallback_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l_Std_DHashMap_Raw_getEntryD(v_00_u03b1_1333_, v_00_u03b2_1334_, v_inst_1335_, v_inst_1336_, v_m_1337_, v_a_1338_, v_fallback_1339_);
lean_dec_ref(v_fallback_1339_);
lean_dec_ref(v_m_1337_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x21___redArg(lean_object* v_inst_1341_, lean_object* v_inst_1342_, lean_object* v_inst_1343_, lean_object* v_m_1344_, lean_object* v_a_1345_){
_start:
{
lean_object* v_buckets_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; uint8_t v___x_1349_; 
v_buckets_1346_ = lean_ctor_get(v_m_1344_, 1);
v___x_1347_ = lean_unsigned_to_nat(0u);
v___x_1348_ = lean_array_get_size(v_buckets_1346_);
v___x_1349_ = lean_nat_dec_lt(v___x_1347_, v___x_1348_);
if (v___x_1349_ == 0)
{
lean_dec(v_a_1345_);
lean_dec_ref(v_inst_1342_);
lean_dec_ref(v_inst_1341_);
lean_inc_ref(v_inst_1343_);
return v_inst_1343_;
}
else
{
lean_object* v___x_1350_; 
v___x_1350_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___redArg(v_inst_1341_, v_inst_1342_, v_m_1344_, v_a_1345_, v_inst_1343_);
return v___x_1350_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x21___redArg___boxed(lean_object* v_inst_1351_, lean_object* v_inst_1352_, lean_object* v_inst_1353_, lean_object* v_m_1354_, lean_object* v_a_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l_Std_DHashMap_Raw_getEntry_x21___redArg(v_inst_1351_, v_inst_1352_, v_inst_1353_, v_m_1354_, v_a_1355_);
lean_dec_ref(v_m_1354_);
lean_dec_ref(v_inst_1353_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x21(lean_object* v_00_u03b1_1357_, lean_object* v_00_u03b2_1358_, lean_object* v_inst_1359_, lean_object* v_inst_1360_, lean_object* v_inst_1361_, lean_object* v_m_1362_, lean_object* v_a_1363_){
_start:
{
lean_object* v_buckets_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; uint8_t v___x_1367_; 
v_buckets_1364_ = lean_ctor_get(v_m_1362_, 1);
v___x_1365_ = lean_unsigned_to_nat(0u);
v___x_1366_ = lean_array_get_size(v_buckets_1364_);
v___x_1367_ = lean_nat_dec_lt(v___x_1365_, v___x_1366_);
if (v___x_1367_ == 0)
{
lean_dec(v_a_1363_);
lean_dec_ref(v_inst_1360_);
lean_dec_ref(v_inst_1359_);
lean_inc_ref(v_inst_1361_);
return v_inst_1361_;
}
else
{
lean_object* v___x_1368_; 
v___x_1368_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___redArg(v_inst_1359_, v_inst_1360_, v_m_1362_, v_a_1363_, v_inst_1361_);
return v___x_1368_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x21___boxed(lean_object* v_00_u03b1_1369_, lean_object* v_00_u03b2_1370_, lean_object* v_inst_1371_, lean_object* v_inst_1372_, lean_object* v_inst_1373_, lean_object* v_m_1374_, lean_object* v_a_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l_Std_DHashMap_Raw_getEntry_x21(v_00_u03b1_1369_, v_00_u03b2_1370_, v_inst_1371_, v_inst_1372_, v_inst_1373_, v_m_1374_, v_a_1375_);
lean_dec_ref(v_m_1374_);
lean_dec_ref(v_inst_1373_);
return v_res_1376_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_isEmpty___redArg(lean_object* v_m_1377_){
_start:
{
lean_object* v_size_1378_; lean_object* v___x_1379_; uint8_t v___x_1380_; 
v_size_1378_ = lean_ctor_get(v_m_1377_, 0);
v___x_1379_ = lean_unsigned_to_nat(0u);
v___x_1380_ = lean_nat_dec_eq(v_size_1378_, v___x_1379_);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_isEmpty___redArg___boxed(lean_object* v_m_1381_){
_start:
{
uint8_t v_res_1382_; lean_object* v_r_1383_; 
v_res_1382_ = l_Std_DHashMap_Raw_isEmpty___redArg(v_m_1381_);
lean_dec_ref(v_m_1381_);
v_r_1383_ = lean_box(v_res_1382_);
return v_r_1383_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_isEmpty(lean_object* v_00_u03b1_1384_, lean_object* v_00_u03b2_1385_, lean_object* v_m_1386_){
_start:
{
lean_object* v_size_1387_; lean_object* v___x_1388_; uint8_t v___x_1389_; 
v_size_1387_ = lean_ctor_get(v_m_1386_, 0);
v___x_1388_ = lean_unsigned_to_nat(0u);
v___x_1389_ = lean_nat_dec_eq(v_size_1387_, v___x_1388_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_isEmpty___boxed(lean_object* v_00_u03b1_1390_, lean_object* v_00_u03b2_1391_, lean_object* v_m_1392_){
_start:
{
uint8_t v_res_1393_; lean_object* v_r_1394_; 
v_res_1393_ = l_Std_DHashMap_Raw_isEmpty(v_00_u03b1_1390_, v_00_u03b2_1391_, v_m_1392_);
lean_dec_ref(v_m_1392_);
v_r_1394_ = lean_box(v_res_1393_);
return v_r_1394_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_modify___redArg(lean_object* v_inst_1395_, lean_object* v_inst_1396_, lean_object* v_m_1397_, lean_object* v_a_1398_, lean_object* v_f_1399_){
_start:
{
lean_object* v_buckets_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; uint8_t v___x_1403_; 
v_buckets_1400_ = lean_ctor_get(v_m_1397_, 1);
v___x_1401_ = lean_unsigned_to_nat(0u);
v___x_1402_ = lean_array_get_size(v_buckets_1400_);
v___x_1403_ = lean_nat_dec_lt(v___x_1401_, v___x_1402_);
if (v___x_1403_ == 0)
{
lean_object* v___x_1404_; 
lean_dec(v_f_1399_);
lean_dec(v_a_1398_);
lean_dec_ref(v_m_1397_);
lean_dec_ref(v_inst_1396_);
lean_dec_ref(v_inst_1395_);
v___x_1404_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_1404_;
}
else
{
lean_object* v___x_1405_; 
v___x_1405_ = l_Std_DHashMap_Internal_Raw_u2080_modify___redArg(v_inst_1395_, v_inst_1396_, v_m_1397_, v_a_1398_, v_f_1399_);
return v___x_1405_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_modify(lean_object* v_00_u03b1_1406_, lean_object* v_00_u03b2_1407_, lean_object* v_inst_1408_, lean_object* v_inst_1409_, lean_object* v_inst_1410_, lean_object* v_m_1411_, lean_object* v_a_1412_, lean_object* v_f_1413_){
_start:
{
lean_object* v_buckets_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; uint8_t v___x_1417_; 
v_buckets_1414_ = lean_ctor_get(v_m_1411_, 1);
v___x_1415_ = lean_unsigned_to_nat(0u);
v___x_1416_ = lean_array_get_size(v_buckets_1414_);
v___x_1417_ = lean_nat_dec_lt(v___x_1415_, v___x_1416_);
if (v___x_1417_ == 0)
{
lean_object* v___x_1418_; 
lean_dec(v_f_1413_);
lean_dec(v_a_1412_);
lean_dec_ref(v_m_1411_);
lean_dec_ref(v_inst_1410_);
lean_dec_ref(v_inst_1408_);
v___x_1418_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_1418_;
}
else
{
lean_object* v___x_1419_; 
v___x_1419_ = l_Std_DHashMap_Internal_Raw_u2080_modify___redArg(v_inst_1408_, v_inst_1410_, v_m_1411_, v_a_1412_, v_f_1413_);
return v___x_1419_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_modify___redArg(lean_object* v_inst_1420_, lean_object* v_inst_1421_, lean_object* v_m_1422_, lean_object* v_a_1423_, lean_object* v_f_1424_){
_start:
{
lean_object* v_buckets_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; uint8_t v___x_1428_; 
v_buckets_1425_ = lean_ctor_get(v_m_1422_, 1);
v___x_1426_ = lean_unsigned_to_nat(0u);
v___x_1427_ = lean_array_get_size(v_buckets_1425_);
v___x_1428_ = lean_nat_dec_lt(v___x_1426_, v___x_1427_);
if (v___x_1428_ == 0)
{
lean_object* v___x_1429_; 
lean_dec(v_f_1424_);
lean_dec(v_a_1423_);
lean_dec_ref(v_m_1422_);
lean_dec_ref(v_inst_1421_);
lean_dec_ref(v_inst_1420_);
v___x_1429_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_1429_;
}
else
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_inst_1420_, v_inst_1421_, v_m_1422_, v_a_1423_, v_f_1424_);
return v___x_1430_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_modify(lean_object* v_00_u03b1_1431_, lean_object* v_inst_1432_, lean_object* v_inst_1433_, lean_object* v_inst_1434_, lean_object* v_00_u03b2_1435_, lean_object* v_m_1436_, lean_object* v_a_1437_, lean_object* v_f_1438_){
_start:
{
lean_object* v_buckets_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; uint8_t v___x_1442_; 
v_buckets_1439_ = lean_ctor_get(v_m_1436_, 1);
v___x_1440_ = lean_unsigned_to_nat(0u);
v___x_1441_ = lean_array_get_size(v_buckets_1439_);
v___x_1442_ = lean_nat_dec_lt(v___x_1440_, v___x_1441_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1443_; 
lean_dec(v_f_1438_);
lean_dec(v_a_1437_);
lean_dec_ref(v_m_1436_);
lean_dec_ref(v_inst_1434_);
lean_dec_ref(v_inst_1432_);
v___x_1443_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_1443_;
}
else
{
lean_object* v___x_1444_; 
v___x_1444_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_inst_1432_, v_inst_1434_, v_m_1436_, v_a_1437_, v_f_1438_);
return v___x_1444_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_alter___redArg(lean_object* v_inst_1445_, lean_object* v_inst_1446_, lean_object* v_m_1447_, lean_object* v_a_1448_, lean_object* v_f_1449_){
_start:
{
lean_object* v_buckets_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; uint8_t v___x_1453_; 
v_buckets_1450_ = lean_ctor_get(v_m_1447_, 1);
v___x_1451_ = lean_unsigned_to_nat(0u);
v___x_1452_ = lean_array_get_size(v_buckets_1450_);
v___x_1453_ = lean_nat_dec_lt(v___x_1451_, v___x_1452_);
if (v___x_1453_ == 0)
{
lean_object* v___x_1454_; 
lean_dec_ref(v_f_1449_);
lean_dec(v_a_1448_);
lean_dec_ref(v_m_1447_);
lean_dec_ref(v_inst_1446_);
lean_dec_ref(v_inst_1445_);
v___x_1454_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_1454_;
}
else
{
lean_object* v___x_1455_; 
v___x_1455_ = l_Std_DHashMap_Internal_Raw_u2080_alter___redArg(v_inst_1445_, v_inst_1446_, v_m_1447_, v_a_1448_, v_f_1449_);
return v___x_1455_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_alter(lean_object* v_00_u03b1_1456_, lean_object* v_00_u03b2_1457_, lean_object* v_inst_1458_, lean_object* v_inst_1459_, lean_object* v_inst_1460_, lean_object* v_m_1461_, lean_object* v_a_1462_, lean_object* v_f_1463_){
_start:
{
lean_object* v_buckets_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; uint8_t v___x_1467_; 
v_buckets_1464_ = lean_ctor_get(v_m_1461_, 1);
v___x_1465_ = lean_unsigned_to_nat(0u);
v___x_1466_ = lean_array_get_size(v_buckets_1464_);
v___x_1467_ = lean_nat_dec_lt(v___x_1465_, v___x_1466_);
if (v___x_1467_ == 0)
{
lean_object* v___x_1468_; 
lean_dec_ref(v_f_1463_);
lean_dec(v_a_1462_);
lean_dec_ref(v_m_1461_);
lean_dec_ref(v_inst_1460_);
lean_dec_ref(v_inst_1458_);
v___x_1468_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_1468_;
}
else
{
lean_object* v___x_1469_; 
v___x_1469_ = l_Std_DHashMap_Internal_Raw_u2080_alter___redArg(v_inst_1458_, v_inst_1460_, v_m_1461_, v_a_1462_, v_f_1463_);
return v___x_1469_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_alter___redArg(lean_object* v_inst_1470_, lean_object* v_inst_1471_, lean_object* v_m_1472_, lean_object* v_a_1473_, lean_object* v_f_1474_){
_start:
{
lean_object* v_buckets_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; uint8_t v___x_1478_; 
v_buckets_1475_ = lean_ctor_get(v_m_1472_, 1);
v___x_1476_ = lean_unsigned_to_nat(0u);
v___x_1477_ = lean_array_get_size(v_buckets_1475_);
v___x_1478_ = lean_nat_dec_lt(v___x_1476_, v___x_1477_);
if (v___x_1478_ == 0)
{
lean_object* v___x_1479_; 
lean_dec_ref(v_f_1474_);
lean_dec(v_a_1473_);
lean_dec_ref(v_m_1472_);
lean_dec_ref(v_inst_1471_);
lean_dec_ref(v_inst_1470_);
v___x_1479_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_1479_;
}
else
{
lean_object* v___x_1480_; 
v___x_1480_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_1470_, v_inst_1471_, v_m_1472_, v_a_1473_, v_f_1474_);
return v___x_1480_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_alter(lean_object* v_00_u03b1_1481_, lean_object* v_inst_1482_, lean_object* v_inst_1483_, lean_object* v_inst_1484_, lean_object* v_00_u03b2_1485_, lean_object* v_m_1486_, lean_object* v_a_1487_, lean_object* v_f_1488_){
_start:
{
lean_object* v_buckets_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; uint8_t v___x_1492_; 
v_buckets_1489_ = lean_ctor_get(v_m_1486_, 1);
v___x_1490_ = lean_unsigned_to_nat(0u);
v___x_1491_ = lean_array_get_size(v_buckets_1489_);
v___x_1492_ = lean_nat_dec_lt(v___x_1490_, v___x_1491_);
if (v___x_1492_ == 0)
{
lean_object* v___x_1493_; 
lean_dec_ref(v_f_1488_);
lean_dec(v_a_1487_);
lean_dec_ref(v_m_1486_);
lean_dec_ref(v_inst_1484_);
lean_dec_ref(v_inst_1482_);
v___x_1493_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_1493_;
}
else
{
lean_object* v___x_1494_; 
v___x_1494_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_1482_, v_inst_1484_, v_m_1486_, v_a_1487_, v_f_1488_);
return v___x_1494_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0(lean_object* v_f_1495_, lean_object* v_a_1496_, lean_object* v_b_1497_, lean_object* v_d_1498_){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = lean_apply_3(v_f_1495_, v_d_1498_, v_a_1496_, v_b_1497_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__1(lean_object* v_inst_1500_, lean_object* v___f_1501_, lean_object* v_l_1502_, lean_object* v_acc_1503_){
_start:
{
lean_object* v___x_1504_; 
v___x_1504_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v_inst_1500_, v___f_1501_, v_acc_1503_, v_l_1502_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRevM___redArg(lean_object* v_inst_1505_, lean_object* v_f_1506_, lean_object* v_init_1507_, lean_object* v_b_1508_){
_start:
{
lean_object* v_toApplicative_1509_; lean_object* v_buckets_1510_; lean_object* v_toPure_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; uint8_t v___x_1514_; 
v_toApplicative_1509_ = lean_ctor_get(v_inst_1505_, 0);
v_buckets_1510_ = lean_ctor_get(v_b_1508_, 1);
lean_inc_ref(v_buckets_1510_);
lean_dec_ref(v_b_1508_);
v_toPure_1511_ = lean_ctor_get(v_toApplicative_1509_, 1);
v___x_1512_ = lean_array_get_size(v_buckets_1510_);
v___x_1513_ = lean_unsigned_to_nat(0u);
v___x_1514_ = lean_nat_dec_lt(v___x_1513_, v___x_1512_);
if (v___x_1514_ == 0)
{
lean_object* v___x_1515_; 
lean_inc(v_toPure_1511_);
lean_dec_ref(v_buckets_1510_);
lean_dec(v_f_1506_);
lean_dec_ref(v_inst_1505_);
v___x_1515_ = lean_apply_2(v_toPure_1511_, lean_box(0), v_init_1507_);
return v___x_1515_;
}
else
{
lean_object* v___f_1516_; lean_object* v___f_1517_; size_t v___x_1518_; size_t v___x_1519_; lean_object* v___x_1520_; 
v___f_1516_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1516_, 0, v_f_1506_);
lean_inc_ref(v_inst_1505_);
v___f_1517_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1517_, 0, v_inst_1505_);
lean_closure_set(v___f_1517_, 1, v___f_1516_);
v___x_1518_ = lean_usize_of_nat(v___x_1512_);
v___x_1519_ = ((size_t)0ULL);
v___x_1520_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1505_, v___f_1517_, v_buckets_1510_, v___x_1518_, v___x_1519_, v_init_1507_);
return v___x_1520_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRevM(lean_object* v_00_u03b1_1521_, lean_object* v_00_u03b2_1522_, lean_object* v_00_u03b4_1523_, lean_object* v_m_1524_, lean_object* v_inst_1525_, lean_object* v_f_1526_, lean_object* v_init_1527_, lean_object* v_b_1528_){
_start:
{
lean_object* v_toApplicative_1529_; lean_object* v_buckets_1530_; lean_object* v_toPure_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; uint8_t v___x_1534_; 
v_toApplicative_1529_ = lean_ctor_get(v_inst_1525_, 0);
v_buckets_1530_ = lean_ctor_get(v_b_1528_, 1);
lean_inc_ref(v_buckets_1530_);
lean_dec_ref(v_b_1528_);
v_toPure_1531_ = lean_ctor_get(v_toApplicative_1529_, 1);
v___x_1532_ = lean_array_get_size(v_buckets_1530_);
v___x_1533_ = lean_unsigned_to_nat(0u);
v___x_1534_ = lean_nat_dec_lt(v___x_1533_, v___x_1532_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; 
lean_inc(v_toPure_1531_);
lean_dec_ref(v_buckets_1530_);
lean_dec(v_f_1526_);
lean_dec_ref(v_inst_1525_);
v___x_1535_ = lean_apply_2(v_toPure_1531_, lean_box(0), v_init_1527_);
return v___x_1535_;
}
else
{
lean_object* v___f_1536_; lean_object* v___f_1537_; size_t v___x_1538_; size_t v___x_1539_; lean_object* v___x_1540_; 
v___f_1536_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1536_, 0, v_f_1526_);
lean_inc_ref(v_inst_1525_);
v___f_1537_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1537_, 0, v_inst_1525_);
lean_closure_set(v___f_1537_, 1, v___f_1536_);
v___x_1538_ = lean_usize_of_nat(v___x_1532_);
v___x_1539_ = ((size_t)0ULL);
v___x_1540_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1525_, v___f_1537_, v_buckets_1530_, v___x_1538_, v___x_1539_, v_init_1527_);
return v___x_1540_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRev___redArg___lam__1(lean_object* v___x_1541_, lean_object* v___f_1542_, lean_object* v_l_1543_, lean_object* v_acc_1544_){
_start:
{
lean_object* v___x_1545_; 
v___x_1545_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_1541_, v___f_1542_, v_acc_1544_, v_l_1543_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRev___redArg(lean_object* v_f_1565_, lean_object* v_init_1566_, lean_object* v_b_1567_){
_start:
{
lean_object* v___x_1568_; lean_object* v_buckets_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; uint8_t v___x_1572_; 
v___x_1568_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_1569_ = lean_ctor_get(v_b_1567_, 1);
lean_inc_ref(v_buckets_1569_);
lean_dec_ref(v_b_1567_);
v___x_1570_ = lean_array_get_size(v_buckets_1569_);
v___x_1571_ = lean_unsigned_to_nat(0u);
v___x_1572_ = lean_nat_dec_lt(v___x_1571_, v___x_1570_);
if (v___x_1572_ == 0)
{
lean_dec_ref(v_buckets_1569_);
lean_dec(v_f_1565_);
return v_init_1566_;
}
else
{
lean_object* v___f_1573_; lean_object* v___f_1574_; size_t v___x_1575_; size_t v___x_1576_; lean_object* v___x_1577_; 
v___f_1573_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1573_, 0, v_f_1565_);
v___f_1574_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1574_, 0, v___x_1568_);
lean_closure_set(v___f_1574_, 1, v___f_1573_);
v___x_1575_ = lean_usize_of_nat(v___x_1570_);
v___x_1576_ = ((size_t)0ULL);
v___x_1577_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1568_, v___f_1574_, v_buckets_1569_, v___x_1575_, v___x_1576_, v_init_1566_);
return v___x_1577_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRev(lean_object* v_00_u03b1_1578_, lean_object* v_00_u03b2_1579_, lean_object* v_00_u03b4_1580_, lean_object* v_f_1581_, lean_object* v_init_1582_, lean_object* v_b_1583_){
_start:
{
lean_object* v___x_1584_; lean_object* v_buckets_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; uint8_t v___x_1588_; 
v___x_1584_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_1585_ = lean_ctor_get(v_b_1583_, 1);
lean_inc_ref(v_buckets_1585_);
lean_dec_ref(v_b_1583_);
v___x_1586_ = lean_array_get_size(v_buckets_1585_);
v___x_1587_ = lean_unsigned_to_nat(0u);
v___x_1588_ = lean_nat_dec_lt(v___x_1587_, v___x_1586_);
if (v___x_1588_ == 0)
{
lean_dec_ref(v_buckets_1585_);
lean_dec(v_f_1581_);
return v_init_1582_;
}
else
{
lean_object* v___f_1589_; lean_object* v___f_1590_; size_t v___x_1591_; size_t v___x_1592_; lean_object* v___x_1593_; 
v___f_1589_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1589_, 0, v_f_1581_);
v___f_1590_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1590_, 0, v___x_1584_);
lean_closure_set(v___f_1590_, 1, v___f_1589_);
v___x_1591_ = lean_usize_of_nat(v___x_1586_);
v___x_1592_ = ((size_t)0ULL);
v___x_1593_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1584_, v___f_1590_, v_buckets_1585_, v___x_1591_, v___x_1592_, v_init_1582_);
return v___x_1593_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevM___redArg(lean_object* v_inst_1594_, lean_object* v_f_1595_, lean_object* v_init_1596_, lean_object* v_b_1597_){
_start:
{
lean_object* v_toApplicative_1598_; lean_object* v_buckets_1599_; lean_object* v_toPure_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; uint8_t v___x_1603_; 
v_toApplicative_1598_ = lean_ctor_get(v_inst_1594_, 0);
v_buckets_1599_ = lean_ctor_get(v_b_1597_, 1);
lean_inc_ref(v_buckets_1599_);
lean_dec_ref(v_b_1597_);
v_toPure_1600_ = lean_ctor_get(v_toApplicative_1598_, 1);
v___x_1601_ = lean_array_get_size(v_buckets_1599_);
v___x_1602_ = lean_unsigned_to_nat(0u);
v___x_1603_ = lean_nat_dec_lt(v___x_1602_, v___x_1601_);
if (v___x_1603_ == 0)
{
lean_object* v___x_1604_; 
lean_inc(v_toPure_1600_);
lean_dec_ref(v_buckets_1599_);
lean_dec(v_f_1595_);
lean_dec_ref(v_inst_1594_);
v___x_1604_ = lean_apply_2(v_toPure_1600_, lean_box(0), v_init_1596_);
return v___x_1604_;
}
else
{
lean_object* v___f_1605_; lean_object* v___f_1606_; size_t v___x_1607_; size_t v___x_1608_; lean_object* v___x_1609_; 
v___f_1605_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1605_, 0, v_f_1595_);
lean_inc_ref(v_inst_1594_);
v___f_1606_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1606_, 0, v_inst_1594_);
lean_closure_set(v___f_1606_, 1, v___f_1605_);
v___x_1607_ = lean_usize_of_nat(v___x_1601_);
v___x_1608_ = ((size_t)0ULL);
v___x_1609_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1594_, v___f_1606_, v_buckets_1599_, v___x_1607_, v___x_1608_, v_init_1596_);
return v___x_1609_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevM(lean_object* v_00_u03b1_1610_, lean_object* v_00_u03b2_1611_, lean_object* v_00_u03b4_1612_, lean_object* v_m_1613_, lean_object* v_inst_1614_, lean_object* v_f_1615_, lean_object* v_init_1616_, lean_object* v_b_1617_){
_start:
{
lean_object* v_toApplicative_1618_; lean_object* v_buckets_1619_; lean_object* v_toPure_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; uint8_t v___x_1623_; 
v_toApplicative_1618_ = lean_ctor_get(v_inst_1614_, 0);
v_buckets_1619_ = lean_ctor_get(v_b_1617_, 1);
lean_inc_ref(v_buckets_1619_);
lean_dec_ref(v_b_1617_);
v_toPure_1620_ = lean_ctor_get(v_toApplicative_1618_, 1);
v___x_1621_ = lean_array_get_size(v_buckets_1619_);
v___x_1622_ = lean_unsigned_to_nat(0u);
v___x_1623_ = lean_nat_dec_lt(v___x_1622_, v___x_1621_);
if (v___x_1623_ == 0)
{
lean_object* v___x_1624_; 
lean_inc(v_toPure_1620_);
lean_dec_ref(v_buckets_1619_);
lean_dec(v_f_1615_);
lean_dec_ref(v_inst_1614_);
v___x_1624_ = lean_apply_2(v_toPure_1620_, lean_box(0), v_init_1616_);
return v___x_1624_;
}
else
{
lean_object* v___f_1625_; lean_object* v___f_1626_; size_t v___x_1627_; size_t v___x_1628_; lean_object* v___x_1629_; 
v___f_1625_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1625_, 0, v_f_1615_);
lean_inc_ref(v_inst_1614_);
v___f_1626_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1626_, 0, v_inst_1614_);
lean_closure_set(v___f_1626_, 1, v___f_1625_);
v___x_1627_ = lean_usize_of_nat(v___x_1621_);
v___x_1628_ = ((size_t)0ULL);
v___x_1629_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1614_, v___f_1626_, v_buckets_1619_, v___x_1627_, v___x_1628_, v_init_1616_);
return v___x_1629_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRev___redArg(lean_object* v_f_1630_, lean_object* v_init_1631_, lean_object* v_b_1632_){
_start:
{
lean_object* v___x_1633_; lean_object* v_buckets_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; uint8_t v___x_1637_; 
v___x_1633_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_1634_ = lean_ctor_get(v_b_1632_, 1);
lean_inc_ref(v_buckets_1634_);
lean_dec_ref(v_b_1632_);
v___x_1635_ = lean_array_get_size(v_buckets_1634_);
v___x_1636_ = lean_unsigned_to_nat(0u);
v___x_1637_ = lean_nat_dec_lt(v___x_1636_, v___x_1635_);
if (v___x_1637_ == 0)
{
lean_dec_ref(v_buckets_1634_);
lean_dec(v_f_1630_);
return v_init_1631_;
}
else
{
lean_object* v___f_1638_; lean_object* v___f_1639_; size_t v___x_1640_; size_t v___x_1641_; lean_object* v___x_1642_; 
v___f_1638_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1638_, 0, v_f_1630_);
v___f_1639_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1639_, 0, v___x_1633_);
lean_closure_set(v___f_1639_, 1, v___f_1638_);
v___x_1640_ = lean_usize_of_nat(v___x_1635_);
v___x_1641_ = ((size_t)0ULL);
v___x_1642_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1633_, v___f_1639_, v_buckets_1634_, v___x_1640_, v___x_1641_, v_init_1631_);
return v___x_1642_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRev(lean_object* v_00_u03b1_1643_, lean_object* v_00_u03b2_1644_, lean_object* v_00_u03b4_1645_, lean_object* v_f_1646_, lean_object* v_init_1647_, lean_object* v_b_1648_){
_start:
{
lean_object* v___x_1649_; lean_object* v_buckets_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; uint8_t v___x_1653_; 
v___x_1649_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_1650_ = lean_ctor_get(v_b_1648_, 1);
lean_inc_ref(v_buckets_1650_);
lean_dec_ref(v_b_1648_);
v___x_1651_ = lean_array_get_size(v_buckets_1650_);
v___x_1652_ = lean_unsigned_to_nat(0u);
v___x_1653_ = lean_nat_dec_lt(v___x_1652_, v___x_1651_);
if (v___x_1653_ == 0)
{
lean_dec_ref(v_buckets_1650_);
lean_dec(v_f_1646_);
return v_init_1647_;
}
else
{
lean_object* v___f_1654_; lean_object* v___f_1655_; size_t v___x_1656_; size_t v___x_1657_; lean_object* v___x_1658_; 
v___f_1654_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1654_, 0, v_f_1646_);
v___f_1655_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1655_, 0, v___x_1649_);
lean_closure_set(v___f_1655_, 1, v___f_1654_);
v___x_1656_ = lean_usize_of_nat(v___x_1651_);
v___x_1657_ = ((size_t)0ULL);
v___x_1658_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1649_, v___f_1655_, v_buckets_1650_, v___x_1656_, v___x_1657_, v_init_1647_);
return v___x_1658_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__0(lean_object* v_f_1659_, lean_object* v_x_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1663_, 0, v___y_1661_);
lean_ctor_set(v___x_1663_, 1, v___y_1662_);
v___x_1664_ = lean_apply_1(v_f_1659_, v___x_1663_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__1(lean_object* v_inst_1665_, lean_object* v___f_1666_, lean_object* v_x_1667_, lean_object* v___y_1668_){
_start:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1669_ = lean_box(0);
v___x_1670_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_1665_, v___f_1666_, v___x_1669_, v___y_1668_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forMUncurried___redArg(lean_object* v_inst_1671_, lean_object* v_f_1672_, lean_object* v_b_1673_){
_start:
{
lean_object* v_toApplicative_1674_; lean_object* v_buckets_1675_; lean_object* v_toPure_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; uint8_t v___x_1680_; 
v_toApplicative_1674_ = lean_ctor_get(v_inst_1671_, 0);
v_buckets_1675_ = lean_ctor_get(v_b_1673_, 1);
lean_inc_ref(v_buckets_1675_);
lean_dec_ref(v_b_1673_);
v_toPure_1676_ = lean_ctor_get(v_toApplicative_1674_, 1);
v___x_1677_ = lean_unsigned_to_nat(0u);
v___x_1678_ = lean_array_get_size(v_buckets_1675_);
v___x_1679_ = lean_box(0);
v___x_1680_ = lean_nat_dec_lt(v___x_1677_, v___x_1678_);
if (v___x_1680_ == 0)
{
lean_object* v___x_1681_; 
lean_inc(v_toPure_1676_);
lean_dec_ref(v_buckets_1675_);
lean_dec(v_f_1672_);
lean_dec_ref(v_inst_1671_);
v___x_1681_ = lean_apply_2(v_toPure_1676_, lean_box(0), v___x_1679_);
return v___x_1681_;
}
else
{
lean_object* v___f_1682_; lean_object* v___f_1683_; size_t v___x_1684_; size_t v___x_1685_; lean_object* v___x_1686_; 
v___f_1682_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1682_, 0, v_f_1672_);
lean_inc_ref(v_inst_1671_);
v___f_1683_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1683_, 0, v_inst_1671_);
lean_closure_set(v___f_1683_, 1, v___f_1682_);
v___x_1684_ = ((size_t)0ULL);
v___x_1685_ = lean_usize_of_nat(v___x_1678_);
v___x_1686_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1671_, v___f_1683_, v_buckets_1675_, v___x_1684_, v___x_1685_, v___x_1679_);
return v___x_1686_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forMUncurried(lean_object* v_00_u03b1_1687_, lean_object* v_m_1688_, lean_object* v_inst_1689_, lean_object* v_00_u03b2_1690_, lean_object* v_f_1691_, lean_object* v_b_1692_){
_start:
{
lean_object* v_toApplicative_1693_; lean_object* v_buckets_1694_; lean_object* v_toPure_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; uint8_t v___x_1699_; 
v_toApplicative_1693_ = lean_ctor_get(v_inst_1689_, 0);
v_buckets_1694_ = lean_ctor_get(v_b_1692_, 1);
lean_inc_ref(v_buckets_1694_);
lean_dec_ref(v_b_1692_);
v_toPure_1695_ = lean_ctor_get(v_toApplicative_1693_, 1);
v___x_1696_ = lean_unsigned_to_nat(0u);
v___x_1697_ = lean_array_get_size(v_buckets_1694_);
v___x_1698_ = lean_box(0);
v___x_1699_ = lean_nat_dec_lt(v___x_1696_, v___x_1697_);
if (v___x_1699_ == 0)
{
lean_object* v___x_1700_; 
lean_inc(v_toPure_1695_);
lean_dec_ref(v_buckets_1694_);
lean_dec(v_f_1691_);
lean_dec_ref(v_inst_1689_);
v___x_1700_ = lean_apply_2(v_toPure_1695_, lean_box(0), v___x_1698_);
return v___x_1700_;
}
else
{
lean_object* v___f_1701_; lean_object* v___f_1702_; size_t v___x_1703_; size_t v___x_1704_; lean_object* v___x_1705_; 
v___f_1701_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1701_, 0, v_f_1691_);
lean_inc_ref(v_inst_1689_);
v___f_1702_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1702_, 0, v_inst_1689_);
lean_closure_set(v___f_1702_, 1, v___f_1701_);
v___x_1703_ = ((size_t)0ULL);
v___x_1704_ = lean_usize_of_nat(v___x_1697_);
v___x_1705_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1689_, v___f_1702_, v_buckets_1694_, v___x_1703_, v___x_1704_, v___x_1698_);
return v___x_1705_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__0(lean_object* v_f_1706_, lean_object* v_a_1707_, lean_object* v_b_1708_, lean_object* v_d_1709_){
_start:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1710_, 0, v_a_1707_);
lean_ctor_set(v___x_1710_, 1, v_b_1708_);
v___x_1711_ = lean_apply_2(v_f_1706_, v___x_1710_, v_d_1709_);
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__1(lean_object* v_inst_1712_, lean_object* v___f_1713_, lean_object* v_a_1714_, lean_object* v_x_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v___x_1717_; 
v___x_1717_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_1712_, v___f_1713_, v_a_1714_, v___y_1716_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forInUncurried___redArg(lean_object* v_inst_1718_, lean_object* v_f_1719_, lean_object* v_init_1720_, lean_object* v_b_1721_){
_start:
{
lean_object* v_buckets_1722_; lean_object* v___f_1723_; lean_object* v___f_1724_; size_t v_sz_1725_; size_t v___x_1726_; lean_object* v___x_1727_; 
v_buckets_1722_ = lean_ctor_get(v_b_1721_, 1);
lean_inc_ref(v_buckets_1722_);
lean_dec_ref(v_b_1721_);
v___f_1723_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1723_, 0, v_f_1719_);
lean_inc_ref(v_inst_1718_);
v___f_1724_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1724_, 0, v_inst_1718_);
lean_closure_set(v___f_1724_, 1, v___f_1723_);
v_sz_1725_ = lean_array_size(v_buckets_1722_);
v___x_1726_ = ((size_t)0ULL);
v___x_1727_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1718_, v_buckets_1722_, v___f_1724_, v_sz_1725_, v___x_1726_, v_init_1720_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forInUncurried(lean_object* v_00_u03b1_1728_, lean_object* v_00_u03b4_1729_, lean_object* v_m_1730_, lean_object* v_inst_1731_, lean_object* v_00_u03b2_1732_, lean_object* v_f_1733_, lean_object* v_init_1734_, lean_object* v_b_1735_){
_start:
{
lean_object* v_buckets_1736_; lean_object* v___f_1737_; lean_object* v___f_1738_; size_t v_sz_1739_; size_t v___x_1740_; lean_object* v___x_1741_; 
v_buckets_1736_ = lean_ctor_get(v_b_1735_, 1);
lean_inc_ref(v_buckets_1736_);
lean_dec_ref(v_b_1735_);
v___f_1737_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1737_, 0, v_f_1733_);
lean_inc_ref(v_inst_1731_);
v___f_1738_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1738_, 0, v_inst_1731_);
lean_closure_set(v___f_1738_, 1, v___f_1737_);
v_sz_1739_ = lean_array_size(v_buckets_1736_);
v___x_1740_ = ((size_t)0ULL);
v___x_1741_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1731_, v_buckets_1736_, v___f_1738_, v_sz_1739_, v___x_1740_, v_init_1734_);
return v___x_1741_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_filterMap___redArg(lean_object* v_f_1742_, lean_object* v_m_1743_){
_start:
{
lean_object* v_buckets_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; uint8_t v___x_1747_; 
v_buckets_1744_ = lean_ctor_get(v_m_1743_, 1);
v___x_1745_ = lean_unsigned_to_nat(0u);
v___x_1746_ = lean_array_get_size(v_buckets_1744_);
v___x_1747_ = lean_nat_dec_lt(v___x_1745_, v___x_1746_);
if (v___x_1747_ == 0)
{
lean_object* v___x_1748_; 
lean_dec_ref(v_m_1743_);
lean_dec_ref(v_f_1742_);
v___x_1748_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_1748_;
}
else
{
lean_object* v___x_1749_; 
v___x_1749_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_1742_, v_m_1743_);
return v___x_1749_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_filterMap(lean_object* v_00_u03b1_1750_, lean_object* v_00_u03b2_1751_, lean_object* v_00_u03b3_1752_, lean_object* v_f_1753_, lean_object* v_m_1754_){
_start:
{
lean_object* v_buckets_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; uint8_t v___x_1758_; 
v_buckets_1755_ = lean_ctor_get(v_m_1754_, 1);
v___x_1756_ = lean_unsigned_to_nat(0u);
v___x_1757_ = lean_array_get_size(v_buckets_1755_);
v___x_1758_ = lean_nat_dec_lt(v___x_1756_, v___x_1757_);
if (v___x_1758_ == 0)
{
lean_object* v___x_1759_; 
lean_dec_ref(v_m_1754_);
lean_dec_ref(v_f_1753_);
v___x_1759_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_1759_;
}
else
{
lean_object* v___x_1760_; 
v___x_1760_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_1753_, v_m_1754_);
return v___x_1760_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_map___redArg(lean_object* v_f_1761_, lean_object* v_m_1762_){
_start:
{
lean_object* v_buckets_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; uint8_t v___x_1766_; 
v_buckets_1763_ = lean_ctor_get(v_m_1762_, 1);
v___x_1764_ = lean_unsigned_to_nat(0u);
v___x_1765_ = lean_array_get_size(v_buckets_1763_);
v___x_1766_ = lean_nat_dec_lt(v___x_1764_, v___x_1765_);
if (v___x_1766_ == 0)
{
lean_object* v___x_1767_; 
lean_dec_ref(v_m_1762_);
lean_dec(v_f_1761_);
v___x_1767_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_1767_;
}
else
{
lean_object* v___x_1768_; 
v___x_1768_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_1761_, v_m_1762_);
return v___x_1768_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_map(lean_object* v_00_u03b1_1769_, lean_object* v_00_u03b2_1770_, lean_object* v_00_u03b3_1771_, lean_object* v_f_1772_, lean_object* v_m_1773_){
_start:
{
lean_object* v_buckets_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; uint8_t v___x_1777_; 
v_buckets_1774_ = lean_ctor_get(v_m_1773_, 1);
v___x_1775_ = lean_unsigned_to_nat(0u);
v___x_1776_ = lean_array_get_size(v_buckets_1774_);
v___x_1777_ = lean_nat_dec_lt(v___x_1775_, v___x_1776_);
if (v___x_1777_ == 0)
{
lean_object* v___x_1778_; 
lean_dec_ref(v_m_1773_);
lean_dec(v_f_1772_);
v___x_1778_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_1778_;
}
else
{
lean_object* v___x_1779_; 
v___x_1779_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_1772_, v_m_1773_);
return v___x_1779_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_filter___redArg(lean_object* v_f_1780_, lean_object* v_m_1781_){
_start:
{
lean_object* v_buckets_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; uint8_t v___x_1785_; 
v_buckets_1782_ = lean_ctor_get(v_m_1781_, 1);
v___x_1783_ = lean_unsigned_to_nat(0u);
v___x_1784_ = lean_array_get_size(v_buckets_1782_);
v___x_1785_ = lean_nat_dec_lt(v___x_1783_, v___x_1784_);
if (v___x_1785_ == 0)
{
lean_object* v___x_1786_; 
lean_dec_ref(v_m_1781_);
lean_dec_ref(v_f_1780_);
v___x_1786_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_1786_;
}
else
{
lean_object* v___x_1787_; 
v___x_1787_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1780_, v_m_1781_);
return v___x_1787_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_filter(lean_object* v_00_u03b1_1788_, lean_object* v_00_u03b2_1789_, lean_object* v_f_1790_, lean_object* v_m_1791_){
_start:
{
lean_object* v_buckets_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; uint8_t v___x_1795_; 
v_buckets_1792_ = lean_ctor_get(v_m_1791_, 1);
v___x_1793_ = lean_unsigned_to_nat(0u);
v___x_1794_ = lean_array_get_size(v_buckets_1792_);
v___x_1795_ = lean_nat_dec_lt(v___x_1793_, v___x_1794_);
if (v___x_1795_ == 0)
{
lean_object* v___x_1796_; 
lean_dec_ref(v_m_1791_);
lean_dec_ref(v_f_1790_);
v___x_1796_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_1796_;
}
else
{
lean_object* v___x_1797_; 
v___x_1797_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1790_, v_m_1791_);
return v___x_1797_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toArray___redArg___lam__0(lean_object* v_x1_1798_, lean_object* v_x2_1799_, lean_object* v_x3_1800_){
_start:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1801_, 0, v_x2_1799_);
lean_ctor_set(v___x_1801_, 1, v_x3_1800_);
v___x_1802_ = lean_array_push(v_x1_1798_, v___x_1801_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toArray___redArg___lam__1(lean_object* v___x_1803_, lean_object* v___f_1804_, lean_object* v_acc_1805_, lean_object* v_l_1806_){
_start:
{
lean_object* v___x_1807_; 
v___x_1807_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1803_, v___f_1804_, v_acc_1805_, v_l_1806_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toArray___redArg(lean_object* v_m_1812_){
_start:
{
lean_object* v_size_1813_; lean_object* v_buckets_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; uint8_t v___x_1819_; 
v_size_1813_ = lean_ctor_get(v_m_1812_, 0);
lean_inc(v_size_1813_);
v_buckets_1814_ = lean_ctor_get(v_m_1812_, 1);
lean_inc_ref(v_buckets_1814_);
lean_dec_ref(v_m_1812_);
v___x_1815_ = lean_mk_empty_array_with_capacity(v_size_1813_);
lean_dec(v_size_1813_);
v___x_1816_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_1817_ = lean_unsigned_to_nat(0u);
v___x_1818_ = lean_array_get_size(v_buckets_1814_);
v___x_1819_ = lean_nat_dec_lt(v___x_1817_, v___x_1818_);
if (v___x_1819_ == 0)
{
lean_dec_ref(v_buckets_1814_);
return v___x_1815_;
}
else
{
lean_object* v___f_1820_; size_t v___x_1821_; size_t v___x_1822_; lean_object* v___x_1823_; 
v___f_1820_ = ((lean_object*)(l_Std_DHashMap_Raw_toArray___redArg___closed__1));
v___x_1821_ = ((size_t)0ULL);
v___x_1822_ = lean_usize_of_nat(v___x_1818_);
v___x_1823_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1816_, v___f_1820_, v_buckets_1814_, v___x_1821_, v___x_1822_, v___x_1815_);
return v___x_1823_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toArray(lean_object* v_00_u03b1_1824_, lean_object* v_00_u03b2_1825_, lean_object* v_m_1826_){
_start:
{
lean_object* v_size_1827_; lean_object* v_buckets_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; uint8_t v___x_1833_; 
v_size_1827_ = lean_ctor_get(v_m_1826_, 0);
lean_inc(v_size_1827_);
v_buckets_1828_ = lean_ctor_get(v_m_1826_, 1);
lean_inc_ref(v_buckets_1828_);
lean_dec_ref(v_m_1826_);
v___x_1829_ = lean_mk_empty_array_with_capacity(v_size_1827_);
lean_dec(v_size_1827_);
v___x_1830_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_1831_ = lean_unsigned_to_nat(0u);
v___x_1832_ = lean_array_get_size(v_buckets_1828_);
v___x_1833_ = lean_nat_dec_lt(v___x_1831_, v___x_1832_);
if (v___x_1833_ == 0)
{
lean_dec_ref(v_buckets_1828_);
return v___x_1829_;
}
else
{
lean_object* v___f_1834_; size_t v___x_1835_; size_t v___x_1836_; lean_object* v___x_1837_; 
v___f_1834_ = ((lean_object*)(l_Std_DHashMap_Raw_toArray___redArg___closed__1));
v___x_1835_ = ((size_t)0ULL);
v___x_1836_ = lean_usize_of_nat(v___x_1832_);
v___x_1837_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1830_, v___f_1834_, v_buckets_1828_, v___x_1835_, v___x_1836_, v___x_1829_);
return v___x_1837_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toArray___redArg___lam__0(lean_object* v_x1_1838_, lean_object* v_x2_1839_, lean_object* v_x3_1840_){
_start:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1841_, 0, v_x2_1839_);
lean_ctor_set(v___x_1841_, 1, v_x3_1840_);
v___x_1842_ = lean_array_push(v_x1_1838_, v___x_1841_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toArray___redArg___lam__1(lean_object* v___x_1843_, lean_object* v___f_1844_, lean_object* v_acc_1845_, lean_object* v_l_1846_){
_start:
{
lean_object* v___x_1847_; 
v___x_1847_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1843_, v___f_1844_, v_acc_1845_, v_l_1846_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toArray___redArg(lean_object* v_m_1852_){
_start:
{
lean_object* v_size_1853_; lean_object* v_buckets_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; uint8_t v___x_1859_; 
v_size_1853_ = lean_ctor_get(v_m_1852_, 0);
lean_inc(v_size_1853_);
v_buckets_1854_ = lean_ctor_get(v_m_1852_, 1);
lean_inc_ref(v_buckets_1854_);
lean_dec_ref(v_m_1852_);
v___x_1855_ = lean_mk_empty_array_with_capacity(v_size_1853_);
lean_dec(v_size_1853_);
v___x_1856_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_1857_ = lean_unsigned_to_nat(0u);
v___x_1858_ = lean_array_get_size(v_buckets_1854_);
v___x_1859_ = lean_nat_dec_lt(v___x_1857_, v___x_1858_);
if (v___x_1859_ == 0)
{
lean_dec_ref(v_buckets_1854_);
return v___x_1855_;
}
else
{
lean_object* v___f_1860_; size_t v___x_1861_; size_t v___x_1862_; lean_object* v___x_1863_; 
v___f_1860_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_toArray___redArg___closed__1));
v___x_1861_ = ((size_t)0ULL);
v___x_1862_ = lean_usize_of_nat(v___x_1858_);
v___x_1863_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1856_, v___f_1860_, v_buckets_1854_, v___x_1861_, v___x_1862_, v___x_1855_);
return v___x_1863_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toArray(lean_object* v_00_u03b1_1864_, lean_object* v_00_u03b2_1865_, lean_object* v_m_1866_){
_start:
{
lean_object* v_size_1867_; lean_object* v_buckets_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; uint8_t v___x_1873_; 
v_size_1867_ = lean_ctor_get(v_m_1866_, 0);
lean_inc(v_size_1867_);
v_buckets_1868_ = lean_ctor_get(v_m_1866_, 1);
lean_inc_ref(v_buckets_1868_);
lean_dec_ref(v_m_1866_);
v___x_1869_ = lean_mk_empty_array_with_capacity(v_size_1867_);
lean_dec(v_size_1867_);
v___x_1870_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_1871_ = lean_unsigned_to_nat(0u);
v___x_1872_ = lean_array_get_size(v_buckets_1868_);
v___x_1873_ = lean_nat_dec_lt(v___x_1871_, v___x_1872_);
if (v___x_1873_ == 0)
{
lean_dec_ref(v_buckets_1868_);
return v___x_1869_;
}
else
{
lean_object* v___f_1874_; size_t v___x_1875_; size_t v___x_1876_; lean_object* v___x_1877_; 
v___f_1874_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_toArray___redArg___closed__1));
v___x_1875_ = ((size_t)0ULL);
v___x_1876_ = lean_usize_of_nat(v___x_1872_);
v___x_1877_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1870_, v___f_1874_, v_buckets_1868_, v___x_1875_, v___x_1876_, v___x_1869_);
return v___x_1877_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keysArray___redArg___lam__0(lean_object* v_x1_1878_, lean_object* v_x2_1879_, lean_object* v_x3_1880_){
_start:
{
lean_object* v___x_1881_; 
v___x_1881_ = lean_array_push(v_x1_1878_, v_x2_1879_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keysArray___redArg___lam__0___boxed(lean_object* v_x1_1882_, lean_object* v_x2_1883_, lean_object* v_x3_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l_Std_DHashMap_Raw_keysArray___redArg___lam__0(v_x1_1882_, v_x2_1883_, v_x3_1884_);
lean_dec(v_x3_1884_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keysArray___redArg___lam__1(lean_object* v___x_1886_, lean_object* v___f_1887_, lean_object* v_acc_1888_, lean_object* v_l_1889_){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1886_, v___f_1887_, v_acc_1888_, v_l_1889_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keysArray___redArg(lean_object* v_m_1895_){
_start:
{
lean_object* v_size_1896_; lean_object* v_buckets_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; uint8_t v___x_1902_; 
v_size_1896_ = lean_ctor_get(v_m_1895_, 0);
lean_inc(v_size_1896_);
v_buckets_1897_ = lean_ctor_get(v_m_1895_, 1);
lean_inc_ref(v_buckets_1897_);
lean_dec_ref(v_m_1895_);
v___x_1898_ = lean_mk_empty_array_with_capacity(v_size_1896_);
lean_dec(v_size_1896_);
v___x_1899_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_1900_ = lean_unsigned_to_nat(0u);
v___x_1901_ = lean_array_get_size(v_buckets_1897_);
v___x_1902_ = lean_nat_dec_lt(v___x_1900_, v___x_1901_);
if (v___x_1902_ == 0)
{
lean_dec_ref(v_buckets_1897_);
return v___x_1898_;
}
else
{
lean_object* v___f_1903_; size_t v___x_1904_; size_t v___x_1905_; lean_object* v___x_1906_; 
v___f_1903_ = ((lean_object*)(l_Std_DHashMap_Raw_keysArray___redArg___closed__1));
v___x_1904_ = ((size_t)0ULL);
v___x_1905_ = lean_usize_of_nat(v___x_1901_);
v___x_1906_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1899_, v___f_1903_, v_buckets_1897_, v___x_1904_, v___x_1905_, v___x_1898_);
return v___x_1906_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keysArray(lean_object* v_00_u03b1_1907_, lean_object* v_00_u03b2_1908_, lean_object* v_m_1909_){
_start:
{
lean_object* v_size_1910_; lean_object* v_buckets_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; uint8_t v___x_1916_; 
v_size_1910_ = lean_ctor_get(v_m_1909_, 0);
lean_inc(v_size_1910_);
v_buckets_1911_ = lean_ctor_get(v_m_1909_, 1);
lean_inc_ref(v_buckets_1911_);
lean_dec_ref(v_m_1909_);
v___x_1912_ = lean_mk_empty_array_with_capacity(v_size_1910_);
lean_dec(v_size_1910_);
v___x_1913_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_1914_ = lean_unsigned_to_nat(0u);
v___x_1915_ = lean_array_get_size(v_buckets_1911_);
v___x_1916_ = lean_nat_dec_lt(v___x_1914_, v___x_1915_);
if (v___x_1916_ == 0)
{
lean_dec_ref(v_buckets_1911_);
return v___x_1912_;
}
else
{
lean_object* v___f_1917_; size_t v___x_1918_; size_t v___x_1919_; lean_object* v___x_1920_; 
v___f_1917_ = ((lean_object*)(l_Std_DHashMap_Raw_keysArray___redArg___closed__1));
v___x_1918_ = ((size_t)0ULL);
v___x_1919_ = lean_usize_of_nat(v___x_1915_);
v___x_1920_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1913_, v___f_1917_, v_buckets_1911_, v___x_1918_, v___x_1919_, v___x_1912_);
return v___x_1920_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_union___redArg___lam__0(lean_object* v_inst_1921_, lean_object* v_inst_1922_, lean_object* v_a_1923_, lean_object* v_b_1924_, lean_object* v_acc_1925_){
_start:
{
lean_object* v_r_1926_; lean_object* v___x_1927_; 
v_r_1926_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_1921_, v_inst_1922_, v_acc_1925_, v_a_1923_, v_b_1924_);
v___x_1927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1927_, 0, v_r_1926_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_union___redArg___lam__1(lean_object* v___x_1928_, lean_object* v___f_1929_, lean_object* v_a_1930_, lean_object* v_x_1931_, lean_object* v___y_1932_){
_start:
{
lean_object* v___x_1933_; 
v___x_1933_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1928_, v___f_1929_, v_a_1930_, v___y_1932_);
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_union___redArg(lean_object* v_inst_1936_, lean_object* v_inst_1937_, lean_object* v_m_u2081_1938_, lean_object* v_m_u2082_1939_){
_start:
{
lean_object* v_size_1940_; lean_object* v_buckets_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; uint8_t v___x_1944_; 
v_size_1940_ = lean_ctor_get(v_m_u2081_1938_, 0);
v_buckets_1941_ = lean_ctor_get(v_m_u2081_1938_, 1);
v___x_1942_ = lean_unsigned_to_nat(0u);
v___x_1943_ = lean_array_get_size(v_buckets_1941_);
v___x_1944_ = lean_nat_dec_lt(v___x_1942_, v___x_1943_);
if (v___x_1944_ == 0)
{
lean_dec_ref(v_m_u2081_1938_);
lean_dec_ref(v_inst_1937_);
lean_dec_ref(v_inst_1936_);
return v_m_u2082_1939_;
}
else
{
lean_object* v_size_1945_; lean_object* v_buckets_1946_; lean_object* v___x_1947_; uint8_t v___x_1948_; 
v_size_1945_ = lean_ctor_get(v_m_u2082_1939_, 0);
v_buckets_1946_ = lean_ctor_get(v_m_u2082_1939_, 1);
v___x_1947_ = lean_array_get_size(v_buckets_1946_);
v___x_1948_ = lean_nat_dec_lt(v___x_1942_, v___x_1947_);
if (v___x_1948_ == 0)
{
lean_dec_ref(v_m_u2082_1939_);
lean_dec_ref(v_inst_1937_);
lean_dec_ref(v_inst_1936_);
return v_m_u2081_1938_;
}
else
{
lean_object* v___x_1949_; uint8_t v___x_1950_; 
v___x_1949_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_1950_ = lean_nat_dec_le(v_size_1940_, v_size_1945_);
if (v___x_1950_ == 0)
{
lean_object* v___f_1951_; lean_object* v___x_1952_; 
v___f_1951_ = ((lean_object*)(l_Std_DHashMap_Raw_union___redArg___closed__0));
v___x_1952_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1951_, v_inst_1936_, v_inst_1937_, v_m_u2081_1938_, v_m_u2082_1939_);
return v___x_1952_;
}
else
{
lean_object* v___f_1953_; lean_object* v___f_1954_; size_t v_sz_1955_; size_t v___x_1956_; lean_object* v___x_1957_; 
lean_inc_ref(v_buckets_1941_);
lean_dec_ref(v_m_u2081_1938_);
v___f_1953_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1953_, 0, v_inst_1936_);
lean_closure_set(v___f_1953_, 1, v_inst_1937_);
v___f_1954_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1954_, 0, v___x_1949_);
lean_closure_set(v___f_1954_, 1, v___f_1953_);
v_sz_1955_ = lean_array_size(v_buckets_1941_);
v___x_1956_ = ((size_t)0ULL);
v___x_1957_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1949_, v_buckets_1941_, v___f_1954_, v_sz_1955_, v___x_1956_, v_m_u2082_1939_);
return v___x_1957_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_union(lean_object* v_00_u03b1_1958_, lean_object* v_00_u03b2_1959_, lean_object* v_inst_1960_, lean_object* v_inst_1961_, lean_object* v_m_u2081_1962_, lean_object* v_m_u2082_1963_){
_start:
{
lean_object* v_size_1964_; lean_object* v_buckets_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; uint8_t v___x_1968_; 
v_size_1964_ = lean_ctor_get(v_m_u2081_1962_, 0);
v_buckets_1965_ = lean_ctor_get(v_m_u2081_1962_, 1);
v___x_1966_ = lean_unsigned_to_nat(0u);
v___x_1967_ = lean_array_get_size(v_buckets_1965_);
v___x_1968_ = lean_nat_dec_lt(v___x_1966_, v___x_1967_);
if (v___x_1968_ == 0)
{
lean_dec_ref(v_m_u2081_1962_);
lean_dec_ref(v_inst_1961_);
lean_dec_ref(v_inst_1960_);
return v_m_u2082_1963_;
}
else
{
lean_object* v_size_1969_; lean_object* v_buckets_1970_; lean_object* v___x_1971_; uint8_t v___x_1972_; 
v_size_1969_ = lean_ctor_get(v_m_u2082_1963_, 0);
v_buckets_1970_ = lean_ctor_get(v_m_u2082_1963_, 1);
v___x_1971_ = lean_array_get_size(v_buckets_1970_);
v___x_1972_ = lean_nat_dec_lt(v___x_1966_, v___x_1971_);
if (v___x_1972_ == 0)
{
lean_dec_ref(v_m_u2082_1963_);
lean_dec_ref(v_inst_1961_);
lean_dec_ref(v_inst_1960_);
return v_m_u2081_1962_;
}
else
{
lean_object* v___x_1973_; uint8_t v___x_1974_; 
v___x_1973_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_1974_ = lean_nat_dec_le(v_size_1964_, v_size_1969_);
if (v___x_1974_ == 0)
{
lean_object* v___f_1975_; lean_object* v___x_1976_; 
v___f_1975_ = ((lean_object*)(l_Std_DHashMap_Raw_union___redArg___closed__0));
v___x_1976_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1975_, v_inst_1960_, v_inst_1961_, v_m_u2081_1962_, v_m_u2082_1963_);
return v___x_1976_;
}
else
{
lean_object* v___f_1977_; lean_object* v___f_1978_; size_t v_sz_1979_; size_t v___x_1980_; lean_object* v___x_1981_; 
lean_inc_ref(v_buckets_1965_);
lean_dec_ref(v_m_u2081_1962_);
v___f_1977_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1977_, 0, v_inst_1960_);
lean_closure_set(v___f_1977_, 1, v_inst_1961_);
v___f_1978_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1978_, 0, v___x_1973_);
lean_closure_set(v___f_1978_, 1, v___f_1977_);
v_sz_1979_ = lean_array_size(v_buckets_1965_);
v___x_1980_ = ((size_t)0ULL);
v___x_1981_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1973_, v_buckets_1965_, v___f_1978_, v_sz_1979_, v___x_1980_, v_m_u2082_1963_);
return v___x_1981_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instUnionOfBEqOfHashable___redArg(lean_object* v_inst_1982_, lean_object* v_inst_1983_){
_start:
{
lean_object* v___x_1984_; 
v___x_1984_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_union), 6, 4);
lean_closure_set(v___x_1984_, 0, lean_box(0));
lean_closure_set(v___x_1984_, 1, lean_box(0));
lean_closure_set(v___x_1984_, 2, v_inst_1982_);
lean_closure_set(v___x_1984_, 3, v_inst_1983_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instUnionOfBEqOfHashable(lean_object* v_00_u03b1_1985_, lean_object* v_00_u03b2_1986_, lean_object* v_inst_1987_, lean_object* v_inst_1988_){
_start:
{
lean_object* v___x_1989_; 
v___x_1989_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_union), 6, 4);
lean_closure_set(v___x_1989_, 0, lean_box(0));
lean_closure_set(v___x_1989_, 1, lean_box(0));
lean_closure_set(v___x_1989_, 2, v_inst_1987_);
lean_closure_set(v___x_1989_, 3, v_inst_1988_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_inter___redArg(lean_object* v_inst_1990_, lean_object* v_inst_1991_, lean_object* v_m_u2081_1992_, lean_object* v_m_u2082_1993_){
_start:
{
lean_object* v_buckets_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; uint8_t v___x_1997_; 
v_buckets_1994_ = lean_ctor_get(v_m_u2081_1992_, 1);
v___x_1995_ = lean_unsigned_to_nat(0u);
v___x_1996_ = lean_array_get_size(v_buckets_1994_);
v___x_1997_ = lean_nat_dec_lt(v___x_1995_, v___x_1996_);
if (v___x_1997_ == 0)
{
lean_dec_ref(v_m_u2081_1992_);
lean_dec_ref(v_inst_1991_);
lean_dec_ref(v_inst_1990_);
return v_m_u2082_1993_;
}
else
{
lean_object* v_buckets_1998_; lean_object* v___x_1999_; uint8_t v___x_2000_; 
v_buckets_1998_ = lean_ctor_get(v_m_u2082_1993_, 1);
v___x_1999_ = lean_array_get_size(v_buckets_1998_);
v___x_2000_ = lean_nat_dec_lt(v___x_1995_, v___x_1999_);
if (v___x_2000_ == 0)
{
lean_dec_ref(v_m_u2082_1993_);
lean_dec_ref(v_inst_1991_);
lean_dec_ref(v_inst_1990_);
return v_m_u2081_1992_;
}
else
{
lean_object* v___x_2001_; 
v___x_2001_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1990_, v_inst_1991_, v_m_u2081_1992_, v_m_u2082_1993_);
return v___x_2001_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_inter(lean_object* v_00_u03b1_2002_, lean_object* v_00_u03b2_2003_, lean_object* v_inst_2004_, lean_object* v_inst_2005_, lean_object* v_m_u2081_2006_, lean_object* v_m_u2082_2007_){
_start:
{
lean_object* v_buckets_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; uint8_t v___x_2011_; 
v_buckets_2008_ = lean_ctor_get(v_m_u2081_2006_, 1);
v___x_2009_ = lean_unsigned_to_nat(0u);
v___x_2010_ = lean_array_get_size(v_buckets_2008_);
v___x_2011_ = lean_nat_dec_lt(v___x_2009_, v___x_2010_);
if (v___x_2011_ == 0)
{
lean_dec_ref(v_m_u2081_2006_);
lean_dec_ref(v_inst_2005_);
lean_dec_ref(v_inst_2004_);
return v_m_u2082_2007_;
}
else
{
lean_object* v_buckets_2012_; lean_object* v___x_2013_; uint8_t v___x_2014_; 
v_buckets_2012_ = lean_ctor_get(v_m_u2082_2007_, 1);
v___x_2013_ = lean_array_get_size(v_buckets_2012_);
v___x_2014_ = lean_nat_dec_lt(v___x_2009_, v___x_2013_);
if (v___x_2014_ == 0)
{
lean_dec_ref(v_m_u2082_2007_);
lean_dec_ref(v_inst_2005_);
lean_dec_ref(v_inst_2004_);
return v_m_u2081_2006_;
}
else
{
lean_object* v___x_2015_; 
v___x_2015_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_2004_, v_inst_2005_, v_m_u2081_2006_, v_m_u2082_2007_);
return v___x_2015_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInterOfBEqOfHashable___redArg(lean_object* v_inst_2016_, lean_object* v_inst_2017_){
_start:
{
lean_object* v___x_2018_; 
v___x_2018_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_inter), 6, 4);
lean_closure_set(v___x_2018_, 0, lean_box(0));
lean_closure_set(v___x_2018_, 1, lean_box(0));
lean_closure_set(v___x_2018_, 2, v_inst_2016_);
lean_closure_set(v___x_2018_, 3, v_inst_2017_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInterOfBEqOfHashable(lean_object* v_00_u03b1_2019_, lean_object* v_00_u03b2_2020_, lean_object* v_inst_2021_, lean_object* v_inst_2022_){
_start:
{
lean_object* v___x_2023_; 
v___x_2023_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_inter), 6, 4);
lean_closure_set(v___x_2023_, 0, lean_box(0));
lean_closure_set(v___x_2023_, 1, lean_box(0));
lean_closure_set(v___x_2023_, 2, v_inst_2021_);
lean_closure_set(v___x_2023_, 3, v_inst_2022_);
return v___x_2023_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_beq___redArg(lean_object* v_inst_2024_, lean_object* v_inst_2025_, lean_object* v_inst_2026_, lean_object* v_m_u2081_2027_, lean_object* v_m_u2082_2028_){
_start:
{
uint8_t v___y_2030_; lean_object* v_buckets_2032_; lean_object* v_buckets_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; uint8_t v___x_2036_; 
v_buckets_2032_ = lean_ctor_get(v_m_u2081_2027_, 1);
v_buckets_2033_ = lean_ctor_get(v_m_u2082_2028_, 1);
v___x_2034_ = lean_unsigned_to_nat(0u);
v___x_2035_ = lean_array_get_size(v_buckets_2032_);
v___x_2036_ = lean_nat_dec_lt(v___x_2034_, v___x_2035_);
if (v___x_2036_ == 0)
{
v___y_2030_ = v___x_2036_;
goto v___jp_2029_;
}
else
{
lean_object* v___x_2037_; uint8_t v___x_2038_; 
v___x_2037_ = lean_array_get_size(v_buckets_2033_);
v___x_2038_ = lean_nat_dec_lt(v___x_2034_, v___x_2037_);
v___y_2030_ = v___x_2038_;
goto v___jp_2029_;
}
v___jp_2029_:
{
if (v___y_2030_ == 0)
{
lean_dec_ref(v_m_u2082_2028_);
lean_dec_ref(v_m_u2081_2027_);
lean_dec_ref(v_inst_2026_);
lean_dec_ref(v_inst_2025_);
lean_dec_ref(v_inst_2024_);
return v___y_2030_;
}
else
{
uint8_t v___x_2031_; 
v___x_2031_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(v_inst_2024_, v_inst_2025_, v_inst_2026_, v_m_u2081_2027_, v_m_u2082_2028_);
return v___x_2031_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_beq___redArg___boxed(lean_object* v_inst_2039_, lean_object* v_inst_2040_, lean_object* v_inst_2041_, lean_object* v_m_u2081_2042_, lean_object* v_m_u2082_2043_){
_start:
{
uint8_t v_res_2044_; lean_object* v_r_2045_; 
v_res_2044_ = l_Std_DHashMap_Raw_beq___redArg(v_inst_2039_, v_inst_2040_, v_inst_2041_, v_m_u2081_2042_, v_m_u2082_2043_);
v_r_2045_ = lean_box(v_res_2044_);
return v_r_2045_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_beq(lean_object* v_00_u03b1_2046_, lean_object* v_00_u03b2_2047_, lean_object* v_inst_2048_, lean_object* v_inst_2049_, lean_object* v_inst_2050_, lean_object* v_inst_2051_, lean_object* v_m_u2081_2052_, lean_object* v_m_u2082_2053_){
_start:
{
uint8_t v___x_2054_; 
v___x_2054_ = l_Std_DHashMap_Raw_beq___redArg(v_inst_2048_, v_inst_2049_, v_inst_2051_, v_m_u2081_2052_, v_m_u2082_2053_);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_beq___boxed(lean_object* v_00_u03b1_2055_, lean_object* v_00_u03b2_2056_, lean_object* v_inst_2057_, lean_object* v_inst_2058_, lean_object* v_inst_2059_, lean_object* v_inst_2060_, lean_object* v_m_u2081_2061_, lean_object* v_m_u2082_2062_){
_start:
{
uint8_t v_res_2063_; lean_object* v_r_2064_; 
v_res_2063_ = l_Std_DHashMap_Raw_beq(v_00_u03b1_2055_, v_00_u03b2_2056_, v_inst_2057_, v_inst_2058_, v_inst_2059_, v_inst_2060_, v_m_u2081_2061_, v_m_u2082_2062_);
v_r_2064_ = lean_box(v_res_2063_);
return v_r_2064_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instBEqOfHashableOfLawfulBEq___redArg(lean_object* v_inst_2065_, lean_object* v_inst_2066_, lean_object* v_inst_2067_){
_start:
{
lean_object* v___x_2068_; 
v___x_2068_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_beq___boxed), 8, 6);
lean_closure_set(v___x_2068_, 0, lean_box(0));
lean_closure_set(v___x_2068_, 1, lean_box(0));
lean_closure_set(v___x_2068_, 2, v_inst_2065_);
lean_closure_set(v___x_2068_, 3, v_inst_2066_);
lean_closure_set(v___x_2068_, 4, lean_box(0));
lean_closure_set(v___x_2068_, 5, v_inst_2067_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instBEqOfHashableOfLawfulBEq(lean_object* v_00_u03b1_2069_, lean_object* v_00_u03b2_2070_, lean_object* v_inst_2071_, lean_object* v_inst_2072_, lean_object* v_inst_2073_, lean_object* v_inst_2074_){
_start:
{
lean_object* v___x_2075_; 
v___x_2075_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_beq___boxed), 8, 6);
lean_closure_set(v___x_2075_, 0, lean_box(0));
lean_closure_set(v___x_2075_, 1, lean_box(0));
lean_closure_set(v___x_2075_, 2, v_inst_2071_);
lean_closure_set(v___x_2075_, 3, v_inst_2072_);
lean_closure_set(v___x_2075_, 4, lean_box(0));
lean_closure_set(v___x_2075_, 5, v_inst_2074_);
return v___x_2075_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_Const_beq___redArg(lean_object* v_inst_2076_, lean_object* v_inst_2077_, lean_object* v_inst_2078_, lean_object* v_m_u2081_2079_, lean_object* v_m_u2082_2080_){
_start:
{
uint8_t v___y_2082_; lean_object* v_buckets_2084_; lean_object* v_buckets_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; uint8_t v___x_2088_; 
v_buckets_2084_ = lean_ctor_get(v_m_u2081_2079_, 1);
v_buckets_2085_ = lean_ctor_get(v_m_u2082_2080_, 1);
v___x_2086_ = lean_unsigned_to_nat(0u);
v___x_2087_ = lean_array_get_size(v_buckets_2084_);
v___x_2088_ = lean_nat_dec_lt(v___x_2086_, v___x_2087_);
if (v___x_2088_ == 0)
{
v___y_2082_ = v___x_2088_;
goto v___jp_2081_;
}
else
{
lean_object* v___x_2089_; uint8_t v___x_2090_; 
v___x_2089_ = lean_array_get_size(v_buckets_2085_);
v___x_2090_ = lean_nat_dec_lt(v___x_2086_, v___x_2089_);
v___y_2082_ = v___x_2090_;
goto v___jp_2081_;
}
v___jp_2081_:
{
if (v___y_2082_ == 0)
{
lean_dec_ref(v_m_u2082_2080_);
lean_dec_ref(v_m_u2081_2079_);
lean_dec_ref(v_inst_2078_);
lean_dec_ref(v_inst_2077_);
lean_dec_ref(v_inst_2076_);
return v___y_2082_;
}
else
{
uint8_t v___x_2083_; 
v___x_2083_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_inst_2076_, v_inst_2077_, v_inst_2078_, v_m_u2081_2079_, v_m_u2082_2080_);
return v___x_2083_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_beq___redArg___boxed(lean_object* v_inst_2091_, lean_object* v_inst_2092_, lean_object* v_inst_2093_, lean_object* v_m_u2081_2094_, lean_object* v_m_u2082_2095_){
_start:
{
uint8_t v_res_2096_; lean_object* v_r_2097_; 
v_res_2096_ = l_Std_DHashMap_Raw_Const_beq___redArg(v_inst_2091_, v_inst_2092_, v_inst_2093_, v_m_u2081_2094_, v_m_u2082_2095_);
v_r_2097_ = lean_box(v_res_2096_);
return v_r_2097_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_Const_beq(lean_object* v_00_u03b1_2098_, lean_object* v_00_u03b2_2099_, lean_object* v_inst_2100_, lean_object* v_inst_2101_, lean_object* v_inst_2102_, lean_object* v_m_u2081_2103_, lean_object* v_m_u2082_2104_){
_start:
{
uint8_t v___x_2105_; 
v___x_2105_ = l_Std_DHashMap_Raw_Const_beq___redArg(v_inst_2100_, v_inst_2101_, v_inst_2102_, v_m_u2081_2103_, v_m_u2082_2104_);
return v___x_2105_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_beq___boxed(lean_object* v_00_u03b1_2106_, lean_object* v_00_u03b2_2107_, lean_object* v_inst_2108_, lean_object* v_inst_2109_, lean_object* v_inst_2110_, lean_object* v_m_u2081_2111_, lean_object* v_m_u2082_2112_){
_start:
{
uint8_t v_res_2113_; lean_object* v_r_2114_; 
v_res_2113_ = l_Std_DHashMap_Raw_Const_beq(v_00_u03b1_2106_, v_00_u03b2_2107_, v_inst_2108_, v_inst_2109_, v_inst_2110_, v_m_u2081_2111_, v_m_u2082_2112_);
v_r_2114_ = lean_box(v_res_2113_);
return v_r_2114_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_diff___redArg___lam__0(lean_object* v_inst_2115_, lean_object* v_inst_2116_, lean_object* v_m_u2082_2117_, uint8_t v___x_2118_, lean_object* v_k_2119_, lean_object* v_x_2120_){
_start:
{
uint8_t v___x_2121_; 
v___x_2121_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_2115_, v_inst_2116_, v_m_u2082_2117_, v_k_2119_);
if (v___x_2121_ == 0)
{
return v___x_2118_;
}
else
{
uint8_t v___x_2122_; 
v___x_2122_ = 0;
return v___x_2122_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_diff___redArg___lam__0___boxed(lean_object* v_inst_2123_, lean_object* v_inst_2124_, lean_object* v_m_u2082_2125_, lean_object* v___x_2126_, lean_object* v_k_2127_, lean_object* v_x_2128_){
_start:
{
uint8_t v___x_92__boxed_2129_; uint8_t v_res_2130_; lean_object* v_r_2131_; 
v___x_92__boxed_2129_ = lean_unbox(v___x_2126_);
v_res_2130_ = l_Std_DHashMap_Raw_diff___redArg___lam__0(v_inst_2123_, v_inst_2124_, v_m_u2082_2125_, v___x_92__boxed_2129_, v_k_2127_, v_x_2128_);
lean_dec(v_x_2128_);
lean_dec_ref(v_m_u2082_2125_);
v_r_2131_ = lean_box(v_res_2130_);
return v_r_2131_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_diff___redArg(lean_object* v_inst_2132_, lean_object* v_inst_2133_, lean_object* v_m_u2081_2134_, lean_object* v_m_u2082_2135_){
_start:
{
lean_object* v_size_2136_; lean_object* v_buckets_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; uint8_t v___x_2140_; 
v_size_2136_ = lean_ctor_get(v_m_u2081_2134_, 0);
v_buckets_2137_ = lean_ctor_get(v_m_u2081_2134_, 1);
v___x_2138_ = lean_unsigned_to_nat(0u);
v___x_2139_ = lean_array_get_size(v_buckets_2137_);
v___x_2140_ = lean_nat_dec_lt(v___x_2138_, v___x_2139_);
if (v___x_2140_ == 0)
{
lean_dec_ref(v_m_u2081_2134_);
lean_dec_ref(v_inst_2133_);
lean_dec_ref(v_inst_2132_);
return v_m_u2082_2135_;
}
else
{
lean_object* v_size_2141_; lean_object* v_buckets_2142_; lean_object* v___x_2143_; uint8_t v___x_2144_; 
v_size_2141_ = lean_ctor_get(v_m_u2082_2135_, 0);
v_buckets_2142_ = lean_ctor_get(v_m_u2082_2135_, 1);
v___x_2143_ = lean_array_get_size(v_buckets_2142_);
v___x_2144_ = lean_nat_dec_lt(v___x_2138_, v___x_2143_);
if (v___x_2144_ == 0)
{
lean_dec_ref(v_m_u2082_2135_);
lean_dec_ref(v_inst_2133_);
lean_dec_ref(v_inst_2132_);
return v_m_u2081_2134_;
}
else
{
uint8_t v___x_2145_; 
v___x_2145_ = lean_nat_dec_le(v_size_2136_, v_size_2141_);
if (v___x_2145_ == 0)
{
lean_object* v___f_2146_; lean_object* v___x_2147_; 
v___f_2146_ = ((lean_object*)(l_Std_DHashMap_Raw_union___redArg___closed__0));
v___x_2147_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_2146_, v_inst_2132_, v_inst_2133_, v_m_u2081_2134_, v_m_u2082_2135_);
return v___x_2147_;
}
else
{
lean_object* v___x_2148_; lean_object* v___f_2149_; lean_object* v___x_2150_; 
v___x_2148_ = lean_box(v___x_2145_);
v___f_2149_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_2149_, 0, v_inst_2132_);
lean_closure_set(v___f_2149_, 1, v_inst_2133_);
lean_closure_set(v___f_2149_, 2, v_m_u2082_2135_);
lean_closure_set(v___f_2149_, 3, v___x_2148_);
v___x_2150_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_2149_, v_m_u2081_2134_);
return v___x_2150_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_diff(lean_object* v_00_u03b1_2151_, lean_object* v_00_u03b2_2152_, lean_object* v_inst_2153_, lean_object* v_inst_2154_, lean_object* v_m_u2081_2155_, lean_object* v_m_u2082_2156_){
_start:
{
lean_object* v_size_2157_; lean_object* v_buckets_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; uint8_t v___x_2161_; 
v_size_2157_ = lean_ctor_get(v_m_u2081_2155_, 0);
v_buckets_2158_ = lean_ctor_get(v_m_u2081_2155_, 1);
v___x_2159_ = lean_unsigned_to_nat(0u);
v___x_2160_ = lean_array_get_size(v_buckets_2158_);
v___x_2161_ = lean_nat_dec_lt(v___x_2159_, v___x_2160_);
if (v___x_2161_ == 0)
{
lean_dec_ref(v_m_u2081_2155_);
lean_dec_ref(v_inst_2154_);
lean_dec_ref(v_inst_2153_);
return v_m_u2082_2156_;
}
else
{
lean_object* v_size_2162_; lean_object* v_buckets_2163_; lean_object* v___x_2164_; uint8_t v___x_2165_; 
v_size_2162_ = lean_ctor_get(v_m_u2082_2156_, 0);
v_buckets_2163_ = lean_ctor_get(v_m_u2082_2156_, 1);
v___x_2164_ = lean_array_get_size(v_buckets_2163_);
v___x_2165_ = lean_nat_dec_lt(v___x_2159_, v___x_2164_);
if (v___x_2165_ == 0)
{
lean_dec_ref(v_m_u2082_2156_);
lean_dec_ref(v_inst_2154_);
lean_dec_ref(v_inst_2153_);
return v_m_u2081_2155_;
}
else
{
uint8_t v___x_2166_; 
v___x_2166_ = lean_nat_dec_le(v_size_2157_, v_size_2162_);
if (v___x_2166_ == 0)
{
lean_object* v___f_2167_; lean_object* v___x_2168_; 
v___f_2167_ = ((lean_object*)(l_Std_DHashMap_Raw_union___redArg___closed__0));
v___x_2168_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_2167_, v_inst_2153_, v_inst_2154_, v_m_u2081_2155_, v_m_u2082_2156_);
return v___x_2168_;
}
else
{
lean_object* v___x_2169_; lean_object* v___f_2170_; lean_object* v___x_2171_; 
v___x_2169_ = lean_box(v___x_2166_);
v___f_2170_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_2170_, 0, v_inst_2153_);
lean_closure_set(v___f_2170_, 1, v_inst_2154_);
lean_closure_set(v___f_2170_, 2, v_m_u2082_2156_);
lean_closure_set(v___f_2170_, 3, v___x_2169_);
v___x_2171_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_2170_, v_m_u2081_2155_);
return v___x_2171_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instSDiffOfBEqOfHashable___redArg(lean_object* v_inst_2172_, lean_object* v_inst_2173_){
_start:
{
lean_object* v___x_2174_; 
v___x_2174_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_diff), 6, 4);
lean_closure_set(v___x_2174_, 0, lean_box(0));
lean_closure_set(v___x_2174_, 1, lean_box(0));
lean_closure_set(v___x_2174_, 2, v_inst_2172_);
lean_closure_set(v___x_2174_, 3, v_inst_2173_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instSDiffOfBEqOfHashable(lean_object* v_00_u03b1_2175_, lean_object* v_00_u03b2_2176_, lean_object* v_inst_2177_, lean_object* v_inst_2178_){
_start:
{
lean_object* v___x_2179_; 
v___x_2179_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_diff), 6, 4);
lean_closure_set(v___x_2179_, 0, lean_box(0));
lean_closure_set(v___x_2179_, 1, lean_box(0));
lean_closure_set(v___x_2179_, 2, v_inst_2177_);
lean_closure_set(v___x_2179_, 3, v_inst_2178_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_values___redArg___lam__0(lean_object* v_a_2180_, lean_object* v_b_2181_, lean_object* v_d_2182_){
_start:
{
lean_object* v___x_2183_; 
v___x_2183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2183_, 0, v_b_2181_);
lean_ctor_set(v___x_2183_, 1, v_d_2182_);
return v___x_2183_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_values___redArg___lam__0___boxed(lean_object* v_a_2184_, lean_object* v_b_2185_, lean_object* v_d_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l_Std_DHashMap_Raw_values___redArg___lam__0(v_a_2184_, v_b_2185_, v_d_2186_);
lean_dec(v_a_2184_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_values___redArg___lam__1(lean_object* v___x_2188_, lean_object* v___f_2189_, lean_object* v_l_2190_, lean_object* v_acc_2191_){
_start:
{
lean_object* v___x_2192_; 
v___x_2192_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_2188_, v___f_2189_, v_acc_2191_, v_l_2190_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_values___redArg(lean_object* v_m_2197_){
_start:
{
lean_object* v___x_2198_; lean_object* v_buckets_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; uint8_t v___x_2203_; 
v___x_2198_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_2199_ = lean_ctor_get(v_m_2197_, 1);
lean_inc_ref(v_buckets_2199_);
lean_dec_ref(v_m_2197_);
v___x_2200_ = lean_box(0);
v___x_2201_ = lean_array_get_size(v_buckets_2199_);
v___x_2202_ = lean_unsigned_to_nat(0u);
v___x_2203_ = lean_nat_dec_lt(v___x_2202_, v___x_2201_);
if (v___x_2203_ == 0)
{
lean_dec_ref(v_buckets_2199_);
return v___x_2200_;
}
else
{
lean_object* v___f_2204_; size_t v___x_2205_; size_t v___x_2206_; lean_object* v___x_2207_; 
v___f_2204_ = ((lean_object*)(l_Std_DHashMap_Raw_values___redArg___closed__1));
v___x_2205_ = lean_usize_of_nat(v___x_2201_);
v___x_2206_ = ((size_t)0ULL);
v___x_2207_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2198_, v___f_2204_, v_buckets_2199_, v___x_2205_, v___x_2206_, v___x_2200_);
return v___x_2207_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_values(lean_object* v_00_u03b1_2208_, lean_object* v_00_u03b2_2209_, lean_object* v_m_2210_){
_start:
{
lean_object* v___x_2211_; lean_object* v_buckets_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; uint8_t v___x_2216_; 
v___x_2211_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_2212_ = lean_ctor_get(v_m_2210_, 1);
lean_inc_ref(v_buckets_2212_);
lean_dec_ref(v_m_2210_);
v___x_2213_ = lean_box(0);
v___x_2214_ = lean_array_get_size(v_buckets_2212_);
v___x_2215_ = lean_unsigned_to_nat(0u);
v___x_2216_ = lean_nat_dec_lt(v___x_2215_, v___x_2214_);
if (v___x_2216_ == 0)
{
lean_dec_ref(v_buckets_2212_);
return v___x_2213_;
}
else
{
lean_object* v___f_2217_; size_t v___x_2218_; size_t v___x_2219_; lean_object* v___x_2220_; 
v___f_2217_ = ((lean_object*)(l_Std_DHashMap_Raw_values___redArg___closed__1));
v___x_2218_ = lean_usize_of_nat(v___x_2214_);
v___x_2219_ = ((size_t)0ULL);
v___x_2220_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2211_, v___f_2217_, v_buckets_2212_, v___x_2218_, v___x_2219_, v___x_2213_);
return v___x_2220_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_valuesArray___redArg___lam__0(lean_object* v_x1_2221_, lean_object* v_x2_2222_, lean_object* v_x3_2223_){
_start:
{
lean_object* v___x_2224_; 
v___x_2224_ = lean_array_push(v_x1_2221_, v_x3_2223_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_valuesArray___redArg___lam__0___boxed(lean_object* v_x1_2225_, lean_object* v_x2_2226_, lean_object* v_x3_2227_){
_start:
{
lean_object* v_res_2228_; 
v_res_2228_ = l_Std_DHashMap_Raw_valuesArray___redArg___lam__0(v_x1_2225_, v_x2_2226_, v_x3_2227_);
lean_dec(v_x2_2226_);
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_valuesArray___redArg(lean_object* v_m_2233_){
_start:
{
lean_object* v_size_2234_; lean_object* v_buckets_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; uint8_t v___x_2240_; 
v_size_2234_ = lean_ctor_get(v_m_2233_, 0);
lean_inc(v_size_2234_);
v_buckets_2235_ = lean_ctor_get(v_m_2233_, 1);
lean_inc_ref(v_buckets_2235_);
lean_dec_ref(v_m_2233_);
v___x_2236_ = lean_mk_empty_array_with_capacity(v_size_2234_);
lean_dec(v_size_2234_);
v___x_2237_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_2238_ = lean_unsigned_to_nat(0u);
v___x_2239_ = lean_array_get_size(v_buckets_2235_);
v___x_2240_ = lean_nat_dec_lt(v___x_2238_, v___x_2239_);
if (v___x_2240_ == 0)
{
lean_dec_ref(v_buckets_2235_);
return v___x_2236_;
}
else
{
lean_object* v___f_2241_; size_t v___x_2242_; size_t v___x_2243_; lean_object* v___x_2244_; 
v___f_2241_ = ((lean_object*)(l_Std_DHashMap_Raw_valuesArray___redArg___closed__1));
v___x_2242_ = ((size_t)0ULL);
v___x_2243_ = lean_usize_of_nat(v___x_2239_);
v___x_2244_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2237_, v___f_2241_, v_buckets_2235_, v___x_2242_, v___x_2243_, v___x_2236_);
return v___x_2244_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_valuesArray(lean_object* v_00_u03b1_2245_, lean_object* v_00_u03b2_2246_, lean_object* v_m_2247_){
_start:
{
lean_object* v_size_2248_; lean_object* v_buckets_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; uint8_t v___x_2254_; 
v_size_2248_ = lean_ctor_get(v_m_2247_, 0);
lean_inc(v_size_2248_);
v_buckets_2249_ = lean_ctor_get(v_m_2247_, 1);
lean_inc_ref(v_buckets_2249_);
lean_dec_ref(v_m_2247_);
v___x_2250_ = lean_mk_empty_array_with_capacity(v_size_2248_);
lean_dec(v_size_2248_);
v___x_2251_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_2252_ = lean_unsigned_to_nat(0u);
v___x_2253_ = lean_array_get_size(v_buckets_2249_);
v___x_2254_ = lean_nat_dec_lt(v___x_2252_, v___x_2253_);
if (v___x_2254_ == 0)
{
lean_dec_ref(v_buckets_2249_);
return v___x_2250_;
}
else
{
lean_object* v___f_2255_; size_t v___x_2256_; size_t v___x_2257_; lean_object* v___x_2258_; 
v___f_2255_ = ((lean_object*)(l_Std_DHashMap_Raw_valuesArray___redArg___closed__1));
v___x_2256_ = ((size_t)0ULL);
v___x_2257_ = lean_usize_of_nat(v___x_2253_);
v___x_2258_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2251_, v___f_2255_, v_buckets_2249_, v___x_2256_, v___x_2257_, v___x_2250_);
return v___x_2258_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insertMany___redArg(lean_object* v_inst_2259_, lean_object* v_inst_2260_, lean_object* v_inst_2261_, lean_object* v_m_2262_, lean_object* v_l_2263_){
_start:
{
lean_object* v_buckets_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; uint8_t v___x_2267_; 
v_buckets_2264_ = lean_ctor_get(v_m_2262_, 1);
v___x_2265_ = lean_unsigned_to_nat(0u);
v___x_2266_ = lean_array_get_size(v_buckets_2264_);
v___x_2267_ = lean_nat_dec_lt(v___x_2265_, v___x_2266_);
if (v___x_2267_ == 0)
{
lean_dec(v_l_2263_);
lean_dec(v_inst_2261_);
lean_dec_ref(v_inst_2260_);
lean_dec_ref(v_inst_2259_);
return v_m_2262_;
}
else
{
lean_object* v___x_2268_; 
v___x_2268_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v_inst_2261_, v_inst_2259_, v_inst_2260_, v_m_2262_, v_l_2263_);
return v___x_2268_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insertMany(lean_object* v_00_u03b1_2269_, lean_object* v_00_u03b2_2270_, lean_object* v_inst_2271_, lean_object* v_inst_2272_, lean_object* v_00_u03c1_2273_, lean_object* v_inst_2274_, lean_object* v_m_2275_, lean_object* v_l_2276_){
_start:
{
lean_object* v_buckets_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; uint8_t v___x_2280_; 
v_buckets_2277_ = lean_ctor_get(v_m_2275_, 1);
v___x_2278_ = lean_unsigned_to_nat(0u);
v___x_2279_ = lean_array_get_size(v_buckets_2277_);
v___x_2280_ = lean_nat_dec_lt(v___x_2278_, v___x_2279_);
if (v___x_2280_ == 0)
{
lean_dec(v_l_2276_);
lean_dec(v_inst_2274_);
lean_dec_ref(v_inst_2272_);
lean_dec_ref(v_inst_2271_);
return v_m_2275_;
}
else
{
lean_object* v___x_2281_; 
v___x_2281_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v_inst_2274_, v_inst_2271_, v_inst_2272_, v_m_2275_, v_l_2276_);
return v___x_2281_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_eraseManyEntries___redArg(lean_object* v_inst_2282_, lean_object* v_inst_2283_, lean_object* v_inst_2284_, lean_object* v_m_2285_, lean_object* v_l_2286_){
_start:
{
lean_object* v_buckets_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; uint8_t v___x_2290_; 
v_buckets_2287_ = lean_ctor_get(v_m_2285_, 1);
v___x_2288_ = lean_unsigned_to_nat(0u);
v___x_2289_ = lean_array_get_size(v_buckets_2287_);
v___x_2290_ = lean_nat_dec_lt(v___x_2288_, v___x_2289_);
if (v___x_2290_ == 0)
{
lean_dec(v_l_2286_);
lean_dec(v_inst_2284_);
lean_dec_ref(v_inst_2283_);
lean_dec_ref(v_inst_2282_);
return v_m_2285_;
}
else
{
lean_object* v___x_2291_; 
v___x_2291_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v_inst_2284_, v_inst_2282_, v_inst_2283_, v_m_2285_, v_l_2286_);
return v___x_2291_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_eraseManyEntries(lean_object* v_00_u03b1_2292_, lean_object* v_00_u03b2_2293_, lean_object* v_inst_2294_, lean_object* v_inst_2295_, lean_object* v_00_u03c1_2296_, lean_object* v_inst_2297_, lean_object* v_m_2298_, lean_object* v_l_2299_){
_start:
{
lean_object* v_buckets_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; uint8_t v___x_2303_; 
v_buckets_2300_ = lean_ctor_get(v_m_2298_, 1);
v___x_2301_ = lean_unsigned_to_nat(0u);
v___x_2302_ = lean_array_get_size(v_buckets_2300_);
v___x_2303_ = lean_nat_dec_lt(v___x_2301_, v___x_2302_);
if (v___x_2303_ == 0)
{
lean_dec(v_l_2299_);
lean_dec(v_inst_2297_);
lean_dec_ref(v_inst_2295_);
lean_dec_ref(v_inst_2294_);
return v_m_2298_;
}
else
{
lean_object* v___x_2304_; 
v___x_2304_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v_inst_2297_, v_inst_2294_, v_inst_2295_, v_m_2298_, v_l_2299_);
return v___x_2304_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_insertMany___redArg(lean_object* v_inst_2305_, lean_object* v_inst_2306_, lean_object* v_inst_2307_, lean_object* v_m_2308_, lean_object* v_l_2309_){
_start:
{
lean_object* v_buckets_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; uint8_t v___x_2313_; 
v_buckets_2310_ = lean_ctor_get(v_m_2308_, 1);
v___x_2311_ = lean_unsigned_to_nat(0u);
v___x_2312_ = lean_array_get_size(v_buckets_2310_);
v___x_2313_ = lean_nat_dec_lt(v___x_2311_, v___x_2312_);
if (v___x_2313_ == 0)
{
lean_dec(v_l_2309_);
lean_dec(v_inst_2307_);
lean_dec_ref(v_inst_2306_);
lean_dec_ref(v_inst_2305_);
return v_m_2308_;
}
else
{
lean_object* v___x_2314_; 
v___x_2314_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v_inst_2307_, v_inst_2305_, v_inst_2306_, v_m_2308_, v_l_2309_);
return v___x_2314_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_insertMany(lean_object* v_00_u03b1_2315_, lean_object* v_00_u03b2_2316_, lean_object* v_inst_2317_, lean_object* v_inst_2318_, lean_object* v_00_u03c1_2319_, lean_object* v_inst_2320_, lean_object* v_m_2321_, lean_object* v_l_2322_){
_start:
{
lean_object* v_buckets_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; uint8_t v___x_2326_; 
v_buckets_2323_ = lean_ctor_get(v_m_2321_, 1);
v___x_2324_ = lean_unsigned_to_nat(0u);
v___x_2325_ = lean_array_get_size(v_buckets_2323_);
v___x_2326_ = lean_nat_dec_lt(v___x_2324_, v___x_2325_);
if (v___x_2326_ == 0)
{
lean_dec(v_l_2322_);
lean_dec(v_inst_2320_);
lean_dec_ref(v_inst_2318_);
lean_dec_ref(v_inst_2317_);
return v_m_2321_;
}
else
{
lean_object* v___x_2327_; 
v___x_2327_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v_inst_2320_, v_inst_2317_, v_inst_2318_, v_m_2321_, v_l_2322_);
return v___x_2327_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_insertManyIfNewUnit___redArg(lean_object* v_inst_2328_, lean_object* v_inst_2329_, lean_object* v_inst_2330_, lean_object* v_m_2331_, lean_object* v_l_2332_){
_start:
{
lean_object* v_buckets_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; uint8_t v___x_2336_; 
v_buckets_2333_ = lean_ctor_get(v_m_2331_, 1);
v___x_2334_ = lean_unsigned_to_nat(0u);
v___x_2335_ = lean_array_get_size(v_buckets_2333_);
v___x_2336_ = lean_nat_dec_lt(v___x_2334_, v___x_2335_);
if (v___x_2336_ == 0)
{
lean_dec(v_l_2332_);
lean_dec(v_inst_2330_);
lean_dec_ref(v_inst_2329_);
lean_dec_ref(v_inst_2328_);
return v_m_2331_;
}
else
{
lean_object* v___x_2337_; 
v___x_2337_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_2330_, v_inst_2328_, v_inst_2329_, v_m_2331_, v_l_2332_);
return v___x_2337_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_insertManyIfNewUnit(lean_object* v_00_u03b1_2338_, lean_object* v_inst_2339_, lean_object* v_inst_2340_, lean_object* v_00_u03c1_2341_, lean_object* v_inst_2342_, lean_object* v_m_2343_, lean_object* v_l_2344_){
_start:
{
lean_object* v_buckets_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; uint8_t v___x_2348_; 
v_buckets_2345_ = lean_ctor_get(v_m_2343_, 1);
v___x_2346_ = lean_unsigned_to_nat(0u);
v___x_2347_ = lean_array_get_size(v_buckets_2345_);
v___x_2348_ = lean_nat_dec_lt(v___x_2346_, v___x_2347_);
if (v___x_2348_ == 0)
{
lean_dec(v_l_2344_);
lean_dec(v_inst_2342_);
lean_dec_ref(v_inst_2340_);
lean_dec_ref(v_inst_2339_);
return v_m_2343_;
}
else
{
lean_object* v___x_2349_; 
v___x_2349_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_2342_, v_inst_2339_, v_inst_2340_, v_m_2343_, v_l_2344_);
return v___x_2349_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_unitOfArray___redArg(lean_object* v_inst_2354_, lean_object* v_inst_2355_, lean_object* v_l_2356_){
_start:
{
lean_object* v___x_2357_; uint8_t v___x_2358_; 
v___x_2357_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
v___x_2358_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2358_ == 0)
{
lean_dec_ref(v_l_2356_);
lean_dec_ref(v_inst_2355_);
lean_dec_ref(v_inst_2354_);
return v___x_2357_;
}
else
{
lean_object* v___f_2359_; lean_object* v___x_2360_; 
v___f_2359_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1));
v___x_2360_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2359_, v_inst_2354_, v_inst_2355_, v___x_2357_, v_l_2356_);
return v___x_2360_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_unitOfArray(lean_object* v_00_u03b1_2361_, lean_object* v_inst_2362_, lean_object* v_inst_2363_, lean_object* v_l_2364_){
_start:
{
lean_object* v___x_2365_; uint8_t v___x_2366_; 
v___x_2365_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
v___x_2366_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2366_ == 0)
{
lean_dec_ref(v_l_2364_);
lean_dec_ref(v_inst_2363_);
lean_dec_ref(v_inst_2362_);
return v___x_2365_;
}
else
{
lean_object* v___f_2367_; lean_object* v___x_2368_; 
v___f_2367_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1));
v___x_2368_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2367_, v_inst_2362_, v_inst_2363_, v___x_2365_, v_l_2364_);
return v___x_2368_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_numBuckets___redArg(lean_object* v_m_2369_){
_start:
{
lean_object* v_buckets_2370_; lean_object* v___x_2371_; 
v_buckets_2370_ = lean_ctor_get(v_m_2369_, 1);
v___x_2371_ = lean_array_get_size(v_buckets_2370_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_numBuckets___redArg___boxed(lean_object* v_m_2372_){
_start:
{
lean_object* v_res_2373_; 
v_res_2373_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2372_);
lean_dec_ref(v_m_2372_);
return v_res_2373_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_numBuckets(lean_object* v_00_u03b1_2374_, lean_object* v_00_u03b2_2375_, lean_object* v_m_2376_){
_start:
{
lean_object* v___x_2377_; 
v___x_2377_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2376_);
return v___x_2377_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_numBuckets___boxed(lean_object* v_00_u03b1_2378_, lean_object* v_00_u03b2_2379_, lean_object* v_m_2380_){
_start:
{
lean_object* v_res_2381_; 
v_res_2381_ = l_Std_DHashMap_Raw_Internal_numBuckets(v_00_u03b1_2378_, v_00_u03b2_2379_, v_m_2380_);
lean_dec_ref(v_m_2380_);
return v_res_2381_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toList___redArg___lam__0(lean_object* v_a_2382_, lean_object* v_b_2383_, lean_object* v_d_2384_){
_start:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2385_, 0, v_a_2382_);
lean_ctor_set(v___x_2385_, 1, v_b_2383_);
v___x_2386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2385_);
lean_ctor_set(v___x_2386_, 1, v_d_2384_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toList___redArg___lam__1(lean_object* v___x_2387_, lean_object* v___f_2388_, lean_object* v_l_2389_, lean_object* v_acc_2390_){
_start:
{
lean_object* v___x_2391_; 
v___x_2391_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_2387_, v___f_2388_, v_acc_2390_, v_l_2389_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toList___redArg(lean_object* v_m_2396_){
_start:
{
lean_object* v___x_2397_; lean_object* v_buckets_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; uint8_t v___x_2402_; 
v___x_2397_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_2398_ = lean_ctor_get(v_m_2396_, 1);
lean_inc_ref(v_buckets_2398_);
lean_dec_ref(v_m_2396_);
v___x_2399_ = lean_box(0);
v___x_2400_ = lean_array_get_size(v_buckets_2398_);
v___x_2401_ = lean_unsigned_to_nat(0u);
v___x_2402_ = lean_nat_dec_lt(v___x_2401_, v___x_2400_);
if (v___x_2402_ == 0)
{
lean_dec_ref(v_buckets_2398_);
return v___x_2399_;
}
else
{
lean_object* v___f_2403_; size_t v___x_2404_; size_t v___x_2405_; lean_object* v___x_2406_; 
v___f_2403_ = ((lean_object*)(l_Std_DHashMap_Raw_toList___redArg___closed__1));
v___x_2404_ = lean_usize_of_nat(v___x_2400_);
v___x_2405_ = ((size_t)0ULL);
v___x_2406_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2397_, v___f_2403_, v_buckets_2398_, v___x_2404_, v___x_2405_, v___x_2399_);
return v___x_2406_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toList(lean_object* v_00_u03b1_2407_, lean_object* v_00_u03b2_2408_, lean_object* v_m_2409_){
_start:
{
lean_object* v___x_2410_; lean_object* v_buckets_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; uint8_t v___x_2415_; 
v___x_2410_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_2411_ = lean_ctor_get(v_m_2409_, 1);
lean_inc_ref(v_buckets_2411_);
lean_dec_ref(v_m_2409_);
v___x_2412_ = lean_box(0);
v___x_2413_ = lean_array_get_size(v_buckets_2411_);
v___x_2414_ = lean_unsigned_to_nat(0u);
v___x_2415_ = lean_nat_dec_lt(v___x_2414_, v___x_2413_);
if (v___x_2415_ == 0)
{
lean_dec_ref(v_buckets_2411_);
return v___x_2412_;
}
else
{
lean_object* v___f_2416_; size_t v___x_2417_; size_t v___x_2418_; lean_object* v___x_2419_; 
v___f_2416_ = ((lean_object*)(l_Std_DHashMap_Raw_toList___redArg___closed__1));
v___x_2417_ = lean_usize_of_nat(v___x_2413_);
v___x_2418_ = ((size_t)0ULL);
v___x_2419_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2410_, v___f_2416_, v_buckets_2411_, v___x_2417_, v___x_2418_, v___x_2412_);
return v___x_2419_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toList___redArg___lam__0(lean_object* v_a_2420_, lean_object* v_b_2421_, lean_object* v_d_2422_){
_start:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2423_, 0, v_a_2420_);
lean_ctor_set(v___x_2423_, 1, v_b_2421_);
v___x_2424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2423_);
lean_ctor_set(v___x_2424_, 1, v_d_2422_);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toList___redArg___lam__1(lean_object* v___x_2425_, lean_object* v___f_2426_, lean_object* v_l_2427_, lean_object* v_acc_2428_){
_start:
{
lean_object* v___x_2429_; 
v___x_2429_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_2425_, v___f_2426_, v_acc_2428_, v_l_2427_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toList___redArg(lean_object* v_m_2434_){
_start:
{
lean_object* v___x_2435_; lean_object* v_buckets_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; uint8_t v___x_2440_; 
v___x_2435_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_2436_ = lean_ctor_get(v_m_2434_, 1);
lean_inc_ref(v_buckets_2436_);
lean_dec_ref(v_m_2434_);
v___x_2437_ = lean_box(0);
v___x_2438_ = lean_array_get_size(v_buckets_2436_);
v___x_2439_ = lean_unsigned_to_nat(0u);
v___x_2440_ = lean_nat_dec_lt(v___x_2439_, v___x_2438_);
if (v___x_2440_ == 0)
{
lean_dec_ref(v_buckets_2436_);
return v___x_2437_;
}
else
{
lean_object* v___f_2441_; size_t v___x_2442_; size_t v___x_2443_; lean_object* v___x_2444_; 
v___f_2441_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_toList___redArg___closed__1));
v___x_2442_ = lean_usize_of_nat(v___x_2438_);
v___x_2443_ = ((size_t)0ULL);
v___x_2444_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2435_, v___f_2441_, v_buckets_2436_, v___x_2442_, v___x_2443_, v___x_2437_);
return v___x_2444_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toList(lean_object* v_00_u03b1_2445_, lean_object* v_00_u03b2_2446_, lean_object* v_m_2447_){
_start:
{
lean_object* v___x_2448_; lean_object* v_buckets_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; uint8_t v___x_2453_; 
v___x_2448_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_2449_ = lean_ctor_get(v_m_2447_, 1);
lean_inc_ref(v_buckets_2449_);
lean_dec_ref(v_m_2447_);
v___x_2450_ = lean_box(0);
v___x_2451_ = lean_array_get_size(v_buckets_2449_);
v___x_2452_ = lean_unsigned_to_nat(0u);
v___x_2453_ = lean_nat_dec_lt(v___x_2452_, v___x_2451_);
if (v___x_2453_ == 0)
{
lean_dec_ref(v_buckets_2449_);
return v___x_2450_;
}
else
{
lean_object* v___f_2454_; size_t v___x_2455_; size_t v___x_2456_; lean_object* v___x_2457_; 
v___f_2454_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_toList___redArg___closed__1));
v___x_2455_ = lean_usize_of_nat(v___x_2451_);
v___x_2456_ = ((size_t)0ULL);
v___x_2457_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2448_, v___f_2454_, v_buckets_2449_, v___x_2455_, v___x_2456_, v___x_2450_);
return v___x_2457_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instRepr___redArg___lam__2(lean_object* v___x_2461_, lean_object* v___f_2462_, lean_object* v_m_2463_, lean_object* v_prec_2464_){
_start:
{
lean_object* v___x_2465_; lean_object* v_buckets_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2486_; 
v___x_2465_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_2466_ = lean_ctor_get(v_m_2463_, 1);
v_isSharedCheck_2486_ = !lean_is_exclusive(v_m_2463_);
if (v_isSharedCheck_2486_ == 0)
{
lean_object* v_unused_2487_; 
v_unused_2487_ = lean_ctor_get(v_m_2463_, 0);
lean_dec(v_unused_2487_);
v___x_2468_ = v_m_2463_;
v_isShared_2469_ = v_isSharedCheck_2486_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_buckets_2466_);
lean_dec(v_m_2463_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2486_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2470_; lean_object* v___y_2472_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; uint8_t v___x_2481_; 
v___x_2470_ = ((lean_object*)(l_Std_DHashMap_Raw_instRepr___redArg___lam__2___closed__1));
v___x_2478_ = lean_box(0);
v___x_2479_ = lean_array_get_size(v_buckets_2466_);
v___x_2480_ = lean_unsigned_to_nat(0u);
v___x_2481_ = lean_nat_dec_lt(v___x_2480_, v___x_2479_);
if (v___x_2481_ == 0)
{
lean_dec_ref(v_buckets_2466_);
lean_dec_ref(v___f_2462_);
v___y_2472_ = v___x_2478_;
goto v___jp_2471_;
}
else
{
lean_object* v___f_2482_; size_t v___x_2483_; size_t v___x_2484_; lean_object* v___x_2485_; 
v___f_2482_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_toList___redArg___lam__1), 4, 2);
lean_closure_set(v___f_2482_, 0, v___x_2465_);
lean_closure_set(v___f_2482_, 1, v___f_2462_);
v___x_2483_ = lean_usize_of_nat(v___x_2479_);
v___x_2484_ = ((size_t)0ULL);
v___x_2485_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2465_, v___f_2482_, v_buckets_2466_, v___x_2483_, v___x_2484_, v___x_2478_);
v___y_2472_ = v___x_2485_;
goto v___jp_2471_;
}
v___jp_2471_:
{
lean_object* v___x_2473_; lean_object* v___x_2475_; 
v___x_2473_ = l_List_repr___redArg(v___x_2461_, v___y_2472_);
if (v_isShared_2469_ == 0)
{
lean_ctor_set_tag(v___x_2468_, 5);
lean_ctor_set(v___x_2468_, 1, v___x_2473_);
lean_ctor_set(v___x_2468_, 0, v___x_2470_);
v___x_2475_ = v___x_2468_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2470_);
lean_ctor_set(v_reuseFailAlloc_2477_, 1, v___x_2473_);
v___x_2475_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
lean_object* v___x_2476_; 
v___x_2476_ = l_Repr_addAppParen(v___x_2475_, v_prec_2464_);
return v___x_2476_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instRepr___redArg___lam__2___boxed(lean_object* v___x_2488_, lean_object* v___f_2489_, lean_object* v_m_2490_, lean_object* v_prec_2491_){
_start:
{
lean_object* v_res_2492_; 
v_res_2492_ = l_Std_DHashMap_Raw_instRepr___redArg___lam__2(v___x_2488_, v___f_2489_, v_m_2490_, v_prec_2491_);
lean_dec(v_prec_2491_);
return v_res_2492_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instRepr___redArg(lean_object* v_inst_2493_, lean_object* v_inst_2494_){
_start:
{
lean_object* v___f_2495_; lean_object* v___x_2496_; lean_object* v___f_2497_; 
v___f_2495_ = ((lean_object*)(l_Std_DHashMap_Raw_toList___redArg___closed__0));
v___x_2496_ = lean_alloc_closure((void*)(l_Sigma_repr___boxed), 6, 4);
lean_closure_set(v___x_2496_, 0, lean_box(0));
lean_closure_set(v___x_2496_, 1, lean_box(0));
lean_closure_set(v___x_2496_, 2, v_inst_2493_);
lean_closure_set(v___x_2496_, 3, v_inst_2494_);
v___f_2497_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instRepr___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2497_, 0, v___x_2496_);
lean_closure_set(v___f_2497_, 1, v___f_2495_);
return v___f_2497_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instRepr(lean_object* v_00_u03b1_2498_, lean_object* v_00_u03b2_2499_, lean_object* v_inst_2500_, lean_object* v_inst_2501_){
_start:
{
lean_object* v___x_2502_; 
v___x_2502_ = l_Std_DHashMap_Raw_instRepr___redArg(v_inst_2500_, v_inst_2501_);
return v___x_2502_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keys___redArg___lam__0(lean_object* v_a_2503_, lean_object* v_b_2504_, lean_object* v_d_2505_){
_start:
{
lean_object* v___x_2506_; 
v___x_2506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2506_, 0, v_a_2503_);
lean_ctor_set(v___x_2506_, 1, v_d_2505_);
return v___x_2506_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keys___redArg___lam__0___boxed(lean_object* v_a_2507_, lean_object* v_b_2508_, lean_object* v_d_2509_){
_start:
{
lean_object* v_res_2510_; 
v_res_2510_ = l_Std_DHashMap_Raw_keys___redArg___lam__0(v_a_2507_, v_b_2508_, v_d_2509_);
lean_dec(v_b_2508_);
return v_res_2510_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keys___redArg(lean_object* v_m_2515_){
_start:
{
lean_object* v___x_2516_; lean_object* v_buckets_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; uint8_t v___x_2521_; 
v___x_2516_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_2517_ = lean_ctor_get(v_m_2515_, 1);
lean_inc_ref(v_buckets_2517_);
lean_dec_ref(v_m_2515_);
v___x_2518_ = lean_box(0);
v___x_2519_ = lean_array_get_size(v_buckets_2517_);
v___x_2520_ = lean_unsigned_to_nat(0u);
v___x_2521_ = lean_nat_dec_lt(v___x_2520_, v___x_2519_);
if (v___x_2521_ == 0)
{
lean_dec_ref(v_buckets_2517_);
return v___x_2518_;
}
else
{
lean_object* v___f_2522_; size_t v___x_2523_; size_t v___x_2524_; lean_object* v___x_2525_; 
v___f_2522_ = ((lean_object*)(l_Std_DHashMap_Raw_keys___redArg___closed__1));
v___x_2523_ = lean_usize_of_nat(v___x_2519_);
v___x_2524_ = ((size_t)0ULL);
v___x_2525_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2516_, v___f_2522_, v_buckets_2517_, v___x_2523_, v___x_2524_, v___x_2518_);
return v___x_2525_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keys(lean_object* v_00_u03b1_2526_, lean_object* v_00_u03b2_2527_, lean_object* v_m_2528_){
_start:
{
lean_object* v___x_2529_; lean_object* v_buckets_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; uint8_t v___x_2534_; 
v___x_2529_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_2530_ = lean_ctor_get(v_m_2528_, 1);
lean_inc_ref(v_buckets_2530_);
lean_dec_ref(v_m_2528_);
v___x_2531_ = lean_box(0);
v___x_2532_ = lean_array_get_size(v_buckets_2530_);
v___x_2533_ = lean_unsigned_to_nat(0u);
v___x_2534_ = lean_nat_dec_lt(v___x_2533_, v___x_2532_);
if (v___x_2534_ == 0)
{
lean_dec_ref(v_buckets_2530_);
return v___x_2531_;
}
else
{
lean_object* v___f_2535_; size_t v___x_2536_; size_t v___x_2537_; lean_object* v___x_2538_; 
v___f_2535_ = ((lean_object*)(l_Std_DHashMap_Raw_keys___redArg___closed__1));
v___x_2536_ = lean_usize_of_nat(v___x_2532_);
v___x_2537_ = ((size_t)0ULL);
v___x_2538_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2529_, v___f_2535_, v_buckets_2530_, v___x_2536_, v___x_2537_, v___x_2531_);
return v___x_2538_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_ofList___redArg(lean_object* v_inst_2543_, lean_object* v_inst_2544_, lean_object* v_l_2545_){
_start:
{
lean_object* v___x_2546_; uint8_t v___x_2547_; 
v___x_2546_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
v___x_2547_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2547_ == 0)
{
lean_dec(v_l_2545_);
lean_dec_ref(v_inst_2544_);
lean_dec_ref(v_inst_2543_);
return v___x_2546_;
}
else
{
lean_object* v___f_2548_; lean_object* v___x_2549_; 
v___f_2548_ = ((lean_object*)(l_Std_DHashMap_Raw_ofList___redArg___closed__1));
v___x_2549_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_2548_, v_inst_2543_, v_inst_2544_, v___x_2546_, v_l_2545_);
return v___x_2549_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_ofList(lean_object* v_00_u03b1_2550_, lean_object* v_00_u03b2_2551_, lean_object* v_inst_2552_, lean_object* v_inst_2553_, lean_object* v_l_2554_){
_start:
{
lean_object* v___x_2555_; uint8_t v___x_2556_; 
v___x_2555_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
v___x_2556_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2556_ == 0)
{
lean_dec(v_l_2554_);
lean_dec_ref(v_inst_2553_);
lean_dec_ref(v_inst_2552_);
return v___x_2555_;
}
else
{
lean_object* v___f_2557_; lean_object* v___x_2558_; 
v___f_2557_ = ((lean_object*)(l_Std_DHashMap_Raw_ofList___redArg___closed__1));
v___x_2558_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_2557_, v_inst_2552_, v_inst_2553_, v___x_2555_, v_l_2554_);
return v___x_2558_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_ofArray___redArg(lean_object* v_inst_2559_, lean_object* v_inst_2560_, lean_object* v_l_2561_){
_start:
{
lean_object* v___x_2562_; uint8_t v___x_2563_; 
v___x_2562_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
v___x_2563_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2563_ == 0)
{
lean_dec_ref(v_l_2561_);
lean_dec_ref(v_inst_2560_);
lean_dec_ref(v_inst_2559_);
return v___x_2562_;
}
else
{
lean_object* v___f_2564_; lean_object* v___x_2565_; 
v___f_2564_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1));
v___x_2565_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_2564_, v_inst_2559_, v_inst_2560_, v___x_2562_, v_l_2561_);
return v___x_2565_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_ofArray(lean_object* v_00_u03b1_2566_, lean_object* v_00_u03b2_2567_, lean_object* v_inst_2568_, lean_object* v_inst_2569_, lean_object* v_l_2570_){
_start:
{
lean_object* v___x_2571_; uint8_t v___x_2572_; 
v___x_2571_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
v___x_2572_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2572_ == 0)
{
lean_dec_ref(v_l_2570_);
lean_dec_ref(v_inst_2569_);
lean_dec_ref(v_inst_2568_);
return v___x_2571_;
}
else
{
lean_object* v___f_2573_; lean_object* v___x_2574_; 
v___f_2573_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1));
v___x_2574_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_2573_, v_inst_2568_, v_inst_2569_, v___x_2571_, v_l_2570_);
return v___x_2574_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_ofList___redArg(lean_object* v_inst_2575_, lean_object* v_inst_2576_, lean_object* v_l_2577_){
_start:
{
lean_object* v___x_2578_; uint8_t v___x_2579_; 
v___x_2578_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
v___x_2579_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2579_ == 0)
{
lean_dec(v_l_2577_);
lean_dec_ref(v_inst_2576_);
lean_dec_ref(v_inst_2575_);
return v___x_2578_;
}
else
{
lean_object* v___f_2580_; lean_object* v___x_2581_; 
v___f_2580_ = ((lean_object*)(l_Std_DHashMap_Raw_ofList___redArg___closed__1));
v___x_2581_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_2580_, v_inst_2575_, v_inst_2576_, v___x_2578_, v_l_2577_);
return v___x_2581_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_ofList(lean_object* v_00_u03b1_2582_, lean_object* v_00_u03b2_2583_, lean_object* v_inst_2584_, lean_object* v_inst_2585_, lean_object* v_l_2586_){
_start:
{
lean_object* v___x_2587_; uint8_t v___x_2588_; 
v___x_2587_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
v___x_2588_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2588_ == 0)
{
lean_dec(v_l_2586_);
lean_dec_ref(v_inst_2585_);
lean_dec_ref(v_inst_2584_);
return v___x_2587_;
}
else
{
lean_object* v___f_2589_; lean_object* v___x_2590_; 
v___f_2589_ = ((lean_object*)(l_Std_DHashMap_Raw_ofList___redArg___closed__1));
v___x_2590_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_2589_, v_inst_2584_, v_inst_2585_, v___x_2587_, v_l_2586_);
return v___x_2590_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_ofArray___redArg(lean_object* v_inst_2591_, lean_object* v_inst_2592_, lean_object* v_l_2593_){
_start:
{
lean_object* v___x_2594_; uint8_t v___x_2595_; 
v___x_2594_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
v___x_2595_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2595_ == 0)
{
lean_dec_ref(v_l_2593_);
lean_dec_ref(v_inst_2592_);
lean_dec_ref(v_inst_2591_);
return v___x_2594_;
}
else
{
lean_object* v___f_2596_; lean_object* v___x_2597_; 
v___f_2596_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1));
v___x_2597_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_2596_, v_inst_2591_, v_inst_2592_, v___x_2594_, v_l_2593_);
return v___x_2597_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_ofArray(lean_object* v_00_u03b1_2598_, lean_object* v_00_u03b2_2599_, lean_object* v_inst_2600_, lean_object* v_inst_2601_, lean_object* v_l_2602_){
_start:
{
lean_object* v___x_2603_; uint8_t v___x_2604_; 
v___x_2603_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
v___x_2604_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2604_ == 0)
{
lean_dec_ref(v_l_2602_);
lean_dec_ref(v_inst_2601_);
lean_dec_ref(v_inst_2600_);
return v___x_2603_;
}
else
{
lean_object* v___f_2605_; lean_object* v___x_2606_; 
v___f_2605_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1));
v___x_2606_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_2605_, v_inst_2600_, v_inst_2601_, v___x_2603_, v_l_2602_);
return v___x_2606_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_unitOfList___redArg(lean_object* v_inst_2607_, lean_object* v_inst_2608_, lean_object* v_l_2609_){
_start:
{
lean_object* v___x_2610_; uint8_t v___x_2611_; 
v___x_2610_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
v___x_2611_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2611_ == 0)
{
lean_dec(v_l_2609_);
lean_dec_ref(v_inst_2608_);
lean_dec_ref(v_inst_2607_);
return v___x_2610_;
}
else
{
lean_object* v___f_2612_; lean_object* v___x_2613_; 
v___f_2612_ = ((lean_object*)(l_Std_DHashMap_Raw_ofList___redArg___closed__1));
v___x_2613_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2612_, v_inst_2607_, v_inst_2608_, v___x_2610_, v_l_2609_);
return v___x_2613_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_unitOfList(lean_object* v_00_u03b1_2614_, lean_object* v_inst_2615_, lean_object* v_inst_2616_, lean_object* v_l_2617_){
_start:
{
lean_object* v___x_2618_; uint8_t v___x_2619_; 
v___x_2618_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
v___x_2619_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2619_ == 0)
{
lean_dec(v_l_2617_);
lean_dec_ref(v_inst_2616_);
lean_dec_ref(v_inst_2615_);
return v___x_2618_;
}
else
{
lean_object* v___f_2620_; lean_object* v___x_2621_; 
v___f_2620_ = ((lean_object*)(l_Std_DHashMap_Raw_ofList___redArg___closed__1));
v___x_2621_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2620_, v_inst_2615_, v_inst_2616_, v___x_2618_, v_l_2617_);
return v___x_2621_;
}
}
}
lean_object* runtime_initialize_Init_Data_LawfulHashable(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DHashMap_Internal_Defs(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DHashMap_Internal_Defs(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DHashMap_Raw(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_LawfulHashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_Internal_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_Internal_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_DHashMap_Raw(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_LawfulHashable(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_Internal_Defs(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_Internal_Defs(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DHashMap_Raw(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_LawfulHashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_Internal_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_Internal_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_DHashMap_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_DHashMap_Raw(builtin);
}
#ifdef __cplusplus
}
#endif
