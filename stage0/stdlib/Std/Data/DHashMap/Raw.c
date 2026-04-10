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
lean_object* l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Std_DHashMap_Raw_ofList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value)} };
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
static lean_object* _init_l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__6(void){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = ((lean_object*)(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__5));
v___x_82_ = l_String_toRawSubstring_x27(v___x_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1(lean_object* v_x_106_, lean_object* v_a_107_, lean_object* v_a_108_){
_start:
{
lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_109_ = ((lean_object*)(l_Std_DHashMap_Raw_term___x7em___00__closed__4));
lean_inc(v_x_106_);
v___x_110_ = l_Lean_Syntax_isOfKind(v_x_106_, v___x_109_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; lean_object* v___x_112_; 
lean_dec(v_x_106_);
v___x_111_ = lean_box(1);
v___x_112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
lean_ctor_set(v___x_112_, 1, v_a_108_);
return v___x_112_;
}
else
{
lean_object* v_quotContext_113_; lean_object* v_currMacroScope_114_; lean_object* v_ref_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; uint8_t v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v_quotContext_113_ = lean_ctor_get(v_a_107_, 1);
v_currMacroScope_114_ = lean_ctor_get(v_a_107_, 2);
v_ref_115_ = lean_ctor_get(v_a_107_, 5);
v___x_116_ = lean_unsigned_to_nat(0u);
v___x_117_ = l_Lean_Syntax_getArg(v_x_106_, v___x_116_);
v___x_118_ = lean_unsigned_to_nat(2u);
v___x_119_ = l_Lean_Syntax_getArg(v_x_106_, v___x_118_);
lean_dec(v_x_106_);
v___x_120_ = 0;
v___x_121_ = l_Lean_SourceInfo_fromRef(v_ref_115_, v___x_120_);
v___x_122_ = ((lean_object*)(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4));
v___x_123_ = lean_obj_once(&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__6, &l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__6_once, _init_l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__6);
v___x_124_ = ((lean_object*)(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__8));
lean_inc(v_currMacroScope_114_);
lean_inc(v_quotContext_113_);
v___x_125_ = l_Lean_addMacroScope(v_quotContext_113_, v___x_124_, v_currMacroScope_114_);
v___x_126_ = ((lean_object*)(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__13));
lean_inc_n(v___x_121_, 2);
v___x_127_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_127_, 0, v___x_121_);
lean_ctor_set(v___x_127_, 1, v___x_123_);
lean_ctor_set(v___x_127_, 2, v___x_125_);
lean_ctor_set(v___x_127_, 3, v___x_126_);
v___x_128_ = ((lean_object*)(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__15));
v___x_129_ = l_Lean_Syntax_node2(v___x_121_, v___x_128_, v___x_117_, v___x_119_);
v___x_130_ = l_Lean_Syntax_node2(v___x_121_, v___x_122_, v___x_127_, v___x_129_);
v___x_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
lean_ctor_set(v___x_131_, 1, v_a_108_);
return v___x_131_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___boxed(lean_object* v_x_132_, lean_object* v_a_133_, lean_object* v_a_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1(v_x_132_, v_a_133_, v_a_134_);
lean_dec_ref(v_a_133_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1(lean_object* v_x_139_, lean_object* v_a_140_, lean_object* v_a_141_){
_start:
{
lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_142_ = ((lean_object*)(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4));
lean_inc(v_x_139_);
v___x_143_ = l_Lean_Syntax_isOfKind(v_x_139_, v___x_142_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; lean_object* v___x_145_; 
lean_dec(v_x_139_);
v___x_144_ = lean_box(0);
v___x_145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
lean_ctor_set(v___x_145_, 1, v_a_141_);
return v___x_145_;
}
else
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_146_ = lean_unsigned_to_nat(0u);
v___x_147_ = l_Lean_Syntax_getArg(v_x_139_, v___x_146_);
v___x_148_ = ((lean_object*)(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___closed__1));
lean_inc(v___x_147_);
v___x_149_ = l_Lean_Syntax_isOfKind(v___x_147_, v___x_148_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; lean_object* v___x_151_; 
lean_dec(v___x_147_);
lean_dec(v_x_139_);
v___x_150_ = lean_box(0);
v___x_151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
lean_ctor_set(v___x_151_, 1, v_a_141_);
return v___x_151_;
}
else
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_152_ = lean_unsigned_to_nat(1u);
v___x_153_ = l_Lean_Syntax_getArg(v_x_139_, v___x_152_);
lean_dec(v_x_139_);
v___x_154_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_153_);
v___x_155_ = l_Lean_Syntax_matchesNull(v___x_153_, v___x_154_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; lean_object* v___x_157_; 
lean_dec(v___x_153_);
lean_dec(v___x_147_);
v___x_156_ = lean_box(0);
v___x_157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
lean_ctor_set(v___x_157_, 1, v_a_141_);
return v___x_157_;
}
else
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v_ref_160_; uint8_t v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_158_ = l_Lean_Syntax_getArg(v___x_153_, v___x_146_);
v___x_159_ = l_Lean_Syntax_getArg(v___x_153_, v___x_152_);
lean_dec(v___x_153_);
v_ref_160_ = l_Lean_replaceRef(v___x_147_, v_a_140_);
lean_dec(v___x_147_);
v___x_161_ = 0;
v___x_162_ = l_Lean_SourceInfo_fromRef(v_ref_160_, v___x_161_);
lean_dec(v_ref_160_);
v___x_163_ = ((lean_object*)(l_Std_DHashMap_Raw_term___x7em___00__closed__4));
v___x_164_ = ((lean_object*)(l_Std_DHashMap_Raw_term___x7em___00__closed__7));
lean_inc(v___x_162_);
v___x_165_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_162_);
lean_ctor_set(v___x_165_, 1, v___x_164_);
v___x_166_ = l_Lean_Syntax_node3(v___x_162_, v___x_163_, v___x_158_, v___x_165_, v___x_159_);
v___x_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
lean_ctor_set(v___x_167_, 1, v_a_141_);
return v___x_167_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___boxed(lean_object* v_x_168_, lean_object* v_a_169_, lean_object* v_a_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1(v_x_168_, v_a_169_, v_a_170_);
lean_dec(v_a_169_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insert___redArg(lean_object* v_inst_172_, lean_object* v_inst_173_, lean_object* v_m_174_, lean_object* v_a_175_, lean_object* v_b_176_){
_start:
{
lean_object* v_buckets_177_; lean_object* v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; 
v_buckets_177_ = lean_ctor_get(v_m_174_, 1);
v___x_178_ = lean_unsigned_to_nat(0u);
v___x_179_ = lean_array_get_size(v_buckets_177_);
v___x_180_ = lean_nat_dec_lt(v___x_178_, v___x_179_);
if (v___x_180_ == 0)
{
lean_dec(v_b_176_);
lean_dec(v_a_175_);
lean_dec_ref(v_inst_173_);
lean_dec_ref(v_inst_172_);
return v_m_174_;
}
else
{
lean_object* v___x_181_; 
v___x_181_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_172_, v_inst_173_, v_m_174_, v_a_175_, v_b_176_);
return v___x_181_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insert(lean_object* v_00_u03b1_182_, lean_object* v_00_u03b2_183_, lean_object* v_inst_184_, lean_object* v_inst_185_, lean_object* v_m_186_, lean_object* v_a_187_, lean_object* v_b_188_){
_start:
{
lean_object* v_buckets_189_; lean_object* v___x_190_; lean_object* v___x_191_; uint8_t v___x_192_; 
v_buckets_189_ = lean_ctor_get(v_m_186_, 1);
v___x_190_ = lean_unsigned_to_nat(0u);
v___x_191_ = lean_array_get_size(v_buckets_189_);
v___x_192_ = lean_nat_dec_lt(v___x_190_, v___x_191_);
if (v___x_192_ == 0)
{
lean_dec(v_b_188_);
lean_dec(v_a_187_);
lean_dec_ref(v_inst_185_);
lean_dec_ref(v_inst_184_);
return v_m_186_;
}
else
{
lean_object* v___x_193_; 
v___x_193_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_184_, v_inst_185_, v_m_186_, v_a_187_, v_b_188_);
return v___x_193_;
}
}
}
static lean_object* _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__0, &l_Std_DHashMap_Raw_instEmptyCollection___closed__0_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__0);
v___x_195_ = lean_array_get_size(v___x_194_);
return v___x_195_;
}
}
static uint8_t _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; uint8_t v___x_198_; 
v___x_196_ = lean_obj_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0);
v___x_197_ = lean_unsigned_to_nat(0u);
v___x_198_ = lean_nat_dec_lt(v___x_197_, v___x_196_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0(lean_object* v_inst_199_, lean_object* v_inst_200_, lean_object* v_x_201_){
_start:
{
lean_object* v_fst_202_; lean_object* v_snd_203_; lean_object* v___x_204_; uint8_t v___x_205_; 
v_fst_202_ = lean_ctor_get(v_x_201_, 0);
lean_inc(v_fst_202_);
v_snd_203_ = lean_ctor_get(v_x_201_, 1);
lean_inc(v_snd_203_);
lean_dec_ref(v_x_201_);
v___x_204_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
v___x_205_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_205_ == 0)
{
lean_dec(v_snd_203_);
lean_dec(v_fst_202_);
lean_dec_ref(v_inst_200_);
lean_dec_ref(v_inst_199_);
return v___x_204_;
}
else
{
lean_object* v___x_206_; 
v___x_206_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_199_, v_inst_200_, v___x_204_, v_fst_202_, v_snd_203_);
return v___x_206_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg(lean_object* v_inst_207_, lean_object* v_inst_208_){
_start:
{
lean_object* v___f_209_; 
v___f_209_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_209_, 0, v_inst_207_);
lean_closure_set(v___f_209_, 1, v_inst_208_);
return v___f_209_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable(lean_object* v_00_u03b1_210_, lean_object* v_00_u03b2_211_, lean_object* v_inst_212_, lean_object* v_inst_213_){
_start:
{
lean_object* v___f_214_; 
v___f_214_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_214_, 0, v_inst_212_);
lean_closure_set(v___f_214_, 1, v_inst_213_);
return v___f_214_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable___redArg___lam__0(lean_object* v_inst_215_, lean_object* v_inst_216_, lean_object* v_x_217_, lean_object* v_s_218_){
_start:
{
lean_object* v_fst_219_; lean_object* v_snd_220_; lean_object* v_buckets_221_; lean_object* v___x_222_; lean_object* v___x_223_; uint8_t v___x_224_; 
v_fst_219_ = lean_ctor_get(v_x_217_, 0);
lean_inc(v_fst_219_);
v_snd_220_ = lean_ctor_get(v_x_217_, 1);
lean_inc(v_snd_220_);
lean_dec_ref(v_x_217_);
v_buckets_221_ = lean_ctor_get(v_s_218_, 1);
v___x_222_ = lean_unsigned_to_nat(0u);
v___x_223_ = lean_array_get_size(v_buckets_221_);
v___x_224_ = lean_nat_dec_lt(v___x_222_, v___x_223_);
if (v___x_224_ == 0)
{
lean_dec(v_snd_220_);
lean_dec(v_fst_219_);
lean_dec_ref(v_inst_216_);
lean_dec_ref(v_inst_215_);
return v_s_218_;
}
else
{
lean_object* v___x_225_; 
v___x_225_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_215_, v_inst_216_, v_s_218_, v_fst_219_, v_snd_220_);
return v___x_225_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable___redArg(lean_object* v_inst_226_, lean_object* v_inst_227_){
_start:
{
lean_object* v___f_228_; 
v___f_228_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_228_, 0, v_inst_226_);
lean_closure_set(v___f_228_, 1, v_inst_227_);
return v___f_228_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable(lean_object* v_00_u03b1_229_, lean_object* v_00_u03b2_230_, lean_object* v_inst_231_, lean_object* v_inst_232_){
_start:
{
lean_object* v___f_233_; 
v___f_233_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_233_, 0, v_inst_231_);
lean_closure_set(v___f_233_, 1, v_inst_232_);
return v___f_233_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insertIfNew___redArg(lean_object* v_inst_234_, lean_object* v_inst_235_, lean_object* v_m_236_, lean_object* v_a_237_, lean_object* v_b_238_){
_start:
{
lean_object* v_buckets_239_; lean_object* v___x_240_; lean_object* v___x_241_; uint8_t v___x_242_; 
v_buckets_239_ = lean_ctor_get(v_m_236_, 1);
v___x_240_ = lean_unsigned_to_nat(0u);
v___x_241_ = lean_array_get_size(v_buckets_239_);
v___x_242_ = lean_nat_dec_lt(v___x_240_, v___x_241_);
if (v___x_242_ == 0)
{
lean_dec(v_b_238_);
lean_dec(v_a_237_);
lean_dec_ref(v_inst_235_);
lean_dec_ref(v_inst_234_);
return v_m_236_;
}
else
{
lean_object* v___x_243_; 
v___x_243_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_234_, v_inst_235_, v_m_236_, v_a_237_, v_b_238_);
return v___x_243_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insertIfNew(lean_object* v_00_u03b1_244_, lean_object* v_00_u03b2_245_, lean_object* v_inst_246_, lean_object* v_inst_247_, lean_object* v_m_248_, lean_object* v_a_249_, lean_object* v_b_250_){
_start:
{
lean_object* v_buckets_251_; lean_object* v___x_252_; lean_object* v___x_253_; uint8_t v___x_254_; 
v_buckets_251_ = lean_ctor_get(v_m_248_, 1);
v___x_252_ = lean_unsigned_to_nat(0u);
v___x_253_ = lean_array_get_size(v_buckets_251_);
v___x_254_ = lean_nat_dec_lt(v___x_252_, v___x_253_);
if (v___x_254_ == 0)
{
lean_dec(v_b_250_);
lean_dec(v_a_249_);
lean_dec_ref(v_inst_247_);
lean_dec_ref(v_inst_246_);
return v_m_248_;
}
else
{
lean_object* v___x_255_; 
v___x_255_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_246_, v_inst_247_, v_m_248_, v_a_249_, v_b_250_);
return v___x_255_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_containsThenInsert___redArg(lean_object* v_inst_256_, lean_object* v_inst_257_, lean_object* v_m_258_, lean_object* v_a_259_, lean_object* v_b_260_){
_start:
{
lean_object* v_size_261_; lean_object* v_buckets_262_; lean_object* v___x_263_; lean_object* v___x_264_; uint8_t v___x_265_; 
v_size_261_ = lean_ctor_get(v_m_258_, 0);
v_buckets_262_ = lean_ctor_get(v_m_258_, 1);
v___x_263_ = lean_unsigned_to_nat(0u);
v___x_264_ = lean_array_get_size(v_buckets_262_);
v___x_265_ = lean_nat_dec_lt(v___x_263_, v___x_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; lean_object* v___x_267_; 
lean_dec(v_b_260_);
lean_dec(v_a_259_);
lean_dec_ref(v_inst_257_);
lean_dec_ref(v_inst_256_);
v___x_266_ = lean_box(v___x_265_);
v___x_267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
lean_ctor_set(v___x_267_, 1, v_m_258_);
return v___x_267_;
}
else
{
lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_317_; 
lean_inc_ref(v_buckets_262_);
lean_inc(v_size_261_);
v_isSharedCheck_317_ = !lean_is_exclusive(v_m_258_);
if (v_isSharedCheck_317_ == 0)
{
lean_object* v_unused_318_; lean_object* v_unused_319_; 
v_unused_318_ = lean_ctor_get(v_m_258_, 1);
lean_dec(v_unused_318_);
v_unused_319_ = lean_ctor_get(v_m_258_, 0);
lean_dec(v_unused_319_);
v___x_269_ = v_m_258_;
v_isShared_270_ = v_isSharedCheck_317_;
goto v_resetjp_268_;
}
else
{
lean_dec(v_m_258_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_317_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_271_; uint64_t v___x_272_; uint64_t v___x_273_; uint64_t v___x_274_; uint64_t v___x_275_; uint64_t v_fold_276_; uint64_t v___x_277_; uint64_t v___x_278_; uint64_t v___x_279_; size_t v___x_280_; size_t v___x_281_; size_t v___x_282_; size_t v___x_283_; size_t v___x_284_; lean_object* v_bkt_285_; uint8_t v___x_286_; 
lean_inc_ref(v_inst_257_);
lean_inc_n(v_a_259_, 2);
v___x_271_ = lean_apply_1(v_inst_257_, v_a_259_);
v___x_272_ = 32ULL;
v___x_273_ = lean_unbox_uint64(v___x_271_);
v___x_274_ = lean_uint64_shift_right(v___x_273_, v___x_272_);
v___x_275_ = lean_unbox_uint64(v___x_271_);
lean_dec_ref(v___x_271_);
v_fold_276_ = lean_uint64_xor(v___x_275_, v___x_274_);
v___x_277_ = 16ULL;
v___x_278_ = lean_uint64_shift_right(v_fold_276_, v___x_277_);
v___x_279_ = lean_uint64_xor(v_fold_276_, v___x_278_);
v___x_280_ = lean_uint64_to_usize(v___x_279_);
v___x_281_ = lean_usize_of_nat(v___x_264_);
v___x_282_ = ((size_t)1ULL);
v___x_283_ = lean_usize_sub(v___x_281_, v___x_282_);
v___x_284_ = lean_usize_land(v___x_280_, v___x_283_);
v_bkt_285_ = lean_array_uget_borrowed(v_buckets_262_, v___x_284_);
lean_inc(v_bkt_285_);
lean_inc_ref(v_inst_256_);
v___x_286_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_256_, v_a_259_, v_bkt_285_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; lean_object* v_size_x27_288_; lean_object* v___x_289_; lean_object* v_buckets_x27_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; uint8_t v___x_296_; 
lean_dec_ref(v_inst_256_);
v___x_287_ = lean_unsigned_to_nat(1u);
v_size_x27_288_ = lean_nat_add(v_size_261_, v___x_287_);
lean_dec(v_size_261_);
lean_inc(v_bkt_285_);
v___x_289_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_289_, 0, v_a_259_);
lean_ctor_set(v___x_289_, 1, v_b_260_);
lean_ctor_set(v___x_289_, 2, v_bkt_285_);
v_buckets_x27_290_ = lean_array_uset(v_buckets_262_, v___x_284_, v___x_289_);
v___x_291_ = lean_unsigned_to_nat(4u);
v___x_292_ = lean_nat_mul(v_size_x27_288_, v___x_291_);
v___x_293_ = lean_unsigned_to_nat(3u);
v___x_294_ = lean_nat_div(v___x_292_, v___x_293_);
lean_dec(v___x_292_);
v___x_295_ = lean_array_get_size(v_buckets_x27_290_);
v___x_296_ = lean_nat_dec_le(v___x_294_, v___x_295_);
lean_dec(v___x_294_);
if (v___x_296_ == 0)
{
lean_object* v_val_297_; lean_object* v___x_299_; 
v_val_297_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_257_, v_buckets_x27_290_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 1, v_val_297_);
lean_ctor_set(v___x_269_, 0, v_size_x27_288_);
v___x_299_ = v___x_269_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_size_x27_288_);
lean_ctor_set(v_reuseFailAlloc_302_, 1, v_val_297_);
v___x_299_ = v_reuseFailAlloc_302_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = lean_box(v___x_286_);
v___x_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
lean_ctor_set(v___x_301_, 1, v___x_299_);
return v___x_301_;
}
}
else
{
lean_object* v___x_304_; 
lean_dec_ref(v_inst_257_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 1, v_buckets_x27_290_);
lean_ctor_set(v___x_269_, 0, v_size_x27_288_);
v___x_304_ = v___x_269_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_size_x27_288_);
lean_ctor_set(v_reuseFailAlloc_307_, 1, v_buckets_x27_290_);
v___x_304_ = v_reuseFailAlloc_307_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = lean_box(v___x_286_);
v___x_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
lean_ctor_set(v___x_306_, 1, v___x_304_);
return v___x_306_;
}
}
}
else
{
lean_object* v___x_308_; lean_object* v_buckets_x27_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_313_; 
lean_inc(v_bkt_285_);
lean_dec_ref(v_inst_257_);
v___x_308_ = lean_box(0);
v_buckets_x27_309_ = lean_array_uset(v_buckets_262_, v___x_284_, v___x_308_);
v___x_310_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_inst_256_, v_a_259_, v_b_260_, v_bkt_285_);
v___x_311_ = lean_array_uset(v_buckets_x27_309_, v___x_284_, v___x_310_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 1, v___x_311_);
v___x_313_ = v___x_269_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_size_261_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v___x_311_);
v___x_313_ = v_reuseFailAlloc_316_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = lean_box(v___x_286_);
v___x_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
lean_ctor_set(v___x_315_, 1, v___x_313_);
return v___x_315_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_containsThenInsert(lean_object* v_00_u03b1_320_, lean_object* v_00_u03b2_321_, lean_object* v_inst_322_, lean_object* v_inst_323_, lean_object* v_m_324_, lean_object* v_a_325_, lean_object* v_b_326_){
_start:
{
lean_object* v_size_327_; lean_object* v_buckets_328_; lean_object* v___x_329_; lean_object* v___x_330_; uint8_t v___x_331_; 
v_size_327_ = lean_ctor_get(v_m_324_, 0);
v_buckets_328_ = lean_ctor_get(v_m_324_, 1);
v___x_329_ = lean_unsigned_to_nat(0u);
v___x_330_ = lean_array_get_size(v_buckets_328_);
v___x_331_ = lean_nat_dec_lt(v___x_329_, v___x_330_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; lean_object* v___x_333_; 
lean_dec(v_b_326_);
lean_dec(v_a_325_);
lean_dec_ref(v_inst_323_);
lean_dec_ref(v_inst_322_);
v___x_332_ = lean_box(v___x_331_);
v___x_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v_m_324_);
return v___x_333_;
}
else
{
lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_383_; 
lean_inc_ref(v_buckets_328_);
lean_inc(v_size_327_);
v_isSharedCheck_383_ = !lean_is_exclusive(v_m_324_);
if (v_isSharedCheck_383_ == 0)
{
lean_object* v_unused_384_; lean_object* v_unused_385_; 
v_unused_384_ = lean_ctor_get(v_m_324_, 1);
lean_dec(v_unused_384_);
v_unused_385_ = lean_ctor_get(v_m_324_, 0);
lean_dec(v_unused_385_);
v___x_335_ = v_m_324_;
v_isShared_336_ = v_isSharedCheck_383_;
goto v_resetjp_334_;
}
else
{
lean_dec(v_m_324_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_383_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_337_; uint64_t v___x_338_; uint64_t v___x_339_; uint64_t v___x_340_; uint64_t v___x_341_; uint64_t v_fold_342_; uint64_t v___x_343_; uint64_t v___x_344_; uint64_t v___x_345_; size_t v___x_346_; size_t v___x_347_; size_t v___x_348_; size_t v___x_349_; size_t v___x_350_; lean_object* v_bkt_351_; uint8_t v___x_352_; 
lean_inc_ref(v_inst_323_);
lean_inc_n(v_a_325_, 2);
v___x_337_ = lean_apply_1(v_inst_323_, v_a_325_);
v___x_338_ = 32ULL;
v___x_339_ = lean_unbox_uint64(v___x_337_);
v___x_340_ = lean_uint64_shift_right(v___x_339_, v___x_338_);
v___x_341_ = lean_unbox_uint64(v___x_337_);
lean_dec_ref(v___x_337_);
v_fold_342_ = lean_uint64_xor(v___x_341_, v___x_340_);
v___x_343_ = 16ULL;
v___x_344_ = lean_uint64_shift_right(v_fold_342_, v___x_343_);
v___x_345_ = lean_uint64_xor(v_fold_342_, v___x_344_);
v___x_346_ = lean_uint64_to_usize(v___x_345_);
v___x_347_ = lean_usize_of_nat(v___x_330_);
v___x_348_ = ((size_t)1ULL);
v___x_349_ = lean_usize_sub(v___x_347_, v___x_348_);
v___x_350_ = lean_usize_land(v___x_346_, v___x_349_);
v_bkt_351_ = lean_array_uget_borrowed(v_buckets_328_, v___x_350_);
lean_inc(v_bkt_351_);
lean_inc_ref(v_inst_322_);
v___x_352_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_322_, v_a_325_, v_bkt_351_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; lean_object* v_size_x27_354_; lean_object* v___x_355_; lean_object* v_buckets_x27_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
lean_dec_ref(v_inst_322_);
v___x_353_ = lean_unsigned_to_nat(1u);
v_size_x27_354_ = lean_nat_add(v_size_327_, v___x_353_);
lean_dec(v_size_327_);
lean_inc(v_bkt_351_);
v___x_355_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_355_, 0, v_a_325_);
lean_ctor_set(v___x_355_, 1, v_b_326_);
lean_ctor_set(v___x_355_, 2, v_bkt_351_);
v_buckets_x27_356_ = lean_array_uset(v_buckets_328_, v___x_350_, v___x_355_);
v___x_357_ = lean_unsigned_to_nat(4u);
v___x_358_ = lean_nat_mul(v_size_x27_354_, v___x_357_);
v___x_359_ = lean_unsigned_to_nat(3u);
v___x_360_ = lean_nat_div(v___x_358_, v___x_359_);
lean_dec(v___x_358_);
v___x_361_ = lean_array_get_size(v_buckets_x27_356_);
v___x_362_ = lean_nat_dec_le(v___x_360_, v___x_361_);
lean_dec(v___x_360_);
if (v___x_362_ == 0)
{
lean_object* v_val_363_; lean_object* v___x_365_; 
v_val_363_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_323_, v_buckets_x27_356_);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 1, v_val_363_);
lean_ctor_set(v___x_335_, 0, v_size_x27_354_);
v___x_365_ = v___x_335_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_size_x27_354_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v_val_363_);
v___x_365_ = v_reuseFailAlloc_368_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = lean_box(v___x_352_);
v___x_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
lean_ctor_set(v___x_367_, 1, v___x_365_);
return v___x_367_;
}
}
else
{
lean_object* v___x_370_; 
lean_dec_ref(v_inst_323_);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 1, v_buckets_x27_356_);
lean_ctor_set(v___x_335_, 0, v_size_x27_354_);
v___x_370_ = v___x_335_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_size_x27_354_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v_buckets_x27_356_);
v___x_370_ = v_reuseFailAlloc_373_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = lean_box(v___x_352_);
v___x_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
lean_ctor_set(v___x_372_, 1, v___x_370_);
return v___x_372_;
}
}
}
else
{
lean_object* v___x_374_; lean_object* v_buckets_x27_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_379_; 
lean_inc(v_bkt_351_);
lean_dec_ref(v_inst_323_);
v___x_374_ = lean_box(0);
v_buckets_x27_375_ = lean_array_uset(v_buckets_328_, v___x_350_, v___x_374_);
v___x_376_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_inst_322_, v_a_325_, v_b_326_, v_bkt_351_);
v___x_377_ = lean_array_uset(v_buckets_x27_375_, v___x_350_, v___x_376_);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 1, v___x_377_);
v___x_379_ = v___x_335_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_size_327_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v___x_377_);
v___x_379_ = v_reuseFailAlloc_382_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = lean_box(v___x_352_);
v___x_381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
lean_ctor_set(v___x_381_, 1, v___x_379_);
return v___x_381_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getThenInsertIfNew_x3f___redArg(lean_object* v_inst_386_, lean_object* v_inst_387_, lean_object* v_m_388_, lean_object* v_a_389_, lean_object* v_b_390_){
_start:
{
lean_object* v_size_391_; lean_object* v_buckets_392_; lean_object* v___x_393_; lean_object* v___x_394_; uint8_t v___x_395_; 
v_size_391_ = lean_ctor_get(v_m_388_, 0);
v_buckets_392_ = lean_ctor_get(v_m_388_, 1);
v___x_393_ = lean_unsigned_to_nat(0u);
v___x_394_ = lean_array_get_size(v_buckets_392_);
v___x_395_ = lean_nat_dec_lt(v___x_393_, v___x_394_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; lean_object* v___x_397_; 
lean_dec(v_b_390_);
lean_dec(v_a_389_);
lean_dec_ref(v_inst_387_);
lean_dec_ref(v_inst_386_);
v___x_396_ = lean_box(0);
v___x_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
lean_ctor_set(v___x_397_, 1, v_m_388_);
return v___x_397_;
}
else
{
lean_object* v___x_398_; uint64_t v___x_399_; uint64_t v___x_400_; uint64_t v___x_401_; uint64_t v___x_402_; uint64_t v_fold_403_; uint64_t v___x_404_; uint64_t v___x_405_; uint64_t v___x_406_; size_t v___x_407_; size_t v___x_408_; size_t v___x_409_; size_t v___x_410_; size_t v___x_411_; lean_object* v_bkt_412_; lean_object* v___x_413_; 
lean_inc_ref(v_inst_387_);
lean_inc_n(v_a_389_, 2);
v___x_398_ = lean_apply_1(v_inst_387_, v_a_389_);
v___x_399_ = 32ULL;
v___x_400_ = lean_unbox_uint64(v___x_398_);
v___x_401_ = lean_uint64_shift_right(v___x_400_, v___x_399_);
v___x_402_ = lean_unbox_uint64(v___x_398_);
lean_dec_ref(v___x_398_);
v_fold_403_ = lean_uint64_xor(v___x_402_, v___x_401_);
v___x_404_ = 16ULL;
v___x_405_ = lean_uint64_shift_right(v_fold_403_, v___x_404_);
v___x_406_ = lean_uint64_xor(v_fold_403_, v___x_405_);
v___x_407_ = lean_uint64_to_usize(v___x_406_);
v___x_408_ = lean_usize_of_nat(v___x_394_);
v___x_409_ = ((size_t)1ULL);
v___x_410_ = lean_usize_sub(v___x_408_, v___x_409_);
v___x_411_ = lean_usize_land(v___x_407_, v___x_410_);
v_bkt_412_ = lean_array_uget_borrowed(v_buckets_392_, v___x_411_);
lean_inc(v_bkt_412_);
v___x_413_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(v_inst_386_, v_a_389_, v_bkt_412_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_436_; 
lean_inc_ref(v_buckets_392_);
lean_inc(v_size_391_);
v_isSharedCheck_436_ = !lean_is_exclusive(v_m_388_);
if (v_isSharedCheck_436_ == 0)
{
lean_object* v_unused_437_; lean_object* v_unused_438_; 
v_unused_437_ = lean_ctor_get(v_m_388_, 1);
lean_dec(v_unused_437_);
v_unused_438_ = lean_ctor_get(v_m_388_, 0);
lean_dec(v_unused_438_);
v___x_415_ = v_m_388_;
v_isShared_416_ = v_isSharedCheck_436_;
goto v_resetjp_414_;
}
else
{
lean_dec(v_m_388_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_436_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_417_; lean_object* v_size_x27_418_; lean_object* v___x_419_; lean_object* v_buckets_x27_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; uint8_t v___x_426_; 
v___x_417_ = lean_unsigned_to_nat(1u);
v_size_x27_418_ = lean_nat_add(v_size_391_, v___x_417_);
lean_dec(v_size_391_);
lean_inc(v_bkt_412_);
v___x_419_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_419_, 0, v_a_389_);
lean_ctor_set(v___x_419_, 1, v_b_390_);
lean_ctor_set(v___x_419_, 2, v_bkt_412_);
v_buckets_x27_420_ = lean_array_uset(v_buckets_392_, v___x_411_, v___x_419_);
v___x_421_ = lean_unsigned_to_nat(4u);
v___x_422_ = lean_nat_mul(v_size_x27_418_, v___x_421_);
v___x_423_ = lean_unsigned_to_nat(3u);
v___x_424_ = lean_nat_div(v___x_422_, v___x_423_);
lean_dec(v___x_422_);
v___x_425_ = lean_array_get_size(v_buckets_x27_420_);
v___x_426_ = lean_nat_dec_le(v___x_424_, v___x_425_);
lean_dec(v___x_424_);
if (v___x_426_ == 0)
{
lean_object* v_val_427_; lean_object* v___x_429_; 
v_val_427_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_387_, v_buckets_x27_420_);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 1, v_val_427_);
lean_ctor_set(v___x_415_, 0, v_size_x27_418_);
v___x_429_ = v___x_415_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_size_x27_418_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v_val_427_);
v___x_429_ = v_reuseFailAlloc_431_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
lean_object* v___x_430_; 
v___x_430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_430_, 0, v___x_413_);
lean_ctor_set(v___x_430_, 1, v___x_429_);
return v___x_430_;
}
}
else
{
lean_object* v___x_433_; 
lean_dec_ref(v_inst_387_);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 1, v_buckets_x27_420_);
lean_ctor_set(v___x_415_, 0, v_size_x27_418_);
v___x_433_ = v___x_415_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_size_x27_418_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v_buckets_x27_420_);
v___x_433_ = v_reuseFailAlloc_435_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
lean_object* v___x_434_; 
v___x_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_413_);
lean_ctor_set(v___x_434_, 1, v___x_433_);
return v___x_434_;
}
}
}
}
else
{
lean_object* v___x_439_; 
lean_dec(v_b_390_);
lean_dec(v_a_389_);
lean_dec_ref(v_inst_387_);
v___x_439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_439_, 0, v___x_413_);
lean_ctor_set(v___x_439_, 1, v_m_388_);
return v___x_439_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_440_, lean_object* v_00_u03b2_441_, lean_object* v_inst_442_, lean_object* v_inst_443_, lean_object* v_inst_444_, lean_object* v_m_445_, lean_object* v_a_446_, lean_object* v_b_447_){
_start:
{
lean_object* v_size_448_; lean_object* v_buckets_449_; lean_object* v___x_450_; lean_object* v___x_451_; uint8_t v___x_452_; 
v_size_448_ = lean_ctor_get(v_m_445_, 0);
v_buckets_449_ = lean_ctor_get(v_m_445_, 1);
v___x_450_ = lean_unsigned_to_nat(0u);
v___x_451_ = lean_array_get_size(v_buckets_449_);
v___x_452_ = lean_nat_dec_lt(v___x_450_, v___x_451_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; lean_object* v___x_454_; 
lean_dec(v_b_447_);
lean_dec(v_a_446_);
lean_dec_ref(v_inst_443_);
lean_dec_ref(v_inst_442_);
v___x_453_ = lean_box(0);
v___x_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_453_);
lean_ctor_set(v___x_454_, 1, v_m_445_);
return v___x_454_;
}
else
{
lean_object* v___x_455_; uint64_t v___x_456_; uint64_t v___x_457_; uint64_t v___x_458_; uint64_t v___x_459_; uint64_t v_fold_460_; uint64_t v___x_461_; uint64_t v___x_462_; uint64_t v___x_463_; size_t v___x_464_; size_t v___x_465_; size_t v___x_466_; size_t v___x_467_; size_t v___x_468_; lean_object* v_bkt_469_; lean_object* v___x_470_; 
lean_inc_ref(v_inst_443_);
lean_inc_n(v_a_446_, 2);
v___x_455_ = lean_apply_1(v_inst_443_, v_a_446_);
v___x_456_ = 32ULL;
v___x_457_ = lean_unbox_uint64(v___x_455_);
v___x_458_ = lean_uint64_shift_right(v___x_457_, v___x_456_);
v___x_459_ = lean_unbox_uint64(v___x_455_);
lean_dec_ref(v___x_455_);
v_fold_460_ = lean_uint64_xor(v___x_459_, v___x_458_);
v___x_461_ = 16ULL;
v___x_462_ = lean_uint64_shift_right(v_fold_460_, v___x_461_);
v___x_463_ = lean_uint64_xor(v_fold_460_, v___x_462_);
v___x_464_ = lean_uint64_to_usize(v___x_463_);
v___x_465_ = lean_usize_of_nat(v___x_451_);
v___x_466_ = ((size_t)1ULL);
v___x_467_ = lean_usize_sub(v___x_465_, v___x_466_);
v___x_468_ = lean_usize_land(v___x_464_, v___x_467_);
v_bkt_469_ = lean_array_uget_borrowed(v_buckets_449_, v___x_468_);
lean_inc(v_bkt_469_);
v___x_470_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(v_inst_442_, v_a_446_, v_bkt_469_);
if (lean_obj_tag(v___x_470_) == 0)
{
lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_493_; 
lean_inc_ref(v_buckets_449_);
lean_inc(v_size_448_);
v_isSharedCheck_493_ = !lean_is_exclusive(v_m_445_);
if (v_isSharedCheck_493_ == 0)
{
lean_object* v_unused_494_; lean_object* v_unused_495_; 
v_unused_494_ = lean_ctor_get(v_m_445_, 1);
lean_dec(v_unused_494_);
v_unused_495_ = lean_ctor_get(v_m_445_, 0);
lean_dec(v_unused_495_);
v___x_472_ = v_m_445_;
v_isShared_473_ = v_isSharedCheck_493_;
goto v_resetjp_471_;
}
else
{
lean_dec(v_m_445_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_493_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_474_; lean_object* v_size_x27_475_; lean_object* v___x_476_; lean_object* v_buckets_x27_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; uint8_t v___x_483_; 
v___x_474_ = lean_unsigned_to_nat(1u);
v_size_x27_475_ = lean_nat_add(v_size_448_, v___x_474_);
lean_dec(v_size_448_);
lean_inc(v_bkt_469_);
v___x_476_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_476_, 0, v_a_446_);
lean_ctor_set(v___x_476_, 1, v_b_447_);
lean_ctor_set(v___x_476_, 2, v_bkt_469_);
v_buckets_x27_477_ = lean_array_uset(v_buckets_449_, v___x_468_, v___x_476_);
v___x_478_ = lean_unsigned_to_nat(4u);
v___x_479_ = lean_nat_mul(v_size_x27_475_, v___x_478_);
v___x_480_ = lean_unsigned_to_nat(3u);
v___x_481_ = lean_nat_div(v___x_479_, v___x_480_);
lean_dec(v___x_479_);
v___x_482_ = lean_array_get_size(v_buckets_x27_477_);
v___x_483_ = lean_nat_dec_le(v___x_481_, v___x_482_);
lean_dec(v___x_481_);
if (v___x_483_ == 0)
{
lean_object* v_val_484_; lean_object* v___x_486_; 
v_val_484_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_443_, v_buckets_x27_477_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 1, v_val_484_);
lean_ctor_set(v___x_472_, 0, v_size_x27_475_);
v___x_486_ = v___x_472_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_size_x27_475_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v_val_484_);
v___x_486_ = v_reuseFailAlloc_488_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
lean_object* v___x_487_; 
v___x_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_470_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
return v___x_487_;
}
}
else
{
lean_object* v___x_490_; 
lean_dec_ref(v_inst_443_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 1, v_buckets_x27_477_);
lean_ctor_set(v___x_472_, 0, v_size_x27_475_);
v___x_490_ = v___x_472_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_size_x27_475_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v_buckets_x27_477_);
v___x_490_ = v_reuseFailAlloc_492_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_object* v___x_491_; 
v___x_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_491_, 0, v___x_470_);
lean_ctor_set(v___x_491_, 1, v___x_490_);
return v___x_491_;
}
}
}
}
else
{
lean_object* v___x_496_; 
lean_dec(v_b_447_);
lean_dec(v_a_446_);
lean_dec_ref(v_inst_443_);
v___x_496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_470_);
lean_ctor_set(v___x_496_, 1, v_m_445_);
return v___x_496_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_containsThenInsertIfNew___redArg(lean_object* v_inst_497_, lean_object* v_inst_498_, lean_object* v_m_499_, lean_object* v_a_500_, lean_object* v_b_501_){
_start:
{
lean_object* v_size_502_; lean_object* v_buckets_503_; lean_object* v___x_504_; lean_object* v___x_505_; uint8_t v___x_506_; 
v_size_502_ = lean_ctor_get(v_m_499_, 0);
v_buckets_503_ = lean_ctor_get(v_m_499_, 1);
v___x_504_ = lean_unsigned_to_nat(0u);
v___x_505_ = lean_array_get_size(v_buckets_503_);
v___x_506_ = lean_nat_dec_lt(v___x_504_, v___x_505_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; lean_object* v___x_508_; 
lean_dec(v_b_501_);
lean_dec(v_a_500_);
lean_dec_ref(v_inst_498_);
lean_dec_ref(v_inst_497_);
v___x_507_ = lean_box(v___x_506_);
v___x_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
lean_ctor_set(v___x_508_, 1, v_m_499_);
return v___x_508_;
}
else
{
lean_object* v___x_509_; uint64_t v___x_510_; uint64_t v___x_511_; uint64_t v___x_512_; uint64_t v___x_513_; uint64_t v_fold_514_; uint64_t v___x_515_; uint64_t v___x_516_; uint64_t v___x_517_; size_t v___x_518_; size_t v___x_519_; size_t v___x_520_; size_t v___x_521_; size_t v___x_522_; lean_object* v_bkt_523_; uint8_t v___x_524_; 
lean_inc_ref(v_inst_498_);
lean_inc_n(v_a_500_, 2);
v___x_509_ = lean_apply_1(v_inst_498_, v_a_500_);
v___x_510_ = 32ULL;
v___x_511_ = lean_unbox_uint64(v___x_509_);
v___x_512_ = lean_uint64_shift_right(v___x_511_, v___x_510_);
v___x_513_ = lean_unbox_uint64(v___x_509_);
lean_dec_ref(v___x_509_);
v_fold_514_ = lean_uint64_xor(v___x_513_, v___x_512_);
v___x_515_ = 16ULL;
v___x_516_ = lean_uint64_shift_right(v_fold_514_, v___x_515_);
v___x_517_ = lean_uint64_xor(v_fold_514_, v___x_516_);
v___x_518_ = lean_uint64_to_usize(v___x_517_);
v___x_519_ = lean_usize_of_nat(v___x_505_);
v___x_520_ = ((size_t)1ULL);
v___x_521_ = lean_usize_sub(v___x_519_, v___x_520_);
v___x_522_ = lean_usize_land(v___x_518_, v___x_521_);
v_bkt_523_ = lean_array_uget_borrowed(v_buckets_503_, v___x_522_);
lean_inc(v_bkt_523_);
v___x_524_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_497_, v_a_500_, v_bkt_523_);
if (v___x_524_ == 0)
{
lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_549_; 
lean_inc_ref(v_buckets_503_);
lean_inc(v_size_502_);
v_isSharedCheck_549_ = !lean_is_exclusive(v_m_499_);
if (v_isSharedCheck_549_ == 0)
{
lean_object* v_unused_550_; lean_object* v_unused_551_; 
v_unused_550_ = lean_ctor_get(v_m_499_, 1);
lean_dec(v_unused_550_);
v_unused_551_ = lean_ctor_get(v_m_499_, 0);
lean_dec(v_unused_551_);
v___x_526_ = v_m_499_;
v_isShared_527_ = v_isSharedCheck_549_;
goto v_resetjp_525_;
}
else
{
lean_dec(v_m_499_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_549_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_528_; lean_object* v_size_x27_529_; lean_object* v___x_530_; lean_object* v_buckets_x27_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; uint8_t v___x_537_; 
v___x_528_ = lean_unsigned_to_nat(1u);
v_size_x27_529_ = lean_nat_add(v_size_502_, v___x_528_);
lean_dec(v_size_502_);
lean_inc(v_bkt_523_);
v___x_530_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_530_, 0, v_a_500_);
lean_ctor_set(v___x_530_, 1, v_b_501_);
lean_ctor_set(v___x_530_, 2, v_bkt_523_);
v_buckets_x27_531_ = lean_array_uset(v_buckets_503_, v___x_522_, v___x_530_);
v___x_532_ = lean_unsigned_to_nat(4u);
v___x_533_ = lean_nat_mul(v_size_x27_529_, v___x_532_);
v___x_534_ = lean_unsigned_to_nat(3u);
v___x_535_ = lean_nat_div(v___x_533_, v___x_534_);
lean_dec(v___x_533_);
v___x_536_ = lean_array_get_size(v_buckets_x27_531_);
v___x_537_ = lean_nat_dec_le(v___x_535_, v___x_536_);
lean_dec(v___x_535_);
if (v___x_537_ == 0)
{
lean_object* v_val_538_; lean_object* v___x_540_; 
v_val_538_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_498_, v_buckets_x27_531_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 1, v_val_538_);
lean_ctor_set(v___x_526_, 0, v_size_x27_529_);
v___x_540_ = v___x_526_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_size_x27_529_);
lean_ctor_set(v_reuseFailAlloc_543_, 1, v_val_538_);
v___x_540_ = v_reuseFailAlloc_543_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = lean_box(v___x_524_);
v___x_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
lean_ctor_set(v___x_542_, 1, v___x_540_);
return v___x_542_;
}
}
else
{
lean_object* v___x_545_; 
lean_dec_ref(v_inst_498_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 1, v_buckets_x27_531_);
lean_ctor_set(v___x_526_, 0, v_size_x27_529_);
v___x_545_ = v___x_526_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_size_x27_529_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v_buckets_x27_531_);
v___x_545_ = v_reuseFailAlloc_548_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = lean_box(v___x_524_);
v___x_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
lean_ctor_set(v___x_547_, 1, v___x_545_);
return v___x_547_;
}
}
}
}
else
{
lean_object* v___x_552_; lean_object* v___x_553_; 
lean_dec(v_b_501_);
lean_dec(v_a_500_);
lean_dec_ref(v_inst_498_);
v___x_552_ = lean_box(v___x_524_);
v___x_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
lean_ctor_set(v___x_553_, 1, v_m_499_);
return v___x_553_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_containsThenInsertIfNew(lean_object* v_00_u03b1_554_, lean_object* v_00_u03b2_555_, lean_object* v_inst_556_, lean_object* v_inst_557_, lean_object* v_m_558_, lean_object* v_a_559_, lean_object* v_b_560_){
_start:
{
lean_object* v_size_561_; lean_object* v_buckets_562_; lean_object* v___x_563_; lean_object* v___x_564_; uint8_t v___x_565_; 
v_size_561_ = lean_ctor_get(v_m_558_, 0);
v_buckets_562_ = lean_ctor_get(v_m_558_, 1);
v___x_563_ = lean_unsigned_to_nat(0u);
v___x_564_ = lean_array_get_size(v_buckets_562_);
v___x_565_ = lean_nat_dec_lt(v___x_563_, v___x_564_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; lean_object* v___x_567_; 
lean_dec(v_b_560_);
lean_dec(v_a_559_);
lean_dec_ref(v_inst_557_);
lean_dec_ref(v_inst_556_);
v___x_566_ = lean_box(v___x_565_);
v___x_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
lean_ctor_set(v___x_567_, 1, v_m_558_);
return v___x_567_;
}
else
{
lean_object* v___x_568_; uint64_t v___x_569_; uint64_t v___x_570_; uint64_t v___x_571_; uint64_t v___x_572_; uint64_t v_fold_573_; uint64_t v___x_574_; uint64_t v___x_575_; uint64_t v___x_576_; size_t v___x_577_; size_t v___x_578_; size_t v___x_579_; size_t v___x_580_; size_t v___x_581_; lean_object* v_bkt_582_; uint8_t v___x_583_; 
lean_inc_ref(v_inst_557_);
lean_inc_n(v_a_559_, 2);
v___x_568_ = lean_apply_1(v_inst_557_, v_a_559_);
v___x_569_ = 32ULL;
v___x_570_ = lean_unbox_uint64(v___x_568_);
v___x_571_ = lean_uint64_shift_right(v___x_570_, v___x_569_);
v___x_572_ = lean_unbox_uint64(v___x_568_);
lean_dec_ref(v___x_568_);
v_fold_573_ = lean_uint64_xor(v___x_572_, v___x_571_);
v___x_574_ = 16ULL;
v___x_575_ = lean_uint64_shift_right(v_fold_573_, v___x_574_);
v___x_576_ = lean_uint64_xor(v_fold_573_, v___x_575_);
v___x_577_ = lean_uint64_to_usize(v___x_576_);
v___x_578_ = lean_usize_of_nat(v___x_564_);
v___x_579_ = ((size_t)1ULL);
v___x_580_ = lean_usize_sub(v___x_578_, v___x_579_);
v___x_581_ = lean_usize_land(v___x_577_, v___x_580_);
v_bkt_582_ = lean_array_uget_borrowed(v_buckets_562_, v___x_581_);
lean_inc(v_bkt_582_);
v___x_583_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_556_, v_a_559_, v_bkt_582_);
if (v___x_583_ == 0)
{
lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_608_; 
lean_inc_ref(v_buckets_562_);
lean_inc(v_size_561_);
v_isSharedCheck_608_ = !lean_is_exclusive(v_m_558_);
if (v_isSharedCheck_608_ == 0)
{
lean_object* v_unused_609_; lean_object* v_unused_610_; 
v_unused_609_ = lean_ctor_get(v_m_558_, 1);
lean_dec(v_unused_609_);
v_unused_610_ = lean_ctor_get(v_m_558_, 0);
lean_dec(v_unused_610_);
v___x_585_ = v_m_558_;
v_isShared_586_ = v_isSharedCheck_608_;
goto v_resetjp_584_;
}
else
{
lean_dec(v_m_558_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_608_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_587_; lean_object* v_size_x27_588_; lean_object* v___x_589_; lean_object* v_buckets_x27_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_587_ = lean_unsigned_to_nat(1u);
v_size_x27_588_ = lean_nat_add(v_size_561_, v___x_587_);
lean_dec(v_size_561_);
lean_inc(v_bkt_582_);
v___x_589_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_589_, 0, v_a_559_);
lean_ctor_set(v___x_589_, 1, v_b_560_);
lean_ctor_set(v___x_589_, 2, v_bkt_582_);
v_buckets_x27_590_ = lean_array_uset(v_buckets_562_, v___x_581_, v___x_589_);
v___x_591_ = lean_unsigned_to_nat(4u);
v___x_592_ = lean_nat_mul(v_size_x27_588_, v___x_591_);
v___x_593_ = lean_unsigned_to_nat(3u);
v___x_594_ = lean_nat_div(v___x_592_, v___x_593_);
lean_dec(v___x_592_);
v___x_595_ = lean_array_get_size(v_buckets_x27_590_);
v___x_596_ = lean_nat_dec_le(v___x_594_, v___x_595_);
lean_dec(v___x_594_);
if (v___x_596_ == 0)
{
lean_object* v_val_597_; lean_object* v___x_599_; 
v_val_597_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_557_, v_buckets_x27_590_);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 1, v_val_597_);
lean_ctor_set(v___x_585_, 0, v_size_x27_588_);
v___x_599_ = v___x_585_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_size_x27_588_);
lean_ctor_set(v_reuseFailAlloc_602_, 1, v_val_597_);
v___x_599_ = v_reuseFailAlloc_602_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = lean_box(v___x_583_);
v___x_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
lean_ctor_set(v___x_601_, 1, v___x_599_);
return v___x_601_;
}
}
else
{
lean_object* v___x_604_; 
lean_dec_ref(v_inst_557_);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 1, v_buckets_x27_590_);
lean_ctor_set(v___x_585_, 0, v_size_x27_588_);
v___x_604_ = v___x_585_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_size_x27_588_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v_buckets_x27_590_);
v___x_604_ = v_reuseFailAlloc_607_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = lean_box(v___x_583_);
v___x_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
lean_ctor_set(v___x_606_, 1, v___x_604_);
return v___x_606_;
}
}
}
}
else
{
lean_object* v___x_611_; lean_object* v___x_612_; 
lean_dec(v_b_560_);
lean_dec(v_a_559_);
lean_dec_ref(v_inst_557_);
v___x_611_ = lean_box(v___x_583_);
v___x_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
lean_ctor_set(v___x_612_, 1, v_m_558_);
return v___x_612_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x3f___redArg(lean_object* v_inst_613_, lean_object* v_inst_614_, lean_object* v_m_615_, lean_object* v_a_616_){
_start:
{
lean_object* v_buckets_617_; lean_object* v___x_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
v_buckets_617_ = lean_ctor_get(v_m_615_, 1);
v___x_618_ = lean_unsigned_to_nat(0u);
v___x_619_ = lean_array_get_size(v_buckets_617_);
v___x_620_ = lean_nat_dec_lt(v___x_618_, v___x_619_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; 
lean_dec(v_a_616_);
lean_dec_ref(v_inst_614_);
lean_dec_ref(v_inst_613_);
v___x_621_ = lean_box(0);
return v___x_621_;
}
else
{
lean_object* v___x_622_; 
v___x_622_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(v_inst_613_, v_inst_614_, v_m_615_, v_a_616_);
return v___x_622_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x3f___redArg___boxed(lean_object* v_inst_623_, lean_object* v_inst_624_, lean_object* v_m_625_, lean_object* v_a_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Std_DHashMap_Raw_get_x3f___redArg(v_inst_623_, v_inst_624_, v_m_625_, v_a_626_);
lean_dec_ref(v_m_625_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x3f(lean_object* v_00_u03b1_628_, lean_object* v_00_u03b2_629_, lean_object* v_inst_630_, lean_object* v_inst_631_, lean_object* v_inst_632_, lean_object* v_m_633_, lean_object* v_a_634_){
_start:
{
lean_object* v_buckets_635_; lean_object* v___x_636_; lean_object* v___x_637_; uint8_t v___x_638_; 
v_buckets_635_ = lean_ctor_get(v_m_633_, 1);
v___x_636_ = lean_unsigned_to_nat(0u);
v___x_637_ = lean_array_get_size(v_buckets_635_);
v___x_638_ = lean_nat_dec_lt(v___x_636_, v___x_637_);
if (v___x_638_ == 0)
{
lean_object* v___x_639_; 
lean_dec(v_a_634_);
lean_dec_ref(v_inst_632_);
lean_dec_ref(v_inst_630_);
v___x_639_ = lean_box(0);
return v___x_639_;
}
else
{
lean_object* v___x_640_; 
v___x_640_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(v_inst_630_, v_inst_632_, v_m_633_, v_a_634_);
return v___x_640_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x3f___boxed(lean_object* v_00_u03b1_641_, lean_object* v_00_u03b2_642_, lean_object* v_inst_643_, lean_object* v_inst_644_, lean_object* v_inst_645_, lean_object* v_m_646_, lean_object* v_a_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Std_DHashMap_Raw_get_x3f(v_00_u03b1_641_, v_00_u03b2_642_, v_inst_643_, v_inst_644_, v_inst_645_, v_m_646_, v_a_647_);
lean_dec_ref(v_m_646_);
return v_res_648_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_contains___redArg(lean_object* v_inst_649_, lean_object* v_inst_650_, lean_object* v_m_651_, lean_object* v_a_652_){
_start:
{
lean_object* v_buckets_653_; lean_object* v___x_654_; lean_object* v___x_655_; uint8_t v___x_656_; 
v_buckets_653_ = lean_ctor_get(v_m_651_, 1);
v___x_654_ = lean_unsigned_to_nat(0u);
v___x_655_ = lean_array_get_size(v_buckets_653_);
v___x_656_ = lean_nat_dec_lt(v___x_654_, v___x_655_);
if (v___x_656_ == 0)
{
lean_dec(v_a_652_);
lean_dec_ref(v_inst_650_);
lean_dec_ref(v_inst_649_);
return v___x_656_;
}
else
{
uint8_t v___x_657_; 
v___x_657_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_649_, v_inst_650_, v_m_651_, v_a_652_);
return v___x_657_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_contains___redArg___boxed(lean_object* v_inst_658_, lean_object* v_inst_659_, lean_object* v_m_660_, lean_object* v_a_661_){
_start:
{
uint8_t v_res_662_; lean_object* v_r_663_; 
v_res_662_ = l_Std_DHashMap_Raw_contains___redArg(v_inst_658_, v_inst_659_, v_m_660_, v_a_661_);
lean_dec_ref(v_m_660_);
v_r_663_ = lean_box(v_res_662_);
return v_r_663_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_contains(lean_object* v_00_u03b1_664_, lean_object* v_00_u03b2_665_, lean_object* v_inst_666_, lean_object* v_inst_667_, lean_object* v_m_668_, lean_object* v_a_669_){
_start:
{
lean_object* v_buckets_670_; lean_object* v___x_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
v_buckets_670_ = lean_ctor_get(v_m_668_, 1);
v___x_671_ = lean_unsigned_to_nat(0u);
v___x_672_ = lean_array_get_size(v_buckets_670_);
v___x_673_ = lean_nat_dec_lt(v___x_671_, v___x_672_);
if (v___x_673_ == 0)
{
lean_dec(v_a_669_);
lean_dec_ref(v_inst_667_);
lean_dec_ref(v_inst_666_);
return v___x_673_;
}
else
{
uint8_t v___x_674_; 
v___x_674_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_666_, v_inst_667_, v_m_668_, v_a_669_);
return v___x_674_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_contains___boxed(lean_object* v_00_u03b1_675_, lean_object* v_00_u03b2_676_, lean_object* v_inst_677_, lean_object* v_inst_678_, lean_object* v_m_679_, lean_object* v_a_680_){
_start:
{
uint8_t v_res_681_; lean_object* v_r_682_; 
v_res_681_ = l_Std_DHashMap_Raw_contains(v_00_u03b1_675_, v_00_u03b2_676_, v_inst_677_, v_inst_678_, v_m_679_, v_a_680_);
lean_dec_ref(v_m_679_);
v_r_682_ = lean_box(v_res_681_);
return v_r_682_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instMembershipOfBEqOfHashable(lean_object* v_00_u03b1_683_, lean_object* v_00_u03b2_684_, lean_object* v_inst_685_, lean_object* v_inst_686_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = lean_box(0);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instMembershipOfBEqOfHashable___boxed(lean_object* v_00_u03b1_688_, lean_object* v_00_u03b2_689_, lean_object* v_inst_690_, lean_object* v_inst_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Std_DHashMap_Raw_instMembershipOfBEqOfHashable(v_00_u03b1_688_, v_00_u03b2_689_, v_inst_690_, v_inst_691_);
lean_dec_ref(v_inst_691_);
lean_dec_ref(v_inst_690_);
return v_res_692_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_instDecidableMem___redArg(lean_object* v_inst_693_, lean_object* v_inst_694_, lean_object* v_m_695_, lean_object* v_a_696_){
_start:
{
lean_object* v_buckets_697_; lean_object* v___x_698_; lean_object* v___x_699_; uint8_t v___x_700_; 
v_buckets_697_ = lean_ctor_get(v_m_695_, 1);
v___x_698_ = lean_unsigned_to_nat(0u);
v___x_699_ = lean_array_get_size(v_buckets_697_);
v___x_700_ = lean_nat_dec_lt(v___x_698_, v___x_699_);
if (v___x_700_ == 0)
{
lean_dec(v_a_696_);
lean_dec_ref(v_inst_694_);
lean_dec_ref(v_inst_693_);
return v___x_700_;
}
else
{
uint8_t v___x_701_; 
v___x_701_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_693_, v_inst_694_, v_m_695_, v_a_696_);
return v___x_701_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instDecidableMem___redArg___boxed(lean_object* v_inst_702_, lean_object* v_inst_703_, lean_object* v_m_704_, lean_object* v_a_705_){
_start:
{
uint8_t v_res_706_; lean_object* v_r_707_; 
v_res_706_ = l_Std_DHashMap_Raw_instDecidableMem___redArg(v_inst_702_, v_inst_703_, v_m_704_, v_a_705_);
lean_dec_ref(v_m_704_);
v_r_707_ = lean_box(v_res_706_);
return v_r_707_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_instDecidableMem(lean_object* v_00_u03b1_708_, lean_object* v_00_u03b2_709_, lean_object* v_inst_710_, lean_object* v_inst_711_, lean_object* v_m_712_, lean_object* v_a_713_){
_start:
{
uint8_t v___x_714_; 
v___x_714_ = l_Std_DHashMap_Raw_instDecidableMem___redArg(v_inst_710_, v_inst_711_, v_m_712_, v_a_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instDecidableMem___boxed(lean_object* v_00_u03b1_715_, lean_object* v_00_u03b2_716_, lean_object* v_inst_717_, lean_object* v_inst_718_, lean_object* v_m_719_, lean_object* v_a_720_){
_start:
{
uint8_t v_res_721_; lean_object* v_r_722_; 
v_res_721_ = l_Std_DHashMap_Raw_instDecidableMem(v_00_u03b1_715_, v_00_u03b2_716_, v_inst_717_, v_inst_718_, v_m_719_, v_a_720_);
lean_dec_ref(v_m_719_);
v_r_722_ = lean_box(v_res_721_);
return v_r_722_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get___redArg(lean_object* v_inst_723_, lean_object* v_inst_724_, lean_object* v_m_725_, lean_object* v_a_726_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l_Std_DHashMap_Internal_Raw_u2080_get___redArg(v_inst_723_, v_inst_724_, v_m_725_, v_a_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get___redArg___boxed(lean_object* v_inst_728_, lean_object* v_inst_729_, lean_object* v_m_730_, lean_object* v_a_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Std_DHashMap_Raw_get___redArg(v_inst_728_, v_inst_729_, v_m_730_, v_a_731_);
lean_dec_ref(v_m_730_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get(lean_object* v_00_u03b1_733_, lean_object* v_00_u03b2_734_, lean_object* v_inst_735_, lean_object* v_inst_736_, lean_object* v_inst_737_, lean_object* v_m_738_, lean_object* v_a_739_, lean_object* v_h_740_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l_Std_DHashMap_Internal_Raw_u2080_get___redArg(v_inst_735_, v_inst_736_, v_m_738_, v_a_739_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get___boxed(lean_object* v_00_u03b1_742_, lean_object* v_00_u03b2_743_, lean_object* v_inst_744_, lean_object* v_inst_745_, lean_object* v_inst_746_, lean_object* v_m_747_, lean_object* v_a_748_, lean_object* v_h_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Std_DHashMap_Raw_get(v_00_u03b1_742_, v_00_u03b2_743_, v_inst_744_, v_inst_745_, v_inst_746_, v_m_747_, v_a_748_, v_h_749_);
lean_dec_ref(v_m_747_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getD___redArg(lean_object* v_inst_751_, lean_object* v_inst_752_, lean_object* v_m_753_, lean_object* v_a_754_, lean_object* v_fallback_755_){
_start:
{
lean_object* v_buckets_756_; lean_object* v___x_757_; lean_object* v___x_758_; uint8_t v___x_759_; 
v_buckets_756_ = lean_ctor_get(v_m_753_, 1);
v___x_757_ = lean_unsigned_to_nat(0u);
v___x_758_ = lean_array_get_size(v_buckets_756_);
v___x_759_ = lean_nat_dec_lt(v___x_757_, v___x_758_);
if (v___x_759_ == 0)
{
lean_dec(v_a_754_);
lean_dec_ref(v_inst_752_);
lean_dec_ref(v_inst_751_);
lean_inc(v_fallback_755_);
return v_fallback_755_;
}
else
{
lean_object* v___x_760_; 
v___x_760_ = l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(v_inst_751_, v_inst_752_, v_m_753_, v_a_754_, v_fallback_755_);
return v___x_760_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getD___redArg___boxed(lean_object* v_inst_761_, lean_object* v_inst_762_, lean_object* v_m_763_, lean_object* v_a_764_, lean_object* v_fallback_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_Std_DHashMap_Raw_getD___redArg(v_inst_761_, v_inst_762_, v_m_763_, v_a_764_, v_fallback_765_);
lean_dec(v_fallback_765_);
lean_dec_ref(v_m_763_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getD(lean_object* v_00_u03b1_767_, lean_object* v_00_u03b2_768_, lean_object* v_inst_769_, lean_object* v_inst_770_, lean_object* v_inst_771_, lean_object* v_m_772_, lean_object* v_a_773_, lean_object* v_fallback_774_){
_start:
{
lean_object* v_buckets_775_; lean_object* v___x_776_; lean_object* v___x_777_; uint8_t v___x_778_; 
v_buckets_775_ = lean_ctor_get(v_m_772_, 1);
v___x_776_ = lean_unsigned_to_nat(0u);
v___x_777_ = lean_array_get_size(v_buckets_775_);
v___x_778_ = lean_nat_dec_lt(v___x_776_, v___x_777_);
if (v___x_778_ == 0)
{
lean_dec(v_a_773_);
lean_dec_ref(v_inst_770_);
lean_dec_ref(v_inst_769_);
lean_inc(v_fallback_774_);
return v_fallback_774_;
}
else
{
lean_object* v___x_779_; 
v___x_779_ = l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(v_inst_769_, v_inst_770_, v_m_772_, v_a_773_, v_fallback_774_);
return v___x_779_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getD___boxed(lean_object* v_00_u03b1_780_, lean_object* v_00_u03b2_781_, lean_object* v_inst_782_, lean_object* v_inst_783_, lean_object* v_inst_784_, lean_object* v_m_785_, lean_object* v_a_786_, lean_object* v_fallback_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Std_DHashMap_Raw_getD(v_00_u03b1_780_, v_00_u03b2_781_, v_inst_782_, v_inst_783_, v_inst_784_, v_m_785_, v_a_786_, v_fallback_787_);
lean_dec(v_fallback_787_);
lean_dec_ref(v_m_785_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x21___redArg(lean_object* v_inst_789_, lean_object* v_inst_790_, lean_object* v_m_791_, lean_object* v_a_792_, lean_object* v_inst_793_){
_start:
{
lean_object* v_buckets_794_; lean_object* v___x_795_; lean_object* v___x_796_; uint8_t v___x_797_; 
v_buckets_794_ = lean_ctor_get(v_m_791_, 1);
v___x_795_ = lean_unsigned_to_nat(0u);
v___x_796_ = lean_array_get_size(v_buckets_794_);
v___x_797_ = lean_nat_dec_lt(v___x_795_, v___x_796_);
if (v___x_797_ == 0)
{
lean_dec(v_a_792_);
lean_dec_ref(v_inst_790_);
lean_dec_ref(v_inst_789_);
lean_inc(v_inst_793_);
return v_inst_793_;
}
else
{
lean_object* v___x_798_; 
v___x_798_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(v_inst_789_, v_inst_790_, v_m_791_, v_a_792_, v_inst_793_);
return v___x_798_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x21___redArg___boxed(lean_object* v_inst_799_, lean_object* v_inst_800_, lean_object* v_m_801_, lean_object* v_a_802_, lean_object* v_inst_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Std_DHashMap_Raw_get_x21___redArg(v_inst_799_, v_inst_800_, v_m_801_, v_a_802_, v_inst_803_);
lean_dec(v_inst_803_);
lean_dec_ref(v_m_801_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x21(lean_object* v_00_u03b1_805_, lean_object* v_00_u03b2_806_, lean_object* v_inst_807_, lean_object* v_inst_808_, lean_object* v_inst_809_, lean_object* v_m_810_, lean_object* v_a_811_, lean_object* v_inst_812_){
_start:
{
lean_object* v_buckets_813_; lean_object* v___x_814_; lean_object* v___x_815_; uint8_t v___x_816_; 
v_buckets_813_ = lean_ctor_get(v_m_810_, 1);
v___x_814_ = lean_unsigned_to_nat(0u);
v___x_815_ = lean_array_get_size(v_buckets_813_);
v___x_816_ = lean_nat_dec_lt(v___x_814_, v___x_815_);
if (v___x_816_ == 0)
{
lean_dec(v_a_811_);
lean_dec_ref(v_inst_808_);
lean_dec_ref(v_inst_807_);
lean_inc(v_inst_812_);
return v_inst_812_;
}
else
{
lean_object* v___x_817_; 
v___x_817_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(v_inst_807_, v_inst_808_, v_m_810_, v_a_811_, v_inst_812_);
return v___x_817_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x21___boxed(lean_object* v_00_u03b1_818_, lean_object* v_00_u03b2_819_, lean_object* v_inst_820_, lean_object* v_inst_821_, lean_object* v_inst_822_, lean_object* v_m_823_, lean_object* v_a_824_, lean_object* v_inst_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Std_DHashMap_Raw_get_x21(v_00_u03b1_818_, v_00_u03b2_819_, v_inst_820_, v_inst_821_, v_inst_822_, v_m_823_, v_a_824_, v_inst_825_);
lean_dec(v_inst_825_);
lean_dec_ref(v_m_823_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_erase___redArg(lean_object* v_inst_827_, lean_object* v_inst_828_, lean_object* v_m_829_, lean_object* v_a_830_){
_start:
{
lean_object* v_buckets_831_; lean_object* v___x_832_; lean_object* v___x_833_; uint8_t v___x_834_; 
v_buckets_831_ = lean_ctor_get(v_m_829_, 1);
v___x_832_ = lean_unsigned_to_nat(0u);
v___x_833_ = lean_array_get_size(v_buckets_831_);
v___x_834_ = lean_nat_dec_lt(v___x_832_, v___x_833_);
if (v___x_834_ == 0)
{
lean_dec(v_a_830_);
lean_dec_ref(v_inst_828_);
lean_dec_ref(v_inst_827_);
return v_m_829_;
}
else
{
lean_object* v___x_835_; 
v___x_835_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_827_, v_inst_828_, v_m_829_, v_a_830_);
return v___x_835_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_erase(lean_object* v_00_u03b1_836_, lean_object* v_00_u03b2_837_, lean_object* v_inst_838_, lean_object* v_inst_839_, lean_object* v_m_840_, lean_object* v_a_841_){
_start:
{
lean_object* v_buckets_842_; lean_object* v___x_843_; lean_object* v___x_844_; uint8_t v___x_845_; 
v_buckets_842_ = lean_ctor_get(v_m_840_, 1);
v___x_843_ = lean_unsigned_to_nat(0u);
v___x_844_ = lean_array_get_size(v_buckets_842_);
v___x_845_ = lean_nat_dec_lt(v___x_843_, v___x_844_);
if (v___x_845_ == 0)
{
lean_dec(v_a_841_);
lean_dec_ref(v_inst_839_);
lean_dec_ref(v_inst_838_);
return v_m_840_;
}
else
{
lean_object* v___x_846_; 
v___x_846_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_838_, v_inst_839_, v_m_840_, v_a_841_);
return v___x_846_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x3f___redArg(lean_object* v_inst_847_, lean_object* v_inst_848_, lean_object* v_m_849_, lean_object* v_a_850_){
_start:
{
lean_object* v_buckets_851_; lean_object* v___x_852_; lean_object* v___x_853_; uint8_t v___x_854_; 
v_buckets_851_ = lean_ctor_get(v_m_849_, 1);
v___x_852_ = lean_unsigned_to_nat(0u);
v___x_853_ = lean_array_get_size(v_buckets_851_);
v___x_854_ = lean_nat_dec_lt(v___x_852_, v___x_853_);
if (v___x_854_ == 0)
{
lean_object* v___x_855_; 
lean_dec(v_a_850_);
lean_dec_ref(v_inst_848_);
lean_dec_ref(v_inst_847_);
v___x_855_ = lean_box(0);
return v___x_855_;
}
else
{
lean_object* v___x_856_; 
v___x_856_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_847_, v_inst_848_, v_m_849_, v_a_850_);
return v___x_856_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x3f___redArg___boxed(lean_object* v_inst_857_, lean_object* v_inst_858_, lean_object* v_m_859_, lean_object* v_a_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Std_DHashMap_Raw_Const_get_x3f___redArg(v_inst_857_, v_inst_858_, v_m_859_, v_a_860_);
lean_dec_ref(v_m_859_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x3f(lean_object* v_00_u03b1_862_, lean_object* v_00_u03b2_863_, lean_object* v_inst_864_, lean_object* v_inst_865_, lean_object* v_m_866_, lean_object* v_a_867_){
_start:
{
lean_object* v_buckets_868_; lean_object* v___x_869_; lean_object* v___x_870_; uint8_t v___x_871_; 
v_buckets_868_ = lean_ctor_get(v_m_866_, 1);
v___x_869_ = lean_unsigned_to_nat(0u);
v___x_870_ = lean_array_get_size(v_buckets_868_);
v___x_871_ = lean_nat_dec_lt(v___x_869_, v___x_870_);
if (v___x_871_ == 0)
{
lean_object* v___x_872_; 
lean_dec(v_a_867_);
lean_dec_ref(v_inst_865_);
lean_dec_ref(v_inst_864_);
v___x_872_ = lean_box(0);
return v___x_872_;
}
else
{
lean_object* v___x_873_; 
v___x_873_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_864_, v_inst_865_, v_m_866_, v_a_867_);
return v___x_873_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x3f___boxed(lean_object* v_00_u03b1_874_, lean_object* v_00_u03b2_875_, lean_object* v_inst_876_, lean_object* v_inst_877_, lean_object* v_m_878_, lean_object* v_a_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Std_DHashMap_Raw_Const_get_x3f(v_00_u03b1_874_, v_00_u03b2_875_, v_inst_876_, v_inst_877_, v_m_878_, v_a_879_);
lean_dec_ref(v_m_878_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get___redArg(lean_object* v_inst_881_, lean_object* v_inst_882_, lean_object* v_m_883_, lean_object* v_a_884_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_881_, v_inst_882_, v_m_883_, v_a_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get___redArg___boxed(lean_object* v_inst_886_, lean_object* v_inst_887_, lean_object* v_m_888_, lean_object* v_a_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Std_DHashMap_Raw_Const_get___redArg(v_inst_886_, v_inst_887_, v_m_888_, v_a_889_);
lean_dec_ref(v_m_888_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get(lean_object* v_00_u03b1_891_, lean_object* v_00_u03b2_892_, lean_object* v_inst_893_, lean_object* v_inst_894_, lean_object* v_m_895_, lean_object* v_a_896_, lean_object* v_h_897_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_893_, v_inst_894_, v_m_895_, v_a_896_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get___boxed(lean_object* v_00_u03b1_899_, lean_object* v_00_u03b2_900_, lean_object* v_inst_901_, lean_object* v_inst_902_, lean_object* v_m_903_, lean_object* v_a_904_, lean_object* v_h_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Std_DHashMap_Raw_Const_get(v_00_u03b1_899_, v_00_u03b2_900_, v_inst_901_, v_inst_902_, v_m_903_, v_a_904_, v_h_905_);
lean_dec_ref(v_m_903_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getD___redArg(lean_object* v_inst_907_, lean_object* v_inst_908_, lean_object* v_m_909_, lean_object* v_a_910_, lean_object* v_fallback_911_){
_start:
{
lean_object* v_buckets_912_; lean_object* v___x_913_; lean_object* v___x_914_; uint8_t v___x_915_; 
v_buckets_912_ = lean_ctor_get(v_m_909_, 1);
v___x_913_ = lean_unsigned_to_nat(0u);
v___x_914_ = lean_array_get_size(v_buckets_912_);
v___x_915_ = lean_nat_dec_lt(v___x_913_, v___x_914_);
if (v___x_915_ == 0)
{
lean_dec(v_a_910_);
lean_dec_ref(v_inst_908_);
lean_dec_ref(v_inst_907_);
lean_inc(v_fallback_911_);
return v_fallback_911_;
}
else
{
lean_object* v___x_916_; 
v___x_916_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_inst_907_, v_inst_908_, v_m_909_, v_a_910_, v_fallback_911_);
return v___x_916_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getD___redArg___boxed(lean_object* v_inst_917_, lean_object* v_inst_918_, lean_object* v_m_919_, lean_object* v_a_920_, lean_object* v_fallback_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Std_DHashMap_Raw_Const_getD___redArg(v_inst_917_, v_inst_918_, v_m_919_, v_a_920_, v_fallback_921_);
lean_dec(v_fallback_921_);
lean_dec_ref(v_m_919_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getD(lean_object* v_00_u03b1_923_, lean_object* v_00_u03b2_924_, lean_object* v_inst_925_, lean_object* v_inst_926_, lean_object* v_m_927_, lean_object* v_a_928_, lean_object* v_fallback_929_){
_start:
{
lean_object* v_buckets_930_; lean_object* v___x_931_; lean_object* v___x_932_; uint8_t v___x_933_; 
v_buckets_930_ = lean_ctor_get(v_m_927_, 1);
v___x_931_ = lean_unsigned_to_nat(0u);
v___x_932_ = lean_array_get_size(v_buckets_930_);
v___x_933_ = lean_nat_dec_lt(v___x_931_, v___x_932_);
if (v___x_933_ == 0)
{
lean_dec(v_a_928_);
lean_dec_ref(v_inst_926_);
lean_dec_ref(v_inst_925_);
lean_inc(v_fallback_929_);
return v_fallback_929_;
}
else
{
lean_object* v___x_934_; 
v___x_934_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_inst_925_, v_inst_926_, v_m_927_, v_a_928_, v_fallback_929_);
return v___x_934_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getD___boxed(lean_object* v_00_u03b1_935_, lean_object* v_00_u03b2_936_, lean_object* v_inst_937_, lean_object* v_inst_938_, lean_object* v_m_939_, lean_object* v_a_940_, lean_object* v_fallback_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Std_DHashMap_Raw_Const_getD(v_00_u03b1_935_, v_00_u03b2_936_, v_inst_937_, v_inst_938_, v_m_939_, v_a_940_, v_fallback_941_);
lean_dec(v_fallback_941_);
lean_dec_ref(v_m_939_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x21___redArg(lean_object* v_inst_943_, lean_object* v_inst_944_, lean_object* v_inst_945_, lean_object* v_m_946_, lean_object* v_a_947_){
_start:
{
lean_object* v_buckets_948_; lean_object* v___x_949_; lean_object* v___x_950_; uint8_t v___x_951_; 
v_buckets_948_ = lean_ctor_get(v_m_946_, 1);
v___x_949_ = lean_unsigned_to_nat(0u);
v___x_950_ = lean_array_get_size(v_buckets_948_);
v___x_951_ = lean_nat_dec_lt(v___x_949_, v___x_950_);
if (v___x_951_ == 0)
{
lean_dec(v_a_947_);
lean_dec_ref(v_inst_944_);
lean_dec_ref(v_inst_943_);
lean_inc(v_inst_945_);
return v_inst_945_;
}
else
{
lean_object* v___x_952_; 
v___x_952_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_943_, v_inst_944_, v_inst_945_, v_m_946_, v_a_947_);
return v___x_952_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x21___redArg___boxed(lean_object* v_inst_953_, lean_object* v_inst_954_, lean_object* v_inst_955_, lean_object* v_m_956_, lean_object* v_a_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Std_DHashMap_Raw_Const_get_x21___redArg(v_inst_953_, v_inst_954_, v_inst_955_, v_m_956_, v_a_957_);
lean_dec_ref(v_m_956_);
lean_dec(v_inst_955_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x21(lean_object* v_00_u03b1_959_, lean_object* v_00_u03b2_960_, lean_object* v_inst_961_, lean_object* v_inst_962_, lean_object* v_inst_963_, lean_object* v_m_964_, lean_object* v_a_965_){
_start:
{
lean_object* v_buckets_966_; lean_object* v___x_967_; lean_object* v___x_968_; uint8_t v___x_969_; 
v_buckets_966_ = lean_ctor_get(v_m_964_, 1);
v___x_967_ = lean_unsigned_to_nat(0u);
v___x_968_ = lean_array_get_size(v_buckets_966_);
v___x_969_ = lean_nat_dec_lt(v___x_967_, v___x_968_);
if (v___x_969_ == 0)
{
lean_dec(v_a_965_);
lean_dec_ref(v_inst_962_);
lean_dec_ref(v_inst_961_);
lean_inc(v_inst_963_);
return v_inst_963_;
}
else
{
lean_object* v___x_970_; 
v___x_970_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_961_, v_inst_962_, v_inst_963_, v_m_964_, v_a_965_);
return v___x_970_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x21___boxed(lean_object* v_00_u03b1_971_, lean_object* v_00_u03b2_972_, lean_object* v_inst_973_, lean_object* v_inst_974_, lean_object* v_inst_975_, lean_object* v_m_976_, lean_object* v_a_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Std_DHashMap_Raw_Const_get_x21(v_00_u03b1_971_, v_00_u03b2_972_, v_inst_973_, v_inst_974_, v_inst_975_, v_m_976_, v_a_977_);
lean_dec_ref(v_m_976_);
lean_dec(v_inst_975_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getThenInsertIfNew_x3f___redArg(lean_object* v_inst_979_, lean_object* v_inst_980_, lean_object* v_m_981_, lean_object* v_a_982_, lean_object* v_b_983_){
_start:
{
lean_object* v_size_984_; lean_object* v_buckets_985_; lean_object* v___x_986_; lean_object* v___x_987_; uint8_t v___x_988_; 
v_size_984_ = lean_ctor_get(v_m_981_, 0);
v_buckets_985_ = lean_ctor_get(v_m_981_, 1);
v___x_986_ = lean_unsigned_to_nat(0u);
v___x_987_ = lean_array_get_size(v_buckets_985_);
v___x_988_ = lean_nat_dec_lt(v___x_986_, v___x_987_);
if (v___x_988_ == 0)
{
lean_object* v___x_989_; lean_object* v___x_990_; 
lean_dec(v_b_983_);
lean_dec(v_a_982_);
lean_dec_ref(v_inst_980_);
lean_dec_ref(v_inst_979_);
v___x_989_ = lean_box(0);
v___x_990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
lean_ctor_set(v___x_990_, 1, v_m_981_);
return v___x_990_;
}
else
{
lean_object* v___x_991_; uint64_t v___x_992_; uint64_t v___x_993_; uint64_t v___x_994_; uint64_t v___x_995_; uint64_t v_fold_996_; uint64_t v___x_997_; uint64_t v___x_998_; uint64_t v___x_999_; size_t v___x_1000_; size_t v___x_1001_; size_t v___x_1002_; size_t v___x_1003_; size_t v___x_1004_; lean_object* v_bkt_1005_; lean_object* v___x_1006_; 
lean_inc_ref(v_inst_980_);
lean_inc_n(v_a_982_, 2);
v___x_991_ = lean_apply_1(v_inst_980_, v_a_982_);
v___x_992_ = 32ULL;
v___x_993_ = lean_unbox_uint64(v___x_991_);
v___x_994_ = lean_uint64_shift_right(v___x_993_, v___x_992_);
v___x_995_ = lean_unbox_uint64(v___x_991_);
lean_dec_ref(v___x_991_);
v_fold_996_ = lean_uint64_xor(v___x_995_, v___x_994_);
v___x_997_ = 16ULL;
v___x_998_ = lean_uint64_shift_right(v_fold_996_, v___x_997_);
v___x_999_ = lean_uint64_xor(v_fold_996_, v___x_998_);
v___x_1000_ = lean_uint64_to_usize(v___x_999_);
v___x_1001_ = lean_usize_of_nat(v___x_987_);
v___x_1002_ = ((size_t)1ULL);
v___x_1003_ = lean_usize_sub(v___x_1001_, v___x_1002_);
v___x_1004_ = lean_usize_land(v___x_1000_, v___x_1003_);
v_bkt_1005_ = lean_array_uget_borrowed(v_buckets_985_, v___x_1004_);
lean_inc(v_bkt_1005_);
v___x_1006_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_inst_979_, v_a_982_, v_bkt_1005_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1029_; 
lean_inc_ref(v_buckets_985_);
lean_inc(v_size_984_);
v_isSharedCheck_1029_ = !lean_is_exclusive(v_m_981_);
if (v_isSharedCheck_1029_ == 0)
{
lean_object* v_unused_1030_; lean_object* v_unused_1031_; 
v_unused_1030_ = lean_ctor_get(v_m_981_, 1);
lean_dec(v_unused_1030_);
v_unused_1031_ = lean_ctor_get(v_m_981_, 0);
lean_dec(v_unused_1031_);
v___x_1008_ = v_m_981_;
v_isShared_1009_ = v_isSharedCheck_1029_;
goto v_resetjp_1007_;
}
else
{
lean_dec(v_m_981_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1029_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1010_; lean_object* v_size_x27_1011_; lean_object* v___x_1012_; lean_object* v_buckets_x27_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; uint8_t v___x_1019_; 
v___x_1010_ = lean_unsigned_to_nat(1u);
v_size_x27_1011_ = lean_nat_add(v_size_984_, v___x_1010_);
lean_dec(v_size_984_);
lean_inc(v_bkt_1005_);
v___x_1012_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1012_, 0, v_a_982_);
lean_ctor_set(v___x_1012_, 1, v_b_983_);
lean_ctor_set(v___x_1012_, 2, v_bkt_1005_);
v_buckets_x27_1013_ = lean_array_uset(v_buckets_985_, v___x_1004_, v___x_1012_);
v___x_1014_ = lean_unsigned_to_nat(4u);
v___x_1015_ = lean_nat_mul(v_size_x27_1011_, v___x_1014_);
v___x_1016_ = lean_unsigned_to_nat(3u);
v___x_1017_ = lean_nat_div(v___x_1015_, v___x_1016_);
lean_dec(v___x_1015_);
v___x_1018_ = lean_array_get_size(v_buckets_x27_1013_);
v___x_1019_ = lean_nat_dec_le(v___x_1017_, v___x_1018_);
lean_dec(v___x_1017_);
if (v___x_1019_ == 0)
{
lean_object* v_val_1020_; lean_object* v___x_1022_; 
v_val_1020_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_980_, v_buckets_x27_1013_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 1, v_val_1020_);
lean_ctor_set(v___x_1008_, 0, v_size_x27_1011_);
v___x_1022_ = v___x_1008_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_size_x27_1011_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v_val_1020_);
v___x_1022_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
lean_object* v___x_1023_; 
v___x_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1006_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
return v___x_1023_;
}
}
else
{
lean_object* v___x_1026_; 
lean_dec_ref(v_inst_980_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 1, v_buckets_x27_1013_);
lean_ctor_set(v___x_1008_, 0, v_size_x27_1011_);
v___x_1026_ = v___x_1008_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_size_x27_1011_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v_buckets_x27_1013_);
v___x_1026_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
lean_object* v___x_1027_; 
v___x_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1006_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
return v___x_1027_;
}
}
}
}
else
{
lean_object* v___x_1032_; 
lean_dec(v_b_983_);
lean_dec(v_a_982_);
lean_dec_ref(v_inst_980_);
v___x_1032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1006_);
lean_ctor_set(v___x_1032_, 1, v_m_981_);
return v___x_1032_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_1033_, lean_object* v_00_u03b2_1034_, lean_object* v_inst_1035_, lean_object* v_inst_1036_, lean_object* v_m_1037_, lean_object* v_a_1038_, lean_object* v_b_1039_){
_start:
{
lean_object* v_size_1040_; lean_object* v_buckets_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; uint8_t v___x_1044_; 
v_size_1040_ = lean_ctor_get(v_m_1037_, 0);
v_buckets_1041_ = lean_ctor_get(v_m_1037_, 1);
v___x_1042_ = lean_unsigned_to_nat(0u);
v___x_1043_ = lean_array_get_size(v_buckets_1041_);
v___x_1044_ = lean_nat_dec_lt(v___x_1042_, v___x_1043_);
if (v___x_1044_ == 0)
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
lean_dec(v_b_1039_);
lean_dec(v_a_1038_);
lean_dec_ref(v_inst_1036_);
lean_dec_ref(v_inst_1035_);
v___x_1045_ = lean_box(0);
v___x_1046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
lean_ctor_set(v___x_1046_, 1, v_m_1037_);
return v___x_1046_;
}
else
{
lean_object* v___x_1047_; uint64_t v___x_1048_; uint64_t v___x_1049_; uint64_t v___x_1050_; uint64_t v___x_1051_; uint64_t v_fold_1052_; uint64_t v___x_1053_; uint64_t v___x_1054_; uint64_t v___x_1055_; size_t v___x_1056_; size_t v___x_1057_; size_t v___x_1058_; size_t v___x_1059_; size_t v___x_1060_; lean_object* v_bkt_1061_; lean_object* v___x_1062_; 
lean_inc_ref(v_inst_1036_);
lean_inc_n(v_a_1038_, 2);
v___x_1047_ = lean_apply_1(v_inst_1036_, v_a_1038_);
v___x_1048_ = 32ULL;
v___x_1049_ = lean_unbox_uint64(v___x_1047_);
v___x_1050_ = lean_uint64_shift_right(v___x_1049_, v___x_1048_);
v___x_1051_ = lean_unbox_uint64(v___x_1047_);
lean_dec_ref(v___x_1047_);
v_fold_1052_ = lean_uint64_xor(v___x_1051_, v___x_1050_);
v___x_1053_ = 16ULL;
v___x_1054_ = lean_uint64_shift_right(v_fold_1052_, v___x_1053_);
v___x_1055_ = lean_uint64_xor(v_fold_1052_, v___x_1054_);
v___x_1056_ = lean_uint64_to_usize(v___x_1055_);
v___x_1057_ = lean_usize_of_nat(v___x_1043_);
v___x_1058_ = ((size_t)1ULL);
v___x_1059_ = lean_usize_sub(v___x_1057_, v___x_1058_);
v___x_1060_ = lean_usize_land(v___x_1056_, v___x_1059_);
v_bkt_1061_ = lean_array_uget_borrowed(v_buckets_1041_, v___x_1060_);
lean_inc(v_bkt_1061_);
v___x_1062_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_inst_1035_, v_a_1038_, v_bkt_1061_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1085_; 
lean_inc_ref(v_buckets_1041_);
lean_inc(v_size_1040_);
v_isSharedCheck_1085_ = !lean_is_exclusive(v_m_1037_);
if (v_isSharedCheck_1085_ == 0)
{
lean_object* v_unused_1086_; lean_object* v_unused_1087_; 
v_unused_1086_ = lean_ctor_get(v_m_1037_, 1);
lean_dec(v_unused_1086_);
v_unused_1087_ = lean_ctor_get(v_m_1037_, 0);
lean_dec(v_unused_1087_);
v___x_1064_ = v_m_1037_;
v_isShared_1065_ = v_isSharedCheck_1085_;
goto v_resetjp_1063_;
}
else
{
lean_dec(v_m_1037_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1085_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1066_; lean_object* v_size_x27_1067_; lean_object* v___x_1068_; lean_object* v_buckets_x27_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; uint8_t v___x_1075_; 
v___x_1066_ = lean_unsigned_to_nat(1u);
v_size_x27_1067_ = lean_nat_add(v_size_1040_, v___x_1066_);
lean_dec(v_size_1040_);
lean_inc(v_bkt_1061_);
v___x_1068_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1068_, 0, v_a_1038_);
lean_ctor_set(v___x_1068_, 1, v_b_1039_);
lean_ctor_set(v___x_1068_, 2, v_bkt_1061_);
v_buckets_x27_1069_ = lean_array_uset(v_buckets_1041_, v___x_1060_, v___x_1068_);
v___x_1070_ = lean_unsigned_to_nat(4u);
v___x_1071_ = lean_nat_mul(v_size_x27_1067_, v___x_1070_);
v___x_1072_ = lean_unsigned_to_nat(3u);
v___x_1073_ = lean_nat_div(v___x_1071_, v___x_1072_);
lean_dec(v___x_1071_);
v___x_1074_ = lean_array_get_size(v_buckets_x27_1069_);
v___x_1075_ = lean_nat_dec_le(v___x_1073_, v___x_1074_);
lean_dec(v___x_1073_);
if (v___x_1075_ == 0)
{
lean_object* v_val_1076_; lean_object* v___x_1078_; 
v_val_1076_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1036_, v_buckets_x27_1069_);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 1, v_val_1076_);
lean_ctor_set(v___x_1064_, 0, v_size_x27_1067_);
v___x_1078_ = v___x_1064_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_size_x27_1067_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v_val_1076_);
v___x_1078_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
lean_object* v___x_1079_; 
v___x_1079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1062_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
return v___x_1079_;
}
}
else
{
lean_object* v___x_1082_; 
lean_dec_ref(v_inst_1036_);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 1, v_buckets_x27_1069_);
lean_ctor_set(v___x_1064_, 0, v_size_x27_1067_);
v___x_1082_ = v___x_1064_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_size_x27_1067_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v_buckets_x27_1069_);
v___x_1082_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
lean_object* v___x_1083_; 
v___x_1083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1062_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
return v___x_1083_;
}
}
}
}
else
{
lean_object* v___x_1088_; 
lean_dec(v_b_1039_);
lean_dec(v_a_1038_);
lean_dec_ref(v_inst_1036_);
v___x_1088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1062_);
lean_ctor_set(v___x_1088_, 1, v_m_1037_);
return v___x_1088_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x3f___redArg(lean_object* v_inst_1089_, lean_object* v_inst_1090_, lean_object* v_m_1091_, lean_object* v_a_1092_){
_start:
{
lean_object* v_buckets_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; uint8_t v___x_1096_; 
v_buckets_1093_ = lean_ctor_get(v_m_1091_, 1);
v___x_1094_ = lean_unsigned_to_nat(0u);
v___x_1095_ = lean_array_get_size(v_buckets_1093_);
v___x_1096_ = lean_nat_dec_lt(v___x_1094_, v___x_1095_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; 
lean_dec(v_a_1092_);
lean_dec_ref(v_inst_1090_);
lean_dec_ref(v_inst_1089_);
v___x_1097_ = lean_box(0);
return v___x_1097_;
}
else
{
lean_object* v___x_1098_; 
v___x_1098_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_1089_, v_inst_1090_, v_m_1091_, v_a_1092_);
return v___x_1098_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x3f___redArg___boxed(lean_object* v_inst_1099_, lean_object* v_inst_1100_, lean_object* v_m_1101_, lean_object* v_a_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Std_DHashMap_Raw_getKey_x3f___redArg(v_inst_1099_, v_inst_1100_, v_m_1101_, v_a_1102_);
lean_dec_ref(v_m_1101_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x3f(lean_object* v_00_u03b1_1104_, lean_object* v_00_u03b2_1105_, lean_object* v_inst_1106_, lean_object* v_inst_1107_, lean_object* v_m_1108_, lean_object* v_a_1109_){
_start:
{
lean_object* v_buckets_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; uint8_t v___x_1113_; 
v_buckets_1110_ = lean_ctor_get(v_m_1108_, 1);
v___x_1111_ = lean_unsigned_to_nat(0u);
v___x_1112_ = lean_array_get_size(v_buckets_1110_);
v___x_1113_ = lean_nat_dec_lt(v___x_1111_, v___x_1112_);
if (v___x_1113_ == 0)
{
lean_object* v___x_1114_; 
lean_dec(v_a_1109_);
lean_dec_ref(v_inst_1107_);
lean_dec_ref(v_inst_1106_);
v___x_1114_ = lean_box(0);
return v___x_1114_;
}
else
{
lean_object* v___x_1115_; 
v___x_1115_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_1106_, v_inst_1107_, v_m_1108_, v_a_1109_);
return v___x_1115_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x3f___boxed(lean_object* v_00_u03b1_1116_, lean_object* v_00_u03b2_1117_, lean_object* v_inst_1118_, lean_object* v_inst_1119_, lean_object* v_m_1120_, lean_object* v_a_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Std_DHashMap_Raw_getKey_x3f(v_00_u03b1_1116_, v_00_u03b2_1117_, v_inst_1118_, v_inst_1119_, v_m_1120_, v_a_1121_);
lean_dec_ref(v_m_1120_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey___redArg(lean_object* v_inst_1123_, lean_object* v_inst_1124_, lean_object* v_m_1125_, lean_object* v_a_1126_){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_1123_, v_inst_1124_, v_m_1125_, v_a_1126_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey___redArg___boxed(lean_object* v_inst_1128_, lean_object* v_inst_1129_, lean_object* v_m_1130_, lean_object* v_a_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l_Std_DHashMap_Raw_getKey___redArg(v_inst_1128_, v_inst_1129_, v_m_1130_, v_a_1131_);
lean_dec_ref(v_m_1130_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey(lean_object* v_00_u03b1_1133_, lean_object* v_00_u03b2_1134_, lean_object* v_inst_1135_, lean_object* v_inst_1136_, lean_object* v_m_1137_, lean_object* v_a_1138_, lean_object* v_h_1139_){
_start:
{
lean_object* v___x_1140_; 
v___x_1140_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_1135_, v_inst_1136_, v_m_1137_, v_a_1138_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey___boxed(lean_object* v_00_u03b1_1141_, lean_object* v_00_u03b2_1142_, lean_object* v_inst_1143_, lean_object* v_inst_1144_, lean_object* v_m_1145_, lean_object* v_a_1146_, lean_object* v_h_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Std_DHashMap_Raw_getKey(v_00_u03b1_1141_, v_00_u03b2_1142_, v_inst_1143_, v_inst_1144_, v_m_1145_, v_a_1146_, v_h_1147_);
lean_dec_ref(v_m_1145_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKeyD___redArg(lean_object* v_inst_1149_, lean_object* v_inst_1150_, lean_object* v_m_1151_, lean_object* v_a_1152_, lean_object* v_fallback_1153_){
_start:
{
lean_object* v_buckets_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; uint8_t v___x_1157_; 
v_buckets_1154_ = lean_ctor_get(v_m_1151_, 1);
v___x_1155_ = lean_unsigned_to_nat(0u);
v___x_1156_ = lean_array_get_size(v_buckets_1154_);
v___x_1157_ = lean_nat_dec_lt(v___x_1155_, v___x_1156_);
if (v___x_1157_ == 0)
{
lean_dec(v_a_1152_);
lean_dec_ref(v_inst_1150_);
lean_dec_ref(v_inst_1149_);
lean_inc(v_fallback_1153_);
return v_fallback_1153_;
}
else
{
lean_object* v___x_1158_; 
v___x_1158_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_1149_, v_inst_1150_, v_m_1151_, v_a_1152_, v_fallback_1153_);
return v___x_1158_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKeyD___redArg___boxed(lean_object* v_inst_1159_, lean_object* v_inst_1160_, lean_object* v_m_1161_, lean_object* v_a_1162_, lean_object* v_fallback_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_Std_DHashMap_Raw_getKeyD___redArg(v_inst_1159_, v_inst_1160_, v_m_1161_, v_a_1162_, v_fallback_1163_);
lean_dec(v_fallback_1163_);
lean_dec_ref(v_m_1161_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKeyD(lean_object* v_00_u03b1_1165_, lean_object* v_00_u03b2_1166_, lean_object* v_inst_1167_, lean_object* v_inst_1168_, lean_object* v_m_1169_, lean_object* v_a_1170_, lean_object* v_fallback_1171_){
_start:
{
lean_object* v_buckets_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; uint8_t v___x_1175_; 
v_buckets_1172_ = lean_ctor_get(v_m_1169_, 1);
v___x_1173_ = lean_unsigned_to_nat(0u);
v___x_1174_ = lean_array_get_size(v_buckets_1172_);
v___x_1175_ = lean_nat_dec_lt(v___x_1173_, v___x_1174_);
if (v___x_1175_ == 0)
{
lean_dec(v_a_1170_);
lean_dec_ref(v_inst_1168_);
lean_dec_ref(v_inst_1167_);
lean_inc(v_fallback_1171_);
return v_fallback_1171_;
}
else
{
lean_object* v___x_1176_; 
v___x_1176_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_1167_, v_inst_1168_, v_m_1169_, v_a_1170_, v_fallback_1171_);
return v___x_1176_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKeyD___boxed(lean_object* v_00_u03b1_1177_, lean_object* v_00_u03b2_1178_, lean_object* v_inst_1179_, lean_object* v_inst_1180_, lean_object* v_m_1181_, lean_object* v_a_1182_, lean_object* v_fallback_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Std_DHashMap_Raw_getKeyD(v_00_u03b1_1177_, v_00_u03b2_1178_, v_inst_1179_, v_inst_1180_, v_m_1181_, v_a_1182_, v_fallback_1183_);
lean_dec(v_fallback_1183_);
lean_dec_ref(v_m_1181_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x21___redArg(lean_object* v_inst_1185_, lean_object* v_inst_1186_, lean_object* v_inst_1187_, lean_object* v_m_1188_, lean_object* v_a_1189_){
_start:
{
lean_object* v_buckets_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; uint8_t v___x_1193_; 
v_buckets_1190_ = lean_ctor_get(v_m_1188_, 1);
v___x_1191_ = lean_unsigned_to_nat(0u);
v___x_1192_ = lean_array_get_size(v_buckets_1190_);
v___x_1193_ = lean_nat_dec_lt(v___x_1191_, v___x_1192_);
if (v___x_1193_ == 0)
{
lean_dec(v_a_1189_);
lean_dec_ref(v_inst_1186_);
lean_dec_ref(v_inst_1185_);
lean_inc(v_inst_1187_);
return v_inst_1187_;
}
else
{
lean_object* v___x_1194_; 
v___x_1194_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_1185_, v_inst_1186_, v_inst_1187_, v_m_1188_, v_a_1189_);
return v___x_1194_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x21___redArg___boxed(lean_object* v_inst_1195_, lean_object* v_inst_1196_, lean_object* v_inst_1197_, lean_object* v_m_1198_, lean_object* v_a_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Std_DHashMap_Raw_getKey_x21___redArg(v_inst_1195_, v_inst_1196_, v_inst_1197_, v_m_1198_, v_a_1199_);
lean_dec_ref(v_m_1198_);
lean_dec(v_inst_1197_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x21(lean_object* v_00_u03b1_1201_, lean_object* v_00_u03b2_1202_, lean_object* v_inst_1203_, lean_object* v_inst_1204_, lean_object* v_inst_1205_, lean_object* v_m_1206_, lean_object* v_a_1207_){
_start:
{
lean_object* v_buckets_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; uint8_t v___x_1211_; 
v_buckets_1208_ = lean_ctor_get(v_m_1206_, 1);
v___x_1209_ = lean_unsigned_to_nat(0u);
v___x_1210_ = lean_array_get_size(v_buckets_1208_);
v___x_1211_ = lean_nat_dec_lt(v___x_1209_, v___x_1210_);
if (v___x_1211_ == 0)
{
lean_dec(v_a_1207_);
lean_dec_ref(v_inst_1204_);
lean_dec_ref(v_inst_1203_);
lean_inc(v_inst_1205_);
return v_inst_1205_;
}
else
{
lean_object* v___x_1212_; 
v___x_1212_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_1203_, v_inst_1204_, v_inst_1205_, v_m_1206_, v_a_1207_);
return v___x_1212_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x21___boxed(lean_object* v_00_u03b1_1213_, lean_object* v_00_u03b2_1214_, lean_object* v_inst_1215_, lean_object* v_inst_1216_, lean_object* v_inst_1217_, lean_object* v_m_1218_, lean_object* v_a_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Std_DHashMap_Raw_getKey_x21(v_00_u03b1_1213_, v_00_u03b2_1214_, v_inst_1215_, v_inst_1216_, v_inst_1217_, v_m_1218_, v_a_1219_);
lean_dec_ref(v_m_1218_);
lean_dec(v_inst_1217_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x3f___redArg(lean_object* v_inst_1221_, lean_object* v_inst_1222_, lean_object* v_m_1223_, lean_object* v_a_1224_){
_start:
{
lean_object* v_buckets_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; uint8_t v___x_1228_; 
v_buckets_1225_ = lean_ctor_get(v_m_1223_, 1);
v___x_1226_ = lean_unsigned_to_nat(0u);
v___x_1227_ = lean_array_get_size(v_buckets_1225_);
v___x_1228_ = lean_nat_dec_lt(v___x_1226_, v___x_1227_);
if (v___x_1228_ == 0)
{
lean_object* v___x_1229_; 
lean_dec(v_a_1224_);
lean_dec_ref(v_inst_1222_);
lean_dec_ref(v_inst_1221_);
v___x_1229_ = lean_box(0);
return v___x_1229_;
}
else
{
lean_object* v___x_1230_; 
v___x_1230_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(v_inst_1221_, v_inst_1222_, v_m_1223_, v_a_1224_);
return v___x_1230_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x3f___redArg___boxed(lean_object* v_inst_1231_, lean_object* v_inst_1232_, lean_object* v_m_1233_, lean_object* v_a_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Std_DHashMap_Raw_getEntry_x3f___redArg(v_inst_1231_, v_inst_1232_, v_m_1233_, v_a_1234_);
lean_dec_ref(v_m_1233_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x3f(lean_object* v_00_u03b1_1236_, lean_object* v_00_u03b2_1237_, lean_object* v_inst_1238_, lean_object* v_inst_1239_, lean_object* v_m_1240_, lean_object* v_a_1241_){
_start:
{
lean_object* v_buckets_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; uint8_t v___x_1245_; 
v_buckets_1242_ = lean_ctor_get(v_m_1240_, 1);
v___x_1243_ = lean_unsigned_to_nat(0u);
v___x_1244_ = lean_array_get_size(v_buckets_1242_);
v___x_1245_ = lean_nat_dec_lt(v___x_1243_, v___x_1244_);
if (v___x_1245_ == 0)
{
lean_object* v___x_1246_; 
lean_dec(v_a_1241_);
lean_dec_ref(v_inst_1239_);
lean_dec_ref(v_inst_1238_);
v___x_1246_ = lean_box(0);
return v___x_1246_;
}
else
{
lean_object* v___x_1247_; 
v___x_1247_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(v_inst_1238_, v_inst_1239_, v_m_1240_, v_a_1241_);
return v___x_1247_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x3f___boxed(lean_object* v_00_u03b1_1248_, lean_object* v_00_u03b2_1249_, lean_object* v_inst_1250_, lean_object* v_inst_1251_, lean_object* v_m_1252_, lean_object* v_a_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Std_DHashMap_Raw_getEntry_x3f(v_00_u03b1_1248_, v_00_u03b2_1249_, v_inst_1250_, v_inst_1251_, v_m_1252_, v_a_1253_);
lean_dec_ref(v_m_1252_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry___redArg(lean_object* v_inst_1255_, lean_object* v_inst_1256_, lean_object* v_m_1257_, lean_object* v_a_1258_){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg(v_inst_1255_, v_inst_1256_, v_m_1257_, v_a_1258_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry___redArg___boxed(lean_object* v_inst_1260_, lean_object* v_inst_1261_, lean_object* v_m_1262_, lean_object* v_a_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Std_DHashMap_Raw_getEntry___redArg(v_inst_1260_, v_inst_1261_, v_m_1262_, v_a_1263_);
lean_dec_ref(v_m_1262_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry(lean_object* v_00_u03b1_1265_, lean_object* v_00_u03b2_1266_, lean_object* v_inst_1267_, lean_object* v_inst_1268_, lean_object* v_m_1269_, lean_object* v_a_1270_, lean_object* v_h_1271_){
_start:
{
lean_object* v___x_1272_; 
v___x_1272_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg(v_inst_1267_, v_inst_1268_, v_m_1269_, v_a_1270_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry___boxed(lean_object* v_00_u03b1_1273_, lean_object* v_00_u03b2_1274_, lean_object* v_inst_1275_, lean_object* v_inst_1276_, lean_object* v_m_1277_, lean_object* v_a_1278_, lean_object* v_h_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_Std_DHashMap_Raw_getEntry(v_00_u03b1_1273_, v_00_u03b2_1274_, v_inst_1275_, v_inst_1276_, v_m_1277_, v_a_1278_, v_h_1279_);
lean_dec_ref(v_m_1277_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntryD___redArg(lean_object* v_inst_1281_, lean_object* v_inst_1282_, lean_object* v_m_1283_, lean_object* v_a_1284_, lean_object* v_fallback_1285_){
_start:
{
lean_object* v_buckets_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; uint8_t v___x_1289_; 
v_buckets_1286_ = lean_ctor_get(v_m_1283_, 1);
v___x_1287_ = lean_unsigned_to_nat(0u);
v___x_1288_ = lean_array_get_size(v_buckets_1286_);
v___x_1289_ = lean_nat_dec_lt(v___x_1287_, v___x_1288_);
if (v___x_1289_ == 0)
{
lean_dec(v_a_1284_);
lean_dec_ref(v_inst_1282_);
lean_dec_ref(v_inst_1281_);
lean_inc_ref(v_fallback_1285_);
return v_fallback_1285_;
}
else
{
lean_object* v___x_1290_; 
v___x_1290_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD___redArg(v_inst_1281_, v_inst_1282_, v_m_1283_, v_a_1284_, v_fallback_1285_);
return v___x_1290_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntryD___redArg___boxed(lean_object* v_inst_1291_, lean_object* v_inst_1292_, lean_object* v_m_1293_, lean_object* v_a_1294_, lean_object* v_fallback_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l_Std_DHashMap_Raw_getEntryD___redArg(v_inst_1291_, v_inst_1292_, v_m_1293_, v_a_1294_, v_fallback_1295_);
lean_dec_ref(v_fallback_1295_);
lean_dec_ref(v_m_1293_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntryD(lean_object* v_00_u03b1_1297_, lean_object* v_00_u03b2_1298_, lean_object* v_inst_1299_, lean_object* v_inst_1300_, lean_object* v_m_1301_, lean_object* v_a_1302_, lean_object* v_fallback_1303_){
_start:
{
lean_object* v_buckets_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; uint8_t v___x_1307_; 
v_buckets_1304_ = lean_ctor_get(v_m_1301_, 1);
v___x_1305_ = lean_unsigned_to_nat(0u);
v___x_1306_ = lean_array_get_size(v_buckets_1304_);
v___x_1307_ = lean_nat_dec_lt(v___x_1305_, v___x_1306_);
if (v___x_1307_ == 0)
{
lean_dec(v_a_1302_);
lean_dec_ref(v_inst_1300_);
lean_dec_ref(v_inst_1299_);
lean_inc_ref(v_fallback_1303_);
return v_fallback_1303_;
}
else
{
lean_object* v___x_1308_; 
v___x_1308_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD___redArg(v_inst_1299_, v_inst_1300_, v_m_1301_, v_a_1302_, v_fallback_1303_);
return v___x_1308_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntryD___boxed(lean_object* v_00_u03b1_1309_, lean_object* v_00_u03b2_1310_, lean_object* v_inst_1311_, lean_object* v_inst_1312_, lean_object* v_m_1313_, lean_object* v_a_1314_, lean_object* v_fallback_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l_Std_DHashMap_Raw_getEntryD(v_00_u03b1_1309_, v_00_u03b2_1310_, v_inst_1311_, v_inst_1312_, v_m_1313_, v_a_1314_, v_fallback_1315_);
lean_dec_ref(v_fallback_1315_);
lean_dec_ref(v_m_1313_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x21___redArg(lean_object* v_inst_1317_, lean_object* v_inst_1318_, lean_object* v_inst_1319_, lean_object* v_m_1320_, lean_object* v_a_1321_){
_start:
{
lean_object* v_buckets_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; uint8_t v___x_1325_; 
v_buckets_1322_ = lean_ctor_get(v_m_1320_, 1);
v___x_1323_ = lean_unsigned_to_nat(0u);
v___x_1324_ = lean_array_get_size(v_buckets_1322_);
v___x_1325_ = lean_nat_dec_lt(v___x_1323_, v___x_1324_);
if (v___x_1325_ == 0)
{
lean_dec(v_a_1321_);
lean_dec_ref(v_inst_1318_);
lean_dec_ref(v_inst_1317_);
lean_inc_ref(v_inst_1319_);
return v_inst_1319_;
}
else
{
lean_object* v___x_1326_; 
v___x_1326_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___redArg(v_inst_1317_, v_inst_1318_, v_m_1320_, v_a_1321_, v_inst_1319_);
return v___x_1326_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x21___redArg___boxed(lean_object* v_inst_1327_, lean_object* v_inst_1328_, lean_object* v_inst_1329_, lean_object* v_m_1330_, lean_object* v_a_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l_Std_DHashMap_Raw_getEntry_x21___redArg(v_inst_1327_, v_inst_1328_, v_inst_1329_, v_m_1330_, v_a_1331_);
lean_dec_ref(v_m_1330_);
lean_dec_ref(v_inst_1329_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x21(lean_object* v_00_u03b1_1333_, lean_object* v_00_u03b2_1334_, lean_object* v_inst_1335_, lean_object* v_inst_1336_, lean_object* v_inst_1337_, lean_object* v_m_1338_, lean_object* v_a_1339_){
_start:
{
lean_object* v_buckets_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; uint8_t v___x_1343_; 
v_buckets_1340_ = lean_ctor_get(v_m_1338_, 1);
v___x_1341_ = lean_unsigned_to_nat(0u);
v___x_1342_ = lean_array_get_size(v_buckets_1340_);
v___x_1343_ = lean_nat_dec_lt(v___x_1341_, v___x_1342_);
if (v___x_1343_ == 0)
{
lean_dec(v_a_1339_);
lean_dec_ref(v_inst_1336_);
lean_dec_ref(v_inst_1335_);
lean_inc_ref(v_inst_1337_);
return v_inst_1337_;
}
else
{
lean_object* v___x_1344_; 
v___x_1344_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___redArg(v_inst_1335_, v_inst_1336_, v_m_1338_, v_a_1339_, v_inst_1337_);
return v___x_1344_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x21___boxed(lean_object* v_00_u03b1_1345_, lean_object* v_00_u03b2_1346_, lean_object* v_inst_1347_, lean_object* v_inst_1348_, lean_object* v_inst_1349_, lean_object* v_m_1350_, lean_object* v_a_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l_Std_DHashMap_Raw_getEntry_x21(v_00_u03b1_1345_, v_00_u03b2_1346_, v_inst_1347_, v_inst_1348_, v_inst_1349_, v_m_1350_, v_a_1351_);
lean_dec_ref(v_m_1350_);
lean_dec_ref(v_inst_1349_);
return v_res_1352_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_isEmpty___redArg(lean_object* v_m_1353_){
_start:
{
lean_object* v_size_1354_; lean_object* v___x_1355_; uint8_t v___x_1356_; 
v_size_1354_ = lean_ctor_get(v_m_1353_, 0);
v___x_1355_ = lean_unsigned_to_nat(0u);
v___x_1356_ = lean_nat_dec_eq(v_size_1354_, v___x_1355_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_isEmpty___redArg___boxed(lean_object* v_m_1357_){
_start:
{
uint8_t v_res_1358_; lean_object* v_r_1359_; 
v_res_1358_ = l_Std_DHashMap_Raw_isEmpty___redArg(v_m_1357_);
lean_dec_ref(v_m_1357_);
v_r_1359_ = lean_box(v_res_1358_);
return v_r_1359_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_isEmpty(lean_object* v_00_u03b1_1360_, lean_object* v_00_u03b2_1361_, lean_object* v_m_1362_){
_start:
{
lean_object* v_size_1363_; lean_object* v___x_1364_; uint8_t v___x_1365_; 
v_size_1363_ = lean_ctor_get(v_m_1362_, 0);
v___x_1364_ = lean_unsigned_to_nat(0u);
v___x_1365_ = lean_nat_dec_eq(v_size_1363_, v___x_1364_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_isEmpty___boxed(lean_object* v_00_u03b1_1366_, lean_object* v_00_u03b2_1367_, lean_object* v_m_1368_){
_start:
{
uint8_t v_res_1369_; lean_object* v_r_1370_; 
v_res_1369_ = l_Std_DHashMap_Raw_isEmpty(v_00_u03b1_1366_, v_00_u03b2_1367_, v_m_1368_);
lean_dec_ref(v_m_1368_);
v_r_1370_ = lean_box(v_res_1369_);
return v_r_1370_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_modify___redArg(lean_object* v_inst_1371_, lean_object* v_inst_1372_, lean_object* v_m_1373_, lean_object* v_a_1374_, lean_object* v_f_1375_){
_start:
{
lean_object* v_buckets_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; uint8_t v___x_1379_; 
v_buckets_1376_ = lean_ctor_get(v_m_1373_, 1);
v___x_1377_ = lean_unsigned_to_nat(0u);
v___x_1378_ = lean_array_get_size(v_buckets_1376_);
v___x_1379_ = lean_nat_dec_lt(v___x_1377_, v___x_1378_);
if (v___x_1379_ == 0)
{
lean_object* v___x_1380_; 
lean_dec(v_f_1375_);
lean_dec(v_a_1374_);
lean_dec_ref(v_m_1373_);
lean_dec_ref(v_inst_1372_);
lean_dec_ref(v_inst_1371_);
v___x_1380_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_1380_;
}
else
{
lean_object* v___x_1381_; 
v___x_1381_ = l_Std_DHashMap_Internal_Raw_u2080_modify___redArg(v_inst_1371_, v_inst_1372_, v_m_1373_, v_a_1374_, v_f_1375_);
return v___x_1381_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_modify(lean_object* v_00_u03b1_1382_, lean_object* v_00_u03b2_1383_, lean_object* v_inst_1384_, lean_object* v_inst_1385_, lean_object* v_inst_1386_, lean_object* v_m_1387_, lean_object* v_a_1388_, lean_object* v_f_1389_){
_start:
{
lean_object* v_buckets_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; uint8_t v___x_1393_; 
v_buckets_1390_ = lean_ctor_get(v_m_1387_, 1);
v___x_1391_ = lean_unsigned_to_nat(0u);
v___x_1392_ = lean_array_get_size(v_buckets_1390_);
v___x_1393_ = lean_nat_dec_lt(v___x_1391_, v___x_1392_);
if (v___x_1393_ == 0)
{
lean_object* v___x_1394_; 
lean_dec(v_f_1389_);
lean_dec(v_a_1388_);
lean_dec_ref(v_m_1387_);
lean_dec_ref(v_inst_1386_);
lean_dec_ref(v_inst_1384_);
v___x_1394_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_1394_;
}
else
{
lean_object* v___x_1395_; 
v___x_1395_ = l_Std_DHashMap_Internal_Raw_u2080_modify___redArg(v_inst_1384_, v_inst_1386_, v_m_1387_, v_a_1388_, v_f_1389_);
return v___x_1395_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_modify___redArg(lean_object* v_inst_1396_, lean_object* v_inst_1397_, lean_object* v_m_1398_, lean_object* v_a_1399_, lean_object* v_f_1400_){
_start:
{
lean_object* v_buckets_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; uint8_t v___x_1404_; 
v_buckets_1401_ = lean_ctor_get(v_m_1398_, 1);
v___x_1402_ = lean_unsigned_to_nat(0u);
v___x_1403_ = lean_array_get_size(v_buckets_1401_);
v___x_1404_ = lean_nat_dec_lt(v___x_1402_, v___x_1403_);
if (v___x_1404_ == 0)
{
lean_object* v___x_1405_; 
lean_dec(v_f_1400_);
lean_dec(v_a_1399_);
lean_dec_ref(v_m_1398_);
lean_dec_ref(v_inst_1397_);
lean_dec_ref(v_inst_1396_);
v___x_1405_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_1405_;
}
else
{
lean_object* v___x_1406_; 
v___x_1406_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_inst_1396_, v_inst_1397_, v_m_1398_, v_a_1399_, v_f_1400_);
return v___x_1406_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_modify(lean_object* v_00_u03b1_1407_, lean_object* v_inst_1408_, lean_object* v_inst_1409_, lean_object* v_inst_1410_, lean_object* v_00_u03b2_1411_, lean_object* v_m_1412_, lean_object* v_a_1413_, lean_object* v_f_1414_){
_start:
{
lean_object* v_buckets_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; uint8_t v___x_1418_; 
v_buckets_1415_ = lean_ctor_get(v_m_1412_, 1);
v___x_1416_ = lean_unsigned_to_nat(0u);
v___x_1417_ = lean_array_get_size(v_buckets_1415_);
v___x_1418_ = lean_nat_dec_lt(v___x_1416_, v___x_1417_);
if (v___x_1418_ == 0)
{
lean_object* v___x_1419_; 
lean_dec(v_f_1414_);
lean_dec(v_a_1413_);
lean_dec_ref(v_m_1412_);
lean_dec_ref(v_inst_1410_);
lean_dec_ref(v_inst_1408_);
v___x_1419_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_1419_;
}
else
{
lean_object* v___x_1420_; 
v___x_1420_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_inst_1408_, v_inst_1410_, v_m_1412_, v_a_1413_, v_f_1414_);
return v___x_1420_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_alter___redArg(lean_object* v_inst_1421_, lean_object* v_inst_1422_, lean_object* v_m_1423_, lean_object* v_a_1424_, lean_object* v_f_1425_){
_start:
{
lean_object* v_buckets_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; uint8_t v___x_1429_; 
v_buckets_1426_ = lean_ctor_get(v_m_1423_, 1);
v___x_1427_ = lean_unsigned_to_nat(0u);
v___x_1428_ = lean_array_get_size(v_buckets_1426_);
v___x_1429_ = lean_nat_dec_lt(v___x_1427_, v___x_1428_);
if (v___x_1429_ == 0)
{
lean_object* v___x_1430_; 
lean_dec_ref(v_f_1425_);
lean_dec(v_a_1424_);
lean_dec_ref(v_m_1423_);
lean_dec_ref(v_inst_1422_);
lean_dec_ref(v_inst_1421_);
v___x_1430_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_1430_;
}
else
{
lean_object* v___x_1431_; 
v___x_1431_ = l_Std_DHashMap_Internal_Raw_u2080_alter___redArg(v_inst_1421_, v_inst_1422_, v_m_1423_, v_a_1424_, v_f_1425_);
return v___x_1431_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_alter(lean_object* v_00_u03b1_1432_, lean_object* v_00_u03b2_1433_, lean_object* v_inst_1434_, lean_object* v_inst_1435_, lean_object* v_inst_1436_, lean_object* v_m_1437_, lean_object* v_a_1438_, lean_object* v_f_1439_){
_start:
{
lean_object* v_buckets_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; uint8_t v___x_1443_; 
v_buckets_1440_ = lean_ctor_get(v_m_1437_, 1);
v___x_1441_ = lean_unsigned_to_nat(0u);
v___x_1442_ = lean_array_get_size(v_buckets_1440_);
v___x_1443_ = lean_nat_dec_lt(v___x_1441_, v___x_1442_);
if (v___x_1443_ == 0)
{
lean_object* v___x_1444_; 
lean_dec_ref(v_f_1439_);
lean_dec(v_a_1438_);
lean_dec_ref(v_m_1437_);
lean_dec_ref(v_inst_1436_);
lean_dec_ref(v_inst_1434_);
v___x_1444_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_1444_;
}
else
{
lean_object* v___x_1445_; 
v___x_1445_ = l_Std_DHashMap_Internal_Raw_u2080_alter___redArg(v_inst_1434_, v_inst_1436_, v_m_1437_, v_a_1438_, v_f_1439_);
return v___x_1445_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_alter___redArg(lean_object* v_inst_1446_, lean_object* v_inst_1447_, lean_object* v_m_1448_, lean_object* v_a_1449_, lean_object* v_f_1450_){
_start:
{
lean_object* v_buckets_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; uint8_t v___x_1454_; 
v_buckets_1451_ = lean_ctor_get(v_m_1448_, 1);
v___x_1452_ = lean_unsigned_to_nat(0u);
v___x_1453_ = lean_array_get_size(v_buckets_1451_);
v___x_1454_ = lean_nat_dec_lt(v___x_1452_, v___x_1453_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1455_; 
lean_dec_ref(v_f_1450_);
lean_dec(v_a_1449_);
lean_dec_ref(v_m_1448_);
lean_dec_ref(v_inst_1447_);
lean_dec_ref(v_inst_1446_);
v___x_1455_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_1455_;
}
else
{
lean_object* v___x_1456_; 
v___x_1456_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_1446_, v_inst_1447_, v_m_1448_, v_a_1449_, v_f_1450_);
return v___x_1456_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_alter(lean_object* v_00_u03b1_1457_, lean_object* v_inst_1458_, lean_object* v_inst_1459_, lean_object* v_inst_1460_, lean_object* v_00_u03b2_1461_, lean_object* v_m_1462_, lean_object* v_a_1463_, lean_object* v_f_1464_){
_start:
{
lean_object* v_buckets_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; uint8_t v___x_1468_; 
v_buckets_1465_ = lean_ctor_get(v_m_1462_, 1);
v___x_1466_ = lean_unsigned_to_nat(0u);
v___x_1467_ = lean_array_get_size(v_buckets_1465_);
v___x_1468_ = lean_nat_dec_lt(v___x_1466_, v___x_1467_);
if (v___x_1468_ == 0)
{
lean_object* v___x_1469_; 
lean_dec_ref(v_f_1464_);
lean_dec(v_a_1463_);
lean_dec_ref(v_m_1462_);
lean_dec_ref(v_inst_1460_);
lean_dec_ref(v_inst_1458_);
v___x_1469_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_1469_;
}
else
{
lean_object* v___x_1470_; 
v___x_1470_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_1458_, v_inst_1460_, v_m_1462_, v_a_1463_, v_f_1464_);
return v___x_1470_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0(lean_object* v_f_1471_, lean_object* v_a_1472_, lean_object* v_b_1473_, lean_object* v_d_1474_){
_start:
{
lean_object* v___x_1475_; 
v___x_1475_ = lean_apply_3(v_f_1471_, v_d_1474_, v_a_1472_, v_b_1473_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__1(lean_object* v_inst_1476_, lean_object* v___f_1477_, lean_object* v_l_1478_, lean_object* v_acc_1479_){
_start:
{
lean_object* v___x_1480_; 
v___x_1480_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v_inst_1476_, v___f_1477_, v_acc_1479_, v_l_1478_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRevM___redArg(lean_object* v_inst_1481_, lean_object* v_f_1482_, lean_object* v_init_1483_, lean_object* v_b_1484_){
_start:
{
lean_object* v_buckets_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; uint8_t v___x_1488_; 
v_buckets_1485_ = lean_ctor_get(v_b_1484_, 1);
lean_inc_ref(v_buckets_1485_);
lean_dec_ref(v_b_1484_);
v___x_1486_ = lean_array_get_size(v_buckets_1485_);
v___x_1487_ = lean_unsigned_to_nat(0u);
v___x_1488_ = lean_nat_dec_lt(v___x_1487_, v___x_1486_);
if (v___x_1488_ == 0)
{
lean_object* v_toApplicative_1489_; lean_object* v_toPure_1490_; lean_object* v___x_1491_; 
lean_dec_ref(v_buckets_1485_);
lean_dec(v_f_1482_);
v_toApplicative_1489_ = lean_ctor_get(v_inst_1481_, 0);
lean_inc_ref(v_toApplicative_1489_);
lean_dec_ref(v_inst_1481_);
v_toPure_1490_ = lean_ctor_get(v_toApplicative_1489_, 1);
lean_inc(v_toPure_1490_);
lean_dec_ref(v_toApplicative_1489_);
v___x_1491_ = lean_apply_2(v_toPure_1490_, lean_box(0), v_init_1483_);
return v___x_1491_;
}
else
{
lean_object* v___f_1492_; lean_object* v___f_1493_; size_t v___x_1494_; size_t v___x_1495_; lean_object* v___x_1496_; 
v___f_1492_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1492_, 0, v_f_1482_);
lean_inc_ref(v_inst_1481_);
v___f_1493_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1493_, 0, v_inst_1481_);
lean_closure_set(v___f_1493_, 1, v___f_1492_);
v___x_1494_ = lean_usize_of_nat(v___x_1486_);
v___x_1495_ = ((size_t)0ULL);
v___x_1496_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1481_, v___f_1493_, v_buckets_1485_, v___x_1494_, v___x_1495_, v_init_1483_);
return v___x_1496_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRevM(lean_object* v_00_u03b1_1497_, lean_object* v_00_u03b2_1498_, lean_object* v_00_u03b4_1499_, lean_object* v_m_1500_, lean_object* v_inst_1501_, lean_object* v_f_1502_, lean_object* v_init_1503_, lean_object* v_b_1504_){
_start:
{
lean_object* v_buckets_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; uint8_t v___x_1508_; 
v_buckets_1505_ = lean_ctor_get(v_b_1504_, 1);
lean_inc_ref(v_buckets_1505_);
lean_dec_ref(v_b_1504_);
v___x_1506_ = lean_array_get_size(v_buckets_1505_);
v___x_1507_ = lean_unsigned_to_nat(0u);
v___x_1508_ = lean_nat_dec_lt(v___x_1507_, v___x_1506_);
if (v___x_1508_ == 0)
{
lean_object* v_toApplicative_1509_; lean_object* v_toPure_1510_; lean_object* v___x_1511_; 
lean_dec_ref(v_buckets_1505_);
lean_dec(v_f_1502_);
v_toApplicative_1509_ = lean_ctor_get(v_inst_1501_, 0);
lean_inc_ref(v_toApplicative_1509_);
lean_dec_ref(v_inst_1501_);
v_toPure_1510_ = lean_ctor_get(v_toApplicative_1509_, 1);
lean_inc(v_toPure_1510_);
lean_dec_ref(v_toApplicative_1509_);
v___x_1511_ = lean_apply_2(v_toPure_1510_, lean_box(0), v_init_1503_);
return v___x_1511_;
}
else
{
lean_object* v___f_1512_; lean_object* v___f_1513_; size_t v___x_1514_; size_t v___x_1515_; lean_object* v___x_1516_; 
v___f_1512_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1512_, 0, v_f_1502_);
lean_inc_ref(v_inst_1501_);
v___f_1513_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1513_, 0, v_inst_1501_);
lean_closure_set(v___f_1513_, 1, v___f_1512_);
v___x_1514_ = lean_usize_of_nat(v___x_1506_);
v___x_1515_ = ((size_t)0ULL);
v___x_1516_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1501_, v___f_1513_, v_buckets_1505_, v___x_1514_, v___x_1515_, v_init_1503_);
return v___x_1516_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRev___redArg___lam__1(lean_object* v___x_1517_, lean_object* v___f_1518_, lean_object* v_l_1519_, lean_object* v_acc_1520_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_1517_, v___f_1518_, v_acc_1520_, v_l_1519_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRev___redArg(lean_object* v_f_1541_, lean_object* v_init_1542_, lean_object* v_b_1543_){
_start:
{
lean_object* v___x_1544_; lean_object* v_buckets_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; 
v___x_1544_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_1545_ = lean_ctor_get(v_b_1543_, 1);
lean_inc_ref(v_buckets_1545_);
lean_dec_ref(v_b_1543_);
v___x_1546_ = lean_array_get_size(v_buckets_1545_);
v___x_1547_ = lean_unsigned_to_nat(0u);
v___x_1548_ = lean_nat_dec_lt(v___x_1547_, v___x_1546_);
if (v___x_1548_ == 0)
{
lean_dec_ref(v_buckets_1545_);
lean_dec(v_f_1541_);
return v_init_1542_;
}
else
{
lean_object* v___f_1549_; lean_object* v___f_1550_; size_t v___x_1551_; size_t v___x_1552_; lean_object* v___x_1553_; 
v___f_1549_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1549_, 0, v_f_1541_);
v___f_1550_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1550_, 0, v___x_1544_);
lean_closure_set(v___f_1550_, 1, v___f_1549_);
v___x_1551_ = lean_usize_of_nat(v___x_1546_);
v___x_1552_ = ((size_t)0ULL);
v___x_1553_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1544_, v___f_1550_, v_buckets_1545_, v___x_1551_, v___x_1552_, v_init_1542_);
return v___x_1553_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRev(lean_object* v_00_u03b1_1554_, lean_object* v_00_u03b2_1555_, lean_object* v_00_u03b4_1556_, lean_object* v_f_1557_, lean_object* v_init_1558_, lean_object* v_b_1559_){
_start:
{
lean_object* v___x_1560_; lean_object* v_buckets_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; uint8_t v___x_1564_; 
v___x_1560_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_1561_ = lean_ctor_get(v_b_1559_, 1);
lean_inc_ref(v_buckets_1561_);
lean_dec_ref(v_b_1559_);
v___x_1562_ = lean_array_get_size(v_buckets_1561_);
v___x_1563_ = lean_unsigned_to_nat(0u);
v___x_1564_ = lean_nat_dec_lt(v___x_1563_, v___x_1562_);
if (v___x_1564_ == 0)
{
lean_dec_ref(v_buckets_1561_);
lean_dec(v_f_1557_);
return v_init_1558_;
}
else
{
lean_object* v___f_1565_; lean_object* v___f_1566_; size_t v___x_1567_; size_t v___x_1568_; lean_object* v___x_1569_; 
v___f_1565_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1565_, 0, v_f_1557_);
v___f_1566_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1566_, 0, v___x_1560_);
lean_closure_set(v___f_1566_, 1, v___f_1565_);
v___x_1567_ = lean_usize_of_nat(v___x_1562_);
v___x_1568_ = ((size_t)0ULL);
v___x_1569_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1560_, v___f_1566_, v_buckets_1561_, v___x_1567_, v___x_1568_, v_init_1558_);
return v___x_1569_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevM___redArg(lean_object* v_inst_1570_, lean_object* v_f_1571_, lean_object* v_init_1572_, lean_object* v_b_1573_){
_start:
{
lean_object* v_buckets_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; uint8_t v___x_1577_; 
v_buckets_1574_ = lean_ctor_get(v_b_1573_, 1);
lean_inc_ref(v_buckets_1574_);
lean_dec_ref(v_b_1573_);
v___x_1575_ = lean_array_get_size(v_buckets_1574_);
v___x_1576_ = lean_unsigned_to_nat(0u);
v___x_1577_ = lean_nat_dec_lt(v___x_1576_, v___x_1575_);
if (v___x_1577_ == 0)
{
lean_object* v_toApplicative_1578_; lean_object* v_toPure_1579_; lean_object* v___x_1580_; 
lean_dec_ref(v_buckets_1574_);
lean_dec(v_f_1571_);
v_toApplicative_1578_ = lean_ctor_get(v_inst_1570_, 0);
lean_inc_ref(v_toApplicative_1578_);
lean_dec_ref(v_inst_1570_);
v_toPure_1579_ = lean_ctor_get(v_toApplicative_1578_, 1);
lean_inc(v_toPure_1579_);
lean_dec_ref(v_toApplicative_1578_);
v___x_1580_ = lean_apply_2(v_toPure_1579_, lean_box(0), v_init_1572_);
return v___x_1580_;
}
else
{
lean_object* v___f_1581_; lean_object* v___f_1582_; size_t v___x_1583_; size_t v___x_1584_; lean_object* v___x_1585_; 
v___f_1581_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1581_, 0, v_f_1571_);
lean_inc_ref(v_inst_1570_);
v___f_1582_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1582_, 0, v_inst_1570_);
lean_closure_set(v___f_1582_, 1, v___f_1581_);
v___x_1583_ = lean_usize_of_nat(v___x_1575_);
v___x_1584_ = ((size_t)0ULL);
v___x_1585_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1570_, v___f_1582_, v_buckets_1574_, v___x_1583_, v___x_1584_, v_init_1572_);
return v___x_1585_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevM(lean_object* v_00_u03b1_1586_, lean_object* v_00_u03b2_1587_, lean_object* v_00_u03b4_1588_, lean_object* v_m_1589_, lean_object* v_inst_1590_, lean_object* v_f_1591_, lean_object* v_init_1592_, lean_object* v_b_1593_){
_start:
{
lean_object* v_buckets_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; uint8_t v___x_1597_; 
v_buckets_1594_ = lean_ctor_get(v_b_1593_, 1);
lean_inc_ref(v_buckets_1594_);
lean_dec_ref(v_b_1593_);
v___x_1595_ = lean_array_get_size(v_buckets_1594_);
v___x_1596_ = lean_unsigned_to_nat(0u);
v___x_1597_ = lean_nat_dec_lt(v___x_1596_, v___x_1595_);
if (v___x_1597_ == 0)
{
lean_object* v_toApplicative_1598_; lean_object* v_toPure_1599_; lean_object* v___x_1600_; 
lean_dec_ref(v_buckets_1594_);
lean_dec(v_f_1591_);
v_toApplicative_1598_ = lean_ctor_get(v_inst_1590_, 0);
lean_inc_ref(v_toApplicative_1598_);
lean_dec_ref(v_inst_1590_);
v_toPure_1599_ = lean_ctor_get(v_toApplicative_1598_, 1);
lean_inc(v_toPure_1599_);
lean_dec_ref(v_toApplicative_1598_);
v___x_1600_ = lean_apply_2(v_toPure_1599_, lean_box(0), v_init_1592_);
return v___x_1600_;
}
else
{
lean_object* v___f_1601_; lean_object* v___f_1602_; size_t v___x_1603_; size_t v___x_1604_; lean_object* v___x_1605_; 
v___f_1601_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1601_, 0, v_f_1591_);
lean_inc_ref(v_inst_1590_);
v___f_1602_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1602_, 0, v_inst_1590_);
lean_closure_set(v___f_1602_, 1, v___f_1601_);
v___x_1603_ = lean_usize_of_nat(v___x_1595_);
v___x_1604_ = ((size_t)0ULL);
v___x_1605_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1590_, v___f_1602_, v_buckets_1594_, v___x_1603_, v___x_1604_, v_init_1592_);
return v___x_1605_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRev___redArg(lean_object* v_f_1606_, lean_object* v_init_1607_, lean_object* v_b_1608_){
_start:
{
lean_object* v___x_1609_; lean_object* v_buckets_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; uint8_t v___x_1613_; 
v___x_1609_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_1610_ = lean_ctor_get(v_b_1608_, 1);
lean_inc_ref(v_buckets_1610_);
lean_dec_ref(v_b_1608_);
v___x_1611_ = lean_array_get_size(v_buckets_1610_);
v___x_1612_ = lean_unsigned_to_nat(0u);
v___x_1613_ = lean_nat_dec_lt(v___x_1612_, v___x_1611_);
if (v___x_1613_ == 0)
{
lean_dec_ref(v_buckets_1610_);
lean_dec(v_f_1606_);
return v_init_1607_;
}
else
{
lean_object* v___f_1614_; lean_object* v___f_1615_; size_t v___x_1616_; size_t v___x_1617_; lean_object* v___x_1618_; 
v___f_1614_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1614_, 0, v_f_1606_);
v___f_1615_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1615_, 0, v___x_1609_);
lean_closure_set(v___f_1615_, 1, v___f_1614_);
v___x_1616_ = lean_usize_of_nat(v___x_1611_);
v___x_1617_ = ((size_t)0ULL);
v___x_1618_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1609_, v___f_1615_, v_buckets_1610_, v___x_1616_, v___x_1617_, v_init_1607_);
return v___x_1618_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRev(lean_object* v_00_u03b1_1619_, lean_object* v_00_u03b2_1620_, lean_object* v_00_u03b4_1621_, lean_object* v_f_1622_, lean_object* v_init_1623_, lean_object* v_b_1624_){
_start:
{
lean_object* v___x_1625_; lean_object* v_buckets_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; uint8_t v___x_1629_; 
v___x_1625_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_1626_ = lean_ctor_get(v_b_1624_, 1);
lean_inc_ref(v_buckets_1626_);
lean_dec_ref(v_b_1624_);
v___x_1627_ = lean_array_get_size(v_buckets_1626_);
v___x_1628_ = lean_unsigned_to_nat(0u);
v___x_1629_ = lean_nat_dec_lt(v___x_1628_, v___x_1627_);
if (v___x_1629_ == 0)
{
lean_dec_ref(v_buckets_1626_);
lean_dec(v_f_1622_);
return v_init_1623_;
}
else
{
lean_object* v___f_1630_; lean_object* v___f_1631_; size_t v___x_1632_; size_t v___x_1633_; lean_object* v___x_1634_; 
v___f_1630_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1630_, 0, v_f_1622_);
v___f_1631_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1631_, 0, v___x_1625_);
lean_closure_set(v___f_1631_, 1, v___f_1630_);
v___x_1632_ = lean_usize_of_nat(v___x_1627_);
v___x_1633_ = ((size_t)0ULL);
v___x_1634_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1625_, v___f_1631_, v_buckets_1626_, v___x_1632_, v___x_1633_, v_init_1623_);
return v___x_1634_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__0(lean_object* v_f_1635_, lean_object* v_x_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_){
_start:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___y_1637_);
lean_ctor_set(v___x_1639_, 1, v___y_1638_);
v___x_1640_ = lean_apply_1(v_f_1635_, v___x_1639_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__1(lean_object* v_inst_1641_, lean_object* v___f_1642_, lean_object* v_x_1643_, lean_object* v___y_1644_){
_start:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1645_ = lean_box(0);
v___x_1646_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_1641_, v___f_1642_, v___x_1645_, v___y_1644_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forMUncurried___redArg(lean_object* v_inst_1647_, lean_object* v_f_1648_, lean_object* v_b_1649_){
_start:
{
lean_object* v_buckets_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; uint8_t v___x_1654_; 
v_buckets_1650_ = lean_ctor_get(v_b_1649_, 1);
lean_inc_ref(v_buckets_1650_);
lean_dec_ref(v_b_1649_);
v___x_1651_ = lean_unsigned_to_nat(0u);
v___x_1652_ = lean_array_get_size(v_buckets_1650_);
v___x_1653_ = lean_box(0);
v___x_1654_ = lean_nat_dec_lt(v___x_1651_, v___x_1652_);
if (v___x_1654_ == 0)
{
lean_object* v_toApplicative_1655_; lean_object* v_toPure_1656_; lean_object* v___x_1657_; 
lean_dec_ref(v_buckets_1650_);
lean_dec(v_f_1648_);
v_toApplicative_1655_ = lean_ctor_get(v_inst_1647_, 0);
lean_inc_ref(v_toApplicative_1655_);
lean_dec_ref(v_inst_1647_);
v_toPure_1656_ = lean_ctor_get(v_toApplicative_1655_, 1);
lean_inc(v_toPure_1656_);
lean_dec_ref(v_toApplicative_1655_);
v___x_1657_ = lean_apply_2(v_toPure_1656_, lean_box(0), v___x_1653_);
return v___x_1657_;
}
else
{
lean_object* v___f_1658_; lean_object* v___f_1659_; uint8_t v___x_1660_; 
v___f_1658_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1658_, 0, v_f_1648_);
lean_inc_ref(v_inst_1647_);
v___f_1659_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1659_, 0, v_inst_1647_);
lean_closure_set(v___f_1659_, 1, v___f_1658_);
v___x_1660_ = lean_nat_dec_le(v___x_1652_, v___x_1652_);
if (v___x_1660_ == 0)
{
if (v___x_1654_ == 0)
{
lean_object* v_toApplicative_1661_; lean_object* v_toPure_1662_; lean_object* v___x_1663_; 
lean_dec_ref(v___f_1659_);
lean_dec_ref(v_buckets_1650_);
v_toApplicative_1661_ = lean_ctor_get(v_inst_1647_, 0);
lean_inc_ref(v_toApplicative_1661_);
lean_dec_ref(v_inst_1647_);
v_toPure_1662_ = lean_ctor_get(v_toApplicative_1661_, 1);
lean_inc(v_toPure_1662_);
lean_dec_ref(v_toApplicative_1661_);
v___x_1663_ = lean_apply_2(v_toPure_1662_, lean_box(0), v___x_1653_);
return v___x_1663_;
}
else
{
size_t v___x_1664_; size_t v___x_1665_; lean_object* v___x_1666_; 
v___x_1664_ = ((size_t)0ULL);
v___x_1665_ = lean_usize_of_nat(v___x_1652_);
v___x_1666_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1647_, v___f_1659_, v_buckets_1650_, v___x_1664_, v___x_1665_, v___x_1653_);
return v___x_1666_;
}
}
else
{
size_t v___x_1667_; size_t v___x_1668_; lean_object* v___x_1669_; 
v___x_1667_ = ((size_t)0ULL);
v___x_1668_ = lean_usize_of_nat(v___x_1652_);
v___x_1669_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1647_, v___f_1659_, v_buckets_1650_, v___x_1667_, v___x_1668_, v___x_1653_);
return v___x_1669_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forMUncurried(lean_object* v_00_u03b1_1670_, lean_object* v_m_1671_, lean_object* v_inst_1672_, lean_object* v_00_u03b2_1673_, lean_object* v_f_1674_, lean_object* v_b_1675_){
_start:
{
lean_object* v_buckets_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; uint8_t v___x_1680_; 
v_buckets_1676_ = lean_ctor_get(v_b_1675_, 1);
lean_inc_ref(v_buckets_1676_);
lean_dec_ref(v_b_1675_);
v___x_1677_ = lean_unsigned_to_nat(0u);
v___x_1678_ = lean_array_get_size(v_buckets_1676_);
v___x_1679_ = lean_box(0);
v___x_1680_ = lean_nat_dec_lt(v___x_1677_, v___x_1678_);
if (v___x_1680_ == 0)
{
lean_object* v_toApplicative_1681_; lean_object* v_toPure_1682_; lean_object* v___x_1683_; 
lean_dec_ref(v_buckets_1676_);
lean_dec(v_f_1674_);
v_toApplicative_1681_ = lean_ctor_get(v_inst_1672_, 0);
lean_inc_ref(v_toApplicative_1681_);
lean_dec_ref(v_inst_1672_);
v_toPure_1682_ = lean_ctor_get(v_toApplicative_1681_, 1);
lean_inc(v_toPure_1682_);
lean_dec_ref(v_toApplicative_1681_);
v___x_1683_ = lean_apply_2(v_toPure_1682_, lean_box(0), v___x_1679_);
return v___x_1683_;
}
else
{
lean_object* v___f_1684_; lean_object* v___f_1685_; uint8_t v___x_1686_; 
v___f_1684_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1684_, 0, v_f_1674_);
lean_inc_ref(v_inst_1672_);
v___f_1685_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1685_, 0, v_inst_1672_);
lean_closure_set(v___f_1685_, 1, v___f_1684_);
v___x_1686_ = lean_nat_dec_le(v___x_1678_, v___x_1678_);
if (v___x_1686_ == 0)
{
if (v___x_1680_ == 0)
{
lean_object* v_toApplicative_1687_; lean_object* v_toPure_1688_; lean_object* v___x_1689_; 
lean_dec_ref(v___f_1685_);
lean_dec_ref(v_buckets_1676_);
v_toApplicative_1687_ = lean_ctor_get(v_inst_1672_, 0);
lean_inc_ref(v_toApplicative_1687_);
lean_dec_ref(v_inst_1672_);
v_toPure_1688_ = lean_ctor_get(v_toApplicative_1687_, 1);
lean_inc(v_toPure_1688_);
lean_dec_ref(v_toApplicative_1687_);
v___x_1689_ = lean_apply_2(v_toPure_1688_, lean_box(0), v___x_1679_);
return v___x_1689_;
}
else
{
size_t v___x_1690_; size_t v___x_1691_; lean_object* v___x_1692_; 
v___x_1690_ = ((size_t)0ULL);
v___x_1691_ = lean_usize_of_nat(v___x_1678_);
v___x_1692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1672_, v___f_1685_, v_buckets_1676_, v___x_1690_, v___x_1691_, v___x_1679_);
return v___x_1692_;
}
}
else
{
size_t v___x_1693_; size_t v___x_1694_; lean_object* v___x_1695_; 
v___x_1693_ = ((size_t)0ULL);
v___x_1694_ = lean_usize_of_nat(v___x_1678_);
v___x_1695_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1672_, v___f_1685_, v_buckets_1676_, v___x_1693_, v___x_1694_, v___x_1679_);
return v___x_1695_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__0(lean_object* v_f_1696_, lean_object* v_a_1697_, lean_object* v_b_1698_, lean_object* v_d_1699_){
_start:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1700_, 0, v_a_1697_);
lean_ctor_set(v___x_1700_, 1, v_b_1698_);
v___x_1701_ = lean_apply_2(v_f_1696_, v___x_1700_, v_d_1699_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__1(lean_object* v_inst_1702_, lean_object* v___f_1703_, lean_object* v_a_1704_, lean_object* v_x_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v___x_1707_; 
v___x_1707_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_1702_, v___f_1703_, v_a_1704_, v___y_1706_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forInUncurried___redArg(lean_object* v_inst_1708_, lean_object* v_f_1709_, lean_object* v_init_1710_, lean_object* v_b_1711_){
_start:
{
lean_object* v_buckets_1712_; lean_object* v___f_1713_; lean_object* v___f_1714_; size_t v_sz_1715_; size_t v___x_1716_; lean_object* v___x_1717_; 
v_buckets_1712_ = lean_ctor_get(v_b_1711_, 1);
lean_inc_ref(v_buckets_1712_);
lean_dec_ref(v_b_1711_);
v___f_1713_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1713_, 0, v_f_1709_);
lean_inc_ref(v_inst_1708_);
v___f_1714_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1714_, 0, v_inst_1708_);
lean_closure_set(v___f_1714_, 1, v___f_1713_);
v_sz_1715_ = lean_array_size(v_buckets_1712_);
v___x_1716_ = ((size_t)0ULL);
v___x_1717_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1708_, v_buckets_1712_, v___f_1714_, v_sz_1715_, v___x_1716_, v_init_1710_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forInUncurried(lean_object* v_00_u03b1_1718_, lean_object* v_00_u03b4_1719_, lean_object* v_m_1720_, lean_object* v_inst_1721_, lean_object* v_00_u03b2_1722_, lean_object* v_f_1723_, lean_object* v_init_1724_, lean_object* v_b_1725_){
_start:
{
lean_object* v_buckets_1726_; lean_object* v___f_1727_; lean_object* v___f_1728_; size_t v_sz_1729_; size_t v___x_1730_; lean_object* v___x_1731_; 
v_buckets_1726_ = lean_ctor_get(v_b_1725_, 1);
lean_inc_ref(v_buckets_1726_);
lean_dec_ref(v_b_1725_);
v___f_1727_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1727_, 0, v_f_1723_);
lean_inc_ref(v_inst_1721_);
v___f_1728_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1728_, 0, v_inst_1721_);
lean_closure_set(v___f_1728_, 1, v___f_1727_);
v_sz_1729_ = lean_array_size(v_buckets_1726_);
v___x_1730_ = ((size_t)0ULL);
v___x_1731_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1721_, v_buckets_1726_, v___f_1728_, v_sz_1729_, v___x_1730_, v_init_1724_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_filterMap___redArg(lean_object* v_f_1732_, lean_object* v_m_1733_){
_start:
{
lean_object* v_buckets_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; uint8_t v___x_1737_; 
v_buckets_1734_ = lean_ctor_get(v_m_1733_, 1);
v___x_1735_ = lean_unsigned_to_nat(0u);
v___x_1736_ = lean_array_get_size(v_buckets_1734_);
v___x_1737_ = lean_nat_dec_lt(v___x_1735_, v___x_1736_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; 
lean_dec_ref(v_m_1733_);
lean_dec_ref(v_f_1732_);
v___x_1738_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_1738_;
}
else
{
lean_object* v___x_1739_; 
v___x_1739_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_1732_, v_m_1733_);
return v___x_1739_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_filterMap(lean_object* v_00_u03b1_1740_, lean_object* v_00_u03b2_1741_, lean_object* v_00_u03b3_1742_, lean_object* v_f_1743_, lean_object* v_m_1744_){
_start:
{
lean_object* v_buckets_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; uint8_t v___x_1748_; 
v_buckets_1745_ = lean_ctor_get(v_m_1744_, 1);
v___x_1746_ = lean_unsigned_to_nat(0u);
v___x_1747_ = lean_array_get_size(v_buckets_1745_);
v___x_1748_ = lean_nat_dec_lt(v___x_1746_, v___x_1747_);
if (v___x_1748_ == 0)
{
lean_object* v___x_1749_; 
lean_dec_ref(v_m_1744_);
lean_dec_ref(v_f_1743_);
v___x_1749_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_1749_;
}
else
{
lean_object* v___x_1750_; 
v___x_1750_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_1743_, v_m_1744_);
return v___x_1750_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_map___redArg(lean_object* v_f_1751_, lean_object* v_m_1752_){
_start:
{
lean_object* v_buckets_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; uint8_t v___x_1756_; 
v_buckets_1753_ = lean_ctor_get(v_m_1752_, 1);
v___x_1754_ = lean_unsigned_to_nat(0u);
v___x_1755_ = lean_array_get_size(v_buckets_1753_);
v___x_1756_ = lean_nat_dec_lt(v___x_1754_, v___x_1755_);
if (v___x_1756_ == 0)
{
lean_object* v___x_1757_; 
lean_dec_ref(v_m_1752_);
lean_dec(v_f_1751_);
v___x_1757_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_1757_;
}
else
{
lean_object* v___x_1758_; 
v___x_1758_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_1751_, v_m_1752_);
return v___x_1758_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_map(lean_object* v_00_u03b1_1759_, lean_object* v_00_u03b2_1760_, lean_object* v_00_u03b3_1761_, lean_object* v_f_1762_, lean_object* v_m_1763_){
_start:
{
lean_object* v_buckets_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; uint8_t v___x_1767_; 
v_buckets_1764_ = lean_ctor_get(v_m_1763_, 1);
v___x_1765_ = lean_unsigned_to_nat(0u);
v___x_1766_ = lean_array_get_size(v_buckets_1764_);
v___x_1767_ = lean_nat_dec_lt(v___x_1765_, v___x_1766_);
if (v___x_1767_ == 0)
{
lean_object* v___x_1768_; 
lean_dec_ref(v_m_1763_);
lean_dec(v_f_1762_);
v___x_1768_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_1768_;
}
else
{
lean_object* v___x_1769_; 
v___x_1769_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_1762_, v_m_1763_);
return v___x_1769_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_filter___redArg(lean_object* v_f_1770_, lean_object* v_m_1771_){
_start:
{
lean_object* v_buckets_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; uint8_t v___x_1775_; 
v_buckets_1772_ = lean_ctor_get(v_m_1771_, 1);
v___x_1773_ = lean_unsigned_to_nat(0u);
v___x_1774_ = lean_array_get_size(v_buckets_1772_);
v___x_1775_ = lean_nat_dec_lt(v___x_1773_, v___x_1774_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1776_; 
lean_dec_ref(v_m_1771_);
lean_dec_ref(v_f_1770_);
v___x_1776_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_1776_;
}
else
{
lean_object* v___x_1777_; 
v___x_1777_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1770_, v_m_1771_);
return v___x_1777_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_filter(lean_object* v_00_u03b1_1778_, lean_object* v_00_u03b2_1779_, lean_object* v_f_1780_, lean_object* v_m_1781_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toArray___redArg___lam__0(lean_object* v_x1_1788_, lean_object* v_x2_1789_, lean_object* v_x3_1790_){
_start:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1791_, 0, v_x2_1789_);
lean_ctor_set(v___x_1791_, 1, v_x3_1790_);
v___x_1792_ = lean_array_push(v_x1_1788_, v___x_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toArray___redArg___lam__1(lean_object* v___x_1793_, lean_object* v___f_1794_, lean_object* v_acc_1795_, lean_object* v_l_1796_){
_start:
{
lean_object* v___x_1797_; 
v___x_1797_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1793_, v___f_1794_, v_acc_1795_, v_l_1796_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toArray___redArg(lean_object* v_m_1802_){
_start:
{
lean_object* v_size_1803_; lean_object* v_buckets_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; uint8_t v___x_1809_; 
v_size_1803_ = lean_ctor_get(v_m_1802_, 0);
lean_inc(v_size_1803_);
v_buckets_1804_ = lean_ctor_get(v_m_1802_, 1);
lean_inc_ref(v_buckets_1804_);
lean_dec_ref(v_m_1802_);
v___x_1805_ = lean_mk_empty_array_with_capacity(v_size_1803_);
lean_dec(v_size_1803_);
v___x_1806_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_1807_ = lean_unsigned_to_nat(0u);
v___x_1808_ = lean_array_get_size(v_buckets_1804_);
v___x_1809_ = lean_nat_dec_lt(v___x_1807_, v___x_1808_);
if (v___x_1809_ == 0)
{
lean_dec_ref(v_buckets_1804_);
return v___x_1805_;
}
else
{
lean_object* v___f_1810_; uint8_t v___x_1811_; 
v___f_1810_ = ((lean_object*)(l_Std_DHashMap_Raw_toArray___redArg___closed__1));
v___x_1811_ = lean_nat_dec_le(v___x_1808_, v___x_1808_);
if (v___x_1811_ == 0)
{
if (v___x_1809_ == 0)
{
lean_dec_ref(v_buckets_1804_);
return v___x_1805_;
}
else
{
size_t v___x_1812_; size_t v___x_1813_; lean_object* v___x_1814_; 
v___x_1812_ = ((size_t)0ULL);
v___x_1813_ = lean_usize_of_nat(v___x_1808_);
v___x_1814_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1806_, v___f_1810_, v_buckets_1804_, v___x_1812_, v___x_1813_, v___x_1805_);
return v___x_1814_;
}
}
else
{
size_t v___x_1815_; size_t v___x_1816_; lean_object* v___x_1817_; 
v___x_1815_ = ((size_t)0ULL);
v___x_1816_ = lean_usize_of_nat(v___x_1808_);
v___x_1817_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1806_, v___f_1810_, v_buckets_1804_, v___x_1815_, v___x_1816_, v___x_1805_);
return v___x_1817_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toArray(lean_object* v_00_u03b1_1818_, lean_object* v_00_u03b2_1819_, lean_object* v_m_1820_){
_start:
{
lean_object* v_size_1821_; lean_object* v_buckets_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; uint8_t v___x_1827_; 
v_size_1821_ = lean_ctor_get(v_m_1820_, 0);
lean_inc(v_size_1821_);
v_buckets_1822_ = lean_ctor_get(v_m_1820_, 1);
lean_inc_ref(v_buckets_1822_);
lean_dec_ref(v_m_1820_);
v___x_1823_ = lean_mk_empty_array_with_capacity(v_size_1821_);
lean_dec(v_size_1821_);
v___x_1824_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_1825_ = lean_unsigned_to_nat(0u);
v___x_1826_ = lean_array_get_size(v_buckets_1822_);
v___x_1827_ = lean_nat_dec_lt(v___x_1825_, v___x_1826_);
if (v___x_1827_ == 0)
{
lean_dec_ref(v_buckets_1822_);
return v___x_1823_;
}
else
{
lean_object* v___f_1828_; uint8_t v___x_1829_; 
v___f_1828_ = ((lean_object*)(l_Std_DHashMap_Raw_toArray___redArg___closed__1));
v___x_1829_ = lean_nat_dec_le(v___x_1826_, v___x_1826_);
if (v___x_1829_ == 0)
{
if (v___x_1827_ == 0)
{
lean_dec_ref(v_buckets_1822_);
return v___x_1823_;
}
else
{
size_t v___x_1830_; size_t v___x_1831_; lean_object* v___x_1832_; 
v___x_1830_ = ((size_t)0ULL);
v___x_1831_ = lean_usize_of_nat(v___x_1826_);
v___x_1832_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1824_, v___f_1828_, v_buckets_1822_, v___x_1830_, v___x_1831_, v___x_1823_);
return v___x_1832_;
}
}
else
{
size_t v___x_1833_; size_t v___x_1834_; lean_object* v___x_1835_; 
v___x_1833_ = ((size_t)0ULL);
v___x_1834_ = lean_usize_of_nat(v___x_1826_);
v___x_1835_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1824_, v___f_1828_, v_buckets_1822_, v___x_1833_, v___x_1834_, v___x_1823_);
return v___x_1835_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toArray___redArg___lam__0(lean_object* v_x1_1836_, lean_object* v_x2_1837_, lean_object* v_x3_1838_){
_start:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1839_, 0, v_x2_1837_);
lean_ctor_set(v___x_1839_, 1, v_x3_1838_);
v___x_1840_ = lean_array_push(v_x1_1836_, v___x_1839_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toArray___redArg___lam__1(lean_object* v___x_1841_, lean_object* v___f_1842_, lean_object* v_acc_1843_, lean_object* v_l_1844_){
_start:
{
lean_object* v___x_1845_; 
v___x_1845_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1841_, v___f_1842_, v_acc_1843_, v_l_1844_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toArray___redArg(lean_object* v_m_1850_){
_start:
{
lean_object* v_size_1851_; lean_object* v_buckets_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; uint8_t v___x_1857_; 
v_size_1851_ = lean_ctor_get(v_m_1850_, 0);
lean_inc(v_size_1851_);
v_buckets_1852_ = lean_ctor_get(v_m_1850_, 1);
lean_inc_ref(v_buckets_1852_);
lean_dec_ref(v_m_1850_);
v___x_1853_ = lean_mk_empty_array_with_capacity(v_size_1851_);
lean_dec(v_size_1851_);
v___x_1854_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_1855_ = lean_unsigned_to_nat(0u);
v___x_1856_ = lean_array_get_size(v_buckets_1852_);
v___x_1857_ = lean_nat_dec_lt(v___x_1855_, v___x_1856_);
if (v___x_1857_ == 0)
{
lean_dec_ref(v_buckets_1852_);
return v___x_1853_;
}
else
{
lean_object* v___f_1858_; uint8_t v___x_1859_; 
v___f_1858_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_toArray___redArg___closed__1));
v___x_1859_ = lean_nat_dec_le(v___x_1856_, v___x_1856_);
if (v___x_1859_ == 0)
{
if (v___x_1857_ == 0)
{
lean_dec_ref(v_buckets_1852_);
return v___x_1853_;
}
else
{
size_t v___x_1860_; size_t v___x_1861_; lean_object* v___x_1862_; 
v___x_1860_ = ((size_t)0ULL);
v___x_1861_ = lean_usize_of_nat(v___x_1856_);
v___x_1862_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1854_, v___f_1858_, v_buckets_1852_, v___x_1860_, v___x_1861_, v___x_1853_);
return v___x_1862_;
}
}
else
{
size_t v___x_1863_; size_t v___x_1864_; lean_object* v___x_1865_; 
v___x_1863_ = ((size_t)0ULL);
v___x_1864_ = lean_usize_of_nat(v___x_1856_);
v___x_1865_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1854_, v___f_1858_, v_buckets_1852_, v___x_1863_, v___x_1864_, v___x_1853_);
return v___x_1865_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toArray(lean_object* v_00_u03b1_1866_, lean_object* v_00_u03b2_1867_, lean_object* v_m_1868_){
_start:
{
lean_object* v_size_1869_; lean_object* v_buckets_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; uint8_t v___x_1875_; 
v_size_1869_ = lean_ctor_get(v_m_1868_, 0);
lean_inc(v_size_1869_);
v_buckets_1870_ = lean_ctor_get(v_m_1868_, 1);
lean_inc_ref(v_buckets_1870_);
lean_dec_ref(v_m_1868_);
v___x_1871_ = lean_mk_empty_array_with_capacity(v_size_1869_);
lean_dec(v_size_1869_);
v___x_1872_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_1873_ = lean_unsigned_to_nat(0u);
v___x_1874_ = lean_array_get_size(v_buckets_1870_);
v___x_1875_ = lean_nat_dec_lt(v___x_1873_, v___x_1874_);
if (v___x_1875_ == 0)
{
lean_dec_ref(v_buckets_1870_);
return v___x_1871_;
}
else
{
lean_object* v___f_1876_; uint8_t v___x_1877_; 
v___f_1876_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_toArray___redArg___closed__1));
v___x_1877_ = lean_nat_dec_le(v___x_1874_, v___x_1874_);
if (v___x_1877_ == 0)
{
if (v___x_1875_ == 0)
{
lean_dec_ref(v_buckets_1870_);
return v___x_1871_;
}
else
{
size_t v___x_1878_; size_t v___x_1879_; lean_object* v___x_1880_; 
v___x_1878_ = ((size_t)0ULL);
v___x_1879_ = lean_usize_of_nat(v___x_1874_);
v___x_1880_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1872_, v___f_1876_, v_buckets_1870_, v___x_1878_, v___x_1879_, v___x_1871_);
return v___x_1880_;
}
}
else
{
size_t v___x_1881_; size_t v___x_1882_; lean_object* v___x_1883_; 
v___x_1881_ = ((size_t)0ULL);
v___x_1882_ = lean_usize_of_nat(v___x_1874_);
v___x_1883_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1872_, v___f_1876_, v_buckets_1870_, v___x_1881_, v___x_1882_, v___x_1871_);
return v___x_1883_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keysArray___redArg___lam__0(lean_object* v_x1_1884_, lean_object* v_x2_1885_, lean_object* v_x3_1886_){
_start:
{
lean_object* v___x_1887_; 
v___x_1887_ = lean_array_push(v_x1_1884_, v_x2_1885_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keysArray___redArg___lam__0___boxed(lean_object* v_x1_1888_, lean_object* v_x2_1889_, lean_object* v_x3_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l_Std_DHashMap_Raw_keysArray___redArg___lam__0(v_x1_1888_, v_x2_1889_, v_x3_1890_);
lean_dec(v_x3_1890_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keysArray___redArg___lam__1(lean_object* v___x_1892_, lean_object* v___f_1893_, lean_object* v_acc_1894_, lean_object* v_l_1895_){
_start:
{
lean_object* v___x_1896_; 
v___x_1896_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1892_, v___f_1893_, v_acc_1894_, v_l_1895_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keysArray___redArg(lean_object* v_m_1901_){
_start:
{
lean_object* v_size_1902_; lean_object* v_buckets_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; uint8_t v___x_1908_; 
v_size_1902_ = lean_ctor_get(v_m_1901_, 0);
lean_inc(v_size_1902_);
v_buckets_1903_ = lean_ctor_get(v_m_1901_, 1);
lean_inc_ref(v_buckets_1903_);
lean_dec_ref(v_m_1901_);
v___x_1904_ = lean_mk_empty_array_with_capacity(v_size_1902_);
lean_dec(v_size_1902_);
v___x_1905_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_1906_ = lean_unsigned_to_nat(0u);
v___x_1907_ = lean_array_get_size(v_buckets_1903_);
v___x_1908_ = lean_nat_dec_lt(v___x_1906_, v___x_1907_);
if (v___x_1908_ == 0)
{
lean_dec_ref(v_buckets_1903_);
return v___x_1904_;
}
else
{
lean_object* v___f_1909_; uint8_t v___x_1910_; 
v___f_1909_ = ((lean_object*)(l_Std_DHashMap_Raw_keysArray___redArg___closed__1));
v___x_1910_ = lean_nat_dec_le(v___x_1907_, v___x_1907_);
if (v___x_1910_ == 0)
{
if (v___x_1908_ == 0)
{
lean_dec_ref(v_buckets_1903_);
return v___x_1904_;
}
else
{
size_t v___x_1911_; size_t v___x_1912_; lean_object* v___x_1913_; 
v___x_1911_ = ((size_t)0ULL);
v___x_1912_ = lean_usize_of_nat(v___x_1907_);
v___x_1913_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1905_, v___f_1909_, v_buckets_1903_, v___x_1911_, v___x_1912_, v___x_1904_);
return v___x_1913_;
}
}
else
{
size_t v___x_1914_; size_t v___x_1915_; lean_object* v___x_1916_; 
v___x_1914_ = ((size_t)0ULL);
v___x_1915_ = lean_usize_of_nat(v___x_1907_);
v___x_1916_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1905_, v___f_1909_, v_buckets_1903_, v___x_1914_, v___x_1915_, v___x_1904_);
return v___x_1916_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keysArray(lean_object* v_00_u03b1_1917_, lean_object* v_00_u03b2_1918_, lean_object* v_m_1919_){
_start:
{
lean_object* v_size_1920_; lean_object* v_buckets_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; uint8_t v___x_1926_; 
v_size_1920_ = lean_ctor_get(v_m_1919_, 0);
lean_inc(v_size_1920_);
v_buckets_1921_ = lean_ctor_get(v_m_1919_, 1);
lean_inc_ref(v_buckets_1921_);
lean_dec_ref(v_m_1919_);
v___x_1922_ = lean_mk_empty_array_with_capacity(v_size_1920_);
lean_dec(v_size_1920_);
v___x_1923_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_1924_ = lean_unsigned_to_nat(0u);
v___x_1925_ = lean_array_get_size(v_buckets_1921_);
v___x_1926_ = lean_nat_dec_lt(v___x_1924_, v___x_1925_);
if (v___x_1926_ == 0)
{
lean_dec_ref(v_buckets_1921_);
return v___x_1922_;
}
else
{
lean_object* v___f_1927_; uint8_t v___x_1928_; 
v___f_1927_ = ((lean_object*)(l_Std_DHashMap_Raw_keysArray___redArg___closed__1));
v___x_1928_ = lean_nat_dec_le(v___x_1925_, v___x_1925_);
if (v___x_1928_ == 0)
{
if (v___x_1926_ == 0)
{
lean_dec_ref(v_buckets_1921_);
return v___x_1922_;
}
else
{
size_t v___x_1929_; size_t v___x_1930_; lean_object* v___x_1931_; 
v___x_1929_ = ((size_t)0ULL);
v___x_1930_ = lean_usize_of_nat(v___x_1925_);
v___x_1931_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1923_, v___f_1927_, v_buckets_1921_, v___x_1929_, v___x_1930_, v___x_1922_);
return v___x_1931_;
}
}
else
{
size_t v___x_1932_; size_t v___x_1933_; lean_object* v___x_1934_; 
v___x_1932_ = ((size_t)0ULL);
v___x_1933_ = lean_usize_of_nat(v___x_1925_);
v___x_1934_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1923_, v___f_1927_, v_buckets_1921_, v___x_1932_, v___x_1933_, v___x_1922_);
return v___x_1934_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_union___redArg___lam__0(lean_object* v_inst_1935_, lean_object* v_inst_1936_, lean_object* v_a_1937_, lean_object* v_b_1938_, lean_object* v_acc_1939_){
_start:
{
lean_object* v_r_1940_; lean_object* v___x_1941_; 
v_r_1940_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_1935_, v_inst_1936_, v_acc_1939_, v_a_1937_, v_b_1938_);
v___x_1941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1941_, 0, v_r_1940_);
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_union___redArg___lam__1(lean_object* v___x_1942_, lean_object* v___f_1943_, lean_object* v_a_1944_, lean_object* v_x_1945_, lean_object* v___y_1946_){
_start:
{
lean_object* v___x_1947_; 
v___x_1947_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1942_, v___f_1943_, v_a_1944_, v___y_1946_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_union___redArg(lean_object* v_inst_1950_, lean_object* v_inst_1951_, lean_object* v_m_u2081_1952_, lean_object* v_m_u2082_1953_){
_start:
{
lean_object* v_size_1954_; lean_object* v_buckets_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; uint8_t v___x_1958_; 
v_size_1954_ = lean_ctor_get(v_m_u2081_1952_, 0);
v_buckets_1955_ = lean_ctor_get(v_m_u2081_1952_, 1);
v___x_1956_ = lean_unsigned_to_nat(0u);
v___x_1957_ = lean_array_get_size(v_buckets_1955_);
v___x_1958_ = lean_nat_dec_lt(v___x_1956_, v___x_1957_);
if (v___x_1958_ == 0)
{
lean_dec_ref(v_m_u2081_1952_);
lean_dec_ref(v_inst_1951_);
lean_dec_ref(v_inst_1950_);
return v_m_u2082_1953_;
}
else
{
lean_object* v_size_1959_; lean_object* v_buckets_1960_; lean_object* v___x_1961_; uint8_t v___x_1962_; 
v_size_1959_ = lean_ctor_get(v_m_u2082_1953_, 0);
v_buckets_1960_ = lean_ctor_get(v_m_u2082_1953_, 1);
v___x_1961_ = lean_array_get_size(v_buckets_1960_);
v___x_1962_ = lean_nat_dec_lt(v___x_1956_, v___x_1961_);
if (v___x_1962_ == 0)
{
lean_dec_ref(v_m_u2082_1953_);
lean_dec_ref(v_inst_1951_);
lean_dec_ref(v_inst_1950_);
return v_m_u2081_1952_;
}
else
{
uint8_t v___x_1963_; 
v___x_1963_ = lean_nat_dec_le(v_size_1954_, v_size_1959_);
if (v___x_1963_ == 0)
{
lean_object* v___f_1964_; lean_object* v___x_1965_; 
v___f_1964_ = ((lean_object*)(l_Std_DHashMap_Raw_union___redArg___closed__0));
v___x_1965_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1964_, v_inst_1950_, v_inst_1951_, v_m_u2081_1952_, v_m_u2082_1953_);
return v___x_1965_;
}
else
{
lean_object* v___f_1966_; lean_object* v___x_1967_; lean_object* v___f_1968_; size_t v_sz_1969_; size_t v___x_1970_; lean_object* v___x_1971_; 
lean_inc_ref(v_buckets_1955_);
lean_dec_ref(v_m_u2081_1952_);
v___f_1966_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1966_, 0, v_inst_1950_);
lean_closure_set(v___f_1966_, 1, v_inst_1951_);
v___x_1967_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___f_1968_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1968_, 0, v___x_1967_);
lean_closure_set(v___f_1968_, 1, v___f_1966_);
v_sz_1969_ = lean_array_size(v_buckets_1955_);
v___x_1970_ = ((size_t)0ULL);
v___x_1971_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1967_, v_buckets_1955_, v___f_1968_, v_sz_1969_, v___x_1970_, v_m_u2082_1953_);
return v___x_1971_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_union(lean_object* v_00_u03b1_1972_, lean_object* v_00_u03b2_1973_, lean_object* v_inst_1974_, lean_object* v_inst_1975_, lean_object* v_m_u2081_1976_, lean_object* v_m_u2082_1977_){
_start:
{
lean_object* v_size_1978_; lean_object* v_buckets_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; uint8_t v___x_1982_; 
v_size_1978_ = lean_ctor_get(v_m_u2081_1976_, 0);
v_buckets_1979_ = lean_ctor_get(v_m_u2081_1976_, 1);
v___x_1980_ = lean_unsigned_to_nat(0u);
v___x_1981_ = lean_array_get_size(v_buckets_1979_);
v___x_1982_ = lean_nat_dec_lt(v___x_1980_, v___x_1981_);
if (v___x_1982_ == 0)
{
lean_dec_ref(v_m_u2081_1976_);
lean_dec_ref(v_inst_1975_);
lean_dec_ref(v_inst_1974_);
return v_m_u2082_1977_;
}
else
{
lean_object* v_size_1983_; lean_object* v_buckets_1984_; lean_object* v___x_1985_; uint8_t v___x_1986_; 
v_size_1983_ = lean_ctor_get(v_m_u2082_1977_, 0);
v_buckets_1984_ = lean_ctor_get(v_m_u2082_1977_, 1);
v___x_1985_ = lean_array_get_size(v_buckets_1984_);
v___x_1986_ = lean_nat_dec_lt(v___x_1980_, v___x_1985_);
if (v___x_1986_ == 0)
{
lean_dec_ref(v_m_u2082_1977_);
lean_dec_ref(v_inst_1975_);
lean_dec_ref(v_inst_1974_);
return v_m_u2081_1976_;
}
else
{
uint8_t v___x_1987_; 
v___x_1987_ = lean_nat_dec_le(v_size_1978_, v_size_1983_);
if (v___x_1987_ == 0)
{
lean_object* v___f_1988_; lean_object* v___x_1989_; 
v___f_1988_ = ((lean_object*)(l_Std_DHashMap_Raw_union___redArg___closed__0));
v___x_1989_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1988_, v_inst_1974_, v_inst_1975_, v_m_u2081_1976_, v_m_u2082_1977_);
return v___x_1989_;
}
else
{
lean_object* v___f_1990_; lean_object* v___x_1991_; lean_object* v___f_1992_; size_t v_sz_1993_; size_t v___x_1994_; lean_object* v___x_1995_; 
lean_inc_ref(v_buckets_1979_);
lean_dec_ref(v_m_u2081_1976_);
v___f_1990_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1990_, 0, v_inst_1974_);
lean_closure_set(v___f_1990_, 1, v_inst_1975_);
v___x_1991_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___f_1992_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1992_, 0, v___x_1991_);
lean_closure_set(v___f_1992_, 1, v___f_1990_);
v_sz_1993_ = lean_array_size(v_buckets_1979_);
v___x_1994_ = ((size_t)0ULL);
v___x_1995_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1991_, v_buckets_1979_, v___f_1992_, v_sz_1993_, v___x_1994_, v_m_u2082_1977_);
return v___x_1995_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instUnionOfBEqOfHashable___redArg(lean_object* v_inst_1996_, lean_object* v_inst_1997_){
_start:
{
lean_object* v___x_1998_; 
v___x_1998_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_union), 6, 4);
lean_closure_set(v___x_1998_, 0, lean_box(0));
lean_closure_set(v___x_1998_, 1, lean_box(0));
lean_closure_set(v___x_1998_, 2, v_inst_1996_);
lean_closure_set(v___x_1998_, 3, v_inst_1997_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instUnionOfBEqOfHashable(lean_object* v_00_u03b1_1999_, lean_object* v_00_u03b2_2000_, lean_object* v_inst_2001_, lean_object* v_inst_2002_){
_start:
{
lean_object* v___x_2003_; 
v___x_2003_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_union), 6, 4);
lean_closure_set(v___x_2003_, 0, lean_box(0));
lean_closure_set(v___x_2003_, 1, lean_box(0));
lean_closure_set(v___x_2003_, 2, v_inst_2001_);
lean_closure_set(v___x_2003_, 3, v_inst_2002_);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_inter___redArg(lean_object* v_inst_2004_, lean_object* v_inst_2005_, lean_object* v_m_u2081_2006_, lean_object* v_m_u2082_2007_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_inter(lean_object* v_00_u03b1_2016_, lean_object* v_00_u03b2_2017_, lean_object* v_inst_2018_, lean_object* v_inst_2019_, lean_object* v_m_u2081_2020_, lean_object* v_m_u2082_2021_){
_start:
{
lean_object* v_buckets_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; uint8_t v___x_2025_; 
v_buckets_2022_ = lean_ctor_get(v_m_u2081_2020_, 1);
v___x_2023_ = lean_unsigned_to_nat(0u);
v___x_2024_ = lean_array_get_size(v_buckets_2022_);
v___x_2025_ = lean_nat_dec_lt(v___x_2023_, v___x_2024_);
if (v___x_2025_ == 0)
{
lean_dec_ref(v_m_u2081_2020_);
lean_dec_ref(v_inst_2019_);
lean_dec_ref(v_inst_2018_);
return v_m_u2082_2021_;
}
else
{
lean_object* v_buckets_2026_; lean_object* v___x_2027_; uint8_t v___x_2028_; 
v_buckets_2026_ = lean_ctor_get(v_m_u2082_2021_, 1);
v___x_2027_ = lean_array_get_size(v_buckets_2026_);
v___x_2028_ = lean_nat_dec_lt(v___x_2023_, v___x_2027_);
if (v___x_2028_ == 0)
{
lean_dec_ref(v_m_u2082_2021_);
lean_dec_ref(v_inst_2019_);
lean_dec_ref(v_inst_2018_);
return v_m_u2081_2020_;
}
else
{
lean_object* v___x_2029_; 
v___x_2029_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_2018_, v_inst_2019_, v_m_u2081_2020_, v_m_u2082_2021_);
return v___x_2029_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInterOfBEqOfHashable___redArg(lean_object* v_inst_2030_, lean_object* v_inst_2031_){
_start:
{
lean_object* v___x_2032_; 
v___x_2032_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_inter), 6, 4);
lean_closure_set(v___x_2032_, 0, lean_box(0));
lean_closure_set(v___x_2032_, 1, lean_box(0));
lean_closure_set(v___x_2032_, 2, v_inst_2030_);
lean_closure_set(v___x_2032_, 3, v_inst_2031_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInterOfBEqOfHashable(lean_object* v_00_u03b1_2033_, lean_object* v_00_u03b2_2034_, lean_object* v_inst_2035_, lean_object* v_inst_2036_){
_start:
{
lean_object* v___x_2037_; 
v___x_2037_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_inter), 6, 4);
lean_closure_set(v___x_2037_, 0, lean_box(0));
lean_closure_set(v___x_2037_, 1, lean_box(0));
lean_closure_set(v___x_2037_, 2, v_inst_2035_);
lean_closure_set(v___x_2037_, 3, v_inst_2036_);
return v___x_2037_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_beq___redArg(lean_object* v_inst_2038_, lean_object* v_inst_2039_, lean_object* v_inst_2040_, lean_object* v_m_u2081_2041_, lean_object* v_m_u2082_2042_){
_start:
{
lean_object* v_buckets_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; uint8_t v___x_2046_; 
v_buckets_2043_ = lean_ctor_get(v_m_u2081_2041_, 1);
v___x_2044_ = lean_unsigned_to_nat(0u);
v___x_2045_ = lean_array_get_size(v_buckets_2043_);
v___x_2046_ = lean_nat_dec_lt(v___x_2044_, v___x_2045_);
if (v___x_2046_ == 0)
{
lean_dec_ref(v_m_u2082_2042_);
lean_dec_ref(v_m_u2081_2041_);
lean_dec_ref(v_inst_2040_);
lean_dec_ref(v_inst_2039_);
lean_dec_ref(v_inst_2038_);
return v___x_2046_;
}
else
{
lean_object* v_buckets_2047_; lean_object* v___x_2048_; uint8_t v___x_2049_; 
v_buckets_2047_ = lean_ctor_get(v_m_u2082_2042_, 1);
v___x_2048_ = lean_array_get_size(v_buckets_2047_);
v___x_2049_ = lean_nat_dec_lt(v___x_2044_, v___x_2048_);
if (v___x_2049_ == 0)
{
lean_dec_ref(v_m_u2082_2042_);
lean_dec_ref(v_m_u2081_2041_);
lean_dec_ref(v_inst_2040_);
lean_dec_ref(v_inst_2039_);
lean_dec_ref(v_inst_2038_);
return v___x_2049_;
}
else
{
uint8_t v___x_2050_; 
v___x_2050_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(v_inst_2038_, v_inst_2039_, v_inst_2040_, v_m_u2081_2041_, v_m_u2082_2042_);
return v___x_2050_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_beq___redArg___boxed(lean_object* v_inst_2051_, lean_object* v_inst_2052_, lean_object* v_inst_2053_, lean_object* v_m_u2081_2054_, lean_object* v_m_u2082_2055_){
_start:
{
uint8_t v_res_2056_; lean_object* v_r_2057_; 
v_res_2056_ = l_Std_DHashMap_Raw_beq___redArg(v_inst_2051_, v_inst_2052_, v_inst_2053_, v_m_u2081_2054_, v_m_u2082_2055_);
v_r_2057_ = lean_box(v_res_2056_);
return v_r_2057_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_beq(lean_object* v_00_u03b1_2058_, lean_object* v_00_u03b2_2059_, lean_object* v_inst_2060_, lean_object* v_inst_2061_, lean_object* v_inst_2062_, lean_object* v_inst_2063_, lean_object* v_m_u2081_2064_, lean_object* v_m_u2082_2065_){
_start:
{
uint8_t v___x_2066_; 
v___x_2066_ = l_Std_DHashMap_Raw_beq___redArg(v_inst_2060_, v_inst_2061_, v_inst_2063_, v_m_u2081_2064_, v_m_u2082_2065_);
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_beq___boxed(lean_object* v_00_u03b1_2067_, lean_object* v_00_u03b2_2068_, lean_object* v_inst_2069_, lean_object* v_inst_2070_, lean_object* v_inst_2071_, lean_object* v_inst_2072_, lean_object* v_m_u2081_2073_, lean_object* v_m_u2082_2074_){
_start:
{
uint8_t v_res_2075_; lean_object* v_r_2076_; 
v_res_2075_ = l_Std_DHashMap_Raw_beq(v_00_u03b1_2067_, v_00_u03b2_2068_, v_inst_2069_, v_inst_2070_, v_inst_2071_, v_inst_2072_, v_m_u2081_2073_, v_m_u2082_2074_);
v_r_2076_ = lean_box(v_res_2075_);
return v_r_2076_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instBEqOfHashableOfLawfulBEq___redArg(lean_object* v_inst_2077_, lean_object* v_inst_2078_, lean_object* v_inst_2079_){
_start:
{
lean_object* v___x_2080_; 
v___x_2080_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_beq___boxed), 8, 6);
lean_closure_set(v___x_2080_, 0, lean_box(0));
lean_closure_set(v___x_2080_, 1, lean_box(0));
lean_closure_set(v___x_2080_, 2, v_inst_2077_);
lean_closure_set(v___x_2080_, 3, v_inst_2078_);
lean_closure_set(v___x_2080_, 4, lean_box(0));
lean_closure_set(v___x_2080_, 5, v_inst_2079_);
return v___x_2080_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instBEqOfHashableOfLawfulBEq(lean_object* v_00_u03b1_2081_, lean_object* v_00_u03b2_2082_, lean_object* v_inst_2083_, lean_object* v_inst_2084_, lean_object* v_inst_2085_, lean_object* v_inst_2086_){
_start:
{
lean_object* v___x_2087_; 
v___x_2087_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_beq___boxed), 8, 6);
lean_closure_set(v___x_2087_, 0, lean_box(0));
lean_closure_set(v___x_2087_, 1, lean_box(0));
lean_closure_set(v___x_2087_, 2, v_inst_2083_);
lean_closure_set(v___x_2087_, 3, v_inst_2084_);
lean_closure_set(v___x_2087_, 4, lean_box(0));
lean_closure_set(v___x_2087_, 5, v_inst_2086_);
return v___x_2087_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_Const_beq___redArg(lean_object* v_inst_2088_, lean_object* v_inst_2089_, lean_object* v_inst_2090_, lean_object* v_m_u2081_2091_, lean_object* v_m_u2082_2092_){
_start:
{
lean_object* v_buckets_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; uint8_t v___x_2096_; 
v_buckets_2093_ = lean_ctor_get(v_m_u2081_2091_, 1);
v___x_2094_ = lean_unsigned_to_nat(0u);
v___x_2095_ = lean_array_get_size(v_buckets_2093_);
v___x_2096_ = lean_nat_dec_lt(v___x_2094_, v___x_2095_);
if (v___x_2096_ == 0)
{
lean_dec_ref(v_m_u2082_2092_);
lean_dec_ref(v_m_u2081_2091_);
lean_dec_ref(v_inst_2090_);
lean_dec_ref(v_inst_2089_);
lean_dec_ref(v_inst_2088_);
return v___x_2096_;
}
else
{
lean_object* v_buckets_2097_; lean_object* v___x_2098_; uint8_t v___x_2099_; 
v_buckets_2097_ = lean_ctor_get(v_m_u2082_2092_, 1);
v___x_2098_ = lean_array_get_size(v_buckets_2097_);
v___x_2099_ = lean_nat_dec_lt(v___x_2094_, v___x_2098_);
if (v___x_2099_ == 0)
{
lean_dec_ref(v_m_u2082_2092_);
lean_dec_ref(v_m_u2081_2091_);
lean_dec_ref(v_inst_2090_);
lean_dec_ref(v_inst_2089_);
lean_dec_ref(v_inst_2088_);
return v___x_2099_;
}
else
{
uint8_t v___x_2100_; 
v___x_2100_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_inst_2088_, v_inst_2089_, v_inst_2090_, v_m_u2081_2091_, v_m_u2082_2092_);
return v___x_2100_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_beq___redArg___boxed(lean_object* v_inst_2101_, lean_object* v_inst_2102_, lean_object* v_inst_2103_, lean_object* v_m_u2081_2104_, lean_object* v_m_u2082_2105_){
_start:
{
uint8_t v_res_2106_; lean_object* v_r_2107_; 
v_res_2106_ = l_Std_DHashMap_Raw_Const_beq___redArg(v_inst_2101_, v_inst_2102_, v_inst_2103_, v_m_u2081_2104_, v_m_u2082_2105_);
v_r_2107_ = lean_box(v_res_2106_);
return v_r_2107_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_Const_beq(lean_object* v_00_u03b1_2108_, lean_object* v_00_u03b2_2109_, lean_object* v_inst_2110_, lean_object* v_inst_2111_, lean_object* v_inst_2112_, lean_object* v_m_u2081_2113_, lean_object* v_m_u2082_2114_){
_start:
{
uint8_t v___x_2115_; 
v___x_2115_ = l_Std_DHashMap_Raw_Const_beq___redArg(v_inst_2110_, v_inst_2111_, v_inst_2112_, v_m_u2081_2113_, v_m_u2082_2114_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_beq___boxed(lean_object* v_00_u03b1_2116_, lean_object* v_00_u03b2_2117_, lean_object* v_inst_2118_, lean_object* v_inst_2119_, lean_object* v_inst_2120_, lean_object* v_m_u2081_2121_, lean_object* v_m_u2082_2122_){
_start:
{
uint8_t v_res_2123_; lean_object* v_r_2124_; 
v_res_2123_ = l_Std_DHashMap_Raw_Const_beq(v_00_u03b1_2116_, v_00_u03b2_2117_, v_inst_2118_, v_inst_2119_, v_inst_2120_, v_m_u2081_2121_, v_m_u2082_2122_);
v_r_2124_ = lean_box(v_res_2123_);
return v_r_2124_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_diff___redArg___lam__0(lean_object* v_inst_2125_, lean_object* v_inst_2126_, lean_object* v_m_u2082_2127_, uint8_t v___x_2128_, lean_object* v_k_2129_, lean_object* v_x_2130_){
_start:
{
uint8_t v___x_2131_; 
v___x_2131_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_2125_, v_inst_2126_, v_m_u2082_2127_, v_k_2129_);
if (v___x_2131_ == 0)
{
return v___x_2128_;
}
else
{
uint8_t v___x_2132_; 
v___x_2132_ = 0;
return v___x_2132_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_diff___redArg___lam__0___boxed(lean_object* v_inst_2133_, lean_object* v_inst_2134_, lean_object* v_m_u2082_2135_, lean_object* v___x_2136_, lean_object* v_k_2137_, lean_object* v_x_2138_){
_start:
{
uint8_t v___x_92__boxed_2139_; uint8_t v_res_2140_; lean_object* v_r_2141_; 
v___x_92__boxed_2139_ = lean_unbox(v___x_2136_);
v_res_2140_ = l_Std_DHashMap_Raw_diff___redArg___lam__0(v_inst_2133_, v_inst_2134_, v_m_u2082_2135_, v___x_92__boxed_2139_, v_k_2137_, v_x_2138_);
lean_dec(v_x_2138_);
lean_dec_ref(v_m_u2082_2135_);
v_r_2141_ = lean_box(v_res_2140_);
return v_r_2141_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_diff___redArg(lean_object* v_inst_2142_, lean_object* v_inst_2143_, lean_object* v_m_u2081_2144_, lean_object* v_m_u2082_2145_){
_start:
{
lean_object* v_size_2146_; lean_object* v_buckets_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; uint8_t v___x_2150_; 
v_size_2146_ = lean_ctor_get(v_m_u2081_2144_, 0);
v_buckets_2147_ = lean_ctor_get(v_m_u2081_2144_, 1);
v___x_2148_ = lean_unsigned_to_nat(0u);
v___x_2149_ = lean_array_get_size(v_buckets_2147_);
v___x_2150_ = lean_nat_dec_lt(v___x_2148_, v___x_2149_);
if (v___x_2150_ == 0)
{
lean_dec_ref(v_m_u2081_2144_);
lean_dec_ref(v_inst_2143_);
lean_dec_ref(v_inst_2142_);
return v_m_u2082_2145_;
}
else
{
lean_object* v_size_2151_; lean_object* v_buckets_2152_; lean_object* v___x_2153_; uint8_t v___x_2154_; 
v_size_2151_ = lean_ctor_get(v_m_u2082_2145_, 0);
v_buckets_2152_ = lean_ctor_get(v_m_u2082_2145_, 1);
v___x_2153_ = lean_array_get_size(v_buckets_2152_);
v___x_2154_ = lean_nat_dec_lt(v___x_2148_, v___x_2153_);
if (v___x_2154_ == 0)
{
lean_dec_ref(v_m_u2082_2145_);
lean_dec_ref(v_inst_2143_);
lean_dec_ref(v_inst_2142_);
return v_m_u2081_2144_;
}
else
{
uint8_t v___x_2155_; 
v___x_2155_ = lean_nat_dec_le(v_size_2146_, v_size_2151_);
if (v___x_2155_ == 0)
{
lean_object* v___f_2156_; lean_object* v___x_2157_; 
v___f_2156_ = ((lean_object*)(l_Std_DHashMap_Raw_union___redArg___closed__0));
v___x_2157_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_2156_, v_inst_2142_, v_inst_2143_, v_m_u2081_2144_, v_m_u2082_2145_);
return v___x_2157_;
}
else
{
lean_object* v___x_2158_; lean_object* v___f_2159_; lean_object* v___x_2160_; 
v___x_2158_ = lean_box(v___x_2155_);
v___f_2159_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_2159_, 0, v_inst_2142_);
lean_closure_set(v___f_2159_, 1, v_inst_2143_);
lean_closure_set(v___f_2159_, 2, v_m_u2082_2145_);
lean_closure_set(v___f_2159_, 3, v___x_2158_);
v___x_2160_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_2159_, v_m_u2081_2144_);
return v___x_2160_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_diff(lean_object* v_00_u03b1_2161_, lean_object* v_00_u03b2_2162_, lean_object* v_inst_2163_, lean_object* v_inst_2164_, lean_object* v_m_u2081_2165_, lean_object* v_m_u2082_2166_){
_start:
{
lean_object* v_size_2167_; lean_object* v_buckets_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; uint8_t v___x_2171_; 
v_size_2167_ = lean_ctor_get(v_m_u2081_2165_, 0);
v_buckets_2168_ = lean_ctor_get(v_m_u2081_2165_, 1);
v___x_2169_ = lean_unsigned_to_nat(0u);
v___x_2170_ = lean_array_get_size(v_buckets_2168_);
v___x_2171_ = lean_nat_dec_lt(v___x_2169_, v___x_2170_);
if (v___x_2171_ == 0)
{
lean_dec_ref(v_m_u2081_2165_);
lean_dec_ref(v_inst_2164_);
lean_dec_ref(v_inst_2163_);
return v_m_u2082_2166_;
}
else
{
lean_object* v_size_2172_; lean_object* v_buckets_2173_; lean_object* v___x_2174_; uint8_t v___x_2175_; 
v_size_2172_ = lean_ctor_get(v_m_u2082_2166_, 0);
v_buckets_2173_ = lean_ctor_get(v_m_u2082_2166_, 1);
v___x_2174_ = lean_array_get_size(v_buckets_2173_);
v___x_2175_ = lean_nat_dec_lt(v___x_2169_, v___x_2174_);
if (v___x_2175_ == 0)
{
lean_dec_ref(v_m_u2082_2166_);
lean_dec_ref(v_inst_2164_);
lean_dec_ref(v_inst_2163_);
return v_m_u2081_2165_;
}
else
{
uint8_t v___x_2176_; 
v___x_2176_ = lean_nat_dec_le(v_size_2167_, v_size_2172_);
if (v___x_2176_ == 0)
{
lean_object* v___f_2177_; lean_object* v___x_2178_; 
v___f_2177_ = ((lean_object*)(l_Std_DHashMap_Raw_union___redArg___closed__0));
v___x_2178_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_2177_, v_inst_2163_, v_inst_2164_, v_m_u2081_2165_, v_m_u2082_2166_);
return v___x_2178_;
}
else
{
lean_object* v___x_2179_; lean_object* v___f_2180_; lean_object* v___x_2181_; 
v___x_2179_ = lean_box(v___x_2176_);
v___f_2180_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_2180_, 0, v_inst_2163_);
lean_closure_set(v___f_2180_, 1, v_inst_2164_);
lean_closure_set(v___f_2180_, 2, v_m_u2082_2166_);
lean_closure_set(v___f_2180_, 3, v___x_2179_);
v___x_2181_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_2180_, v_m_u2081_2165_);
return v___x_2181_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instSDiffOfBEqOfHashable___redArg(lean_object* v_inst_2182_, lean_object* v_inst_2183_){
_start:
{
lean_object* v___x_2184_; 
v___x_2184_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_diff), 6, 4);
lean_closure_set(v___x_2184_, 0, lean_box(0));
lean_closure_set(v___x_2184_, 1, lean_box(0));
lean_closure_set(v___x_2184_, 2, v_inst_2182_);
lean_closure_set(v___x_2184_, 3, v_inst_2183_);
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instSDiffOfBEqOfHashable(lean_object* v_00_u03b1_2185_, lean_object* v_00_u03b2_2186_, lean_object* v_inst_2187_, lean_object* v_inst_2188_){
_start:
{
lean_object* v___x_2189_; 
v___x_2189_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_diff), 6, 4);
lean_closure_set(v___x_2189_, 0, lean_box(0));
lean_closure_set(v___x_2189_, 1, lean_box(0));
lean_closure_set(v___x_2189_, 2, v_inst_2187_);
lean_closure_set(v___x_2189_, 3, v_inst_2188_);
return v___x_2189_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_values___redArg___lam__0(lean_object* v_a_2190_, lean_object* v_b_2191_, lean_object* v_d_2192_){
_start:
{
lean_object* v___x_2193_; 
v___x_2193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2193_, 0, v_b_2191_);
lean_ctor_set(v___x_2193_, 1, v_d_2192_);
return v___x_2193_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_values___redArg___lam__0___boxed(lean_object* v_a_2194_, lean_object* v_b_2195_, lean_object* v_d_2196_){
_start:
{
lean_object* v_res_2197_; 
v_res_2197_ = l_Std_DHashMap_Raw_values___redArg___lam__0(v_a_2194_, v_b_2195_, v_d_2196_);
lean_dec(v_a_2194_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_values___redArg___lam__1(lean_object* v___x_2198_, lean_object* v___f_2199_, lean_object* v_l_2200_, lean_object* v_acc_2201_){
_start:
{
lean_object* v___x_2202_; 
v___x_2202_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_2198_, v___f_2199_, v_acc_2201_, v_l_2200_);
return v___x_2202_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_values___redArg(lean_object* v_m_2207_){
_start:
{
lean_object* v___x_2208_; lean_object* v_buckets_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; uint8_t v___x_2213_; 
v___x_2208_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_2209_ = lean_ctor_get(v_m_2207_, 1);
lean_inc_ref(v_buckets_2209_);
lean_dec_ref(v_m_2207_);
v___x_2210_ = lean_box(0);
v___x_2211_ = lean_array_get_size(v_buckets_2209_);
v___x_2212_ = lean_unsigned_to_nat(0u);
v___x_2213_ = lean_nat_dec_lt(v___x_2212_, v___x_2211_);
if (v___x_2213_ == 0)
{
lean_dec_ref(v_buckets_2209_);
return v___x_2210_;
}
else
{
lean_object* v___f_2214_; size_t v___x_2215_; size_t v___x_2216_; lean_object* v___x_2217_; 
v___f_2214_ = ((lean_object*)(l_Std_DHashMap_Raw_values___redArg___closed__1));
v___x_2215_ = lean_usize_of_nat(v___x_2211_);
v___x_2216_ = ((size_t)0ULL);
v___x_2217_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2208_, v___f_2214_, v_buckets_2209_, v___x_2215_, v___x_2216_, v___x_2210_);
return v___x_2217_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_values(lean_object* v_00_u03b1_2218_, lean_object* v_00_u03b2_2219_, lean_object* v_m_2220_){
_start:
{
lean_object* v___x_2221_; lean_object* v_buckets_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; uint8_t v___x_2226_; 
v___x_2221_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_2222_ = lean_ctor_get(v_m_2220_, 1);
lean_inc_ref(v_buckets_2222_);
lean_dec_ref(v_m_2220_);
v___x_2223_ = lean_box(0);
v___x_2224_ = lean_array_get_size(v_buckets_2222_);
v___x_2225_ = lean_unsigned_to_nat(0u);
v___x_2226_ = lean_nat_dec_lt(v___x_2225_, v___x_2224_);
if (v___x_2226_ == 0)
{
lean_dec_ref(v_buckets_2222_);
return v___x_2223_;
}
else
{
lean_object* v___f_2227_; size_t v___x_2228_; size_t v___x_2229_; lean_object* v___x_2230_; 
v___f_2227_ = ((lean_object*)(l_Std_DHashMap_Raw_values___redArg___closed__1));
v___x_2228_ = lean_usize_of_nat(v___x_2224_);
v___x_2229_ = ((size_t)0ULL);
v___x_2230_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2221_, v___f_2227_, v_buckets_2222_, v___x_2228_, v___x_2229_, v___x_2223_);
return v___x_2230_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_valuesArray___redArg___lam__0(lean_object* v_x1_2231_, lean_object* v_x2_2232_, lean_object* v_x3_2233_){
_start:
{
lean_object* v___x_2234_; 
v___x_2234_ = lean_array_push(v_x1_2231_, v_x3_2233_);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_valuesArray___redArg___lam__0___boxed(lean_object* v_x1_2235_, lean_object* v_x2_2236_, lean_object* v_x3_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l_Std_DHashMap_Raw_valuesArray___redArg___lam__0(v_x1_2235_, v_x2_2236_, v_x3_2237_);
lean_dec(v_x2_2236_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_valuesArray___redArg(lean_object* v_m_2243_){
_start:
{
lean_object* v_size_2244_; lean_object* v_buckets_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; uint8_t v___x_2250_; 
v_size_2244_ = lean_ctor_get(v_m_2243_, 0);
lean_inc(v_size_2244_);
v_buckets_2245_ = lean_ctor_get(v_m_2243_, 1);
lean_inc_ref(v_buckets_2245_);
lean_dec_ref(v_m_2243_);
v___x_2246_ = lean_mk_empty_array_with_capacity(v_size_2244_);
lean_dec(v_size_2244_);
v___x_2247_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_2248_ = lean_unsigned_to_nat(0u);
v___x_2249_ = lean_array_get_size(v_buckets_2245_);
v___x_2250_ = lean_nat_dec_lt(v___x_2248_, v___x_2249_);
if (v___x_2250_ == 0)
{
lean_dec_ref(v_buckets_2245_);
return v___x_2246_;
}
else
{
lean_object* v___f_2251_; uint8_t v___x_2252_; 
v___f_2251_ = ((lean_object*)(l_Std_DHashMap_Raw_valuesArray___redArg___closed__1));
v___x_2252_ = lean_nat_dec_le(v___x_2249_, v___x_2249_);
if (v___x_2252_ == 0)
{
if (v___x_2250_ == 0)
{
lean_dec_ref(v_buckets_2245_);
return v___x_2246_;
}
else
{
size_t v___x_2253_; size_t v___x_2254_; lean_object* v___x_2255_; 
v___x_2253_ = ((size_t)0ULL);
v___x_2254_ = lean_usize_of_nat(v___x_2249_);
v___x_2255_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2247_, v___f_2251_, v_buckets_2245_, v___x_2253_, v___x_2254_, v___x_2246_);
return v___x_2255_;
}
}
else
{
size_t v___x_2256_; size_t v___x_2257_; lean_object* v___x_2258_; 
v___x_2256_ = ((size_t)0ULL);
v___x_2257_ = lean_usize_of_nat(v___x_2249_);
v___x_2258_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2247_, v___f_2251_, v_buckets_2245_, v___x_2256_, v___x_2257_, v___x_2246_);
return v___x_2258_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_valuesArray(lean_object* v_00_u03b1_2259_, lean_object* v_00_u03b2_2260_, lean_object* v_m_2261_){
_start:
{
lean_object* v_size_2262_; lean_object* v_buckets_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; uint8_t v___x_2268_; 
v_size_2262_ = lean_ctor_get(v_m_2261_, 0);
lean_inc(v_size_2262_);
v_buckets_2263_ = lean_ctor_get(v_m_2261_, 1);
lean_inc_ref(v_buckets_2263_);
lean_dec_ref(v_m_2261_);
v___x_2264_ = lean_mk_empty_array_with_capacity(v_size_2262_);
lean_dec(v_size_2262_);
v___x_2265_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_2266_ = lean_unsigned_to_nat(0u);
v___x_2267_ = lean_array_get_size(v_buckets_2263_);
v___x_2268_ = lean_nat_dec_lt(v___x_2266_, v___x_2267_);
if (v___x_2268_ == 0)
{
lean_dec_ref(v_buckets_2263_);
return v___x_2264_;
}
else
{
lean_object* v___f_2269_; uint8_t v___x_2270_; 
v___f_2269_ = ((lean_object*)(l_Std_DHashMap_Raw_valuesArray___redArg___closed__1));
v___x_2270_ = lean_nat_dec_le(v___x_2267_, v___x_2267_);
if (v___x_2270_ == 0)
{
if (v___x_2268_ == 0)
{
lean_dec_ref(v_buckets_2263_);
return v___x_2264_;
}
else
{
size_t v___x_2271_; size_t v___x_2272_; lean_object* v___x_2273_; 
v___x_2271_ = ((size_t)0ULL);
v___x_2272_ = lean_usize_of_nat(v___x_2267_);
v___x_2273_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2265_, v___f_2269_, v_buckets_2263_, v___x_2271_, v___x_2272_, v___x_2264_);
return v___x_2273_;
}
}
else
{
size_t v___x_2274_; size_t v___x_2275_; lean_object* v___x_2276_; 
v___x_2274_ = ((size_t)0ULL);
v___x_2275_ = lean_usize_of_nat(v___x_2267_);
v___x_2276_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2265_, v___f_2269_, v_buckets_2263_, v___x_2274_, v___x_2275_, v___x_2264_);
return v___x_2276_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insertMany___redArg(lean_object* v_inst_2277_, lean_object* v_inst_2278_, lean_object* v_inst_2279_, lean_object* v_m_2280_, lean_object* v_l_2281_){
_start:
{
lean_object* v_buckets_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; uint8_t v___x_2285_; 
v_buckets_2282_ = lean_ctor_get(v_m_2280_, 1);
v___x_2283_ = lean_unsigned_to_nat(0u);
v___x_2284_ = lean_array_get_size(v_buckets_2282_);
v___x_2285_ = lean_nat_dec_lt(v___x_2283_, v___x_2284_);
if (v___x_2285_ == 0)
{
lean_dec(v_l_2281_);
lean_dec(v_inst_2279_);
lean_dec_ref(v_inst_2278_);
lean_dec_ref(v_inst_2277_);
return v_m_2280_;
}
else
{
lean_object* v___x_2286_; 
v___x_2286_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v_inst_2279_, v_inst_2277_, v_inst_2278_, v_m_2280_, v_l_2281_);
return v___x_2286_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insertMany(lean_object* v_00_u03b1_2287_, lean_object* v_00_u03b2_2288_, lean_object* v_inst_2289_, lean_object* v_inst_2290_, lean_object* v_00_u03c1_2291_, lean_object* v_inst_2292_, lean_object* v_m_2293_, lean_object* v_l_2294_){
_start:
{
lean_object* v_buckets_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; uint8_t v___x_2298_; 
v_buckets_2295_ = lean_ctor_get(v_m_2293_, 1);
v___x_2296_ = lean_unsigned_to_nat(0u);
v___x_2297_ = lean_array_get_size(v_buckets_2295_);
v___x_2298_ = lean_nat_dec_lt(v___x_2296_, v___x_2297_);
if (v___x_2298_ == 0)
{
lean_dec(v_l_2294_);
lean_dec(v_inst_2292_);
lean_dec_ref(v_inst_2290_);
lean_dec_ref(v_inst_2289_);
return v_m_2293_;
}
else
{
lean_object* v___x_2299_; 
v___x_2299_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v_inst_2292_, v_inst_2289_, v_inst_2290_, v_m_2293_, v_l_2294_);
return v___x_2299_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_eraseManyEntries___redArg(lean_object* v_inst_2300_, lean_object* v_inst_2301_, lean_object* v_inst_2302_, lean_object* v_m_2303_, lean_object* v_l_2304_){
_start:
{
lean_object* v_buckets_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; uint8_t v___x_2308_; 
v_buckets_2305_ = lean_ctor_get(v_m_2303_, 1);
v___x_2306_ = lean_unsigned_to_nat(0u);
v___x_2307_ = lean_array_get_size(v_buckets_2305_);
v___x_2308_ = lean_nat_dec_lt(v___x_2306_, v___x_2307_);
if (v___x_2308_ == 0)
{
lean_dec(v_l_2304_);
lean_dec(v_inst_2302_);
lean_dec_ref(v_inst_2301_);
lean_dec_ref(v_inst_2300_);
return v_m_2303_;
}
else
{
lean_object* v___x_2309_; 
v___x_2309_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v_inst_2302_, v_inst_2300_, v_inst_2301_, v_m_2303_, v_l_2304_);
return v___x_2309_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_eraseManyEntries(lean_object* v_00_u03b1_2310_, lean_object* v_00_u03b2_2311_, lean_object* v_inst_2312_, lean_object* v_inst_2313_, lean_object* v_00_u03c1_2314_, lean_object* v_inst_2315_, lean_object* v_m_2316_, lean_object* v_l_2317_){
_start:
{
lean_object* v_buckets_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; uint8_t v___x_2321_; 
v_buckets_2318_ = lean_ctor_get(v_m_2316_, 1);
v___x_2319_ = lean_unsigned_to_nat(0u);
v___x_2320_ = lean_array_get_size(v_buckets_2318_);
v___x_2321_ = lean_nat_dec_lt(v___x_2319_, v___x_2320_);
if (v___x_2321_ == 0)
{
lean_dec(v_l_2317_);
lean_dec(v_inst_2315_);
lean_dec_ref(v_inst_2313_);
lean_dec_ref(v_inst_2312_);
return v_m_2316_;
}
else
{
lean_object* v___x_2322_; 
v___x_2322_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v_inst_2315_, v_inst_2312_, v_inst_2313_, v_m_2316_, v_l_2317_);
return v___x_2322_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_insertMany___redArg(lean_object* v_inst_2323_, lean_object* v_inst_2324_, lean_object* v_inst_2325_, lean_object* v_m_2326_, lean_object* v_l_2327_){
_start:
{
lean_object* v_buckets_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; uint8_t v___x_2331_; 
v_buckets_2328_ = lean_ctor_get(v_m_2326_, 1);
v___x_2329_ = lean_unsigned_to_nat(0u);
v___x_2330_ = lean_array_get_size(v_buckets_2328_);
v___x_2331_ = lean_nat_dec_lt(v___x_2329_, v___x_2330_);
if (v___x_2331_ == 0)
{
lean_dec(v_l_2327_);
lean_dec(v_inst_2325_);
lean_dec_ref(v_inst_2324_);
lean_dec_ref(v_inst_2323_);
return v_m_2326_;
}
else
{
lean_object* v___x_2332_; 
v___x_2332_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v_inst_2325_, v_inst_2323_, v_inst_2324_, v_m_2326_, v_l_2327_);
return v___x_2332_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_insertMany(lean_object* v_00_u03b1_2333_, lean_object* v_00_u03b2_2334_, lean_object* v_inst_2335_, lean_object* v_inst_2336_, lean_object* v_00_u03c1_2337_, lean_object* v_inst_2338_, lean_object* v_m_2339_, lean_object* v_l_2340_){
_start:
{
lean_object* v_buckets_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; uint8_t v___x_2344_; 
v_buckets_2341_ = lean_ctor_get(v_m_2339_, 1);
v___x_2342_ = lean_unsigned_to_nat(0u);
v___x_2343_ = lean_array_get_size(v_buckets_2341_);
v___x_2344_ = lean_nat_dec_lt(v___x_2342_, v___x_2343_);
if (v___x_2344_ == 0)
{
lean_dec(v_l_2340_);
lean_dec(v_inst_2338_);
lean_dec_ref(v_inst_2336_);
lean_dec_ref(v_inst_2335_);
return v_m_2339_;
}
else
{
lean_object* v___x_2345_; 
v___x_2345_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v_inst_2338_, v_inst_2335_, v_inst_2336_, v_m_2339_, v_l_2340_);
return v___x_2345_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_insertManyIfNewUnit___redArg(lean_object* v_inst_2346_, lean_object* v_inst_2347_, lean_object* v_inst_2348_, lean_object* v_m_2349_, lean_object* v_l_2350_){
_start:
{
lean_object* v_buckets_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; uint8_t v___x_2354_; 
v_buckets_2351_ = lean_ctor_get(v_m_2349_, 1);
v___x_2352_ = lean_unsigned_to_nat(0u);
v___x_2353_ = lean_array_get_size(v_buckets_2351_);
v___x_2354_ = lean_nat_dec_lt(v___x_2352_, v___x_2353_);
if (v___x_2354_ == 0)
{
lean_dec(v_l_2350_);
lean_dec(v_inst_2348_);
lean_dec_ref(v_inst_2347_);
lean_dec_ref(v_inst_2346_);
return v_m_2349_;
}
else
{
lean_object* v___x_2355_; 
v___x_2355_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_2348_, v_inst_2346_, v_inst_2347_, v_m_2349_, v_l_2350_);
return v___x_2355_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_insertManyIfNewUnit(lean_object* v_00_u03b1_2356_, lean_object* v_inst_2357_, lean_object* v_inst_2358_, lean_object* v_00_u03c1_2359_, lean_object* v_inst_2360_, lean_object* v_m_2361_, lean_object* v_l_2362_){
_start:
{
lean_object* v_buckets_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; uint8_t v___x_2366_; 
v_buckets_2363_ = lean_ctor_get(v_m_2361_, 1);
v___x_2364_ = lean_unsigned_to_nat(0u);
v___x_2365_ = lean_array_get_size(v_buckets_2363_);
v___x_2366_ = lean_nat_dec_lt(v___x_2364_, v___x_2365_);
if (v___x_2366_ == 0)
{
lean_dec(v_l_2362_);
lean_dec(v_inst_2360_);
lean_dec_ref(v_inst_2358_);
lean_dec_ref(v_inst_2357_);
return v_m_2361_;
}
else
{
lean_object* v___x_2367_; 
v___x_2367_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_2360_, v_inst_2357_, v_inst_2358_, v_m_2361_, v_l_2362_);
return v___x_2367_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_unitOfArray___redArg(lean_object* v_inst_2372_, lean_object* v_inst_2373_, lean_object* v_l_2374_){
_start:
{
lean_object* v___x_2375_; uint8_t v___x_2376_; 
v___x_2375_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
v___x_2376_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2376_ == 0)
{
lean_dec_ref(v_l_2374_);
lean_dec_ref(v_inst_2373_);
lean_dec_ref(v_inst_2372_);
return v___x_2375_;
}
else
{
lean_object* v___f_2377_; lean_object* v___x_2378_; 
v___f_2377_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1));
v___x_2378_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2377_, v_inst_2372_, v_inst_2373_, v___x_2375_, v_l_2374_);
return v___x_2378_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_unitOfArray(lean_object* v_00_u03b1_2379_, lean_object* v_inst_2380_, lean_object* v_inst_2381_, lean_object* v_l_2382_){
_start:
{
lean_object* v___x_2383_; uint8_t v___x_2384_; 
v___x_2383_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
v___x_2384_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2384_ == 0)
{
lean_dec_ref(v_l_2382_);
lean_dec_ref(v_inst_2381_);
lean_dec_ref(v_inst_2380_);
return v___x_2383_;
}
else
{
lean_object* v___f_2385_; lean_object* v___x_2386_; 
v___f_2385_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1));
v___x_2386_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2385_, v_inst_2380_, v_inst_2381_, v___x_2383_, v_l_2382_);
return v___x_2386_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_numBuckets___redArg(lean_object* v_m_2387_){
_start:
{
lean_object* v_buckets_2388_; lean_object* v___x_2389_; 
v_buckets_2388_ = lean_ctor_get(v_m_2387_, 1);
v___x_2389_ = lean_array_get_size(v_buckets_2388_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_numBuckets___redArg___boxed(lean_object* v_m_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2390_);
lean_dec_ref(v_m_2390_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_numBuckets(lean_object* v_00_u03b1_2392_, lean_object* v_00_u03b2_2393_, lean_object* v_m_2394_){
_start:
{
lean_object* v___x_2395_; 
v___x_2395_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2394_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_numBuckets___boxed(lean_object* v_00_u03b1_2396_, lean_object* v_00_u03b2_2397_, lean_object* v_m_2398_){
_start:
{
lean_object* v_res_2399_; 
v_res_2399_ = l_Std_DHashMap_Raw_Internal_numBuckets(v_00_u03b1_2396_, v_00_u03b2_2397_, v_m_2398_);
lean_dec_ref(v_m_2398_);
return v_res_2399_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toList___redArg___lam__0(lean_object* v_a_2400_, lean_object* v_b_2401_, lean_object* v_d_2402_){
_start:
{
lean_object* v___x_2403_; lean_object* v___x_2404_; 
v___x_2403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2403_, 0, v_a_2400_);
lean_ctor_set(v___x_2403_, 1, v_b_2401_);
v___x_2404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2403_);
lean_ctor_set(v___x_2404_, 1, v_d_2402_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toList___redArg___lam__1(lean_object* v___x_2405_, lean_object* v___f_2406_, lean_object* v_l_2407_, lean_object* v_acc_2408_){
_start:
{
lean_object* v___x_2409_; 
v___x_2409_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_2405_, v___f_2406_, v_acc_2408_, v_l_2407_);
return v___x_2409_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toList___redArg(lean_object* v_m_2414_){
_start:
{
lean_object* v___x_2415_; lean_object* v_buckets_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; uint8_t v___x_2420_; 
v___x_2415_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_2416_ = lean_ctor_get(v_m_2414_, 1);
lean_inc_ref(v_buckets_2416_);
lean_dec_ref(v_m_2414_);
v___x_2417_ = lean_box(0);
v___x_2418_ = lean_array_get_size(v_buckets_2416_);
v___x_2419_ = lean_unsigned_to_nat(0u);
v___x_2420_ = lean_nat_dec_lt(v___x_2419_, v___x_2418_);
if (v___x_2420_ == 0)
{
lean_dec_ref(v_buckets_2416_);
return v___x_2417_;
}
else
{
lean_object* v___f_2421_; size_t v___x_2422_; size_t v___x_2423_; lean_object* v___x_2424_; 
v___f_2421_ = ((lean_object*)(l_Std_DHashMap_Raw_toList___redArg___closed__1));
v___x_2422_ = lean_usize_of_nat(v___x_2418_);
v___x_2423_ = ((size_t)0ULL);
v___x_2424_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2415_, v___f_2421_, v_buckets_2416_, v___x_2422_, v___x_2423_, v___x_2417_);
return v___x_2424_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toList(lean_object* v_00_u03b1_2425_, lean_object* v_00_u03b2_2426_, lean_object* v_m_2427_){
_start:
{
lean_object* v___x_2428_; lean_object* v_buckets_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; uint8_t v___x_2433_; 
v___x_2428_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_2429_ = lean_ctor_get(v_m_2427_, 1);
lean_inc_ref(v_buckets_2429_);
lean_dec_ref(v_m_2427_);
v___x_2430_ = lean_box(0);
v___x_2431_ = lean_array_get_size(v_buckets_2429_);
v___x_2432_ = lean_unsigned_to_nat(0u);
v___x_2433_ = lean_nat_dec_lt(v___x_2432_, v___x_2431_);
if (v___x_2433_ == 0)
{
lean_dec_ref(v_buckets_2429_);
return v___x_2430_;
}
else
{
lean_object* v___f_2434_; size_t v___x_2435_; size_t v___x_2436_; lean_object* v___x_2437_; 
v___f_2434_ = ((lean_object*)(l_Std_DHashMap_Raw_toList___redArg___closed__1));
v___x_2435_ = lean_usize_of_nat(v___x_2431_);
v___x_2436_ = ((size_t)0ULL);
v___x_2437_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2428_, v___f_2434_, v_buckets_2429_, v___x_2435_, v___x_2436_, v___x_2430_);
return v___x_2437_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toList___redArg___lam__0(lean_object* v_a_2438_, lean_object* v_b_2439_, lean_object* v_d_2440_){
_start:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2441_, 0, v_a_2438_);
lean_ctor_set(v___x_2441_, 1, v_b_2439_);
v___x_2442_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2441_);
lean_ctor_set(v___x_2442_, 1, v_d_2440_);
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toList___redArg___lam__1(lean_object* v___x_2443_, lean_object* v___f_2444_, lean_object* v_l_2445_, lean_object* v_acc_2446_){
_start:
{
lean_object* v___x_2447_; 
v___x_2447_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_2443_, v___f_2444_, v_acc_2446_, v_l_2445_);
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toList___redArg(lean_object* v_m_2452_){
_start:
{
lean_object* v___x_2453_; lean_object* v_buckets_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; uint8_t v___x_2458_; 
v___x_2453_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_2454_ = lean_ctor_get(v_m_2452_, 1);
lean_inc_ref(v_buckets_2454_);
lean_dec_ref(v_m_2452_);
v___x_2455_ = lean_box(0);
v___x_2456_ = lean_array_get_size(v_buckets_2454_);
v___x_2457_ = lean_unsigned_to_nat(0u);
v___x_2458_ = lean_nat_dec_lt(v___x_2457_, v___x_2456_);
if (v___x_2458_ == 0)
{
lean_dec_ref(v_buckets_2454_);
return v___x_2455_;
}
else
{
lean_object* v___f_2459_; size_t v___x_2460_; size_t v___x_2461_; lean_object* v___x_2462_; 
v___f_2459_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_toList___redArg___closed__1));
v___x_2460_ = lean_usize_of_nat(v___x_2456_);
v___x_2461_ = ((size_t)0ULL);
v___x_2462_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2453_, v___f_2459_, v_buckets_2454_, v___x_2460_, v___x_2461_, v___x_2455_);
return v___x_2462_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toList(lean_object* v_00_u03b1_2463_, lean_object* v_00_u03b2_2464_, lean_object* v_m_2465_){
_start:
{
lean_object* v___x_2466_; lean_object* v_buckets_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; uint8_t v___x_2471_; 
v___x_2466_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_2467_ = lean_ctor_get(v_m_2465_, 1);
lean_inc_ref(v_buckets_2467_);
lean_dec_ref(v_m_2465_);
v___x_2468_ = lean_box(0);
v___x_2469_ = lean_array_get_size(v_buckets_2467_);
v___x_2470_ = lean_unsigned_to_nat(0u);
v___x_2471_ = lean_nat_dec_lt(v___x_2470_, v___x_2469_);
if (v___x_2471_ == 0)
{
lean_dec_ref(v_buckets_2467_);
return v___x_2468_;
}
else
{
lean_object* v___f_2472_; size_t v___x_2473_; size_t v___x_2474_; lean_object* v___x_2475_; 
v___f_2472_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_toList___redArg___closed__1));
v___x_2473_ = lean_usize_of_nat(v___x_2469_);
v___x_2474_ = ((size_t)0ULL);
v___x_2475_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2466_, v___f_2472_, v_buckets_2467_, v___x_2473_, v___x_2474_, v___x_2468_);
return v___x_2475_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instRepr___redArg___lam__2(lean_object* v___x_2479_, lean_object* v___f_2480_, lean_object* v_m_2481_, lean_object* v_prec_2482_){
_start:
{
lean_object* v___x_2483_; lean_object* v_buckets_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2504_; 
v___x_2483_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_2484_ = lean_ctor_get(v_m_2481_, 1);
v_isSharedCheck_2504_ = !lean_is_exclusive(v_m_2481_);
if (v_isSharedCheck_2504_ == 0)
{
lean_object* v_unused_2505_; 
v_unused_2505_ = lean_ctor_get(v_m_2481_, 0);
lean_dec(v_unused_2505_);
v___x_2486_ = v_m_2481_;
v_isShared_2487_ = v_isSharedCheck_2504_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_buckets_2484_);
lean_dec(v_m_2481_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2504_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2488_; lean_object* v___y_2490_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; uint8_t v___x_2499_; 
v___x_2488_ = ((lean_object*)(l_Std_DHashMap_Raw_instRepr___redArg___lam__2___closed__1));
v___x_2496_ = lean_box(0);
v___x_2497_ = lean_array_get_size(v_buckets_2484_);
v___x_2498_ = lean_unsigned_to_nat(0u);
v___x_2499_ = lean_nat_dec_lt(v___x_2498_, v___x_2497_);
if (v___x_2499_ == 0)
{
lean_dec_ref(v_buckets_2484_);
lean_dec_ref(v___f_2480_);
v___y_2490_ = v___x_2496_;
goto v___jp_2489_;
}
else
{
lean_object* v___f_2500_; size_t v___x_2501_; size_t v___x_2502_; lean_object* v___x_2503_; 
v___f_2500_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_toList___redArg___lam__1), 4, 2);
lean_closure_set(v___f_2500_, 0, v___x_2483_);
lean_closure_set(v___f_2500_, 1, v___f_2480_);
v___x_2501_ = lean_usize_of_nat(v___x_2497_);
v___x_2502_ = ((size_t)0ULL);
v___x_2503_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2483_, v___f_2500_, v_buckets_2484_, v___x_2501_, v___x_2502_, v___x_2496_);
v___y_2490_ = v___x_2503_;
goto v___jp_2489_;
}
v___jp_2489_:
{
lean_object* v___x_2491_; lean_object* v___x_2493_; 
v___x_2491_ = l_List_repr___redArg(v___x_2479_, v___y_2490_);
if (v_isShared_2487_ == 0)
{
lean_ctor_set_tag(v___x_2486_, 5);
lean_ctor_set(v___x_2486_, 1, v___x_2491_);
lean_ctor_set(v___x_2486_, 0, v___x_2488_);
v___x_2493_ = v___x_2486_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v___x_2488_);
lean_ctor_set(v_reuseFailAlloc_2495_, 1, v___x_2491_);
v___x_2493_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
lean_object* v___x_2494_; 
v___x_2494_ = l_Repr_addAppParen(v___x_2493_, v_prec_2482_);
return v___x_2494_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instRepr___redArg___lam__2___boxed(lean_object* v___x_2506_, lean_object* v___f_2507_, lean_object* v_m_2508_, lean_object* v_prec_2509_){
_start:
{
lean_object* v_res_2510_; 
v_res_2510_ = l_Std_DHashMap_Raw_instRepr___redArg___lam__2(v___x_2506_, v___f_2507_, v_m_2508_, v_prec_2509_);
lean_dec(v_prec_2509_);
return v_res_2510_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instRepr___redArg(lean_object* v_inst_2511_, lean_object* v_inst_2512_){
_start:
{
lean_object* v___f_2513_; lean_object* v___x_2514_; lean_object* v___f_2515_; 
v___f_2513_ = ((lean_object*)(l_Std_DHashMap_Raw_toList___redArg___closed__0));
v___x_2514_ = lean_alloc_closure((void*)(l_Sigma_repr___boxed), 6, 4);
lean_closure_set(v___x_2514_, 0, lean_box(0));
lean_closure_set(v___x_2514_, 1, lean_box(0));
lean_closure_set(v___x_2514_, 2, v_inst_2511_);
lean_closure_set(v___x_2514_, 3, v_inst_2512_);
v___f_2515_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instRepr___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2515_, 0, v___x_2514_);
lean_closure_set(v___f_2515_, 1, v___f_2513_);
return v___f_2515_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instRepr(lean_object* v_00_u03b1_2516_, lean_object* v_00_u03b2_2517_, lean_object* v_inst_2518_, lean_object* v_inst_2519_){
_start:
{
lean_object* v___x_2520_; 
v___x_2520_ = l_Std_DHashMap_Raw_instRepr___redArg(v_inst_2518_, v_inst_2519_);
return v___x_2520_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keys___redArg___lam__0(lean_object* v_a_2521_, lean_object* v_b_2522_, lean_object* v_d_2523_){
_start:
{
lean_object* v___x_2524_; 
v___x_2524_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2524_, 0, v_a_2521_);
lean_ctor_set(v___x_2524_, 1, v_d_2523_);
return v___x_2524_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keys___redArg___lam__0___boxed(lean_object* v_a_2525_, lean_object* v_b_2526_, lean_object* v_d_2527_){
_start:
{
lean_object* v_res_2528_; 
v_res_2528_ = l_Std_DHashMap_Raw_keys___redArg___lam__0(v_a_2525_, v_b_2526_, v_d_2527_);
lean_dec(v_b_2526_);
return v_res_2528_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keys___redArg(lean_object* v_m_2533_){
_start:
{
lean_object* v___x_2534_; lean_object* v_buckets_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; uint8_t v___x_2539_; 
v___x_2534_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_2535_ = lean_ctor_get(v_m_2533_, 1);
lean_inc_ref(v_buckets_2535_);
lean_dec_ref(v_m_2533_);
v___x_2536_ = lean_box(0);
v___x_2537_ = lean_array_get_size(v_buckets_2535_);
v___x_2538_ = lean_unsigned_to_nat(0u);
v___x_2539_ = lean_nat_dec_lt(v___x_2538_, v___x_2537_);
if (v___x_2539_ == 0)
{
lean_dec_ref(v_buckets_2535_);
return v___x_2536_;
}
else
{
lean_object* v___f_2540_; size_t v___x_2541_; size_t v___x_2542_; lean_object* v___x_2543_; 
v___f_2540_ = ((lean_object*)(l_Std_DHashMap_Raw_keys___redArg___closed__1));
v___x_2541_ = lean_usize_of_nat(v___x_2537_);
v___x_2542_ = ((size_t)0ULL);
v___x_2543_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2534_, v___f_2540_, v_buckets_2535_, v___x_2541_, v___x_2542_, v___x_2536_);
return v___x_2543_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keys(lean_object* v_00_u03b1_2544_, lean_object* v_00_u03b2_2545_, lean_object* v_m_2546_){
_start:
{
lean_object* v___x_2547_; lean_object* v_buckets_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; uint8_t v___x_2552_; 
v___x_2547_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_2548_ = lean_ctor_get(v_m_2546_, 1);
lean_inc_ref(v_buckets_2548_);
lean_dec_ref(v_m_2546_);
v___x_2549_ = lean_box(0);
v___x_2550_ = lean_array_get_size(v_buckets_2548_);
v___x_2551_ = lean_unsigned_to_nat(0u);
v___x_2552_ = lean_nat_dec_lt(v___x_2551_, v___x_2550_);
if (v___x_2552_ == 0)
{
lean_dec_ref(v_buckets_2548_);
return v___x_2549_;
}
else
{
lean_object* v___f_2553_; size_t v___x_2554_; size_t v___x_2555_; lean_object* v___x_2556_; 
v___f_2553_ = ((lean_object*)(l_Std_DHashMap_Raw_keys___redArg___closed__1));
v___x_2554_ = lean_usize_of_nat(v___x_2550_);
v___x_2555_ = ((size_t)0ULL);
v___x_2556_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2547_, v___f_2553_, v_buckets_2548_, v___x_2554_, v___x_2555_, v___x_2549_);
return v___x_2556_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_ofList___redArg(lean_object* v_inst_2561_, lean_object* v_inst_2562_, lean_object* v_l_2563_){
_start:
{
lean_object* v___x_2564_; uint8_t v___x_2565_; 
v___x_2564_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
v___x_2565_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2565_ == 0)
{
lean_dec(v_l_2563_);
lean_dec_ref(v_inst_2562_);
lean_dec_ref(v_inst_2561_);
return v___x_2564_;
}
else
{
lean_object* v___f_2566_; lean_object* v___x_2567_; 
v___f_2566_ = ((lean_object*)(l_Std_DHashMap_Raw_ofList___redArg___closed__1));
v___x_2567_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_2566_, v_inst_2561_, v_inst_2562_, v___x_2564_, v_l_2563_);
return v___x_2567_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_ofList(lean_object* v_00_u03b1_2568_, lean_object* v_00_u03b2_2569_, lean_object* v_inst_2570_, lean_object* v_inst_2571_, lean_object* v_l_2572_){
_start:
{
lean_object* v___x_2573_; uint8_t v___x_2574_; 
v___x_2573_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
v___x_2574_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2574_ == 0)
{
lean_dec(v_l_2572_);
lean_dec_ref(v_inst_2571_);
lean_dec_ref(v_inst_2570_);
return v___x_2573_;
}
else
{
lean_object* v___f_2575_; lean_object* v___x_2576_; 
v___f_2575_ = ((lean_object*)(l_Std_DHashMap_Raw_ofList___redArg___closed__1));
v___x_2576_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_2575_, v_inst_2570_, v_inst_2571_, v___x_2573_, v_l_2572_);
return v___x_2576_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_ofArray___redArg(lean_object* v_inst_2577_, lean_object* v_inst_2578_, lean_object* v_l_2579_){
_start:
{
lean_object* v___x_2580_; uint8_t v___x_2581_; 
v___x_2580_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
v___x_2581_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2581_ == 0)
{
lean_dec_ref(v_l_2579_);
lean_dec_ref(v_inst_2578_);
lean_dec_ref(v_inst_2577_);
return v___x_2580_;
}
else
{
lean_object* v___f_2582_; lean_object* v___x_2583_; 
v___f_2582_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1));
v___x_2583_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_2582_, v_inst_2577_, v_inst_2578_, v___x_2580_, v_l_2579_);
return v___x_2583_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_ofArray(lean_object* v_00_u03b1_2584_, lean_object* v_00_u03b2_2585_, lean_object* v_inst_2586_, lean_object* v_inst_2587_, lean_object* v_l_2588_){
_start:
{
lean_object* v___x_2589_; uint8_t v___x_2590_; 
v___x_2589_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
v___x_2590_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2590_ == 0)
{
lean_dec_ref(v_l_2588_);
lean_dec_ref(v_inst_2587_);
lean_dec_ref(v_inst_2586_);
return v___x_2589_;
}
else
{
lean_object* v___f_2591_; lean_object* v___x_2592_; 
v___f_2591_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1));
v___x_2592_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_2591_, v_inst_2586_, v_inst_2587_, v___x_2589_, v_l_2588_);
return v___x_2592_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_ofList___redArg(lean_object* v_inst_2593_, lean_object* v_inst_2594_, lean_object* v_l_2595_){
_start:
{
lean_object* v___x_2596_; uint8_t v___x_2597_; 
v___x_2596_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
v___x_2597_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2597_ == 0)
{
lean_dec(v_l_2595_);
lean_dec_ref(v_inst_2594_);
lean_dec_ref(v_inst_2593_);
return v___x_2596_;
}
else
{
lean_object* v___f_2598_; lean_object* v___x_2599_; 
v___f_2598_ = ((lean_object*)(l_Std_DHashMap_Raw_ofList___redArg___closed__1));
v___x_2599_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_2598_, v_inst_2593_, v_inst_2594_, v___x_2596_, v_l_2595_);
return v___x_2599_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_ofList(lean_object* v_00_u03b1_2600_, lean_object* v_00_u03b2_2601_, lean_object* v_inst_2602_, lean_object* v_inst_2603_, lean_object* v_l_2604_){
_start:
{
lean_object* v___x_2605_; uint8_t v___x_2606_; 
v___x_2605_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
v___x_2606_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2606_ == 0)
{
lean_dec(v_l_2604_);
lean_dec_ref(v_inst_2603_);
lean_dec_ref(v_inst_2602_);
return v___x_2605_;
}
else
{
lean_object* v___f_2607_; lean_object* v___x_2608_; 
v___f_2607_ = ((lean_object*)(l_Std_DHashMap_Raw_ofList___redArg___closed__1));
v___x_2608_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_2607_, v_inst_2602_, v_inst_2603_, v___x_2605_, v_l_2604_);
return v___x_2608_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_ofArray___redArg(lean_object* v_inst_2609_, lean_object* v_inst_2610_, lean_object* v_l_2611_){
_start:
{
lean_object* v___x_2612_; uint8_t v___x_2613_; 
v___x_2612_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
v___x_2613_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2613_ == 0)
{
lean_dec_ref(v_l_2611_);
lean_dec_ref(v_inst_2610_);
lean_dec_ref(v_inst_2609_);
return v___x_2612_;
}
else
{
lean_object* v___f_2614_; lean_object* v___x_2615_; 
v___f_2614_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1));
v___x_2615_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_2614_, v_inst_2609_, v_inst_2610_, v___x_2612_, v_l_2611_);
return v___x_2615_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_ofArray(lean_object* v_00_u03b1_2616_, lean_object* v_00_u03b2_2617_, lean_object* v_inst_2618_, lean_object* v_inst_2619_, lean_object* v_l_2620_){
_start:
{
lean_object* v___x_2621_; uint8_t v___x_2622_; 
v___x_2621_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
v___x_2622_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2622_ == 0)
{
lean_dec_ref(v_l_2620_);
lean_dec_ref(v_inst_2619_);
lean_dec_ref(v_inst_2618_);
return v___x_2621_;
}
else
{
lean_object* v___f_2623_; lean_object* v___x_2624_; 
v___f_2623_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1));
v___x_2624_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_2623_, v_inst_2618_, v_inst_2619_, v___x_2621_, v_l_2620_);
return v___x_2624_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_unitOfList___redArg(lean_object* v_inst_2625_, lean_object* v_inst_2626_, lean_object* v_l_2627_){
_start:
{
lean_object* v___x_2628_; uint8_t v___x_2629_; 
v___x_2628_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
v___x_2629_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2629_ == 0)
{
lean_dec(v_l_2627_);
lean_dec_ref(v_inst_2626_);
lean_dec_ref(v_inst_2625_);
return v___x_2628_;
}
else
{
lean_object* v___f_2630_; lean_object* v___x_2631_; 
v___f_2630_ = ((lean_object*)(l_Std_DHashMap_Raw_ofList___redArg___closed__1));
v___x_2631_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2630_, v_inst_2625_, v_inst_2626_, v___x_2628_, v_l_2627_);
return v___x_2631_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_unitOfList(lean_object* v_00_u03b1_2632_, lean_object* v_inst_2633_, lean_object* v_inst_2634_, lean_object* v_l_2635_){
_start:
{
lean_object* v___x_2636_; uint8_t v___x_2637_; 
v___x_2636_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
v___x_2637_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2637_ == 0)
{
lean_dec(v_l_2635_);
lean_dec_ref(v_inst_2634_);
lean_dec_ref(v_inst_2633_);
return v___x_2636_;
}
else
{
lean_object* v___f_2638_; lean_object* v___x_2639_; 
v___f_2638_ = ((lean_object*)(l_Std_DHashMap_Raw_ofList___redArg___closed__1));
v___x_2639_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2638_, v_inst_2633_, v_inst_2634_, v___x_2636_, v_l_2635_);
return v___x_2639_;
}
}
}
lean_object* runtime_initialize_Init_Data_LawfulHashable(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DHashMap_Internal_Defs(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DHashMap_Internal_Defs(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DHashMap_Raw(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
