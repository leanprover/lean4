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
lean_dec_ref(v_a_107_);
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
lean_inc(v_quotContext_113_);
v_currMacroScope_114_ = lean_ctor_get(v_a_107_, 2);
lean_inc(v_currMacroScope_114_);
v_ref_115_ = lean_ctor_get(v_a_107_, 5);
lean_inc(v_ref_115_);
lean_dec_ref(v_a_107_);
v___x_116_ = lean_unsigned_to_nat(0u);
v___x_117_ = l_Lean_Syntax_getArg(v_x_106_, v___x_116_);
v___x_118_ = lean_unsigned_to_nat(2u);
v___x_119_ = l_Lean_Syntax_getArg(v_x_106_, v___x_118_);
lean_dec(v_x_106_);
v___x_120_ = 0;
v___x_121_ = l_Lean_SourceInfo_fromRef(v_ref_115_, v___x_120_);
lean_dec(v_ref_115_);
v___x_122_ = ((lean_object*)(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4));
v___x_123_ = lean_obj_once(&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__6, &l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__6_once, _init_l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__6);
v___x_124_ = ((lean_object*)(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__8));
v___x_125_ = l_Lean_addMacroScope(v_quotContext_113_, v___x_124_, v_currMacroScope_114_);
v___x_126_ = ((lean_object*)(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__13));
lean_inc(v___x_121_);
v___x_127_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_127_, 0, v___x_121_);
lean_ctor_set(v___x_127_, 1, v___x_123_);
lean_ctor_set(v___x_127_, 2, v___x_125_);
lean_ctor_set(v___x_127_, 3, v___x_126_);
v___x_128_ = ((lean_object*)(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__15));
lean_inc(v___x_121_);
v___x_129_ = l_Lean_Syntax_node2(v___x_121_, v___x_128_, v___x_117_, v___x_119_);
v___x_130_ = l_Lean_Syntax_node2(v___x_121_, v___x_122_, v___x_127_, v___x_129_);
v___x_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
lean_ctor_set(v___x_131_, 1, v_a_108_);
return v___x_131_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1(lean_object* v_x_135_, lean_object* v_a_136_, lean_object* v_a_137_){
_start:
{
lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_138_ = ((lean_object*)(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4));
lean_inc(v_x_135_);
v___x_139_ = l_Lean_Syntax_isOfKind(v_x_135_, v___x_138_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; lean_object* v___x_141_; 
lean_dec(v_x_135_);
v___x_140_ = lean_box(0);
v___x_141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
lean_ctor_set(v___x_141_, 1, v_a_137_);
return v___x_141_;
}
else
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_142_ = lean_unsigned_to_nat(0u);
v___x_143_ = l_Lean_Syntax_getArg(v_x_135_, v___x_142_);
v___x_144_ = ((lean_object*)(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___closed__1));
lean_inc(v___x_143_);
v___x_145_ = l_Lean_Syntax_isOfKind(v___x_143_, v___x_144_);
if (v___x_145_ == 0)
{
lean_object* v___x_146_; lean_object* v___x_147_; 
lean_dec(v___x_143_);
lean_dec(v_x_135_);
v___x_146_ = lean_box(0);
v___x_147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
lean_ctor_set(v___x_147_, 1, v_a_137_);
return v___x_147_;
}
else
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; uint8_t v___x_151_; 
v___x_148_ = lean_unsigned_to_nat(1u);
v___x_149_ = l_Lean_Syntax_getArg(v_x_135_, v___x_148_);
lean_dec(v_x_135_);
v___x_150_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_149_);
v___x_151_ = l_Lean_Syntax_matchesNull(v___x_149_, v___x_150_);
if (v___x_151_ == 0)
{
lean_object* v___x_152_; lean_object* v___x_153_; 
lean_dec(v___x_149_);
lean_dec(v___x_143_);
v___x_152_ = lean_box(0);
v___x_153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
lean_ctor_set(v___x_153_, 1, v_a_137_);
return v___x_153_;
}
else
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v_ref_156_; uint8_t v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_154_ = l_Lean_Syntax_getArg(v___x_149_, v___x_142_);
v___x_155_ = l_Lean_Syntax_getArg(v___x_149_, v___x_148_);
lean_dec(v___x_149_);
v_ref_156_ = l_Lean_replaceRef(v___x_143_, v_a_136_);
lean_dec(v___x_143_);
v___x_157_ = 0;
v___x_158_ = l_Lean_SourceInfo_fromRef(v_ref_156_, v___x_157_);
lean_dec(v_ref_156_);
v___x_159_ = ((lean_object*)(l_Std_DHashMap_Raw_term___x7em___00__closed__4));
v___x_160_ = ((lean_object*)(l_Std_DHashMap_Raw_term___x7em___00__closed__7));
lean_inc(v___x_158_);
v___x_161_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_158_);
lean_ctor_set(v___x_161_, 1, v___x_160_);
v___x_162_ = l_Lean_Syntax_node3(v___x_158_, v___x_159_, v___x_154_, v___x_161_, v___x_155_);
v___x_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
lean_ctor_set(v___x_163_, 1, v_a_137_);
return v___x_163_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___boxed(lean_object* v_x_164_, lean_object* v_a_165_, lean_object* v_a_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1(v_x_164_, v_a_165_, v_a_166_);
lean_dec(v_a_165_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insert___redArg(lean_object* v_inst_168_, lean_object* v_inst_169_, lean_object* v_m_170_, lean_object* v_a_171_, lean_object* v_b_172_){
_start:
{
lean_object* v_buckets_173_; lean_object* v___x_174_; lean_object* v___x_175_; uint8_t v___x_176_; 
v_buckets_173_ = lean_ctor_get(v_m_170_, 1);
v___x_174_ = lean_unsigned_to_nat(0u);
v___x_175_ = lean_array_get_size(v_buckets_173_);
v___x_176_ = lean_nat_dec_lt(v___x_174_, v___x_175_);
if (v___x_176_ == 0)
{
lean_dec(v_b_172_);
lean_dec(v_a_171_);
lean_dec_ref(v_inst_169_);
lean_dec_ref(v_inst_168_);
return v_m_170_;
}
else
{
lean_object* v___x_177_; 
v___x_177_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_168_, v_inst_169_, v_m_170_, v_a_171_, v_b_172_);
return v___x_177_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insert(lean_object* v_00_u03b1_178_, lean_object* v_00_u03b2_179_, lean_object* v_inst_180_, lean_object* v_inst_181_, lean_object* v_m_182_, lean_object* v_a_183_, lean_object* v_b_184_){
_start:
{
lean_object* v_buckets_185_; lean_object* v___x_186_; lean_object* v___x_187_; uint8_t v___x_188_; 
v_buckets_185_ = lean_ctor_get(v_m_182_, 1);
v___x_186_ = lean_unsigned_to_nat(0u);
v___x_187_ = lean_array_get_size(v_buckets_185_);
v___x_188_ = lean_nat_dec_lt(v___x_186_, v___x_187_);
if (v___x_188_ == 0)
{
lean_dec(v_b_184_);
lean_dec(v_a_183_);
lean_dec_ref(v_inst_181_);
lean_dec_ref(v_inst_180_);
return v_m_182_;
}
else
{
lean_object* v___x_189_; 
v___x_189_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_180_, v_inst_181_, v_m_182_, v_a_183_, v_b_184_);
return v___x_189_;
}
}
}
static lean_object* _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__0, &l_Std_DHashMap_Raw_instEmptyCollection___closed__0_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__0);
v___x_191_ = lean_array_get_size(v___x_190_);
return v___x_191_;
}
}
static uint8_t _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_192_ = lean_obj_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0);
v___x_193_ = lean_unsigned_to_nat(0u);
v___x_194_ = lean_nat_dec_lt(v___x_193_, v___x_192_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0(lean_object* v_inst_195_, lean_object* v_inst_196_, lean_object* v_x_197_){
_start:
{
lean_object* v_fst_198_; lean_object* v_snd_199_; lean_object* v___x_200_; uint8_t v___x_201_; 
v_fst_198_ = lean_ctor_get(v_x_197_, 0);
lean_inc(v_fst_198_);
v_snd_199_ = lean_ctor_get(v_x_197_, 1);
lean_inc(v_snd_199_);
lean_dec_ref(v_x_197_);
v___x_200_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
v___x_201_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_201_ == 0)
{
lean_dec(v_snd_199_);
lean_dec(v_fst_198_);
lean_dec_ref(v_inst_196_);
lean_dec_ref(v_inst_195_);
return v___x_200_;
}
else
{
lean_object* v___x_202_; 
v___x_202_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_195_, v_inst_196_, v___x_200_, v_fst_198_, v_snd_199_);
return v___x_202_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg(lean_object* v_inst_203_, lean_object* v_inst_204_){
_start:
{
lean_object* v___f_205_; 
v___f_205_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_205_, 0, v_inst_203_);
lean_closure_set(v___f_205_, 1, v_inst_204_);
return v___f_205_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable(lean_object* v_00_u03b1_206_, lean_object* v_00_u03b2_207_, lean_object* v_inst_208_, lean_object* v_inst_209_){
_start:
{
lean_object* v___f_210_; 
v___f_210_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_210_, 0, v_inst_208_);
lean_closure_set(v___f_210_, 1, v_inst_209_);
return v___f_210_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable___redArg___lam__0(lean_object* v_inst_211_, lean_object* v_inst_212_, lean_object* v_x_213_, lean_object* v_s_214_){
_start:
{
lean_object* v_fst_215_; lean_object* v_snd_216_; lean_object* v_buckets_217_; lean_object* v___x_218_; lean_object* v___x_219_; uint8_t v___x_220_; 
v_fst_215_ = lean_ctor_get(v_x_213_, 0);
lean_inc(v_fst_215_);
v_snd_216_ = lean_ctor_get(v_x_213_, 1);
lean_inc(v_snd_216_);
lean_dec_ref(v_x_213_);
v_buckets_217_ = lean_ctor_get(v_s_214_, 1);
v___x_218_ = lean_unsigned_to_nat(0u);
v___x_219_ = lean_array_get_size(v_buckets_217_);
v___x_220_ = lean_nat_dec_lt(v___x_218_, v___x_219_);
if (v___x_220_ == 0)
{
lean_dec(v_snd_216_);
lean_dec(v_fst_215_);
lean_dec_ref(v_inst_212_);
lean_dec_ref(v_inst_211_);
return v_s_214_;
}
else
{
lean_object* v___x_221_; 
v___x_221_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_211_, v_inst_212_, v_s_214_, v_fst_215_, v_snd_216_);
return v___x_221_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable___redArg(lean_object* v_inst_222_, lean_object* v_inst_223_){
_start:
{
lean_object* v___f_224_; 
v___f_224_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_224_, 0, v_inst_222_);
lean_closure_set(v___f_224_, 1, v_inst_223_);
return v___f_224_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable(lean_object* v_00_u03b1_225_, lean_object* v_00_u03b2_226_, lean_object* v_inst_227_, lean_object* v_inst_228_){
_start:
{
lean_object* v___f_229_; 
v___f_229_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_229_, 0, v_inst_227_);
lean_closure_set(v___f_229_, 1, v_inst_228_);
return v___f_229_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insertIfNew___redArg(lean_object* v_inst_230_, lean_object* v_inst_231_, lean_object* v_m_232_, lean_object* v_a_233_, lean_object* v_b_234_){
_start:
{
lean_object* v_buckets_235_; lean_object* v___x_236_; lean_object* v___x_237_; uint8_t v___x_238_; 
v_buckets_235_ = lean_ctor_get(v_m_232_, 1);
v___x_236_ = lean_unsigned_to_nat(0u);
v___x_237_ = lean_array_get_size(v_buckets_235_);
v___x_238_ = lean_nat_dec_lt(v___x_236_, v___x_237_);
if (v___x_238_ == 0)
{
lean_dec(v_b_234_);
lean_dec(v_a_233_);
lean_dec_ref(v_inst_231_);
lean_dec_ref(v_inst_230_);
return v_m_232_;
}
else
{
lean_object* v___x_239_; 
v___x_239_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_230_, v_inst_231_, v_m_232_, v_a_233_, v_b_234_);
return v___x_239_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insertIfNew(lean_object* v_00_u03b1_240_, lean_object* v_00_u03b2_241_, lean_object* v_inst_242_, lean_object* v_inst_243_, lean_object* v_m_244_, lean_object* v_a_245_, lean_object* v_b_246_){
_start:
{
lean_object* v_buckets_247_; lean_object* v___x_248_; lean_object* v___x_249_; uint8_t v___x_250_; 
v_buckets_247_ = lean_ctor_get(v_m_244_, 1);
v___x_248_ = lean_unsigned_to_nat(0u);
v___x_249_ = lean_array_get_size(v_buckets_247_);
v___x_250_ = lean_nat_dec_lt(v___x_248_, v___x_249_);
if (v___x_250_ == 0)
{
lean_dec(v_b_246_);
lean_dec(v_a_245_);
lean_dec_ref(v_inst_243_);
lean_dec_ref(v_inst_242_);
return v_m_244_;
}
else
{
lean_object* v___x_251_; 
v___x_251_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_242_, v_inst_243_, v_m_244_, v_a_245_, v_b_246_);
return v___x_251_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_containsThenInsert___redArg(lean_object* v_inst_252_, lean_object* v_inst_253_, lean_object* v_m_254_, lean_object* v_a_255_, lean_object* v_b_256_){
_start:
{
lean_object* v_size_257_; lean_object* v_buckets_258_; lean_object* v___x_259_; lean_object* v___x_260_; uint8_t v___x_261_; 
v_size_257_ = lean_ctor_get(v_m_254_, 0);
v_buckets_258_ = lean_ctor_get(v_m_254_, 1);
v___x_259_ = lean_unsigned_to_nat(0u);
v___x_260_ = lean_array_get_size(v_buckets_258_);
v___x_261_ = lean_nat_dec_lt(v___x_259_, v___x_260_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; lean_object* v___x_263_; 
lean_dec(v_b_256_);
lean_dec(v_a_255_);
lean_dec_ref(v_inst_253_);
lean_dec_ref(v_inst_252_);
v___x_262_ = lean_box(v___x_261_);
v___x_263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
lean_ctor_set(v___x_263_, 1, v_m_254_);
return v___x_263_;
}
else
{
lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_313_; 
lean_inc_ref(v_buckets_258_);
lean_inc(v_size_257_);
v_isSharedCheck_313_ = !lean_is_exclusive(v_m_254_);
if (v_isSharedCheck_313_ == 0)
{
lean_object* v_unused_314_; lean_object* v_unused_315_; 
v_unused_314_ = lean_ctor_get(v_m_254_, 1);
lean_dec(v_unused_314_);
v_unused_315_ = lean_ctor_get(v_m_254_, 0);
lean_dec(v_unused_315_);
v___x_265_ = v_m_254_;
v_isShared_266_ = v_isSharedCheck_313_;
goto v_resetjp_264_;
}
else
{
lean_dec(v_m_254_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_313_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_267_; uint64_t v___x_268_; uint64_t v___x_269_; uint64_t v___x_270_; uint64_t v___x_271_; uint64_t v_fold_272_; uint64_t v___x_273_; uint64_t v___x_274_; uint64_t v___x_275_; size_t v___x_276_; size_t v___x_277_; size_t v___x_278_; size_t v___x_279_; size_t v___x_280_; lean_object* v_bkt_281_; uint8_t v___x_282_; 
lean_inc_ref(v_inst_253_);
lean_inc(v_a_255_);
v___x_267_ = lean_apply_1(v_inst_253_, v_a_255_);
v___x_268_ = 32ULL;
v___x_269_ = lean_unbox_uint64(v___x_267_);
v___x_270_ = lean_uint64_shift_right(v___x_269_, v___x_268_);
v___x_271_ = lean_unbox_uint64(v___x_267_);
lean_dec_ref(v___x_267_);
v_fold_272_ = lean_uint64_xor(v___x_271_, v___x_270_);
v___x_273_ = 16ULL;
v___x_274_ = lean_uint64_shift_right(v_fold_272_, v___x_273_);
v___x_275_ = lean_uint64_xor(v_fold_272_, v___x_274_);
v___x_276_ = lean_uint64_to_usize(v___x_275_);
v___x_277_ = lean_usize_of_nat(v___x_260_);
v___x_278_ = ((size_t)1ULL);
v___x_279_ = lean_usize_sub(v___x_277_, v___x_278_);
v___x_280_ = lean_usize_land(v___x_276_, v___x_279_);
v_bkt_281_ = lean_array_uget_borrowed(v_buckets_258_, v___x_280_);
lean_inc(v_bkt_281_);
lean_inc(v_a_255_);
lean_inc_ref(v_inst_252_);
v___x_282_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_252_, v_a_255_, v_bkt_281_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; lean_object* v_size_x27_284_; lean_object* v___x_285_; lean_object* v_buckets_x27_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; uint8_t v___x_292_; 
lean_dec_ref(v_inst_252_);
v___x_283_ = lean_unsigned_to_nat(1u);
v_size_x27_284_ = lean_nat_add(v_size_257_, v___x_283_);
lean_dec(v_size_257_);
lean_inc(v_bkt_281_);
v___x_285_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_285_, 0, v_a_255_);
lean_ctor_set(v___x_285_, 1, v_b_256_);
lean_ctor_set(v___x_285_, 2, v_bkt_281_);
v_buckets_x27_286_ = lean_array_uset(v_buckets_258_, v___x_280_, v___x_285_);
v___x_287_ = lean_unsigned_to_nat(4u);
v___x_288_ = lean_nat_mul(v_size_x27_284_, v___x_287_);
v___x_289_ = lean_unsigned_to_nat(3u);
v___x_290_ = lean_nat_div(v___x_288_, v___x_289_);
lean_dec(v___x_288_);
v___x_291_ = lean_array_get_size(v_buckets_x27_286_);
v___x_292_ = lean_nat_dec_le(v___x_290_, v___x_291_);
lean_dec(v___x_290_);
if (v___x_292_ == 0)
{
lean_object* v_val_293_; lean_object* v___x_295_; 
v_val_293_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_253_, v_buckets_x27_286_);
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 1, v_val_293_);
lean_ctor_set(v___x_265_, 0, v_size_x27_284_);
v___x_295_ = v___x_265_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_size_x27_284_);
lean_ctor_set(v_reuseFailAlloc_298_, 1, v_val_293_);
v___x_295_ = v_reuseFailAlloc_298_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = lean_box(v___x_282_);
v___x_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v___x_295_);
return v___x_297_;
}
}
else
{
lean_object* v___x_300_; 
lean_dec_ref(v_inst_253_);
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 1, v_buckets_x27_286_);
lean_ctor_set(v___x_265_, 0, v_size_x27_284_);
v___x_300_ = v___x_265_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_size_x27_284_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v_buckets_x27_286_);
v___x_300_ = v_reuseFailAlloc_303_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = lean_box(v___x_282_);
v___x_302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
lean_ctor_set(v___x_302_, 1, v___x_300_);
return v___x_302_;
}
}
}
else
{
lean_object* v___x_304_; lean_object* v_buckets_x27_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_309_; 
lean_inc(v_bkt_281_);
lean_dec_ref(v_inst_253_);
v___x_304_ = lean_box(0);
v_buckets_x27_305_ = lean_array_uset(v_buckets_258_, v___x_280_, v___x_304_);
v___x_306_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_inst_252_, v_a_255_, v_b_256_, v_bkt_281_);
v___x_307_ = lean_array_uset(v_buckets_x27_305_, v___x_280_, v___x_306_);
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 1, v___x_307_);
v___x_309_ = v___x_265_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_size_257_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v___x_307_);
v___x_309_ = v_reuseFailAlloc_312_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = lean_box(v___x_282_);
v___x_311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
lean_ctor_set(v___x_311_, 1, v___x_309_);
return v___x_311_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_containsThenInsert(lean_object* v_00_u03b1_316_, lean_object* v_00_u03b2_317_, lean_object* v_inst_318_, lean_object* v_inst_319_, lean_object* v_m_320_, lean_object* v_a_321_, lean_object* v_b_322_){
_start:
{
lean_object* v_size_323_; lean_object* v_buckets_324_; lean_object* v___x_325_; lean_object* v___x_326_; uint8_t v___x_327_; 
v_size_323_ = lean_ctor_get(v_m_320_, 0);
v_buckets_324_ = lean_ctor_get(v_m_320_, 1);
v___x_325_ = lean_unsigned_to_nat(0u);
v___x_326_ = lean_array_get_size(v_buckets_324_);
v___x_327_ = lean_nat_dec_lt(v___x_325_, v___x_326_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; lean_object* v___x_329_; 
lean_dec(v_b_322_);
lean_dec(v_a_321_);
lean_dec_ref(v_inst_319_);
lean_dec_ref(v_inst_318_);
v___x_328_ = lean_box(v___x_327_);
v___x_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
lean_ctor_set(v___x_329_, 1, v_m_320_);
return v___x_329_;
}
else
{
lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_379_; 
lean_inc_ref(v_buckets_324_);
lean_inc(v_size_323_);
v_isSharedCheck_379_ = !lean_is_exclusive(v_m_320_);
if (v_isSharedCheck_379_ == 0)
{
lean_object* v_unused_380_; lean_object* v_unused_381_; 
v_unused_380_ = lean_ctor_get(v_m_320_, 1);
lean_dec(v_unused_380_);
v_unused_381_ = lean_ctor_get(v_m_320_, 0);
lean_dec(v_unused_381_);
v___x_331_ = v_m_320_;
v_isShared_332_ = v_isSharedCheck_379_;
goto v_resetjp_330_;
}
else
{
lean_dec(v_m_320_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_379_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_333_; uint64_t v___x_334_; uint64_t v___x_335_; uint64_t v___x_336_; uint64_t v___x_337_; uint64_t v_fold_338_; uint64_t v___x_339_; uint64_t v___x_340_; uint64_t v___x_341_; size_t v___x_342_; size_t v___x_343_; size_t v___x_344_; size_t v___x_345_; size_t v___x_346_; lean_object* v_bkt_347_; uint8_t v___x_348_; 
lean_inc_ref(v_inst_319_);
lean_inc(v_a_321_);
v___x_333_ = lean_apply_1(v_inst_319_, v_a_321_);
v___x_334_ = 32ULL;
v___x_335_ = lean_unbox_uint64(v___x_333_);
v___x_336_ = lean_uint64_shift_right(v___x_335_, v___x_334_);
v___x_337_ = lean_unbox_uint64(v___x_333_);
lean_dec_ref(v___x_333_);
v_fold_338_ = lean_uint64_xor(v___x_337_, v___x_336_);
v___x_339_ = 16ULL;
v___x_340_ = lean_uint64_shift_right(v_fold_338_, v___x_339_);
v___x_341_ = lean_uint64_xor(v_fold_338_, v___x_340_);
v___x_342_ = lean_uint64_to_usize(v___x_341_);
v___x_343_ = lean_usize_of_nat(v___x_326_);
v___x_344_ = ((size_t)1ULL);
v___x_345_ = lean_usize_sub(v___x_343_, v___x_344_);
v___x_346_ = lean_usize_land(v___x_342_, v___x_345_);
v_bkt_347_ = lean_array_uget_borrowed(v_buckets_324_, v___x_346_);
lean_inc(v_bkt_347_);
lean_inc(v_a_321_);
lean_inc_ref(v_inst_318_);
v___x_348_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_318_, v_a_321_, v_bkt_347_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; lean_object* v_size_x27_350_; lean_object* v___x_351_; lean_object* v_buckets_x27_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; uint8_t v___x_358_; 
lean_dec_ref(v_inst_318_);
v___x_349_ = lean_unsigned_to_nat(1u);
v_size_x27_350_ = lean_nat_add(v_size_323_, v___x_349_);
lean_dec(v_size_323_);
lean_inc(v_bkt_347_);
v___x_351_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_351_, 0, v_a_321_);
lean_ctor_set(v___x_351_, 1, v_b_322_);
lean_ctor_set(v___x_351_, 2, v_bkt_347_);
v_buckets_x27_352_ = lean_array_uset(v_buckets_324_, v___x_346_, v___x_351_);
v___x_353_ = lean_unsigned_to_nat(4u);
v___x_354_ = lean_nat_mul(v_size_x27_350_, v___x_353_);
v___x_355_ = lean_unsigned_to_nat(3u);
v___x_356_ = lean_nat_div(v___x_354_, v___x_355_);
lean_dec(v___x_354_);
v___x_357_ = lean_array_get_size(v_buckets_x27_352_);
v___x_358_ = lean_nat_dec_le(v___x_356_, v___x_357_);
lean_dec(v___x_356_);
if (v___x_358_ == 0)
{
lean_object* v_val_359_; lean_object* v___x_361_; 
v_val_359_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_319_, v_buckets_x27_352_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 1, v_val_359_);
lean_ctor_set(v___x_331_, 0, v_size_x27_350_);
v___x_361_ = v___x_331_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_size_x27_350_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v_val_359_);
v___x_361_ = v_reuseFailAlloc_364_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = lean_box(v___x_348_);
v___x_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
lean_ctor_set(v___x_363_, 1, v___x_361_);
return v___x_363_;
}
}
else
{
lean_object* v___x_366_; 
lean_dec_ref(v_inst_319_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 1, v_buckets_x27_352_);
lean_ctor_set(v___x_331_, 0, v_size_x27_350_);
v___x_366_ = v___x_331_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_size_x27_350_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_buckets_x27_352_);
v___x_366_ = v_reuseFailAlloc_369_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = lean_box(v___x_348_);
v___x_368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
lean_ctor_set(v___x_368_, 1, v___x_366_);
return v___x_368_;
}
}
}
else
{
lean_object* v___x_370_; lean_object* v_buckets_x27_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_375_; 
lean_inc(v_bkt_347_);
lean_dec_ref(v_inst_319_);
v___x_370_ = lean_box(0);
v_buckets_x27_371_ = lean_array_uset(v_buckets_324_, v___x_346_, v___x_370_);
v___x_372_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_inst_318_, v_a_321_, v_b_322_, v_bkt_347_);
v___x_373_ = lean_array_uset(v_buckets_x27_371_, v___x_346_, v___x_372_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 1, v___x_373_);
v___x_375_ = v___x_331_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_size_323_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v___x_373_);
v___x_375_ = v_reuseFailAlloc_378_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = lean_box(v___x_348_);
v___x_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
lean_ctor_set(v___x_377_, 1, v___x_375_);
return v___x_377_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getThenInsertIfNew_x3f___redArg(lean_object* v_inst_382_, lean_object* v_inst_383_, lean_object* v_m_384_, lean_object* v_a_385_, lean_object* v_b_386_){
_start:
{
lean_object* v_size_387_; lean_object* v_buckets_388_; lean_object* v___x_389_; lean_object* v___x_390_; uint8_t v___x_391_; 
v_size_387_ = lean_ctor_get(v_m_384_, 0);
v_buckets_388_ = lean_ctor_get(v_m_384_, 1);
v___x_389_ = lean_unsigned_to_nat(0u);
v___x_390_ = lean_array_get_size(v_buckets_388_);
v___x_391_ = lean_nat_dec_lt(v___x_389_, v___x_390_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; lean_object* v___x_393_; 
lean_dec(v_b_386_);
lean_dec(v_a_385_);
lean_dec_ref(v_inst_383_);
lean_dec_ref(v_inst_382_);
v___x_392_ = lean_box(0);
v___x_393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
lean_ctor_set(v___x_393_, 1, v_m_384_);
return v___x_393_;
}
else
{
lean_object* v___x_394_; uint64_t v___x_395_; uint64_t v___x_396_; uint64_t v___x_397_; uint64_t v___x_398_; uint64_t v_fold_399_; uint64_t v___x_400_; uint64_t v___x_401_; uint64_t v___x_402_; size_t v___x_403_; size_t v___x_404_; size_t v___x_405_; size_t v___x_406_; size_t v___x_407_; lean_object* v_bkt_408_; lean_object* v___x_409_; 
lean_inc_ref(v_inst_383_);
lean_inc(v_a_385_);
v___x_394_ = lean_apply_1(v_inst_383_, v_a_385_);
v___x_395_ = 32ULL;
v___x_396_ = lean_unbox_uint64(v___x_394_);
v___x_397_ = lean_uint64_shift_right(v___x_396_, v___x_395_);
v___x_398_ = lean_unbox_uint64(v___x_394_);
lean_dec_ref(v___x_394_);
v_fold_399_ = lean_uint64_xor(v___x_398_, v___x_397_);
v___x_400_ = 16ULL;
v___x_401_ = lean_uint64_shift_right(v_fold_399_, v___x_400_);
v___x_402_ = lean_uint64_xor(v_fold_399_, v___x_401_);
v___x_403_ = lean_uint64_to_usize(v___x_402_);
v___x_404_ = lean_usize_of_nat(v___x_390_);
v___x_405_ = ((size_t)1ULL);
v___x_406_ = lean_usize_sub(v___x_404_, v___x_405_);
v___x_407_ = lean_usize_land(v___x_403_, v___x_406_);
v_bkt_408_ = lean_array_uget_borrowed(v_buckets_388_, v___x_407_);
lean_inc(v_bkt_408_);
lean_inc(v_a_385_);
v___x_409_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(v_inst_382_, v_a_385_, v_bkt_408_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_432_; 
lean_inc_ref(v_buckets_388_);
lean_inc(v_size_387_);
v_isSharedCheck_432_ = !lean_is_exclusive(v_m_384_);
if (v_isSharedCheck_432_ == 0)
{
lean_object* v_unused_433_; lean_object* v_unused_434_; 
v_unused_433_ = lean_ctor_get(v_m_384_, 1);
lean_dec(v_unused_433_);
v_unused_434_ = lean_ctor_get(v_m_384_, 0);
lean_dec(v_unused_434_);
v___x_411_ = v_m_384_;
v_isShared_412_ = v_isSharedCheck_432_;
goto v_resetjp_410_;
}
else
{
lean_dec(v_m_384_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_432_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_413_; lean_object* v_size_x27_414_; lean_object* v___x_415_; lean_object* v_buckets_x27_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; uint8_t v___x_422_; 
v___x_413_ = lean_unsigned_to_nat(1u);
v_size_x27_414_ = lean_nat_add(v_size_387_, v___x_413_);
lean_dec(v_size_387_);
lean_inc(v_bkt_408_);
v___x_415_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_415_, 0, v_a_385_);
lean_ctor_set(v___x_415_, 1, v_b_386_);
lean_ctor_set(v___x_415_, 2, v_bkt_408_);
v_buckets_x27_416_ = lean_array_uset(v_buckets_388_, v___x_407_, v___x_415_);
v___x_417_ = lean_unsigned_to_nat(4u);
v___x_418_ = lean_nat_mul(v_size_x27_414_, v___x_417_);
v___x_419_ = lean_unsigned_to_nat(3u);
v___x_420_ = lean_nat_div(v___x_418_, v___x_419_);
lean_dec(v___x_418_);
v___x_421_ = lean_array_get_size(v_buckets_x27_416_);
v___x_422_ = lean_nat_dec_le(v___x_420_, v___x_421_);
lean_dec(v___x_420_);
if (v___x_422_ == 0)
{
lean_object* v_val_423_; lean_object* v___x_425_; 
v_val_423_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_383_, v_buckets_x27_416_);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 1, v_val_423_);
lean_ctor_set(v___x_411_, 0, v_size_x27_414_);
v___x_425_ = v___x_411_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_size_x27_414_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v_val_423_);
v___x_425_ = v_reuseFailAlloc_427_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
lean_object* v___x_426_; 
v___x_426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_426_, 0, v___x_409_);
lean_ctor_set(v___x_426_, 1, v___x_425_);
return v___x_426_;
}
}
else
{
lean_object* v___x_429_; 
lean_dec_ref(v_inst_383_);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 1, v_buckets_x27_416_);
lean_ctor_set(v___x_411_, 0, v_size_x27_414_);
v___x_429_ = v___x_411_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_size_x27_414_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v_buckets_x27_416_);
v___x_429_ = v_reuseFailAlloc_431_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
lean_object* v___x_430_; 
v___x_430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_430_, 0, v___x_409_);
lean_ctor_set(v___x_430_, 1, v___x_429_);
return v___x_430_;
}
}
}
}
else
{
lean_object* v___x_435_; 
lean_dec(v_b_386_);
lean_dec(v_a_385_);
lean_dec_ref(v_inst_383_);
v___x_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_435_, 0, v___x_409_);
lean_ctor_set(v___x_435_, 1, v_m_384_);
return v___x_435_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_436_, lean_object* v_00_u03b2_437_, lean_object* v_inst_438_, lean_object* v_inst_439_, lean_object* v_inst_440_, lean_object* v_m_441_, lean_object* v_a_442_, lean_object* v_b_443_){
_start:
{
lean_object* v_size_444_; lean_object* v_buckets_445_; lean_object* v___x_446_; lean_object* v___x_447_; uint8_t v___x_448_; 
v_size_444_ = lean_ctor_get(v_m_441_, 0);
v_buckets_445_ = lean_ctor_get(v_m_441_, 1);
v___x_446_ = lean_unsigned_to_nat(0u);
v___x_447_ = lean_array_get_size(v_buckets_445_);
v___x_448_ = lean_nat_dec_lt(v___x_446_, v___x_447_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; lean_object* v___x_450_; 
lean_dec(v_b_443_);
lean_dec(v_a_442_);
lean_dec_ref(v_inst_439_);
lean_dec_ref(v_inst_438_);
v___x_449_ = lean_box(0);
v___x_450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_450_, 0, v___x_449_);
lean_ctor_set(v___x_450_, 1, v_m_441_);
return v___x_450_;
}
else
{
lean_object* v___x_451_; uint64_t v___x_452_; uint64_t v___x_453_; uint64_t v___x_454_; uint64_t v___x_455_; uint64_t v_fold_456_; uint64_t v___x_457_; uint64_t v___x_458_; uint64_t v___x_459_; size_t v___x_460_; size_t v___x_461_; size_t v___x_462_; size_t v___x_463_; size_t v___x_464_; lean_object* v_bkt_465_; lean_object* v___x_466_; 
lean_inc_ref(v_inst_439_);
lean_inc(v_a_442_);
v___x_451_ = lean_apply_1(v_inst_439_, v_a_442_);
v___x_452_ = 32ULL;
v___x_453_ = lean_unbox_uint64(v___x_451_);
v___x_454_ = lean_uint64_shift_right(v___x_453_, v___x_452_);
v___x_455_ = lean_unbox_uint64(v___x_451_);
lean_dec_ref(v___x_451_);
v_fold_456_ = lean_uint64_xor(v___x_455_, v___x_454_);
v___x_457_ = 16ULL;
v___x_458_ = lean_uint64_shift_right(v_fold_456_, v___x_457_);
v___x_459_ = lean_uint64_xor(v_fold_456_, v___x_458_);
v___x_460_ = lean_uint64_to_usize(v___x_459_);
v___x_461_ = lean_usize_of_nat(v___x_447_);
v___x_462_ = ((size_t)1ULL);
v___x_463_ = lean_usize_sub(v___x_461_, v___x_462_);
v___x_464_ = lean_usize_land(v___x_460_, v___x_463_);
v_bkt_465_ = lean_array_uget_borrowed(v_buckets_445_, v___x_464_);
lean_inc(v_bkt_465_);
lean_inc(v_a_442_);
v___x_466_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(v_inst_438_, v_a_442_, v_bkt_465_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_489_; 
lean_inc_ref(v_buckets_445_);
lean_inc(v_size_444_);
v_isSharedCheck_489_ = !lean_is_exclusive(v_m_441_);
if (v_isSharedCheck_489_ == 0)
{
lean_object* v_unused_490_; lean_object* v_unused_491_; 
v_unused_490_ = lean_ctor_get(v_m_441_, 1);
lean_dec(v_unused_490_);
v_unused_491_ = lean_ctor_get(v_m_441_, 0);
lean_dec(v_unused_491_);
v___x_468_ = v_m_441_;
v_isShared_469_ = v_isSharedCheck_489_;
goto v_resetjp_467_;
}
else
{
lean_dec(v_m_441_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_489_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_470_; lean_object* v_size_x27_471_; lean_object* v___x_472_; lean_object* v_buckets_x27_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_470_ = lean_unsigned_to_nat(1u);
v_size_x27_471_ = lean_nat_add(v_size_444_, v___x_470_);
lean_dec(v_size_444_);
lean_inc(v_bkt_465_);
v___x_472_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_472_, 0, v_a_442_);
lean_ctor_set(v___x_472_, 1, v_b_443_);
lean_ctor_set(v___x_472_, 2, v_bkt_465_);
v_buckets_x27_473_ = lean_array_uset(v_buckets_445_, v___x_464_, v___x_472_);
v___x_474_ = lean_unsigned_to_nat(4u);
v___x_475_ = lean_nat_mul(v_size_x27_471_, v___x_474_);
v___x_476_ = lean_unsigned_to_nat(3u);
v___x_477_ = lean_nat_div(v___x_475_, v___x_476_);
lean_dec(v___x_475_);
v___x_478_ = lean_array_get_size(v_buckets_x27_473_);
v___x_479_ = lean_nat_dec_le(v___x_477_, v___x_478_);
lean_dec(v___x_477_);
if (v___x_479_ == 0)
{
lean_object* v_val_480_; lean_object* v___x_482_; 
v_val_480_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_439_, v_buckets_x27_473_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 1, v_val_480_);
lean_ctor_set(v___x_468_, 0, v_size_x27_471_);
v___x_482_ = v___x_468_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_size_x27_471_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v_val_480_);
v___x_482_ = v_reuseFailAlloc_484_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
lean_object* v___x_483_; 
v___x_483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_466_);
lean_ctor_set(v___x_483_, 1, v___x_482_);
return v___x_483_;
}
}
else
{
lean_object* v___x_486_; 
lean_dec_ref(v_inst_439_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 1, v_buckets_x27_473_);
lean_ctor_set(v___x_468_, 0, v_size_x27_471_);
v___x_486_ = v___x_468_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_size_x27_471_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v_buckets_x27_473_);
v___x_486_ = v_reuseFailAlloc_488_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
lean_object* v___x_487_; 
v___x_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_466_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
return v___x_487_;
}
}
}
}
else
{
lean_object* v___x_492_; 
lean_dec(v_b_443_);
lean_dec(v_a_442_);
lean_dec_ref(v_inst_439_);
v___x_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_466_);
lean_ctor_set(v___x_492_, 1, v_m_441_);
return v___x_492_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_containsThenInsertIfNew___redArg(lean_object* v_inst_493_, lean_object* v_inst_494_, lean_object* v_m_495_, lean_object* v_a_496_, lean_object* v_b_497_){
_start:
{
lean_object* v_size_498_; lean_object* v_buckets_499_; lean_object* v___x_500_; lean_object* v___x_501_; uint8_t v___x_502_; 
v_size_498_ = lean_ctor_get(v_m_495_, 0);
v_buckets_499_ = lean_ctor_get(v_m_495_, 1);
v___x_500_ = lean_unsigned_to_nat(0u);
v___x_501_ = lean_array_get_size(v_buckets_499_);
v___x_502_ = lean_nat_dec_lt(v___x_500_, v___x_501_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; lean_object* v___x_504_; 
lean_dec(v_b_497_);
lean_dec(v_a_496_);
lean_dec_ref(v_inst_494_);
lean_dec_ref(v_inst_493_);
v___x_503_ = lean_box(v___x_502_);
v___x_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
lean_ctor_set(v___x_504_, 1, v_m_495_);
return v___x_504_;
}
else
{
lean_object* v___x_505_; uint64_t v___x_506_; uint64_t v___x_507_; uint64_t v___x_508_; uint64_t v___x_509_; uint64_t v_fold_510_; uint64_t v___x_511_; uint64_t v___x_512_; uint64_t v___x_513_; size_t v___x_514_; size_t v___x_515_; size_t v___x_516_; size_t v___x_517_; size_t v___x_518_; lean_object* v_bkt_519_; uint8_t v___x_520_; 
lean_inc_ref(v_inst_494_);
lean_inc(v_a_496_);
v___x_505_ = lean_apply_1(v_inst_494_, v_a_496_);
v___x_506_ = 32ULL;
v___x_507_ = lean_unbox_uint64(v___x_505_);
v___x_508_ = lean_uint64_shift_right(v___x_507_, v___x_506_);
v___x_509_ = lean_unbox_uint64(v___x_505_);
lean_dec_ref(v___x_505_);
v_fold_510_ = lean_uint64_xor(v___x_509_, v___x_508_);
v___x_511_ = 16ULL;
v___x_512_ = lean_uint64_shift_right(v_fold_510_, v___x_511_);
v___x_513_ = lean_uint64_xor(v_fold_510_, v___x_512_);
v___x_514_ = lean_uint64_to_usize(v___x_513_);
v___x_515_ = lean_usize_of_nat(v___x_501_);
v___x_516_ = ((size_t)1ULL);
v___x_517_ = lean_usize_sub(v___x_515_, v___x_516_);
v___x_518_ = lean_usize_land(v___x_514_, v___x_517_);
v_bkt_519_ = lean_array_uget_borrowed(v_buckets_499_, v___x_518_);
lean_inc(v_bkt_519_);
lean_inc(v_a_496_);
v___x_520_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_493_, v_a_496_, v_bkt_519_);
if (v___x_520_ == 0)
{
lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_545_; 
lean_inc_ref(v_buckets_499_);
lean_inc(v_size_498_);
v_isSharedCheck_545_ = !lean_is_exclusive(v_m_495_);
if (v_isSharedCheck_545_ == 0)
{
lean_object* v_unused_546_; lean_object* v_unused_547_; 
v_unused_546_ = lean_ctor_get(v_m_495_, 1);
lean_dec(v_unused_546_);
v_unused_547_ = lean_ctor_get(v_m_495_, 0);
lean_dec(v_unused_547_);
v___x_522_ = v_m_495_;
v_isShared_523_ = v_isSharedCheck_545_;
goto v_resetjp_521_;
}
else
{
lean_dec(v_m_495_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_545_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_524_; lean_object* v_size_x27_525_; lean_object* v___x_526_; lean_object* v_buckets_x27_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; uint8_t v___x_533_; 
v___x_524_ = lean_unsigned_to_nat(1u);
v_size_x27_525_ = lean_nat_add(v_size_498_, v___x_524_);
lean_dec(v_size_498_);
lean_inc(v_bkt_519_);
v___x_526_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_526_, 0, v_a_496_);
lean_ctor_set(v___x_526_, 1, v_b_497_);
lean_ctor_set(v___x_526_, 2, v_bkt_519_);
v_buckets_x27_527_ = lean_array_uset(v_buckets_499_, v___x_518_, v___x_526_);
v___x_528_ = lean_unsigned_to_nat(4u);
v___x_529_ = lean_nat_mul(v_size_x27_525_, v___x_528_);
v___x_530_ = lean_unsigned_to_nat(3u);
v___x_531_ = lean_nat_div(v___x_529_, v___x_530_);
lean_dec(v___x_529_);
v___x_532_ = lean_array_get_size(v_buckets_x27_527_);
v___x_533_ = lean_nat_dec_le(v___x_531_, v___x_532_);
lean_dec(v___x_531_);
if (v___x_533_ == 0)
{
lean_object* v_val_534_; lean_object* v___x_536_; 
v_val_534_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_494_, v_buckets_x27_527_);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 1, v_val_534_);
lean_ctor_set(v___x_522_, 0, v_size_x27_525_);
v___x_536_ = v___x_522_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_size_x27_525_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v_val_534_);
v___x_536_ = v_reuseFailAlloc_539_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = lean_box(v___x_520_);
v___x_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
lean_ctor_set(v___x_538_, 1, v___x_536_);
return v___x_538_;
}
}
else
{
lean_object* v___x_541_; 
lean_dec_ref(v_inst_494_);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 1, v_buckets_x27_527_);
lean_ctor_set(v___x_522_, 0, v_size_x27_525_);
v___x_541_ = v___x_522_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_size_x27_525_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v_buckets_x27_527_);
v___x_541_ = v_reuseFailAlloc_544_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = lean_box(v___x_520_);
v___x_543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
lean_ctor_set(v___x_543_, 1, v___x_541_);
return v___x_543_;
}
}
}
}
else
{
lean_object* v___x_548_; lean_object* v___x_549_; 
lean_dec(v_b_497_);
lean_dec(v_a_496_);
lean_dec_ref(v_inst_494_);
v___x_548_ = lean_box(v___x_520_);
v___x_549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
lean_ctor_set(v___x_549_, 1, v_m_495_);
return v___x_549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_containsThenInsertIfNew(lean_object* v_00_u03b1_550_, lean_object* v_00_u03b2_551_, lean_object* v_inst_552_, lean_object* v_inst_553_, lean_object* v_m_554_, lean_object* v_a_555_, lean_object* v_b_556_){
_start:
{
lean_object* v_size_557_; lean_object* v_buckets_558_; lean_object* v___x_559_; lean_object* v___x_560_; uint8_t v___x_561_; 
v_size_557_ = lean_ctor_get(v_m_554_, 0);
v_buckets_558_ = lean_ctor_get(v_m_554_, 1);
v___x_559_ = lean_unsigned_to_nat(0u);
v___x_560_ = lean_array_get_size(v_buckets_558_);
v___x_561_ = lean_nat_dec_lt(v___x_559_, v___x_560_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; lean_object* v___x_563_; 
lean_dec(v_b_556_);
lean_dec(v_a_555_);
lean_dec_ref(v_inst_553_);
lean_dec_ref(v_inst_552_);
v___x_562_ = lean_box(v___x_561_);
v___x_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
lean_ctor_set(v___x_563_, 1, v_m_554_);
return v___x_563_;
}
else
{
lean_object* v___x_564_; uint64_t v___x_565_; uint64_t v___x_566_; uint64_t v___x_567_; uint64_t v___x_568_; uint64_t v_fold_569_; uint64_t v___x_570_; uint64_t v___x_571_; uint64_t v___x_572_; size_t v___x_573_; size_t v___x_574_; size_t v___x_575_; size_t v___x_576_; size_t v___x_577_; lean_object* v_bkt_578_; uint8_t v___x_579_; 
lean_inc_ref(v_inst_553_);
lean_inc(v_a_555_);
v___x_564_ = lean_apply_1(v_inst_553_, v_a_555_);
v___x_565_ = 32ULL;
v___x_566_ = lean_unbox_uint64(v___x_564_);
v___x_567_ = lean_uint64_shift_right(v___x_566_, v___x_565_);
v___x_568_ = lean_unbox_uint64(v___x_564_);
lean_dec_ref(v___x_564_);
v_fold_569_ = lean_uint64_xor(v___x_568_, v___x_567_);
v___x_570_ = 16ULL;
v___x_571_ = lean_uint64_shift_right(v_fold_569_, v___x_570_);
v___x_572_ = lean_uint64_xor(v_fold_569_, v___x_571_);
v___x_573_ = lean_uint64_to_usize(v___x_572_);
v___x_574_ = lean_usize_of_nat(v___x_560_);
v___x_575_ = ((size_t)1ULL);
v___x_576_ = lean_usize_sub(v___x_574_, v___x_575_);
v___x_577_ = lean_usize_land(v___x_573_, v___x_576_);
v_bkt_578_ = lean_array_uget_borrowed(v_buckets_558_, v___x_577_);
lean_inc(v_bkt_578_);
lean_inc(v_a_555_);
v___x_579_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_552_, v_a_555_, v_bkt_578_);
if (v___x_579_ == 0)
{
lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_604_; 
lean_inc_ref(v_buckets_558_);
lean_inc(v_size_557_);
v_isSharedCheck_604_ = !lean_is_exclusive(v_m_554_);
if (v_isSharedCheck_604_ == 0)
{
lean_object* v_unused_605_; lean_object* v_unused_606_; 
v_unused_605_ = lean_ctor_get(v_m_554_, 1);
lean_dec(v_unused_605_);
v_unused_606_ = lean_ctor_get(v_m_554_, 0);
lean_dec(v_unused_606_);
v___x_581_ = v_m_554_;
v_isShared_582_ = v_isSharedCheck_604_;
goto v_resetjp_580_;
}
else
{
lean_dec(v_m_554_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_604_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_583_; lean_object* v_size_x27_584_; lean_object* v___x_585_; lean_object* v_buckets_x27_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_583_ = lean_unsigned_to_nat(1u);
v_size_x27_584_ = lean_nat_add(v_size_557_, v___x_583_);
lean_dec(v_size_557_);
lean_inc(v_bkt_578_);
v___x_585_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_585_, 0, v_a_555_);
lean_ctor_set(v___x_585_, 1, v_b_556_);
lean_ctor_set(v___x_585_, 2, v_bkt_578_);
v_buckets_x27_586_ = lean_array_uset(v_buckets_558_, v___x_577_, v___x_585_);
v___x_587_ = lean_unsigned_to_nat(4u);
v___x_588_ = lean_nat_mul(v_size_x27_584_, v___x_587_);
v___x_589_ = lean_unsigned_to_nat(3u);
v___x_590_ = lean_nat_div(v___x_588_, v___x_589_);
lean_dec(v___x_588_);
v___x_591_ = lean_array_get_size(v_buckets_x27_586_);
v___x_592_ = lean_nat_dec_le(v___x_590_, v___x_591_);
lean_dec(v___x_590_);
if (v___x_592_ == 0)
{
lean_object* v_val_593_; lean_object* v___x_595_; 
v_val_593_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_553_, v_buckets_x27_586_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 1, v_val_593_);
lean_ctor_set(v___x_581_, 0, v_size_x27_584_);
v___x_595_ = v___x_581_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_size_x27_584_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_val_593_);
v___x_595_ = v_reuseFailAlloc_598_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = lean_box(v___x_579_);
v___x_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
lean_ctor_set(v___x_597_, 1, v___x_595_);
return v___x_597_;
}
}
else
{
lean_object* v___x_600_; 
lean_dec_ref(v_inst_553_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 1, v_buckets_x27_586_);
lean_ctor_set(v___x_581_, 0, v_size_x27_584_);
v___x_600_ = v___x_581_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_size_x27_584_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v_buckets_x27_586_);
v___x_600_ = v_reuseFailAlloc_603_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_601_ = lean_box(v___x_579_);
v___x_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
lean_ctor_set(v___x_602_, 1, v___x_600_);
return v___x_602_;
}
}
}
}
else
{
lean_object* v___x_607_; lean_object* v___x_608_; 
lean_dec(v_b_556_);
lean_dec(v_a_555_);
lean_dec_ref(v_inst_553_);
v___x_607_ = lean_box(v___x_579_);
v___x_608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
lean_ctor_set(v___x_608_, 1, v_m_554_);
return v___x_608_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x3f___redArg(lean_object* v_inst_609_, lean_object* v_inst_610_, lean_object* v_m_611_, lean_object* v_a_612_){
_start:
{
lean_object* v_buckets_613_; lean_object* v___x_614_; lean_object* v___x_615_; uint8_t v___x_616_; 
v_buckets_613_ = lean_ctor_get(v_m_611_, 1);
v___x_614_ = lean_unsigned_to_nat(0u);
v___x_615_ = lean_array_get_size(v_buckets_613_);
v___x_616_ = lean_nat_dec_lt(v___x_614_, v___x_615_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; 
lean_dec(v_a_612_);
lean_dec_ref(v_inst_610_);
lean_dec_ref(v_inst_609_);
v___x_617_ = lean_box(0);
return v___x_617_;
}
else
{
lean_object* v___x_618_; 
v___x_618_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(v_inst_609_, v_inst_610_, v_m_611_, v_a_612_);
return v___x_618_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x3f___redArg___boxed(lean_object* v_inst_619_, lean_object* v_inst_620_, lean_object* v_m_621_, lean_object* v_a_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Std_DHashMap_Raw_get_x3f___redArg(v_inst_619_, v_inst_620_, v_m_621_, v_a_622_);
lean_dec_ref(v_m_621_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x3f(lean_object* v_00_u03b1_624_, lean_object* v_00_u03b2_625_, lean_object* v_inst_626_, lean_object* v_inst_627_, lean_object* v_inst_628_, lean_object* v_m_629_, lean_object* v_a_630_){
_start:
{
lean_object* v_buckets_631_; lean_object* v___x_632_; lean_object* v___x_633_; uint8_t v___x_634_; 
v_buckets_631_ = lean_ctor_get(v_m_629_, 1);
v___x_632_ = lean_unsigned_to_nat(0u);
v___x_633_ = lean_array_get_size(v_buckets_631_);
v___x_634_ = lean_nat_dec_lt(v___x_632_, v___x_633_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; 
lean_dec(v_a_630_);
lean_dec_ref(v_inst_628_);
lean_dec_ref(v_inst_626_);
v___x_635_ = lean_box(0);
return v___x_635_;
}
else
{
lean_object* v___x_636_; 
v___x_636_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(v_inst_626_, v_inst_628_, v_m_629_, v_a_630_);
return v___x_636_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x3f___boxed(lean_object* v_00_u03b1_637_, lean_object* v_00_u03b2_638_, lean_object* v_inst_639_, lean_object* v_inst_640_, lean_object* v_inst_641_, lean_object* v_m_642_, lean_object* v_a_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Std_DHashMap_Raw_get_x3f(v_00_u03b1_637_, v_00_u03b2_638_, v_inst_639_, v_inst_640_, v_inst_641_, v_m_642_, v_a_643_);
lean_dec_ref(v_m_642_);
return v_res_644_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_contains___redArg(lean_object* v_inst_645_, lean_object* v_inst_646_, lean_object* v_m_647_, lean_object* v_a_648_){
_start:
{
lean_object* v_buckets_649_; lean_object* v___x_650_; lean_object* v___x_651_; uint8_t v___x_652_; 
v_buckets_649_ = lean_ctor_get(v_m_647_, 1);
v___x_650_ = lean_unsigned_to_nat(0u);
v___x_651_ = lean_array_get_size(v_buckets_649_);
v___x_652_ = lean_nat_dec_lt(v___x_650_, v___x_651_);
if (v___x_652_ == 0)
{
lean_dec(v_a_648_);
lean_dec_ref(v_inst_646_);
lean_dec_ref(v_inst_645_);
return v___x_652_;
}
else
{
uint8_t v___x_653_; 
v___x_653_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_645_, v_inst_646_, v_m_647_, v_a_648_);
return v___x_653_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_contains___redArg___boxed(lean_object* v_inst_654_, lean_object* v_inst_655_, lean_object* v_m_656_, lean_object* v_a_657_){
_start:
{
uint8_t v_res_658_; lean_object* v_r_659_; 
v_res_658_ = l_Std_DHashMap_Raw_contains___redArg(v_inst_654_, v_inst_655_, v_m_656_, v_a_657_);
lean_dec_ref(v_m_656_);
v_r_659_ = lean_box(v_res_658_);
return v_r_659_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_contains(lean_object* v_00_u03b1_660_, lean_object* v_00_u03b2_661_, lean_object* v_inst_662_, lean_object* v_inst_663_, lean_object* v_m_664_, lean_object* v_a_665_){
_start:
{
lean_object* v_buckets_666_; lean_object* v___x_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v_buckets_666_ = lean_ctor_get(v_m_664_, 1);
v___x_667_ = lean_unsigned_to_nat(0u);
v___x_668_ = lean_array_get_size(v_buckets_666_);
v___x_669_ = lean_nat_dec_lt(v___x_667_, v___x_668_);
if (v___x_669_ == 0)
{
lean_dec(v_a_665_);
lean_dec_ref(v_inst_663_);
lean_dec_ref(v_inst_662_);
return v___x_669_;
}
else
{
uint8_t v___x_670_; 
v___x_670_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_662_, v_inst_663_, v_m_664_, v_a_665_);
return v___x_670_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_contains___boxed(lean_object* v_00_u03b1_671_, lean_object* v_00_u03b2_672_, lean_object* v_inst_673_, lean_object* v_inst_674_, lean_object* v_m_675_, lean_object* v_a_676_){
_start:
{
uint8_t v_res_677_; lean_object* v_r_678_; 
v_res_677_ = l_Std_DHashMap_Raw_contains(v_00_u03b1_671_, v_00_u03b2_672_, v_inst_673_, v_inst_674_, v_m_675_, v_a_676_);
lean_dec_ref(v_m_675_);
v_r_678_ = lean_box(v_res_677_);
return v_r_678_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instMembershipOfBEqOfHashable(lean_object* v_00_u03b1_679_, lean_object* v_00_u03b2_680_, lean_object* v_inst_681_, lean_object* v_inst_682_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = lean_box(0);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instMembershipOfBEqOfHashable___boxed(lean_object* v_00_u03b1_684_, lean_object* v_00_u03b2_685_, lean_object* v_inst_686_, lean_object* v_inst_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Std_DHashMap_Raw_instMembershipOfBEqOfHashable(v_00_u03b1_684_, v_00_u03b2_685_, v_inst_686_, v_inst_687_);
lean_dec_ref(v_inst_687_);
lean_dec_ref(v_inst_686_);
return v_res_688_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_instDecidableMem___redArg(lean_object* v_inst_689_, lean_object* v_inst_690_, lean_object* v_m_691_, lean_object* v_a_692_){
_start:
{
lean_object* v_buckets_693_; lean_object* v___x_694_; lean_object* v___x_695_; uint8_t v___x_696_; 
v_buckets_693_ = lean_ctor_get(v_m_691_, 1);
v___x_694_ = lean_unsigned_to_nat(0u);
v___x_695_ = lean_array_get_size(v_buckets_693_);
v___x_696_ = lean_nat_dec_lt(v___x_694_, v___x_695_);
if (v___x_696_ == 0)
{
lean_dec(v_a_692_);
lean_dec_ref(v_inst_690_);
lean_dec_ref(v_inst_689_);
return v___x_696_;
}
else
{
uint8_t v___x_697_; 
v___x_697_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_689_, v_inst_690_, v_m_691_, v_a_692_);
return v___x_697_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instDecidableMem___redArg___boxed(lean_object* v_inst_698_, lean_object* v_inst_699_, lean_object* v_m_700_, lean_object* v_a_701_){
_start:
{
uint8_t v_res_702_; lean_object* v_r_703_; 
v_res_702_ = l_Std_DHashMap_Raw_instDecidableMem___redArg(v_inst_698_, v_inst_699_, v_m_700_, v_a_701_);
lean_dec_ref(v_m_700_);
v_r_703_ = lean_box(v_res_702_);
return v_r_703_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_instDecidableMem(lean_object* v_00_u03b1_704_, lean_object* v_00_u03b2_705_, lean_object* v_inst_706_, lean_object* v_inst_707_, lean_object* v_m_708_, lean_object* v_a_709_){
_start:
{
uint8_t v___x_710_; 
v___x_710_ = l_Std_DHashMap_Raw_instDecidableMem___redArg(v_inst_706_, v_inst_707_, v_m_708_, v_a_709_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instDecidableMem___boxed(lean_object* v_00_u03b1_711_, lean_object* v_00_u03b2_712_, lean_object* v_inst_713_, lean_object* v_inst_714_, lean_object* v_m_715_, lean_object* v_a_716_){
_start:
{
uint8_t v_res_717_; lean_object* v_r_718_; 
v_res_717_ = l_Std_DHashMap_Raw_instDecidableMem(v_00_u03b1_711_, v_00_u03b2_712_, v_inst_713_, v_inst_714_, v_m_715_, v_a_716_);
lean_dec_ref(v_m_715_);
v_r_718_ = lean_box(v_res_717_);
return v_r_718_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get___redArg(lean_object* v_inst_719_, lean_object* v_inst_720_, lean_object* v_m_721_, lean_object* v_a_722_){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = l_Std_DHashMap_Internal_Raw_u2080_get___redArg(v_inst_719_, v_inst_720_, v_m_721_, v_a_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get___redArg___boxed(lean_object* v_inst_724_, lean_object* v_inst_725_, lean_object* v_m_726_, lean_object* v_a_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Std_DHashMap_Raw_get___redArg(v_inst_724_, v_inst_725_, v_m_726_, v_a_727_);
lean_dec_ref(v_m_726_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get(lean_object* v_00_u03b1_729_, lean_object* v_00_u03b2_730_, lean_object* v_inst_731_, lean_object* v_inst_732_, lean_object* v_inst_733_, lean_object* v_m_734_, lean_object* v_a_735_, lean_object* v_h_736_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l_Std_DHashMap_Internal_Raw_u2080_get___redArg(v_inst_731_, v_inst_732_, v_m_734_, v_a_735_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get___boxed(lean_object* v_00_u03b1_738_, lean_object* v_00_u03b2_739_, lean_object* v_inst_740_, lean_object* v_inst_741_, lean_object* v_inst_742_, lean_object* v_m_743_, lean_object* v_a_744_, lean_object* v_h_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Std_DHashMap_Raw_get(v_00_u03b1_738_, v_00_u03b2_739_, v_inst_740_, v_inst_741_, v_inst_742_, v_m_743_, v_a_744_, v_h_745_);
lean_dec_ref(v_m_743_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getD___redArg(lean_object* v_inst_747_, lean_object* v_inst_748_, lean_object* v_m_749_, lean_object* v_a_750_, lean_object* v_fallback_751_){
_start:
{
lean_object* v_buckets_752_; lean_object* v___x_753_; lean_object* v___x_754_; uint8_t v___x_755_; 
v_buckets_752_ = lean_ctor_get(v_m_749_, 1);
v___x_753_ = lean_unsigned_to_nat(0u);
v___x_754_ = lean_array_get_size(v_buckets_752_);
v___x_755_ = lean_nat_dec_lt(v___x_753_, v___x_754_);
if (v___x_755_ == 0)
{
lean_dec(v_a_750_);
lean_dec_ref(v_inst_748_);
lean_dec_ref(v_inst_747_);
lean_inc(v_fallback_751_);
return v_fallback_751_;
}
else
{
lean_object* v___x_756_; 
v___x_756_ = l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(v_inst_747_, v_inst_748_, v_m_749_, v_a_750_, v_fallback_751_);
return v___x_756_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getD___redArg___boxed(lean_object* v_inst_757_, lean_object* v_inst_758_, lean_object* v_m_759_, lean_object* v_a_760_, lean_object* v_fallback_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Std_DHashMap_Raw_getD___redArg(v_inst_757_, v_inst_758_, v_m_759_, v_a_760_, v_fallback_761_);
lean_dec(v_fallback_761_);
lean_dec_ref(v_m_759_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getD(lean_object* v_00_u03b1_763_, lean_object* v_00_u03b2_764_, lean_object* v_inst_765_, lean_object* v_inst_766_, lean_object* v_inst_767_, lean_object* v_m_768_, lean_object* v_a_769_, lean_object* v_fallback_770_){
_start:
{
lean_object* v_buckets_771_; lean_object* v___x_772_; lean_object* v___x_773_; uint8_t v___x_774_; 
v_buckets_771_ = lean_ctor_get(v_m_768_, 1);
v___x_772_ = lean_unsigned_to_nat(0u);
v___x_773_ = lean_array_get_size(v_buckets_771_);
v___x_774_ = lean_nat_dec_lt(v___x_772_, v___x_773_);
if (v___x_774_ == 0)
{
lean_dec(v_a_769_);
lean_dec_ref(v_inst_766_);
lean_dec_ref(v_inst_765_);
lean_inc(v_fallback_770_);
return v_fallback_770_;
}
else
{
lean_object* v___x_775_; 
v___x_775_ = l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(v_inst_765_, v_inst_766_, v_m_768_, v_a_769_, v_fallback_770_);
return v___x_775_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getD___boxed(lean_object* v_00_u03b1_776_, lean_object* v_00_u03b2_777_, lean_object* v_inst_778_, lean_object* v_inst_779_, lean_object* v_inst_780_, lean_object* v_m_781_, lean_object* v_a_782_, lean_object* v_fallback_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Std_DHashMap_Raw_getD(v_00_u03b1_776_, v_00_u03b2_777_, v_inst_778_, v_inst_779_, v_inst_780_, v_m_781_, v_a_782_, v_fallback_783_);
lean_dec(v_fallback_783_);
lean_dec_ref(v_m_781_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x21___redArg(lean_object* v_inst_785_, lean_object* v_inst_786_, lean_object* v_m_787_, lean_object* v_a_788_, lean_object* v_inst_789_){
_start:
{
lean_object* v_buckets_790_; lean_object* v___x_791_; lean_object* v___x_792_; uint8_t v___x_793_; 
v_buckets_790_ = lean_ctor_get(v_m_787_, 1);
v___x_791_ = lean_unsigned_to_nat(0u);
v___x_792_ = lean_array_get_size(v_buckets_790_);
v___x_793_ = lean_nat_dec_lt(v___x_791_, v___x_792_);
if (v___x_793_ == 0)
{
lean_dec(v_a_788_);
lean_dec_ref(v_inst_786_);
lean_dec_ref(v_inst_785_);
return v_inst_789_;
}
else
{
lean_object* v___x_794_; 
v___x_794_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(v_inst_785_, v_inst_786_, v_m_787_, v_a_788_, v_inst_789_);
return v___x_794_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x21___redArg___boxed(lean_object* v_inst_795_, lean_object* v_inst_796_, lean_object* v_m_797_, lean_object* v_a_798_, lean_object* v_inst_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Std_DHashMap_Raw_get_x21___redArg(v_inst_795_, v_inst_796_, v_m_797_, v_a_798_, v_inst_799_);
lean_dec_ref(v_m_797_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x21(lean_object* v_00_u03b1_801_, lean_object* v_00_u03b2_802_, lean_object* v_inst_803_, lean_object* v_inst_804_, lean_object* v_inst_805_, lean_object* v_m_806_, lean_object* v_a_807_, lean_object* v_inst_808_){
_start:
{
lean_object* v_buckets_809_; lean_object* v___x_810_; lean_object* v___x_811_; uint8_t v___x_812_; 
v_buckets_809_ = lean_ctor_get(v_m_806_, 1);
v___x_810_ = lean_unsigned_to_nat(0u);
v___x_811_ = lean_array_get_size(v_buckets_809_);
v___x_812_ = lean_nat_dec_lt(v___x_810_, v___x_811_);
if (v___x_812_ == 0)
{
lean_dec(v_a_807_);
lean_dec_ref(v_inst_804_);
lean_dec_ref(v_inst_803_);
return v_inst_808_;
}
else
{
lean_object* v___x_813_; 
v___x_813_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(v_inst_803_, v_inst_804_, v_m_806_, v_a_807_, v_inst_808_);
return v___x_813_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x21___boxed(lean_object* v_00_u03b1_814_, lean_object* v_00_u03b2_815_, lean_object* v_inst_816_, lean_object* v_inst_817_, lean_object* v_inst_818_, lean_object* v_m_819_, lean_object* v_a_820_, lean_object* v_inst_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Std_DHashMap_Raw_get_x21(v_00_u03b1_814_, v_00_u03b2_815_, v_inst_816_, v_inst_817_, v_inst_818_, v_m_819_, v_a_820_, v_inst_821_);
lean_dec_ref(v_m_819_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_erase___redArg(lean_object* v_inst_823_, lean_object* v_inst_824_, lean_object* v_m_825_, lean_object* v_a_826_){
_start:
{
lean_object* v_buckets_827_; lean_object* v___x_828_; lean_object* v___x_829_; uint8_t v___x_830_; 
v_buckets_827_ = lean_ctor_get(v_m_825_, 1);
v___x_828_ = lean_unsigned_to_nat(0u);
v___x_829_ = lean_array_get_size(v_buckets_827_);
v___x_830_ = lean_nat_dec_lt(v___x_828_, v___x_829_);
if (v___x_830_ == 0)
{
lean_dec(v_a_826_);
lean_dec_ref(v_inst_824_);
lean_dec_ref(v_inst_823_);
return v_m_825_;
}
else
{
lean_object* v___x_831_; 
v___x_831_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_823_, v_inst_824_, v_m_825_, v_a_826_);
return v___x_831_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_erase(lean_object* v_00_u03b1_832_, lean_object* v_00_u03b2_833_, lean_object* v_inst_834_, lean_object* v_inst_835_, lean_object* v_m_836_, lean_object* v_a_837_){
_start:
{
lean_object* v_buckets_838_; lean_object* v___x_839_; lean_object* v___x_840_; uint8_t v___x_841_; 
v_buckets_838_ = lean_ctor_get(v_m_836_, 1);
v___x_839_ = lean_unsigned_to_nat(0u);
v___x_840_ = lean_array_get_size(v_buckets_838_);
v___x_841_ = lean_nat_dec_lt(v___x_839_, v___x_840_);
if (v___x_841_ == 0)
{
lean_dec(v_a_837_);
lean_dec_ref(v_inst_835_);
lean_dec_ref(v_inst_834_);
return v_m_836_;
}
else
{
lean_object* v___x_842_; 
v___x_842_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_834_, v_inst_835_, v_m_836_, v_a_837_);
return v___x_842_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x3f___redArg(lean_object* v_inst_843_, lean_object* v_inst_844_, lean_object* v_m_845_, lean_object* v_a_846_){
_start:
{
lean_object* v_buckets_847_; lean_object* v___x_848_; lean_object* v___x_849_; uint8_t v___x_850_; 
v_buckets_847_ = lean_ctor_get(v_m_845_, 1);
v___x_848_ = lean_unsigned_to_nat(0u);
v___x_849_ = lean_array_get_size(v_buckets_847_);
v___x_850_ = lean_nat_dec_lt(v___x_848_, v___x_849_);
if (v___x_850_ == 0)
{
lean_object* v___x_851_; 
lean_dec(v_a_846_);
lean_dec_ref(v_inst_844_);
lean_dec_ref(v_inst_843_);
v___x_851_ = lean_box(0);
return v___x_851_;
}
else
{
lean_object* v___x_852_; 
v___x_852_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_843_, v_inst_844_, v_m_845_, v_a_846_);
return v___x_852_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x3f___redArg___boxed(lean_object* v_inst_853_, lean_object* v_inst_854_, lean_object* v_m_855_, lean_object* v_a_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Std_DHashMap_Raw_Const_get_x3f___redArg(v_inst_853_, v_inst_854_, v_m_855_, v_a_856_);
lean_dec_ref(v_m_855_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x3f(lean_object* v_00_u03b1_858_, lean_object* v_00_u03b2_859_, lean_object* v_inst_860_, lean_object* v_inst_861_, lean_object* v_m_862_, lean_object* v_a_863_){
_start:
{
lean_object* v_buckets_864_; lean_object* v___x_865_; lean_object* v___x_866_; uint8_t v___x_867_; 
v_buckets_864_ = lean_ctor_get(v_m_862_, 1);
v___x_865_ = lean_unsigned_to_nat(0u);
v___x_866_ = lean_array_get_size(v_buckets_864_);
v___x_867_ = lean_nat_dec_lt(v___x_865_, v___x_866_);
if (v___x_867_ == 0)
{
lean_object* v___x_868_; 
lean_dec(v_a_863_);
lean_dec_ref(v_inst_861_);
lean_dec_ref(v_inst_860_);
v___x_868_ = lean_box(0);
return v___x_868_;
}
else
{
lean_object* v___x_869_; 
v___x_869_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_860_, v_inst_861_, v_m_862_, v_a_863_);
return v___x_869_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x3f___boxed(lean_object* v_00_u03b1_870_, lean_object* v_00_u03b2_871_, lean_object* v_inst_872_, lean_object* v_inst_873_, lean_object* v_m_874_, lean_object* v_a_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Std_DHashMap_Raw_Const_get_x3f(v_00_u03b1_870_, v_00_u03b2_871_, v_inst_872_, v_inst_873_, v_m_874_, v_a_875_);
lean_dec_ref(v_m_874_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get___redArg(lean_object* v_inst_877_, lean_object* v_inst_878_, lean_object* v_m_879_, lean_object* v_a_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_877_, v_inst_878_, v_m_879_, v_a_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get___redArg___boxed(lean_object* v_inst_882_, lean_object* v_inst_883_, lean_object* v_m_884_, lean_object* v_a_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Std_DHashMap_Raw_Const_get___redArg(v_inst_882_, v_inst_883_, v_m_884_, v_a_885_);
lean_dec_ref(v_m_884_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get(lean_object* v_00_u03b1_887_, lean_object* v_00_u03b2_888_, lean_object* v_inst_889_, lean_object* v_inst_890_, lean_object* v_m_891_, lean_object* v_a_892_, lean_object* v_h_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_889_, v_inst_890_, v_m_891_, v_a_892_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get___boxed(lean_object* v_00_u03b1_895_, lean_object* v_00_u03b2_896_, lean_object* v_inst_897_, lean_object* v_inst_898_, lean_object* v_m_899_, lean_object* v_a_900_, lean_object* v_h_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Std_DHashMap_Raw_Const_get(v_00_u03b1_895_, v_00_u03b2_896_, v_inst_897_, v_inst_898_, v_m_899_, v_a_900_, v_h_901_);
lean_dec_ref(v_m_899_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getD___redArg(lean_object* v_inst_903_, lean_object* v_inst_904_, lean_object* v_m_905_, lean_object* v_a_906_, lean_object* v_fallback_907_){
_start:
{
lean_object* v_buckets_908_; lean_object* v___x_909_; lean_object* v___x_910_; uint8_t v___x_911_; 
v_buckets_908_ = lean_ctor_get(v_m_905_, 1);
v___x_909_ = lean_unsigned_to_nat(0u);
v___x_910_ = lean_array_get_size(v_buckets_908_);
v___x_911_ = lean_nat_dec_lt(v___x_909_, v___x_910_);
if (v___x_911_ == 0)
{
lean_dec(v_a_906_);
lean_dec_ref(v_inst_904_);
lean_dec_ref(v_inst_903_);
lean_inc(v_fallback_907_);
return v_fallback_907_;
}
else
{
lean_object* v___x_912_; 
v___x_912_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_inst_903_, v_inst_904_, v_m_905_, v_a_906_, v_fallback_907_);
return v___x_912_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getD___redArg___boxed(lean_object* v_inst_913_, lean_object* v_inst_914_, lean_object* v_m_915_, lean_object* v_a_916_, lean_object* v_fallback_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_Std_DHashMap_Raw_Const_getD___redArg(v_inst_913_, v_inst_914_, v_m_915_, v_a_916_, v_fallback_917_);
lean_dec(v_fallback_917_);
lean_dec_ref(v_m_915_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getD(lean_object* v_00_u03b1_919_, lean_object* v_00_u03b2_920_, lean_object* v_inst_921_, lean_object* v_inst_922_, lean_object* v_m_923_, lean_object* v_a_924_, lean_object* v_fallback_925_){
_start:
{
lean_object* v_buckets_926_; lean_object* v___x_927_; lean_object* v___x_928_; uint8_t v___x_929_; 
v_buckets_926_ = lean_ctor_get(v_m_923_, 1);
v___x_927_ = lean_unsigned_to_nat(0u);
v___x_928_ = lean_array_get_size(v_buckets_926_);
v___x_929_ = lean_nat_dec_lt(v___x_927_, v___x_928_);
if (v___x_929_ == 0)
{
lean_dec(v_a_924_);
lean_dec_ref(v_inst_922_);
lean_dec_ref(v_inst_921_);
lean_inc(v_fallback_925_);
return v_fallback_925_;
}
else
{
lean_object* v___x_930_; 
v___x_930_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_inst_921_, v_inst_922_, v_m_923_, v_a_924_, v_fallback_925_);
return v___x_930_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getD___boxed(lean_object* v_00_u03b1_931_, lean_object* v_00_u03b2_932_, lean_object* v_inst_933_, lean_object* v_inst_934_, lean_object* v_m_935_, lean_object* v_a_936_, lean_object* v_fallback_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Std_DHashMap_Raw_Const_getD(v_00_u03b1_931_, v_00_u03b2_932_, v_inst_933_, v_inst_934_, v_m_935_, v_a_936_, v_fallback_937_);
lean_dec(v_fallback_937_);
lean_dec_ref(v_m_935_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x21___redArg(lean_object* v_inst_939_, lean_object* v_inst_940_, lean_object* v_inst_941_, lean_object* v_m_942_, lean_object* v_a_943_){
_start:
{
lean_object* v_buckets_944_; lean_object* v___x_945_; lean_object* v___x_946_; uint8_t v___x_947_; 
v_buckets_944_ = lean_ctor_get(v_m_942_, 1);
v___x_945_ = lean_unsigned_to_nat(0u);
v___x_946_ = lean_array_get_size(v_buckets_944_);
v___x_947_ = lean_nat_dec_lt(v___x_945_, v___x_946_);
if (v___x_947_ == 0)
{
lean_dec(v_a_943_);
lean_dec_ref(v_inst_940_);
lean_dec_ref(v_inst_939_);
return v_inst_941_;
}
else
{
lean_object* v___x_948_; 
v___x_948_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_939_, v_inst_940_, v_inst_941_, v_m_942_, v_a_943_);
return v___x_948_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x21___redArg___boxed(lean_object* v_inst_949_, lean_object* v_inst_950_, lean_object* v_inst_951_, lean_object* v_m_952_, lean_object* v_a_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Std_DHashMap_Raw_Const_get_x21___redArg(v_inst_949_, v_inst_950_, v_inst_951_, v_m_952_, v_a_953_);
lean_dec_ref(v_m_952_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x21(lean_object* v_00_u03b1_955_, lean_object* v_00_u03b2_956_, lean_object* v_inst_957_, lean_object* v_inst_958_, lean_object* v_inst_959_, lean_object* v_m_960_, lean_object* v_a_961_){
_start:
{
lean_object* v_buckets_962_; lean_object* v___x_963_; lean_object* v___x_964_; uint8_t v___x_965_; 
v_buckets_962_ = lean_ctor_get(v_m_960_, 1);
v___x_963_ = lean_unsigned_to_nat(0u);
v___x_964_ = lean_array_get_size(v_buckets_962_);
v___x_965_ = lean_nat_dec_lt(v___x_963_, v___x_964_);
if (v___x_965_ == 0)
{
lean_dec(v_a_961_);
lean_dec_ref(v_inst_958_);
lean_dec_ref(v_inst_957_);
return v_inst_959_;
}
else
{
lean_object* v___x_966_; 
v___x_966_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_957_, v_inst_958_, v_inst_959_, v_m_960_, v_a_961_);
return v___x_966_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x21___boxed(lean_object* v_00_u03b1_967_, lean_object* v_00_u03b2_968_, lean_object* v_inst_969_, lean_object* v_inst_970_, lean_object* v_inst_971_, lean_object* v_m_972_, lean_object* v_a_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Std_DHashMap_Raw_Const_get_x21(v_00_u03b1_967_, v_00_u03b2_968_, v_inst_969_, v_inst_970_, v_inst_971_, v_m_972_, v_a_973_);
lean_dec_ref(v_m_972_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getThenInsertIfNew_x3f___redArg(lean_object* v_inst_975_, lean_object* v_inst_976_, lean_object* v_m_977_, lean_object* v_a_978_, lean_object* v_b_979_){
_start:
{
lean_object* v_size_980_; lean_object* v_buckets_981_; lean_object* v___x_982_; lean_object* v___x_983_; uint8_t v___x_984_; 
v_size_980_ = lean_ctor_get(v_m_977_, 0);
v_buckets_981_ = lean_ctor_get(v_m_977_, 1);
v___x_982_ = lean_unsigned_to_nat(0u);
v___x_983_ = lean_array_get_size(v_buckets_981_);
v___x_984_ = lean_nat_dec_lt(v___x_982_, v___x_983_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; lean_object* v___x_986_; 
lean_dec(v_b_979_);
lean_dec(v_a_978_);
lean_dec_ref(v_inst_976_);
lean_dec_ref(v_inst_975_);
v___x_985_ = lean_box(0);
v___x_986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
lean_ctor_set(v___x_986_, 1, v_m_977_);
return v___x_986_;
}
else
{
lean_object* v___x_987_; uint64_t v___x_988_; uint64_t v___x_989_; uint64_t v___x_990_; uint64_t v___x_991_; uint64_t v_fold_992_; uint64_t v___x_993_; uint64_t v___x_994_; uint64_t v___x_995_; size_t v___x_996_; size_t v___x_997_; size_t v___x_998_; size_t v___x_999_; size_t v___x_1000_; lean_object* v_bkt_1001_; lean_object* v___x_1002_; 
lean_inc_ref(v_inst_976_);
lean_inc(v_a_978_);
v___x_987_ = lean_apply_1(v_inst_976_, v_a_978_);
v___x_988_ = 32ULL;
v___x_989_ = lean_unbox_uint64(v___x_987_);
v___x_990_ = lean_uint64_shift_right(v___x_989_, v___x_988_);
v___x_991_ = lean_unbox_uint64(v___x_987_);
lean_dec_ref(v___x_987_);
v_fold_992_ = lean_uint64_xor(v___x_991_, v___x_990_);
v___x_993_ = 16ULL;
v___x_994_ = lean_uint64_shift_right(v_fold_992_, v___x_993_);
v___x_995_ = lean_uint64_xor(v_fold_992_, v___x_994_);
v___x_996_ = lean_uint64_to_usize(v___x_995_);
v___x_997_ = lean_usize_of_nat(v___x_983_);
v___x_998_ = ((size_t)1ULL);
v___x_999_ = lean_usize_sub(v___x_997_, v___x_998_);
v___x_1000_ = lean_usize_land(v___x_996_, v___x_999_);
v_bkt_1001_ = lean_array_uget_borrowed(v_buckets_981_, v___x_1000_);
lean_inc(v_bkt_1001_);
lean_inc(v_a_978_);
v___x_1002_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_inst_975_, v_a_978_, v_bkt_1001_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1025_; 
lean_inc_ref(v_buckets_981_);
lean_inc(v_size_980_);
v_isSharedCheck_1025_ = !lean_is_exclusive(v_m_977_);
if (v_isSharedCheck_1025_ == 0)
{
lean_object* v_unused_1026_; lean_object* v_unused_1027_; 
v_unused_1026_ = lean_ctor_get(v_m_977_, 1);
lean_dec(v_unused_1026_);
v_unused_1027_ = lean_ctor_get(v_m_977_, 0);
lean_dec(v_unused_1027_);
v___x_1004_ = v_m_977_;
v_isShared_1005_ = v_isSharedCheck_1025_;
goto v_resetjp_1003_;
}
else
{
lean_dec(v_m_977_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1025_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1006_; lean_object* v_size_x27_1007_; lean_object* v___x_1008_; lean_object* v_buckets_x27_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; uint8_t v___x_1015_; 
v___x_1006_ = lean_unsigned_to_nat(1u);
v_size_x27_1007_ = lean_nat_add(v_size_980_, v___x_1006_);
lean_dec(v_size_980_);
lean_inc(v_bkt_1001_);
v___x_1008_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1008_, 0, v_a_978_);
lean_ctor_set(v___x_1008_, 1, v_b_979_);
lean_ctor_set(v___x_1008_, 2, v_bkt_1001_);
v_buckets_x27_1009_ = lean_array_uset(v_buckets_981_, v___x_1000_, v___x_1008_);
v___x_1010_ = lean_unsigned_to_nat(4u);
v___x_1011_ = lean_nat_mul(v_size_x27_1007_, v___x_1010_);
v___x_1012_ = lean_unsigned_to_nat(3u);
v___x_1013_ = lean_nat_div(v___x_1011_, v___x_1012_);
lean_dec(v___x_1011_);
v___x_1014_ = lean_array_get_size(v_buckets_x27_1009_);
v___x_1015_ = lean_nat_dec_le(v___x_1013_, v___x_1014_);
lean_dec(v___x_1013_);
if (v___x_1015_ == 0)
{
lean_object* v_val_1016_; lean_object* v___x_1018_; 
v_val_1016_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_976_, v_buckets_x27_1009_);
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 1, v_val_1016_);
lean_ctor_set(v___x_1004_, 0, v_size_x27_1007_);
v___x_1018_ = v___x_1004_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_size_x27_1007_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v_val_1016_);
v___x_1018_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
lean_object* v___x_1019_; 
v___x_1019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1002_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
return v___x_1019_;
}
}
else
{
lean_object* v___x_1022_; 
lean_dec_ref(v_inst_976_);
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 1, v_buckets_x27_1009_);
lean_ctor_set(v___x_1004_, 0, v_size_x27_1007_);
v___x_1022_ = v___x_1004_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_size_x27_1007_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v_buckets_x27_1009_);
v___x_1022_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
lean_object* v___x_1023_; 
v___x_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1002_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
return v___x_1023_;
}
}
}
}
else
{
lean_object* v___x_1028_; 
lean_dec(v_b_979_);
lean_dec(v_a_978_);
lean_dec_ref(v_inst_976_);
v___x_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1002_);
lean_ctor_set(v___x_1028_, 1, v_m_977_);
return v___x_1028_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_1029_, lean_object* v_00_u03b2_1030_, lean_object* v_inst_1031_, lean_object* v_inst_1032_, lean_object* v_m_1033_, lean_object* v_a_1034_, lean_object* v_b_1035_){
_start:
{
lean_object* v_size_1036_; lean_object* v_buckets_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; uint8_t v___x_1040_; 
v_size_1036_ = lean_ctor_get(v_m_1033_, 0);
v_buckets_1037_ = lean_ctor_get(v_m_1033_, 1);
v___x_1038_ = lean_unsigned_to_nat(0u);
v___x_1039_ = lean_array_get_size(v_buckets_1037_);
v___x_1040_ = lean_nat_dec_lt(v___x_1038_, v___x_1039_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
lean_dec(v_b_1035_);
lean_dec(v_a_1034_);
lean_dec_ref(v_inst_1032_);
lean_dec_ref(v_inst_1031_);
v___x_1041_ = lean_box(0);
v___x_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
lean_ctor_set(v___x_1042_, 1, v_m_1033_);
return v___x_1042_;
}
else
{
lean_object* v___x_1043_; uint64_t v___x_1044_; uint64_t v___x_1045_; uint64_t v___x_1046_; uint64_t v___x_1047_; uint64_t v_fold_1048_; uint64_t v___x_1049_; uint64_t v___x_1050_; uint64_t v___x_1051_; size_t v___x_1052_; size_t v___x_1053_; size_t v___x_1054_; size_t v___x_1055_; size_t v___x_1056_; lean_object* v_bkt_1057_; lean_object* v___x_1058_; 
lean_inc_ref(v_inst_1032_);
lean_inc(v_a_1034_);
v___x_1043_ = lean_apply_1(v_inst_1032_, v_a_1034_);
v___x_1044_ = 32ULL;
v___x_1045_ = lean_unbox_uint64(v___x_1043_);
v___x_1046_ = lean_uint64_shift_right(v___x_1045_, v___x_1044_);
v___x_1047_ = lean_unbox_uint64(v___x_1043_);
lean_dec_ref(v___x_1043_);
v_fold_1048_ = lean_uint64_xor(v___x_1047_, v___x_1046_);
v___x_1049_ = 16ULL;
v___x_1050_ = lean_uint64_shift_right(v_fold_1048_, v___x_1049_);
v___x_1051_ = lean_uint64_xor(v_fold_1048_, v___x_1050_);
v___x_1052_ = lean_uint64_to_usize(v___x_1051_);
v___x_1053_ = lean_usize_of_nat(v___x_1039_);
v___x_1054_ = ((size_t)1ULL);
v___x_1055_ = lean_usize_sub(v___x_1053_, v___x_1054_);
v___x_1056_ = lean_usize_land(v___x_1052_, v___x_1055_);
v_bkt_1057_ = lean_array_uget_borrowed(v_buckets_1037_, v___x_1056_);
lean_inc(v_bkt_1057_);
lean_inc(v_a_1034_);
v___x_1058_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_inst_1031_, v_a_1034_, v_bkt_1057_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1081_; 
lean_inc_ref(v_buckets_1037_);
lean_inc(v_size_1036_);
v_isSharedCheck_1081_ = !lean_is_exclusive(v_m_1033_);
if (v_isSharedCheck_1081_ == 0)
{
lean_object* v_unused_1082_; lean_object* v_unused_1083_; 
v_unused_1082_ = lean_ctor_get(v_m_1033_, 1);
lean_dec(v_unused_1082_);
v_unused_1083_ = lean_ctor_get(v_m_1033_, 0);
lean_dec(v_unused_1083_);
v___x_1060_ = v_m_1033_;
v_isShared_1061_ = v_isSharedCheck_1081_;
goto v_resetjp_1059_;
}
else
{
lean_dec(v_m_1033_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1081_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1062_; lean_object* v_size_x27_1063_; lean_object* v___x_1064_; lean_object* v_buckets_x27_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; uint8_t v___x_1071_; 
v___x_1062_ = lean_unsigned_to_nat(1u);
v_size_x27_1063_ = lean_nat_add(v_size_1036_, v___x_1062_);
lean_dec(v_size_1036_);
lean_inc(v_bkt_1057_);
v___x_1064_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1064_, 0, v_a_1034_);
lean_ctor_set(v___x_1064_, 1, v_b_1035_);
lean_ctor_set(v___x_1064_, 2, v_bkt_1057_);
v_buckets_x27_1065_ = lean_array_uset(v_buckets_1037_, v___x_1056_, v___x_1064_);
v___x_1066_ = lean_unsigned_to_nat(4u);
v___x_1067_ = lean_nat_mul(v_size_x27_1063_, v___x_1066_);
v___x_1068_ = lean_unsigned_to_nat(3u);
v___x_1069_ = lean_nat_div(v___x_1067_, v___x_1068_);
lean_dec(v___x_1067_);
v___x_1070_ = lean_array_get_size(v_buckets_x27_1065_);
v___x_1071_ = lean_nat_dec_le(v___x_1069_, v___x_1070_);
lean_dec(v___x_1069_);
if (v___x_1071_ == 0)
{
lean_object* v_val_1072_; lean_object* v___x_1074_; 
v_val_1072_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1032_, v_buckets_x27_1065_);
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 1, v_val_1072_);
lean_ctor_set(v___x_1060_, 0, v_size_x27_1063_);
v___x_1074_ = v___x_1060_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_size_x27_1063_);
lean_ctor_set(v_reuseFailAlloc_1076_, 1, v_val_1072_);
v___x_1074_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
lean_object* v___x_1075_; 
v___x_1075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1058_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
return v___x_1075_;
}
}
else
{
lean_object* v___x_1078_; 
lean_dec_ref(v_inst_1032_);
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 1, v_buckets_x27_1065_);
lean_ctor_set(v___x_1060_, 0, v_size_x27_1063_);
v___x_1078_ = v___x_1060_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_size_x27_1063_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v_buckets_x27_1065_);
v___x_1078_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
lean_object* v___x_1079_; 
v___x_1079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1058_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
return v___x_1079_;
}
}
}
}
else
{
lean_object* v___x_1084_; 
lean_dec(v_b_1035_);
lean_dec(v_a_1034_);
lean_dec_ref(v_inst_1032_);
v___x_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1058_);
lean_ctor_set(v___x_1084_, 1, v_m_1033_);
return v___x_1084_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x3f___redArg(lean_object* v_inst_1085_, lean_object* v_inst_1086_, lean_object* v_m_1087_, lean_object* v_a_1088_){
_start:
{
lean_object* v_buckets_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; uint8_t v___x_1092_; 
v_buckets_1089_ = lean_ctor_get(v_m_1087_, 1);
v___x_1090_ = lean_unsigned_to_nat(0u);
v___x_1091_ = lean_array_get_size(v_buckets_1089_);
v___x_1092_ = lean_nat_dec_lt(v___x_1090_, v___x_1091_);
if (v___x_1092_ == 0)
{
lean_object* v___x_1093_; 
lean_dec(v_a_1088_);
lean_dec_ref(v_inst_1086_);
lean_dec_ref(v_inst_1085_);
v___x_1093_ = lean_box(0);
return v___x_1093_;
}
else
{
lean_object* v___x_1094_; 
v___x_1094_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_1085_, v_inst_1086_, v_m_1087_, v_a_1088_);
return v___x_1094_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x3f___redArg___boxed(lean_object* v_inst_1095_, lean_object* v_inst_1096_, lean_object* v_m_1097_, lean_object* v_a_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Std_DHashMap_Raw_getKey_x3f___redArg(v_inst_1095_, v_inst_1096_, v_m_1097_, v_a_1098_);
lean_dec_ref(v_m_1097_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x3f(lean_object* v_00_u03b1_1100_, lean_object* v_00_u03b2_1101_, lean_object* v_inst_1102_, lean_object* v_inst_1103_, lean_object* v_m_1104_, lean_object* v_a_1105_){
_start:
{
lean_object* v_buckets_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; uint8_t v___x_1109_; 
v_buckets_1106_ = lean_ctor_get(v_m_1104_, 1);
v___x_1107_ = lean_unsigned_to_nat(0u);
v___x_1108_ = lean_array_get_size(v_buckets_1106_);
v___x_1109_ = lean_nat_dec_lt(v___x_1107_, v___x_1108_);
if (v___x_1109_ == 0)
{
lean_object* v___x_1110_; 
lean_dec(v_a_1105_);
lean_dec_ref(v_inst_1103_);
lean_dec_ref(v_inst_1102_);
v___x_1110_ = lean_box(0);
return v___x_1110_;
}
else
{
lean_object* v___x_1111_; 
v___x_1111_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_1102_, v_inst_1103_, v_m_1104_, v_a_1105_);
return v___x_1111_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x3f___boxed(lean_object* v_00_u03b1_1112_, lean_object* v_00_u03b2_1113_, lean_object* v_inst_1114_, lean_object* v_inst_1115_, lean_object* v_m_1116_, lean_object* v_a_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l_Std_DHashMap_Raw_getKey_x3f(v_00_u03b1_1112_, v_00_u03b2_1113_, v_inst_1114_, v_inst_1115_, v_m_1116_, v_a_1117_);
lean_dec_ref(v_m_1116_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey___redArg(lean_object* v_inst_1119_, lean_object* v_inst_1120_, lean_object* v_m_1121_, lean_object* v_a_1122_){
_start:
{
lean_object* v___x_1123_; 
v___x_1123_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_1119_, v_inst_1120_, v_m_1121_, v_a_1122_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey___redArg___boxed(lean_object* v_inst_1124_, lean_object* v_inst_1125_, lean_object* v_m_1126_, lean_object* v_a_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_Std_DHashMap_Raw_getKey___redArg(v_inst_1124_, v_inst_1125_, v_m_1126_, v_a_1127_);
lean_dec_ref(v_m_1126_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey(lean_object* v_00_u03b1_1129_, lean_object* v_00_u03b2_1130_, lean_object* v_inst_1131_, lean_object* v_inst_1132_, lean_object* v_m_1133_, lean_object* v_a_1134_, lean_object* v_h_1135_){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_1131_, v_inst_1132_, v_m_1133_, v_a_1134_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey___boxed(lean_object* v_00_u03b1_1137_, lean_object* v_00_u03b2_1138_, lean_object* v_inst_1139_, lean_object* v_inst_1140_, lean_object* v_m_1141_, lean_object* v_a_1142_, lean_object* v_h_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Std_DHashMap_Raw_getKey(v_00_u03b1_1137_, v_00_u03b2_1138_, v_inst_1139_, v_inst_1140_, v_m_1141_, v_a_1142_, v_h_1143_);
lean_dec_ref(v_m_1141_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKeyD___redArg(lean_object* v_inst_1145_, lean_object* v_inst_1146_, lean_object* v_m_1147_, lean_object* v_a_1148_, lean_object* v_fallback_1149_){
_start:
{
lean_object* v_buckets_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; uint8_t v___x_1153_; 
v_buckets_1150_ = lean_ctor_get(v_m_1147_, 1);
v___x_1151_ = lean_unsigned_to_nat(0u);
v___x_1152_ = lean_array_get_size(v_buckets_1150_);
v___x_1153_ = lean_nat_dec_lt(v___x_1151_, v___x_1152_);
if (v___x_1153_ == 0)
{
lean_dec(v_a_1148_);
lean_dec_ref(v_inst_1146_);
lean_dec_ref(v_inst_1145_);
lean_inc(v_fallback_1149_);
return v_fallback_1149_;
}
else
{
lean_object* v___x_1154_; 
v___x_1154_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_1145_, v_inst_1146_, v_m_1147_, v_a_1148_, v_fallback_1149_);
return v___x_1154_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKeyD___redArg___boxed(lean_object* v_inst_1155_, lean_object* v_inst_1156_, lean_object* v_m_1157_, lean_object* v_a_1158_, lean_object* v_fallback_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l_Std_DHashMap_Raw_getKeyD___redArg(v_inst_1155_, v_inst_1156_, v_m_1157_, v_a_1158_, v_fallback_1159_);
lean_dec(v_fallback_1159_);
lean_dec_ref(v_m_1157_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKeyD(lean_object* v_00_u03b1_1161_, lean_object* v_00_u03b2_1162_, lean_object* v_inst_1163_, lean_object* v_inst_1164_, lean_object* v_m_1165_, lean_object* v_a_1166_, lean_object* v_fallback_1167_){
_start:
{
lean_object* v_buckets_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; uint8_t v___x_1171_; 
v_buckets_1168_ = lean_ctor_get(v_m_1165_, 1);
v___x_1169_ = lean_unsigned_to_nat(0u);
v___x_1170_ = lean_array_get_size(v_buckets_1168_);
v___x_1171_ = lean_nat_dec_lt(v___x_1169_, v___x_1170_);
if (v___x_1171_ == 0)
{
lean_dec(v_a_1166_);
lean_dec_ref(v_inst_1164_);
lean_dec_ref(v_inst_1163_);
lean_inc(v_fallback_1167_);
return v_fallback_1167_;
}
else
{
lean_object* v___x_1172_; 
v___x_1172_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_1163_, v_inst_1164_, v_m_1165_, v_a_1166_, v_fallback_1167_);
return v___x_1172_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKeyD___boxed(lean_object* v_00_u03b1_1173_, lean_object* v_00_u03b2_1174_, lean_object* v_inst_1175_, lean_object* v_inst_1176_, lean_object* v_m_1177_, lean_object* v_a_1178_, lean_object* v_fallback_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l_Std_DHashMap_Raw_getKeyD(v_00_u03b1_1173_, v_00_u03b2_1174_, v_inst_1175_, v_inst_1176_, v_m_1177_, v_a_1178_, v_fallback_1179_);
lean_dec(v_fallback_1179_);
lean_dec_ref(v_m_1177_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x21___redArg(lean_object* v_inst_1181_, lean_object* v_inst_1182_, lean_object* v_inst_1183_, lean_object* v_m_1184_, lean_object* v_a_1185_){
_start:
{
lean_object* v_buckets_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; uint8_t v___x_1189_; 
v_buckets_1186_ = lean_ctor_get(v_m_1184_, 1);
v___x_1187_ = lean_unsigned_to_nat(0u);
v___x_1188_ = lean_array_get_size(v_buckets_1186_);
v___x_1189_ = lean_nat_dec_lt(v___x_1187_, v___x_1188_);
if (v___x_1189_ == 0)
{
lean_dec(v_a_1185_);
lean_dec_ref(v_inst_1182_);
lean_dec_ref(v_inst_1181_);
return v_inst_1183_;
}
else
{
lean_object* v___x_1190_; 
v___x_1190_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_1181_, v_inst_1182_, v_inst_1183_, v_m_1184_, v_a_1185_);
return v___x_1190_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x21___redArg___boxed(lean_object* v_inst_1191_, lean_object* v_inst_1192_, lean_object* v_inst_1193_, lean_object* v_m_1194_, lean_object* v_a_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_Std_DHashMap_Raw_getKey_x21___redArg(v_inst_1191_, v_inst_1192_, v_inst_1193_, v_m_1194_, v_a_1195_);
lean_dec_ref(v_m_1194_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x21(lean_object* v_00_u03b1_1197_, lean_object* v_00_u03b2_1198_, lean_object* v_inst_1199_, lean_object* v_inst_1200_, lean_object* v_inst_1201_, lean_object* v_m_1202_, lean_object* v_a_1203_){
_start:
{
lean_object* v_buckets_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; uint8_t v___x_1207_; 
v_buckets_1204_ = lean_ctor_get(v_m_1202_, 1);
v___x_1205_ = lean_unsigned_to_nat(0u);
v___x_1206_ = lean_array_get_size(v_buckets_1204_);
v___x_1207_ = lean_nat_dec_lt(v___x_1205_, v___x_1206_);
if (v___x_1207_ == 0)
{
lean_dec(v_a_1203_);
lean_dec_ref(v_inst_1200_);
lean_dec_ref(v_inst_1199_);
return v_inst_1201_;
}
else
{
lean_object* v___x_1208_; 
v___x_1208_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_1199_, v_inst_1200_, v_inst_1201_, v_m_1202_, v_a_1203_);
return v___x_1208_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x21___boxed(lean_object* v_00_u03b1_1209_, lean_object* v_00_u03b2_1210_, lean_object* v_inst_1211_, lean_object* v_inst_1212_, lean_object* v_inst_1213_, lean_object* v_m_1214_, lean_object* v_a_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_Std_DHashMap_Raw_getKey_x21(v_00_u03b1_1209_, v_00_u03b2_1210_, v_inst_1211_, v_inst_1212_, v_inst_1213_, v_m_1214_, v_a_1215_);
lean_dec_ref(v_m_1214_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x3f___redArg(lean_object* v_inst_1217_, lean_object* v_inst_1218_, lean_object* v_m_1219_, lean_object* v_a_1220_){
_start:
{
lean_object* v_buckets_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; uint8_t v___x_1224_; 
v_buckets_1221_ = lean_ctor_get(v_m_1219_, 1);
v___x_1222_ = lean_unsigned_to_nat(0u);
v___x_1223_ = lean_array_get_size(v_buckets_1221_);
v___x_1224_ = lean_nat_dec_lt(v___x_1222_, v___x_1223_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; 
lean_dec(v_a_1220_);
lean_dec_ref(v_inst_1218_);
lean_dec_ref(v_inst_1217_);
v___x_1225_ = lean_box(0);
return v___x_1225_;
}
else
{
lean_object* v___x_1226_; 
v___x_1226_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(v_inst_1217_, v_inst_1218_, v_m_1219_, v_a_1220_);
return v___x_1226_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x3f___redArg___boxed(lean_object* v_inst_1227_, lean_object* v_inst_1228_, lean_object* v_m_1229_, lean_object* v_a_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Std_DHashMap_Raw_getEntry_x3f___redArg(v_inst_1227_, v_inst_1228_, v_m_1229_, v_a_1230_);
lean_dec_ref(v_m_1229_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x3f(lean_object* v_00_u03b1_1232_, lean_object* v_00_u03b2_1233_, lean_object* v_inst_1234_, lean_object* v_inst_1235_, lean_object* v_m_1236_, lean_object* v_a_1237_){
_start:
{
lean_object* v_buckets_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; uint8_t v___x_1241_; 
v_buckets_1238_ = lean_ctor_get(v_m_1236_, 1);
v___x_1239_ = lean_unsigned_to_nat(0u);
v___x_1240_ = lean_array_get_size(v_buckets_1238_);
v___x_1241_ = lean_nat_dec_lt(v___x_1239_, v___x_1240_);
if (v___x_1241_ == 0)
{
lean_object* v___x_1242_; 
lean_dec(v_a_1237_);
lean_dec_ref(v_inst_1235_);
lean_dec_ref(v_inst_1234_);
v___x_1242_ = lean_box(0);
return v___x_1242_;
}
else
{
lean_object* v___x_1243_; 
v___x_1243_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(v_inst_1234_, v_inst_1235_, v_m_1236_, v_a_1237_);
return v___x_1243_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x3f___boxed(lean_object* v_00_u03b1_1244_, lean_object* v_00_u03b2_1245_, lean_object* v_inst_1246_, lean_object* v_inst_1247_, lean_object* v_m_1248_, lean_object* v_a_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Std_DHashMap_Raw_getEntry_x3f(v_00_u03b1_1244_, v_00_u03b2_1245_, v_inst_1246_, v_inst_1247_, v_m_1248_, v_a_1249_);
lean_dec_ref(v_m_1248_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry___redArg(lean_object* v_inst_1251_, lean_object* v_inst_1252_, lean_object* v_m_1253_, lean_object* v_a_1254_){
_start:
{
lean_object* v___x_1255_; 
v___x_1255_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg(v_inst_1251_, v_inst_1252_, v_m_1253_, v_a_1254_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry___redArg___boxed(lean_object* v_inst_1256_, lean_object* v_inst_1257_, lean_object* v_m_1258_, lean_object* v_a_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_Std_DHashMap_Raw_getEntry___redArg(v_inst_1256_, v_inst_1257_, v_m_1258_, v_a_1259_);
lean_dec_ref(v_m_1258_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry(lean_object* v_00_u03b1_1261_, lean_object* v_00_u03b2_1262_, lean_object* v_inst_1263_, lean_object* v_inst_1264_, lean_object* v_m_1265_, lean_object* v_a_1266_, lean_object* v_h_1267_){
_start:
{
lean_object* v___x_1268_; 
v___x_1268_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg(v_inst_1263_, v_inst_1264_, v_m_1265_, v_a_1266_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry___boxed(lean_object* v_00_u03b1_1269_, lean_object* v_00_u03b2_1270_, lean_object* v_inst_1271_, lean_object* v_inst_1272_, lean_object* v_m_1273_, lean_object* v_a_1274_, lean_object* v_h_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_Std_DHashMap_Raw_getEntry(v_00_u03b1_1269_, v_00_u03b2_1270_, v_inst_1271_, v_inst_1272_, v_m_1273_, v_a_1274_, v_h_1275_);
lean_dec_ref(v_m_1273_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntryD___redArg(lean_object* v_inst_1277_, lean_object* v_inst_1278_, lean_object* v_m_1279_, lean_object* v_a_1280_, lean_object* v_fallback_1281_){
_start:
{
lean_object* v_buckets_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; uint8_t v___x_1285_; 
v_buckets_1282_ = lean_ctor_get(v_m_1279_, 1);
v___x_1283_ = lean_unsigned_to_nat(0u);
v___x_1284_ = lean_array_get_size(v_buckets_1282_);
v___x_1285_ = lean_nat_dec_lt(v___x_1283_, v___x_1284_);
if (v___x_1285_ == 0)
{
lean_dec(v_a_1280_);
lean_dec_ref(v_inst_1278_);
lean_dec_ref(v_inst_1277_);
lean_inc_ref(v_fallback_1281_);
return v_fallback_1281_;
}
else
{
lean_object* v___x_1286_; 
v___x_1286_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD___redArg(v_inst_1277_, v_inst_1278_, v_m_1279_, v_a_1280_, v_fallback_1281_);
return v___x_1286_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntryD___redArg___boxed(lean_object* v_inst_1287_, lean_object* v_inst_1288_, lean_object* v_m_1289_, lean_object* v_a_1290_, lean_object* v_fallback_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l_Std_DHashMap_Raw_getEntryD___redArg(v_inst_1287_, v_inst_1288_, v_m_1289_, v_a_1290_, v_fallback_1291_);
lean_dec_ref(v_fallback_1291_);
lean_dec_ref(v_m_1289_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntryD(lean_object* v_00_u03b1_1293_, lean_object* v_00_u03b2_1294_, lean_object* v_inst_1295_, lean_object* v_inst_1296_, lean_object* v_m_1297_, lean_object* v_a_1298_, lean_object* v_fallback_1299_){
_start:
{
lean_object* v_buckets_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; uint8_t v___x_1303_; 
v_buckets_1300_ = lean_ctor_get(v_m_1297_, 1);
v___x_1301_ = lean_unsigned_to_nat(0u);
v___x_1302_ = lean_array_get_size(v_buckets_1300_);
v___x_1303_ = lean_nat_dec_lt(v___x_1301_, v___x_1302_);
if (v___x_1303_ == 0)
{
lean_dec(v_a_1298_);
lean_dec_ref(v_inst_1296_);
lean_dec_ref(v_inst_1295_);
lean_inc_ref(v_fallback_1299_);
return v_fallback_1299_;
}
else
{
lean_object* v___x_1304_; 
v___x_1304_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD___redArg(v_inst_1295_, v_inst_1296_, v_m_1297_, v_a_1298_, v_fallback_1299_);
return v___x_1304_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntryD___boxed(lean_object* v_00_u03b1_1305_, lean_object* v_00_u03b2_1306_, lean_object* v_inst_1307_, lean_object* v_inst_1308_, lean_object* v_m_1309_, lean_object* v_a_1310_, lean_object* v_fallback_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l_Std_DHashMap_Raw_getEntryD(v_00_u03b1_1305_, v_00_u03b2_1306_, v_inst_1307_, v_inst_1308_, v_m_1309_, v_a_1310_, v_fallback_1311_);
lean_dec_ref(v_fallback_1311_);
lean_dec_ref(v_m_1309_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x21___redArg(lean_object* v_inst_1313_, lean_object* v_inst_1314_, lean_object* v_inst_1315_, lean_object* v_m_1316_, lean_object* v_a_1317_){
_start:
{
lean_object* v_buckets_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; uint8_t v___x_1321_; 
v_buckets_1318_ = lean_ctor_get(v_m_1316_, 1);
v___x_1319_ = lean_unsigned_to_nat(0u);
v___x_1320_ = lean_array_get_size(v_buckets_1318_);
v___x_1321_ = lean_nat_dec_lt(v___x_1319_, v___x_1320_);
if (v___x_1321_ == 0)
{
lean_dec(v_a_1317_);
lean_dec_ref(v_inst_1314_);
lean_dec_ref(v_inst_1313_);
lean_inc_ref(v_inst_1315_);
return v_inst_1315_;
}
else
{
lean_object* v___x_1322_; 
v___x_1322_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___redArg(v_inst_1313_, v_inst_1314_, v_m_1316_, v_a_1317_, v_inst_1315_);
return v___x_1322_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x21___redArg___boxed(lean_object* v_inst_1323_, lean_object* v_inst_1324_, lean_object* v_inst_1325_, lean_object* v_m_1326_, lean_object* v_a_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l_Std_DHashMap_Raw_getEntry_x21___redArg(v_inst_1323_, v_inst_1324_, v_inst_1325_, v_m_1326_, v_a_1327_);
lean_dec_ref(v_m_1326_);
lean_dec_ref(v_inst_1325_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x21(lean_object* v_00_u03b1_1329_, lean_object* v_00_u03b2_1330_, lean_object* v_inst_1331_, lean_object* v_inst_1332_, lean_object* v_inst_1333_, lean_object* v_m_1334_, lean_object* v_a_1335_){
_start:
{
lean_object* v_buckets_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; uint8_t v___x_1339_; 
v_buckets_1336_ = lean_ctor_get(v_m_1334_, 1);
v___x_1337_ = lean_unsigned_to_nat(0u);
v___x_1338_ = lean_array_get_size(v_buckets_1336_);
v___x_1339_ = lean_nat_dec_lt(v___x_1337_, v___x_1338_);
if (v___x_1339_ == 0)
{
lean_dec(v_a_1335_);
lean_dec_ref(v_inst_1332_);
lean_dec_ref(v_inst_1331_);
lean_inc_ref(v_inst_1333_);
return v_inst_1333_;
}
else
{
lean_object* v___x_1340_; 
v___x_1340_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___redArg(v_inst_1331_, v_inst_1332_, v_m_1334_, v_a_1335_, v_inst_1333_);
return v___x_1340_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x21___boxed(lean_object* v_00_u03b1_1341_, lean_object* v_00_u03b2_1342_, lean_object* v_inst_1343_, lean_object* v_inst_1344_, lean_object* v_inst_1345_, lean_object* v_m_1346_, lean_object* v_a_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_Std_DHashMap_Raw_getEntry_x21(v_00_u03b1_1341_, v_00_u03b2_1342_, v_inst_1343_, v_inst_1344_, v_inst_1345_, v_m_1346_, v_a_1347_);
lean_dec_ref(v_m_1346_);
lean_dec_ref(v_inst_1345_);
return v_res_1348_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_isEmpty___redArg(lean_object* v_m_1349_){
_start:
{
lean_object* v_size_1350_; lean_object* v___x_1351_; uint8_t v___x_1352_; 
v_size_1350_ = lean_ctor_get(v_m_1349_, 0);
v___x_1351_ = lean_unsigned_to_nat(0u);
v___x_1352_ = lean_nat_dec_eq(v_size_1350_, v___x_1351_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_isEmpty___redArg___boxed(lean_object* v_m_1353_){
_start:
{
uint8_t v_res_1354_; lean_object* v_r_1355_; 
v_res_1354_ = l_Std_DHashMap_Raw_isEmpty___redArg(v_m_1353_);
lean_dec_ref(v_m_1353_);
v_r_1355_ = lean_box(v_res_1354_);
return v_r_1355_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_isEmpty(lean_object* v_00_u03b1_1356_, lean_object* v_00_u03b2_1357_, lean_object* v_m_1358_){
_start:
{
lean_object* v_size_1359_; lean_object* v___x_1360_; uint8_t v___x_1361_; 
v_size_1359_ = lean_ctor_get(v_m_1358_, 0);
v___x_1360_ = lean_unsigned_to_nat(0u);
v___x_1361_ = lean_nat_dec_eq(v_size_1359_, v___x_1360_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_isEmpty___boxed(lean_object* v_00_u03b1_1362_, lean_object* v_00_u03b2_1363_, lean_object* v_m_1364_){
_start:
{
uint8_t v_res_1365_; lean_object* v_r_1366_; 
v_res_1365_ = l_Std_DHashMap_Raw_isEmpty(v_00_u03b1_1362_, v_00_u03b2_1363_, v_m_1364_);
lean_dec_ref(v_m_1364_);
v_r_1366_ = lean_box(v_res_1365_);
return v_r_1366_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_modify___redArg(lean_object* v_inst_1367_, lean_object* v_inst_1368_, lean_object* v_m_1369_, lean_object* v_a_1370_, lean_object* v_f_1371_){
_start:
{
lean_object* v_buckets_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; uint8_t v___x_1375_; 
v_buckets_1372_ = lean_ctor_get(v_m_1369_, 1);
v___x_1373_ = lean_unsigned_to_nat(0u);
v___x_1374_ = lean_array_get_size(v_buckets_1372_);
v___x_1375_ = lean_nat_dec_lt(v___x_1373_, v___x_1374_);
if (v___x_1375_ == 0)
{
lean_object* v___x_1376_; 
lean_dec(v_f_1371_);
lean_dec(v_a_1370_);
lean_dec_ref(v_m_1369_);
lean_dec_ref(v_inst_1368_);
lean_dec_ref(v_inst_1367_);
v___x_1376_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_1376_;
}
else
{
lean_object* v___x_1377_; 
v___x_1377_ = l_Std_DHashMap_Internal_Raw_u2080_modify___redArg(v_inst_1367_, v_inst_1368_, v_m_1369_, v_a_1370_, v_f_1371_);
return v___x_1377_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_modify(lean_object* v_00_u03b1_1378_, lean_object* v_00_u03b2_1379_, lean_object* v_inst_1380_, lean_object* v_inst_1381_, lean_object* v_inst_1382_, lean_object* v_m_1383_, lean_object* v_a_1384_, lean_object* v_f_1385_){
_start:
{
lean_object* v_buckets_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; uint8_t v___x_1389_; 
v_buckets_1386_ = lean_ctor_get(v_m_1383_, 1);
v___x_1387_ = lean_unsigned_to_nat(0u);
v___x_1388_ = lean_array_get_size(v_buckets_1386_);
v___x_1389_ = lean_nat_dec_lt(v___x_1387_, v___x_1388_);
if (v___x_1389_ == 0)
{
lean_object* v___x_1390_; 
lean_dec(v_f_1385_);
lean_dec(v_a_1384_);
lean_dec_ref(v_m_1383_);
lean_dec_ref(v_inst_1382_);
lean_dec_ref(v_inst_1380_);
v___x_1390_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_1390_;
}
else
{
lean_object* v___x_1391_; 
v___x_1391_ = l_Std_DHashMap_Internal_Raw_u2080_modify___redArg(v_inst_1380_, v_inst_1382_, v_m_1383_, v_a_1384_, v_f_1385_);
return v___x_1391_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_modify___redArg(lean_object* v_inst_1392_, lean_object* v_inst_1393_, lean_object* v_m_1394_, lean_object* v_a_1395_, lean_object* v_f_1396_){
_start:
{
lean_object* v_buckets_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; uint8_t v___x_1400_; 
v_buckets_1397_ = lean_ctor_get(v_m_1394_, 1);
v___x_1398_ = lean_unsigned_to_nat(0u);
v___x_1399_ = lean_array_get_size(v_buckets_1397_);
v___x_1400_ = lean_nat_dec_lt(v___x_1398_, v___x_1399_);
if (v___x_1400_ == 0)
{
lean_object* v___x_1401_; 
lean_dec(v_f_1396_);
lean_dec(v_a_1395_);
lean_dec_ref(v_m_1394_);
lean_dec_ref(v_inst_1393_);
lean_dec_ref(v_inst_1392_);
v___x_1401_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_1401_;
}
else
{
lean_object* v___x_1402_; 
v___x_1402_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_inst_1392_, v_inst_1393_, v_m_1394_, v_a_1395_, v_f_1396_);
return v___x_1402_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_modify(lean_object* v_00_u03b1_1403_, lean_object* v_inst_1404_, lean_object* v_inst_1405_, lean_object* v_inst_1406_, lean_object* v_00_u03b2_1407_, lean_object* v_m_1408_, lean_object* v_a_1409_, lean_object* v_f_1410_){
_start:
{
lean_object* v_buckets_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; uint8_t v___x_1414_; 
v_buckets_1411_ = lean_ctor_get(v_m_1408_, 1);
v___x_1412_ = lean_unsigned_to_nat(0u);
v___x_1413_ = lean_array_get_size(v_buckets_1411_);
v___x_1414_ = lean_nat_dec_lt(v___x_1412_, v___x_1413_);
if (v___x_1414_ == 0)
{
lean_object* v___x_1415_; 
lean_dec(v_f_1410_);
lean_dec(v_a_1409_);
lean_dec_ref(v_m_1408_);
lean_dec_ref(v_inst_1406_);
lean_dec_ref(v_inst_1404_);
v___x_1415_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_1415_;
}
else
{
lean_object* v___x_1416_; 
v___x_1416_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_inst_1404_, v_inst_1406_, v_m_1408_, v_a_1409_, v_f_1410_);
return v___x_1416_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_alter___redArg(lean_object* v_inst_1417_, lean_object* v_inst_1418_, lean_object* v_m_1419_, lean_object* v_a_1420_, lean_object* v_f_1421_){
_start:
{
lean_object* v_buckets_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; uint8_t v___x_1425_; 
v_buckets_1422_ = lean_ctor_get(v_m_1419_, 1);
v___x_1423_ = lean_unsigned_to_nat(0u);
v___x_1424_ = lean_array_get_size(v_buckets_1422_);
v___x_1425_ = lean_nat_dec_lt(v___x_1423_, v___x_1424_);
if (v___x_1425_ == 0)
{
lean_object* v___x_1426_; 
lean_dec_ref(v_f_1421_);
lean_dec(v_a_1420_);
lean_dec_ref(v_m_1419_);
lean_dec_ref(v_inst_1418_);
lean_dec_ref(v_inst_1417_);
v___x_1426_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_1426_;
}
else
{
lean_object* v___x_1427_; 
v___x_1427_ = l_Std_DHashMap_Internal_Raw_u2080_alter___redArg(v_inst_1417_, v_inst_1418_, v_m_1419_, v_a_1420_, v_f_1421_);
return v___x_1427_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_alter(lean_object* v_00_u03b1_1428_, lean_object* v_00_u03b2_1429_, lean_object* v_inst_1430_, lean_object* v_inst_1431_, lean_object* v_inst_1432_, lean_object* v_m_1433_, lean_object* v_a_1434_, lean_object* v_f_1435_){
_start:
{
lean_object* v_buckets_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; uint8_t v___x_1439_; 
v_buckets_1436_ = lean_ctor_get(v_m_1433_, 1);
v___x_1437_ = lean_unsigned_to_nat(0u);
v___x_1438_ = lean_array_get_size(v_buckets_1436_);
v___x_1439_ = lean_nat_dec_lt(v___x_1437_, v___x_1438_);
if (v___x_1439_ == 0)
{
lean_object* v___x_1440_; 
lean_dec_ref(v_f_1435_);
lean_dec(v_a_1434_);
lean_dec_ref(v_m_1433_);
lean_dec_ref(v_inst_1432_);
lean_dec_ref(v_inst_1430_);
v___x_1440_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_1440_;
}
else
{
lean_object* v___x_1441_; 
v___x_1441_ = l_Std_DHashMap_Internal_Raw_u2080_alter___redArg(v_inst_1430_, v_inst_1432_, v_m_1433_, v_a_1434_, v_f_1435_);
return v___x_1441_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_alter___redArg(lean_object* v_inst_1442_, lean_object* v_inst_1443_, lean_object* v_m_1444_, lean_object* v_a_1445_, lean_object* v_f_1446_){
_start:
{
lean_object* v_buckets_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; uint8_t v___x_1450_; 
v_buckets_1447_ = lean_ctor_get(v_m_1444_, 1);
v___x_1448_ = lean_unsigned_to_nat(0u);
v___x_1449_ = lean_array_get_size(v_buckets_1447_);
v___x_1450_ = lean_nat_dec_lt(v___x_1448_, v___x_1449_);
if (v___x_1450_ == 0)
{
lean_object* v___x_1451_; 
lean_dec_ref(v_f_1446_);
lean_dec(v_a_1445_);
lean_dec_ref(v_m_1444_);
lean_dec_ref(v_inst_1443_);
lean_dec_ref(v_inst_1442_);
v___x_1451_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_1451_;
}
else
{
lean_object* v___x_1452_; 
v___x_1452_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_1442_, v_inst_1443_, v_m_1444_, v_a_1445_, v_f_1446_);
return v___x_1452_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_alter(lean_object* v_00_u03b1_1453_, lean_object* v_inst_1454_, lean_object* v_inst_1455_, lean_object* v_inst_1456_, lean_object* v_00_u03b2_1457_, lean_object* v_m_1458_, lean_object* v_a_1459_, lean_object* v_f_1460_){
_start:
{
lean_object* v_buckets_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; uint8_t v___x_1464_; 
v_buckets_1461_ = lean_ctor_get(v_m_1458_, 1);
v___x_1462_ = lean_unsigned_to_nat(0u);
v___x_1463_ = lean_array_get_size(v_buckets_1461_);
v___x_1464_ = lean_nat_dec_lt(v___x_1462_, v___x_1463_);
if (v___x_1464_ == 0)
{
lean_object* v___x_1465_; 
lean_dec_ref(v_f_1460_);
lean_dec(v_a_1459_);
lean_dec_ref(v_m_1458_);
lean_dec_ref(v_inst_1456_);
lean_dec_ref(v_inst_1454_);
v___x_1465_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_1465_;
}
else
{
lean_object* v___x_1466_; 
v___x_1466_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_1454_, v_inst_1456_, v_m_1458_, v_a_1459_, v_f_1460_);
return v___x_1466_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0(lean_object* v_f_1467_, lean_object* v_a_1468_, lean_object* v_b_1469_, lean_object* v_d_1470_){
_start:
{
lean_object* v___x_1471_; 
v___x_1471_ = lean_apply_3(v_f_1467_, v_d_1470_, v_a_1468_, v_b_1469_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__1(lean_object* v_inst_1472_, lean_object* v___f_1473_, lean_object* v_l_1474_, lean_object* v_acc_1475_){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v_inst_1472_, v___f_1473_, v_acc_1475_, v_l_1474_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRevM___redArg(lean_object* v_inst_1477_, lean_object* v_f_1478_, lean_object* v_init_1479_, lean_object* v_b_1480_){
_start:
{
lean_object* v_buckets_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; uint8_t v___x_1484_; 
v_buckets_1481_ = lean_ctor_get(v_b_1480_, 1);
lean_inc_ref(v_buckets_1481_);
lean_dec_ref(v_b_1480_);
v___x_1482_ = lean_array_get_size(v_buckets_1481_);
v___x_1483_ = lean_unsigned_to_nat(0u);
v___x_1484_ = lean_nat_dec_lt(v___x_1483_, v___x_1482_);
if (v___x_1484_ == 0)
{
lean_object* v_toApplicative_1485_; lean_object* v_toPure_1486_; lean_object* v___x_1487_; 
lean_dec_ref(v_buckets_1481_);
lean_dec(v_f_1478_);
v_toApplicative_1485_ = lean_ctor_get(v_inst_1477_, 0);
lean_inc_ref(v_toApplicative_1485_);
lean_dec_ref(v_inst_1477_);
v_toPure_1486_ = lean_ctor_get(v_toApplicative_1485_, 1);
lean_inc(v_toPure_1486_);
lean_dec_ref(v_toApplicative_1485_);
v___x_1487_ = lean_apply_2(v_toPure_1486_, lean_box(0), v_init_1479_);
return v___x_1487_;
}
else
{
lean_object* v___f_1488_; lean_object* v___f_1489_; size_t v___x_1490_; size_t v___x_1491_; lean_object* v___x_1492_; 
v___f_1488_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1488_, 0, v_f_1478_);
lean_inc_ref(v_inst_1477_);
v___f_1489_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1489_, 0, v_inst_1477_);
lean_closure_set(v___f_1489_, 1, v___f_1488_);
v___x_1490_ = lean_usize_of_nat(v___x_1482_);
v___x_1491_ = ((size_t)0ULL);
v___x_1492_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1477_, v___f_1489_, v_buckets_1481_, v___x_1490_, v___x_1491_, v_init_1479_);
return v___x_1492_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRevM(lean_object* v_00_u03b1_1493_, lean_object* v_00_u03b2_1494_, lean_object* v_00_u03b4_1495_, lean_object* v_m_1496_, lean_object* v_inst_1497_, lean_object* v_f_1498_, lean_object* v_init_1499_, lean_object* v_b_1500_){
_start:
{
lean_object* v_buckets_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; uint8_t v___x_1504_; 
v_buckets_1501_ = lean_ctor_get(v_b_1500_, 1);
lean_inc_ref(v_buckets_1501_);
lean_dec_ref(v_b_1500_);
v___x_1502_ = lean_array_get_size(v_buckets_1501_);
v___x_1503_ = lean_unsigned_to_nat(0u);
v___x_1504_ = lean_nat_dec_lt(v___x_1503_, v___x_1502_);
if (v___x_1504_ == 0)
{
lean_object* v_toApplicative_1505_; lean_object* v_toPure_1506_; lean_object* v___x_1507_; 
lean_dec_ref(v_buckets_1501_);
lean_dec(v_f_1498_);
v_toApplicative_1505_ = lean_ctor_get(v_inst_1497_, 0);
lean_inc_ref(v_toApplicative_1505_);
lean_dec_ref(v_inst_1497_);
v_toPure_1506_ = lean_ctor_get(v_toApplicative_1505_, 1);
lean_inc(v_toPure_1506_);
lean_dec_ref(v_toApplicative_1505_);
v___x_1507_ = lean_apply_2(v_toPure_1506_, lean_box(0), v_init_1499_);
return v___x_1507_;
}
else
{
lean_object* v___f_1508_; lean_object* v___f_1509_; size_t v___x_1510_; size_t v___x_1511_; lean_object* v___x_1512_; 
v___f_1508_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1508_, 0, v_f_1498_);
lean_inc_ref(v_inst_1497_);
v___f_1509_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1509_, 0, v_inst_1497_);
lean_closure_set(v___f_1509_, 1, v___f_1508_);
v___x_1510_ = lean_usize_of_nat(v___x_1502_);
v___x_1511_ = ((size_t)0ULL);
v___x_1512_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1497_, v___f_1509_, v_buckets_1501_, v___x_1510_, v___x_1511_, v_init_1499_);
return v___x_1512_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRev___redArg___lam__1(lean_object* v___x_1513_, lean_object* v___f_1514_, lean_object* v_l_1515_, lean_object* v_acc_1516_){
_start:
{
lean_object* v___x_1517_; 
v___x_1517_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_1513_, v___f_1514_, v_acc_1516_, v_l_1515_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRev___redArg(lean_object* v_f_1537_, lean_object* v_init_1538_, lean_object* v_b_1539_){
_start:
{
lean_object* v___x_1540_; lean_object* v_buckets_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; uint8_t v___x_1544_; 
v___x_1540_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_1541_ = lean_ctor_get(v_b_1539_, 1);
lean_inc_ref(v_buckets_1541_);
lean_dec_ref(v_b_1539_);
v___x_1542_ = lean_array_get_size(v_buckets_1541_);
v___x_1543_ = lean_unsigned_to_nat(0u);
v___x_1544_ = lean_nat_dec_lt(v___x_1543_, v___x_1542_);
if (v___x_1544_ == 0)
{
lean_dec_ref(v_buckets_1541_);
lean_dec(v_f_1537_);
return v_init_1538_;
}
else
{
lean_object* v___f_1545_; lean_object* v___f_1546_; size_t v___x_1547_; size_t v___x_1548_; lean_object* v___x_1549_; 
v___f_1545_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1545_, 0, v_f_1537_);
v___f_1546_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1546_, 0, v___x_1540_);
lean_closure_set(v___f_1546_, 1, v___f_1545_);
v___x_1547_ = lean_usize_of_nat(v___x_1542_);
v___x_1548_ = ((size_t)0ULL);
v___x_1549_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1540_, v___f_1546_, v_buckets_1541_, v___x_1547_, v___x_1548_, v_init_1538_);
return v___x_1549_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRev(lean_object* v_00_u03b1_1550_, lean_object* v_00_u03b2_1551_, lean_object* v_00_u03b4_1552_, lean_object* v_f_1553_, lean_object* v_init_1554_, lean_object* v_b_1555_){
_start:
{
lean_object* v___x_1556_; lean_object* v_buckets_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; uint8_t v___x_1560_; 
v___x_1556_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_1557_ = lean_ctor_get(v_b_1555_, 1);
lean_inc_ref(v_buckets_1557_);
lean_dec_ref(v_b_1555_);
v___x_1558_ = lean_array_get_size(v_buckets_1557_);
v___x_1559_ = lean_unsigned_to_nat(0u);
v___x_1560_ = lean_nat_dec_lt(v___x_1559_, v___x_1558_);
if (v___x_1560_ == 0)
{
lean_dec_ref(v_buckets_1557_);
lean_dec(v_f_1553_);
return v_init_1554_;
}
else
{
lean_object* v___f_1561_; lean_object* v___f_1562_; size_t v___x_1563_; size_t v___x_1564_; lean_object* v___x_1565_; 
v___f_1561_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1561_, 0, v_f_1553_);
v___f_1562_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1562_, 0, v___x_1556_);
lean_closure_set(v___f_1562_, 1, v___f_1561_);
v___x_1563_ = lean_usize_of_nat(v___x_1558_);
v___x_1564_ = ((size_t)0ULL);
v___x_1565_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1556_, v___f_1562_, v_buckets_1557_, v___x_1563_, v___x_1564_, v_init_1554_);
return v___x_1565_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevM___redArg(lean_object* v_inst_1566_, lean_object* v_f_1567_, lean_object* v_init_1568_, lean_object* v_b_1569_){
_start:
{
lean_object* v_buckets_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; uint8_t v___x_1573_; 
v_buckets_1570_ = lean_ctor_get(v_b_1569_, 1);
lean_inc_ref(v_buckets_1570_);
lean_dec_ref(v_b_1569_);
v___x_1571_ = lean_array_get_size(v_buckets_1570_);
v___x_1572_ = lean_unsigned_to_nat(0u);
v___x_1573_ = lean_nat_dec_lt(v___x_1572_, v___x_1571_);
if (v___x_1573_ == 0)
{
lean_object* v_toApplicative_1574_; lean_object* v_toPure_1575_; lean_object* v___x_1576_; 
lean_dec_ref(v_buckets_1570_);
lean_dec(v_f_1567_);
v_toApplicative_1574_ = lean_ctor_get(v_inst_1566_, 0);
lean_inc_ref(v_toApplicative_1574_);
lean_dec_ref(v_inst_1566_);
v_toPure_1575_ = lean_ctor_get(v_toApplicative_1574_, 1);
lean_inc(v_toPure_1575_);
lean_dec_ref(v_toApplicative_1574_);
v___x_1576_ = lean_apply_2(v_toPure_1575_, lean_box(0), v_init_1568_);
return v___x_1576_;
}
else
{
lean_object* v___f_1577_; lean_object* v___f_1578_; size_t v___x_1579_; size_t v___x_1580_; lean_object* v___x_1581_; 
v___f_1577_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1577_, 0, v_f_1567_);
lean_inc_ref(v_inst_1566_);
v___f_1578_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1578_, 0, v_inst_1566_);
lean_closure_set(v___f_1578_, 1, v___f_1577_);
v___x_1579_ = lean_usize_of_nat(v___x_1571_);
v___x_1580_ = ((size_t)0ULL);
v___x_1581_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1566_, v___f_1578_, v_buckets_1570_, v___x_1579_, v___x_1580_, v_init_1568_);
return v___x_1581_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevM(lean_object* v_00_u03b1_1582_, lean_object* v_00_u03b2_1583_, lean_object* v_00_u03b4_1584_, lean_object* v_m_1585_, lean_object* v_inst_1586_, lean_object* v_f_1587_, lean_object* v_init_1588_, lean_object* v_b_1589_){
_start:
{
lean_object* v_buckets_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; uint8_t v___x_1593_; 
v_buckets_1590_ = lean_ctor_get(v_b_1589_, 1);
lean_inc_ref(v_buckets_1590_);
lean_dec_ref(v_b_1589_);
v___x_1591_ = lean_array_get_size(v_buckets_1590_);
v___x_1592_ = lean_unsigned_to_nat(0u);
v___x_1593_ = lean_nat_dec_lt(v___x_1592_, v___x_1591_);
if (v___x_1593_ == 0)
{
lean_object* v_toApplicative_1594_; lean_object* v_toPure_1595_; lean_object* v___x_1596_; 
lean_dec_ref(v_buckets_1590_);
lean_dec(v_f_1587_);
v_toApplicative_1594_ = lean_ctor_get(v_inst_1586_, 0);
lean_inc_ref(v_toApplicative_1594_);
lean_dec_ref(v_inst_1586_);
v_toPure_1595_ = lean_ctor_get(v_toApplicative_1594_, 1);
lean_inc(v_toPure_1595_);
lean_dec_ref(v_toApplicative_1594_);
v___x_1596_ = lean_apply_2(v_toPure_1595_, lean_box(0), v_init_1588_);
return v___x_1596_;
}
else
{
lean_object* v___f_1597_; lean_object* v___f_1598_; size_t v___x_1599_; size_t v___x_1600_; lean_object* v___x_1601_; 
v___f_1597_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1597_, 0, v_f_1587_);
lean_inc_ref(v_inst_1586_);
v___f_1598_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1598_, 0, v_inst_1586_);
lean_closure_set(v___f_1598_, 1, v___f_1597_);
v___x_1599_ = lean_usize_of_nat(v___x_1591_);
v___x_1600_ = ((size_t)0ULL);
v___x_1601_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1586_, v___f_1598_, v_buckets_1590_, v___x_1599_, v___x_1600_, v_init_1588_);
return v___x_1601_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRev___redArg(lean_object* v_f_1602_, lean_object* v_init_1603_, lean_object* v_b_1604_){
_start:
{
lean_object* v___x_1605_; lean_object* v_buckets_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; uint8_t v___x_1609_; 
v___x_1605_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_1606_ = lean_ctor_get(v_b_1604_, 1);
lean_inc_ref(v_buckets_1606_);
lean_dec_ref(v_b_1604_);
v___x_1607_ = lean_array_get_size(v_buckets_1606_);
v___x_1608_ = lean_unsigned_to_nat(0u);
v___x_1609_ = lean_nat_dec_lt(v___x_1608_, v___x_1607_);
if (v___x_1609_ == 0)
{
lean_dec_ref(v_buckets_1606_);
lean_dec(v_f_1602_);
return v_init_1603_;
}
else
{
lean_object* v___f_1610_; lean_object* v___f_1611_; size_t v___x_1612_; size_t v___x_1613_; lean_object* v___x_1614_; 
v___f_1610_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1610_, 0, v_f_1602_);
v___f_1611_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1611_, 0, v___x_1605_);
lean_closure_set(v___f_1611_, 1, v___f_1610_);
v___x_1612_ = lean_usize_of_nat(v___x_1607_);
v___x_1613_ = ((size_t)0ULL);
v___x_1614_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1605_, v___f_1611_, v_buckets_1606_, v___x_1612_, v___x_1613_, v_init_1603_);
return v___x_1614_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRev(lean_object* v_00_u03b1_1615_, lean_object* v_00_u03b2_1616_, lean_object* v_00_u03b4_1617_, lean_object* v_f_1618_, lean_object* v_init_1619_, lean_object* v_b_1620_){
_start:
{
lean_object* v___x_1621_; lean_object* v_buckets_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; uint8_t v___x_1625_; 
v___x_1621_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_1622_ = lean_ctor_get(v_b_1620_, 1);
lean_inc_ref(v_buckets_1622_);
lean_dec_ref(v_b_1620_);
v___x_1623_ = lean_array_get_size(v_buckets_1622_);
v___x_1624_ = lean_unsigned_to_nat(0u);
v___x_1625_ = lean_nat_dec_lt(v___x_1624_, v___x_1623_);
if (v___x_1625_ == 0)
{
lean_dec_ref(v_buckets_1622_);
lean_dec(v_f_1618_);
return v_init_1619_;
}
else
{
lean_object* v___f_1626_; lean_object* v___f_1627_; size_t v___x_1628_; size_t v___x_1629_; lean_object* v___x_1630_; 
v___f_1626_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1626_, 0, v_f_1618_);
v___f_1627_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1627_, 0, v___x_1621_);
lean_closure_set(v___f_1627_, 1, v___f_1626_);
v___x_1628_ = lean_usize_of_nat(v___x_1623_);
v___x_1629_ = ((size_t)0ULL);
v___x_1630_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1621_, v___f_1627_, v_buckets_1622_, v___x_1628_, v___x_1629_, v_init_1619_);
return v___x_1630_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__0(lean_object* v_f_1631_, lean_object* v_x_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___y_1633_);
lean_ctor_set(v___x_1635_, 1, v___y_1634_);
v___x_1636_ = lean_apply_1(v_f_1631_, v___x_1635_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__1(lean_object* v_inst_1637_, lean_object* v___f_1638_, lean_object* v_x_1639_, lean_object* v___y_1640_){
_start:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1641_ = lean_box(0);
v___x_1642_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_1637_, v___f_1638_, v___x_1641_, v___y_1640_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forMUncurried___redArg(lean_object* v_inst_1643_, lean_object* v_f_1644_, lean_object* v_b_1645_){
_start:
{
lean_object* v_buckets_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; uint8_t v___x_1650_; 
v_buckets_1646_ = lean_ctor_get(v_b_1645_, 1);
lean_inc_ref(v_buckets_1646_);
lean_dec_ref(v_b_1645_);
v___x_1647_ = lean_unsigned_to_nat(0u);
v___x_1648_ = lean_array_get_size(v_buckets_1646_);
v___x_1649_ = lean_box(0);
v___x_1650_ = lean_nat_dec_lt(v___x_1647_, v___x_1648_);
if (v___x_1650_ == 0)
{
lean_object* v_toApplicative_1651_; lean_object* v_toPure_1652_; lean_object* v___x_1653_; 
lean_dec_ref(v_buckets_1646_);
lean_dec(v_f_1644_);
v_toApplicative_1651_ = lean_ctor_get(v_inst_1643_, 0);
lean_inc_ref(v_toApplicative_1651_);
lean_dec_ref(v_inst_1643_);
v_toPure_1652_ = lean_ctor_get(v_toApplicative_1651_, 1);
lean_inc(v_toPure_1652_);
lean_dec_ref(v_toApplicative_1651_);
v___x_1653_ = lean_apply_2(v_toPure_1652_, lean_box(0), v___x_1649_);
return v___x_1653_;
}
else
{
lean_object* v___f_1654_; lean_object* v___f_1655_; uint8_t v___x_1656_; 
v___f_1654_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1654_, 0, v_f_1644_);
lean_inc_ref(v_inst_1643_);
v___f_1655_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1655_, 0, v_inst_1643_);
lean_closure_set(v___f_1655_, 1, v___f_1654_);
v___x_1656_ = lean_nat_dec_le(v___x_1648_, v___x_1648_);
if (v___x_1656_ == 0)
{
if (v___x_1650_ == 0)
{
lean_object* v_toApplicative_1657_; lean_object* v_toPure_1658_; lean_object* v___x_1659_; 
lean_dec_ref(v___f_1655_);
lean_dec_ref(v_buckets_1646_);
v_toApplicative_1657_ = lean_ctor_get(v_inst_1643_, 0);
lean_inc_ref(v_toApplicative_1657_);
lean_dec_ref(v_inst_1643_);
v_toPure_1658_ = lean_ctor_get(v_toApplicative_1657_, 1);
lean_inc(v_toPure_1658_);
lean_dec_ref(v_toApplicative_1657_);
v___x_1659_ = lean_apply_2(v_toPure_1658_, lean_box(0), v___x_1649_);
return v___x_1659_;
}
else
{
size_t v___x_1660_; size_t v___x_1661_; lean_object* v___x_1662_; 
v___x_1660_ = ((size_t)0ULL);
v___x_1661_ = lean_usize_of_nat(v___x_1648_);
v___x_1662_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1643_, v___f_1655_, v_buckets_1646_, v___x_1660_, v___x_1661_, v___x_1649_);
return v___x_1662_;
}
}
else
{
size_t v___x_1663_; size_t v___x_1664_; lean_object* v___x_1665_; 
v___x_1663_ = ((size_t)0ULL);
v___x_1664_ = lean_usize_of_nat(v___x_1648_);
v___x_1665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1643_, v___f_1655_, v_buckets_1646_, v___x_1663_, v___x_1664_, v___x_1649_);
return v___x_1665_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forMUncurried(lean_object* v_00_u03b1_1666_, lean_object* v_m_1667_, lean_object* v_inst_1668_, lean_object* v_00_u03b2_1669_, lean_object* v_f_1670_, lean_object* v_b_1671_){
_start:
{
lean_object* v_buckets_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; uint8_t v___x_1676_; 
v_buckets_1672_ = lean_ctor_get(v_b_1671_, 1);
lean_inc_ref(v_buckets_1672_);
lean_dec_ref(v_b_1671_);
v___x_1673_ = lean_unsigned_to_nat(0u);
v___x_1674_ = lean_array_get_size(v_buckets_1672_);
v___x_1675_ = lean_box(0);
v___x_1676_ = lean_nat_dec_lt(v___x_1673_, v___x_1674_);
if (v___x_1676_ == 0)
{
lean_object* v_toApplicative_1677_; lean_object* v_toPure_1678_; lean_object* v___x_1679_; 
lean_dec_ref(v_buckets_1672_);
lean_dec(v_f_1670_);
v_toApplicative_1677_ = lean_ctor_get(v_inst_1668_, 0);
lean_inc_ref(v_toApplicative_1677_);
lean_dec_ref(v_inst_1668_);
v_toPure_1678_ = lean_ctor_get(v_toApplicative_1677_, 1);
lean_inc(v_toPure_1678_);
lean_dec_ref(v_toApplicative_1677_);
v___x_1679_ = lean_apply_2(v_toPure_1678_, lean_box(0), v___x_1675_);
return v___x_1679_;
}
else
{
lean_object* v___f_1680_; lean_object* v___f_1681_; uint8_t v___x_1682_; 
v___f_1680_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1680_, 0, v_f_1670_);
lean_inc_ref(v_inst_1668_);
v___f_1681_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1681_, 0, v_inst_1668_);
lean_closure_set(v___f_1681_, 1, v___f_1680_);
v___x_1682_ = lean_nat_dec_le(v___x_1674_, v___x_1674_);
if (v___x_1682_ == 0)
{
if (v___x_1676_ == 0)
{
lean_object* v_toApplicative_1683_; lean_object* v_toPure_1684_; lean_object* v___x_1685_; 
lean_dec_ref(v___f_1681_);
lean_dec_ref(v_buckets_1672_);
v_toApplicative_1683_ = lean_ctor_get(v_inst_1668_, 0);
lean_inc_ref(v_toApplicative_1683_);
lean_dec_ref(v_inst_1668_);
v_toPure_1684_ = lean_ctor_get(v_toApplicative_1683_, 1);
lean_inc(v_toPure_1684_);
lean_dec_ref(v_toApplicative_1683_);
v___x_1685_ = lean_apply_2(v_toPure_1684_, lean_box(0), v___x_1675_);
return v___x_1685_;
}
else
{
size_t v___x_1686_; size_t v___x_1687_; lean_object* v___x_1688_; 
v___x_1686_ = ((size_t)0ULL);
v___x_1687_ = lean_usize_of_nat(v___x_1674_);
v___x_1688_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1668_, v___f_1681_, v_buckets_1672_, v___x_1686_, v___x_1687_, v___x_1675_);
return v___x_1688_;
}
}
else
{
size_t v___x_1689_; size_t v___x_1690_; lean_object* v___x_1691_; 
v___x_1689_ = ((size_t)0ULL);
v___x_1690_ = lean_usize_of_nat(v___x_1674_);
v___x_1691_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1668_, v___f_1681_, v_buckets_1672_, v___x_1689_, v___x_1690_, v___x_1675_);
return v___x_1691_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__0(lean_object* v_f_1692_, lean_object* v_a_1693_, lean_object* v_b_1694_, lean_object* v_d_1695_){
_start:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1696_, 0, v_a_1693_);
lean_ctor_set(v___x_1696_, 1, v_b_1694_);
v___x_1697_ = lean_apply_2(v_f_1692_, v___x_1696_, v_d_1695_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__1(lean_object* v_inst_1698_, lean_object* v___f_1699_, lean_object* v_a_1700_, lean_object* v_x_1701_, lean_object* v___y_1702_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_1698_, v___f_1699_, v_a_1700_, v___y_1702_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forInUncurried___redArg(lean_object* v_inst_1704_, lean_object* v_f_1705_, lean_object* v_init_1706_, lean_object* v_b_1707_){
_start:
{
lean_object* v_buckets_1708_; lean_object* v___f_1709_; lean_object* v___f_1710_; size_t v_sz_1711_; size_t v___x_1712_; lean_object* v___x_1713_; 
v_buckets_1708_ = lean_ctor_get(v_b_1707_, 1);
lean_inc_ref(v_buckets_1708_);
lean_dec_ref(v_b_1707_);
v___f_1709_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1709_, 0, v_f_1705_);
lean_inc_ref(v_inst_1704_);
v___f_1710_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1710_, 0, v_inst_1704_);
lean_closure_set(v___f_1710_, 1, v___f_1709_);
v_sz_1711_ = lean_array_size(v_buckets_1708_);
v___x_1712_ = ((size_t)0ULL);
v___x_1713_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1704_, v_buckets_1708_, v___f_1710_, v_sz_1711_, v___x_1712_, v_init_1706_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forInUncurried(lean_object* v_00_u03b1_1714_, lean_object* v_00_u03b4_1715_, lean_object* v_m_1716_, lean_object* v_inst_1717_, lean_object* v_00_u03b2_1718_, lean_object* v_f_1719_, lean_object* v_init_1720_, lean_object* v_b_1721_){
_start:
{
lean_object* v_buckets_1722_; lean_object* v___f_1723_; lean_object* v___f_1724_; size_t v_sz_1725_; size_t v___x_1726_; lean_object* v___x_1727_; 
v_buckets_1722_ = lean_ctor_get(v_b_1721_, 1);
lean_inc_ref(v_buckets_1722_);
lean_dec_ref(v_b_1721_);
v___f_1723_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1723_, 0, v_f_1719_);
lean_inc_ref(v_inst_1717_);
v___f_1724_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1724_, 0, v_inst_1717_);
lean_closure_set(v___f_1724_, 1, v___f_1723_);
v_sz_1725_ = lean_array_size(v_buckets_1722_);
v___x_1726_ = ((size_t)0ULL);
v___x_1727_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1717_, v_buckets_1722_, v___f_1724_, v_sz_1725_, v___x_1726_, v_init_1720_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_filterMap___redArg(lean_object* v_f_1728_, lean_object* v_m_1729_){
_start:
{
lean_object* v_buckets_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; uint8_t v___x_1733_; 
v_buckets_1730_ = lean_ctor_get(v_m_1729_, 1);
v___x_1731_ = lean_unsigned_to_nat(0u);
v___x_1732_ = lean_array_get_size(v_buckets_1730_);
v___x_1733_ = lean_nat_dec_lt(v___x_1731_, v___x_1732_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; 
lean_dec_ref(v_m_1729_);
lean_dec_ref(v_f_1728_);
v___x_1734_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_1734_;
}
else
{
lean_object* v___x_1735_; 
v___x_1735_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_1728_, v_m_1729_);
return v___x_1735_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_filterMap(lean_object* v_00_u03b1_1736_, lean_object* v_00_u03b2_1737_, lean_object* v_00_u03b3_1738_, lean_object* v_f_1739_, lean_object* v_m_1740_){
_start:
{
lean_object* v_buckets_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; uint8_t v___x_1744_; 
v_buckets_1741_ = lean_ctor_get(v_m_1740_, 1);
v___x_1742_ = lean_unsigned_to_nat(0u);
v___x_1743_ = lean_array_get_size(v_buckets_1741_);
v___x_1744_ = lean_nat_dec_lt(v___x_1742_, v___x_1743_);
if (v___x_1744_ == 0)
{
lean_object* v___x_1745_; 
lean_dec_ref(v_m_1740_);
lean_dec_ref(v_f_1739_);
v___x_1745_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_1745_;
}
else
{
lean_object* v___x_1746_; 
v___x_1746_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_1739_, v_m_1740_);
return v___x_1746_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_map___redArg(lean_object* v_f_1747_, lean_object* v_m_1748_){
_start:
{
lean_object* v_buckets_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; uint8_t v___x_1752_; 
v_buckets_1749_ = lean_ctor_get(v_m_1748_, 1);
v___x_1750_ = lean_unsigned_to_nat(0u);
v___x_1751_ = lean_array_get_size(v_buckets_1749_);
v___x_1752_ = lean_nat_dec_lt(v___x_1750_, v___x_1751_);
if (v___x_1752_ == 0)
{
lean_object* v___x_1753_; 
lean_dec_ref(v_m_1748_);
lean_dec(v_f_1747_);
v___x_1753_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_1753_;
}
else
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_1747_, v_m_1748_);
return v___x_1754_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_map(lean_object* v_00_u03b1_1755_, lean_object* v_00_u03b2_1756_, lean_object* v_00_u03b3_1757_, lean_object* v_f_1758_, lean_object* v_m_1759_){
_start:
{
lean_object* v_buckets_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; uint8_t v___x_1763_; 
v_buckets_1760_ = lean_ctor_get(v_m_1759_, 1);
v___x_1761_ = lean_unsigned_to_nat(0u);
v___x_1762_ = lean_array_get_size(v_buckets_1760_);
v___x_1763_ = lean_nat_dec_lt(v___x_1761_, v___x_1762_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1764_; 
lean_dec_ref(v_m_1759_);
lean_dec(v_f_1758_);
v___x_1764_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_1764_;
}
else
{
lean_object* v___x_1765_; 
v___x_1765_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_1758_, v_m_1759_);
return v___x_1765_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_filter___redArg(lean_object* v_f_1766_, lean_object* v_m_1767_){
_start:
{
lean_object* v_buckets_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; uint8_t v___x_1771_; 
v_buckets_1768_ = lean_ctor_get(v_m_1767_, 1);
v___x_1769_ = lean_unsigned_to_nat(0u);
v___x_1770_ = lean_array_get_size(v_buckets_1768_);
v___x_1771_ = lean_nat_dec_lt(v___x_1769_, v___x_1770_);
if (v___x_1771_ == 0)
{
lean_object* v___x_1772_; 
lean_dec_ref(v_m_1767_);
lean_dec_ref(v_f_1766_);
v___x_1772_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_1772_;
}
else
{
lean_object* v___x_1773_; 
v___x_1773_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1766_, v_m_1767_);
return v___x_1773_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_filter(lean_object* v_00_u03b1_1774_, lean_object* v_00_u03b2_1775_, lean_object* v_f_1776_, lean_object* v_m_1777_){
_start:
{
lean_object* v_buckets_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; uint8_t v___x_1781_; 
v_buckets_1778_ = lean_ctor_get(v_m_1777_, 1);
v___x_1779_ = lean_unsigned_to_nat(0u);
v___x_1780_ = lean_array_get_size(v_buckets_1778_);
v___x_1781_ = lean_nat_dec_lt(v___x_1779_, v___x_1780_);
if (v___x_1781_ == 0)
{
lean_object* v___x_1782_; 
lean_dec_ref(v_m_1777_);
lean_dec_ref(v_f_1776_);
v___x_1782_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
return v___x_1782_;
}
else
{
lean_object* v___x_1783_; 
v___x_1783_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1776_, v_m_1777_);
return v___x_1783_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toArray___redArg___lam__0(lean_object* v_x1_1784_, lean_object* v_x2_1785_, lean_object* v_x3_1786_){
_start:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1787_, 0, v_x2_1785_);
lean_ctor_set(v___x_1787_, 1, v_x3_1786_);
v___x_1788_ = lean_array_push(v_x1_1784_, v___x_1787_);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toArray___redArg___lam__1(lean_object* v___x_1789_, lean_object* v___f_1790_, lean_object* v_acc_1791_, lean_object* v_l_1792_){
_start:
{
lean_object* v___x_1793_; 
v___x_1793_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1789_, v___f_1790_, v_acc_1791_, v_l_1792_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toArray___redArg(lean_object* v_m_1798_){
_start:
{
lean_object* v_size_1799_; lean_object* v_buckets_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; uint8_t v___x_1805_; 
v_size_1799_ = lean_ctor_get(v_m_1798_, 0);
lean_inc(v_size_1799_);
v_buckets_1800_ = lean_ctor_get(v_m_1798_, 1);
lean_inc_ref(v_buckets_1800_);
lean_dec_ref(v_m_1798_);
v___x_1801_ = lean_mk_empty_array_with_capacity(v_size_1799_);
lean_dec(v_size_1799_);
v___x_1802_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_1803_ = lean_unsigned_to_nat(0u);
v___x_1804_ = lean_array_get_size(v_buckets_1800_);
v___x_1805_ = lean_nat_dec_lt(v___x_1803_, v___x_1804_);
if (v___x_1805_ == 0)
{
lean_dec_ref(v_buckets_1800_);
return v___x_1801_;
}
else
{
lean_object* v___f_1806_; uint8_t v___x_1807_; 
v___f_1806_ = ((lean_object*)(l_Std_DHashMap_Raw_toArray___redArg___closed__1));
v___x_1807_ = lean_nat_dec_le(v___x_1804_, v___x_1804_);
if (v___x_1807_ == 0)
{
if (v___x_1805_ == 0)
{
lean_dec_ref(v_buckets_1800_);
return v___x_1801_;
}
else
{
size_t v___x_1808_; size_t v___x_1809_; lean_object* v___x_1810_; 
v___x_1808_ = ((size_t)0ULL);
v___x_1809_ = lean_usize_of_nat(v___x_1804_);
v___x_1810_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1802_, v___f_1806_, v_buckets_1800_, v___x_1808_, v___x_1809_, v___x_1801_);
return v___x_1810_;
}
}
else
{
size_t v___x_1811_; size_t v___x_1812_; lean_object* v___x_1813_; 
v___x_1811_ = ((size_t)0ULL);
v___x_1812_ = lean_usize_of_nat(v___x_1804_);
v___x_1813_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1802_, v___f_1806_, v_buckets_1800_, v___x_1811_, v___x_1812_, v___x_1801_);
return v___x_1813_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toArray(lean_object* v_00_u03b1_1814_, lean_object* v_00_u03b2_1815_, lean_object* v_m_1816_){
_start:
{
lean_object* v_size_1817_; lean_object* v_buckets_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; uint8_t v___x_1823_; 
v_size_1817_ = lean_ctor_get(v_m_1816_, 0);
lean_inc(v_size_1817_);
v_buckets_1818_ = lean_ctor_get(v_m_1816_, 1);
lean_inc_ref(v_buckets_1818_);
lean_dec_ref(v_m_1816_);
v___x_1819_ = lean_mk_empty_array_with_capacity(v_size_1817_);
lean_dec(v_size_1817_);
v___x_1820_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_1821_ = lean_unsigned_to_nat(0u);
v___x_1822_ = lean_array_get_size(v_buckets_1818_);
v___x_1823_ = lean_nat_dec_lt(v___x_1821_, v___x_1822_);
if (v___x_1823_ == 0)
{
lean_dec_ref(v_buckets_1818_);
return v___x_1819_;
}
else
{
lean_object* v___f_1824_; uint8_t v___x_1825_; 
v___f_1824_ = ((lean_object*)(l_Std_DHashMap_Raw_toArray___redArg___closed__1));
v___x_1825_ = lean_nat_dec_le(v___x_1822_, v___x_1822_);
if (v___x_1825_ == 0)
{
if (v___x_1823_ == 0)
{
lean_dec_ref(v_buckets_1818_);
return v___x_1819_;
}
else
{
size_t v___x_1826_; size_t v___x_1827_; lean_object* v___x_1828_; 
v___x_1826_ = ((size_t)0ULL);
v___x_1827_ = lean_usize_of_nat(v___x_1822_);
v___x_1828_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1820_, v___f_1824_, v_buckets_1818_, v___x_1826_, v___x_1827_, v___x_1819_);
return v___x_1828_;
}
}
else
{
size_t v___x_1829_; size_t v___x_1830_; lean_object* v___x_1831_; 
v___x_1829_ = ((size_t)0ULL);
v___x_1830_ = lean_usize_of_nat(v___x_1822_);
v___x_1831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1820_, v___f_1824_, v_buckets_1818_, v___x_1829_, v___x_1830_, v___x_1819_);
return v___x_1831_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toArray___redArg___lam__0(lean_object* v_x1_1832_, lean_object* v_x2_1833_, lean_object* v_x3_1834_){
_start:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1835_, 0, v_x2_1833_);
lean_ctor_set(v___x_1835_, 1, v_x3_1834_);
v___x_1836_ = lean_array_push(v_x1_1832_, v___x_1835_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toArray___redArg___lam__1(lean_object* v___x_1837_, lean_object* v___f_1838_, lean_object* v_acc_1839_, lean_object* v_l_1840_){
_start:
{
lean_object* v___x_1841_; 
v___x_1841_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1837_, v___f_1838_, v_acc_1839_, v_l_1840_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toArray___redArg(lean_object* v_m_1846_){
_start:
{
lean_object* v_size_1847_; lean_object* v_buckets_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; uint8_t v___x_1853_; 
v_size_1847_ = lean_ctor_get(v_m_1846_, 0);
lean_inc(v_size_1847_);
v_buckets_1848_ = lean_ctor_get(v_m_1846_, 1);
lean_inc_ref(v_buckets_1848_);
lean_dec_ref(v_m_1846_);
v___x_1849_ = lean_mk_empty_array_with_capacity(v_size_1847_);
lean_dec(v_size_1847_);
v___x_1850_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_1851_ = lean_unsigned_to_nat(0u);
v___x_1852_ = lean_array_get_size(v_buckets_1848_);
v___x_1853_ = lean_nat_dec_lt(v___x_1851_, v___x_1852_);
if (v___x_1853_ == 0)
{
lean_dec_ref(v_buckets_1848_);
return v___x_1849_;
}
else
{
lean_object* v___f_1854_; uint8_t v___x_1855_; 
v___f_1854_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_toArray___redArg___closed__1));
v___x_1855_ = lean_nat_dec_le(v___x_1852_, v___x_1852_);
if (v___x_1855_ == 0)
{
if (v___x_1853_ == 0)
{
lean_dec_ref(v_buckets_1848_);
return v___x_1849_;
}
else
{
size_t v___x_1856_; size_t v___x_1857_; lean_object* v___x_1858_; 
v___x_1856_ = ((size_t)0ULL);
v___x_1857_ = lean_usize_of_nat(v___x_1852_);
v___x_1858_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1850_, v___f_1854_, v_buckets_1848_, v___x_1856_, v___x_1857_, v___x_1849_);
return v___x_1858_;
}
}
else
{
size_t v___x_1859_; size_t v___x_1860_; lean_object* v___x_1861_; 
v___x_1859_ = ((size_t)0ULL);
v___x_1860_ = lean_usize_of_nat(v___x_1852_);
v___x_1861_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1850_, v___f_1854_, v_buckets_1848_, v___x_1859_, v___x_1860_, v___x_1849_);
return v___x_1861_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toArray(lean_object* v_00_u03b1_1862_, lean_object* v_00_u03b2_1863_, lean_object* v_m_1864_){
_start:
{
lean_object* v_size_1865_; lean_object* v_buckets_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; uint8_t v___x_1871_; 
v_size_1865_ = lean_ctor_get(v_m_1864_, 0);
lean_inc(v_size_1865_);
v_buckets_1866_ = lean_ctor_get(v_m_1864_, 1);
lean_inc_ref(v_buckets_1866_);
lean_dec_ref(v_m_1864_);
v___x_1867_ = lean_mk_empty_array_with_capacity(v_size_1865_);
lean_dec(v_size_1865_);
v___x_1868_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_1869_ = lean_unsigned_to_nat(0u);
v___x_1870_ = lean_array_get_size(v_buckets_1866_);
v___x_1871_ = lean_nat_dec_lt(v___x_1869_, v___x_1870_);
if (v___x_1871_ == 0)
{
lean_dec_ref(v_buckets_1866_);
return v___x_1867_;
}
else
{
lean_object* v___f_1872_; uint8_t v___x_1873_; 
v___f_1872_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_toArray___redArg___closed__1));
v___x_1873_ = lean_nat_dec_le(v___x_1870_, v___x_1870_);
if (v___x_1873_ == 0)
{
if (v___x_1871_ == 0)
{
lean_dec_ref(v_buckets_1866_);
return v___x_1867_;
}
else
{
size_t v___x_1874_; size_t v___x_1875_; lean_object* v___x_1876_; 
v___x_1874_ = ((size_t)0ULL);
v___x_1875_ = lean_usize_of_nat(v___x_1870_);
v___x_1876_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1868_, v___f_1872_, v_buckets_1866_, v___x_1874_, v___x_1875_, v___x_1867_);
return v___x_1876_;
}
}
else
{
size_t v___x_1877_; size_t v___x_1878_; lean_object* v___x_1879_; 
v___x_1877_ = ((size_t)0ULL);
v___x_1878_ = lean_usize_of_nat(v___x_1870_);
v___x_1879_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1868_, v___f_1872_, v_buckets_1866_, v___x_1877_, v___x_1878_, v___x_1867_);
return v___x_1879_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keysArray___redArg___lam__0(lean_object* v_x1_1880_, lean_object* v_x2_1881_, lean_object* v_x3_1882_){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = lean_array_push(v_x1_1880_, v_x2_1881_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keysArray___redArg___lam__0___boxed(lean_object* v_x1_1884_, lean_object* v_x2_1885_, lean_object* v_x3_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l_Std_DHashMap_Raw_keysArray___redArg___lam__0(v_x1_1884_, v_x2_1885_, v_x3_1886_);
lean_dec(v_x3_1886_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keysArray___redArg___lam__1(lean_object* v___x_1888_, lean_object* v___f_1889_, lean_object* v_acc_1890_, lean_object* v_l_1891_){
_start:
{
lean_object* v___x_1892_; 
v___x_1892_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1888_, v___f_1889_, v_acc_1890_, v_l_1891_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keysArray___redArg(lean_object* v_m_1897_){
_start:
{
lean_object* v_size_1898_; lean_object* v_buckets_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; uint8_t v___x_1904_; 
v_size_1898_ = lean_ctor_get(v_m_1897_, 0);
lean_inc(v_size_1898_);
v_buckets_1899_ = lean_ctor_get(v_m_1897_, 1);
lean_inc_ref(v_buckets_1899_);
lean_dec_ref(v_m_1897_);
v___x_1900_ = lean_mk_empty_array_with_capacity(v_size_1898_);
lean_dec(v_size_1898_);
v___x_1901_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_1902_ = lean_unsigned_to_nat(0u);
v___x_1903_ = lean_array_get_size(v_buckets_1899_);
v___x_1904_ = lean_nat_dec_lt(v___x_1902_, v___x_1903_);
if (v___x_1904_ == 0)
{
lean_dec_ref(v_buckets_1899_);
return v___x_1900_;
}
else
{
lean_object* v___f_1905_; uint8_t v___x_1906_; 
v___f_1905_ = ((lean_object*)(l_Std_DHashMap_Raw_keysArray___redArg___closed__1));
v___x_1906_ = lean_nat_dec_le(v___x_1903_, v___x_1903_);
if (v___x_1906_ == 0)
{
if (v___x_1904_ == 0)
{
lean_dec_ref(v_buckets_1899_);
return v___x_1900_;
}
else
{
size_t v___x_1907_; size_t v___x_1908_; lean_object* v___x_1909_; 
v___x_1907_ = ((size_t)0ULL);
v___x_1908_ = lean_usize_of_nat(v___x_1903_);
v___x_1909_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1901_, v___f_1905_, v_buckets_1899_, v___x_1907_, v___x_1908_, v___x_1900_);
return v___x_1909_;
}
}
else
{
size_t v___x_1910_; size_t v___x_1911_; lean_object* v___x_1912_; 
v___x_1910_ = ((size_t)0ULL);
v___x_1911_ = lean_usize_of_nat(v___x_1903_);
v___x_1912_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1901_, v___f_1905_, v_buckets_1899_, v___x_1910_, v___x_1911_, v___x_1900_);
return v___x_1912_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keysArray(lean_object* v_00_u03b1_1913_, lean_object* v_00_u03b2_1914_, lean_object* v_m_1915_){
_start:
{
lean_object* v_size_1916_; lean_object* v_buckets_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; uint8_t v___x_1922_; 
v_size_1916_ = lean_ctor_get(v_m_1915_, 0);
lean_inc(v_size_1916_);
v_buckets_1917_ = lean_ctor_get(v_m_1915_, 1);
lean_inc_ref(v_buckets_1917_);
lean_dec_ref(v_m_1915_);
v___x_1918_ = lean_mk_empty_array_with_capacity(v_size_1916_);
lean_dec(v_size_1916_);
v___x_1919_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_1920_ = lean_unsigned_to_nat(0u);
v___x_1921_ = lean_array_get_size(v_buckets_1917_);
v___x_1922_ = lean_nat_dec_lt(v___x_1920_, v___x_1921_);
if (v___x_1922_ == 0)
{
lean_dec_ref(v_buckets_1917_);
return v___x_1918_;
}
else
{
lean_object* v___f_1923_; uint8_t v___x_1924_; 
v___f_1923_ = ((lean_object*)(l_Std_DHashMap_Raw_keysArray___redArg___closed__1));
v___x_1924_ = lean_nat_dec_le(v___x_1921_, v___x_1921_);
if (v___x_1924_ == 0)
{
if (v___x_1922_ == 0)
{
lean_dec_ref(v_buckets_1917_);
return v___x_1918_;
}
else
{
size_t v___x_1925_; size_t v___x_1926_; lean_object* v___x_1927_; 
v___x_1925_ = ((size_t)0ULL);
v___x_1926_ = lean_usize_of_nat(v___x_1921_);
v___x_1927_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1919_, v___f_1923_, v_buckets_1917_, v___x_1925_, v___x_1926_, v___x_1918_);
return v___x_1927_;
}
}
else
{
size_t v___x_1928_; size_t v___x_1929_; lean_object* v___x_1930_; 
v___x_1928_ = ((size_t)0ULL);
v___x_1929_ = lean_usize_of_nat(v___x_1921_);
v___x_1930_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1919_, v___f_1923_, v_buckets_1917_, v___x_1928_, v___x_1929_, v___x_1918_);
return v___x_1930_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_union___redArg___lam__0(lean_object* v_inst_1931_, lean_object* v_inst_1932_, lean_object* v_a_1933_, lean_object* v_b_1934_, lean_object* v_acc_1935_){
_start:
{
lean_object* v_r_1936_; lean_object* v___x_1937_; 
v_r_1936_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_1931_, v_inst_1932_, v_acc_1935_, v_a_1933_, v_b_1934_);
v___x_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1937_, 0, v_r_1936_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_union___redArg___lam__1(lean_object* v___x_1938_, lean_object* v___f_1939_, lean_object* v_a_1940_, lean_object* v_x_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v___x_1943_; 
v___x_1943_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1938_, v___f_1939_, v_a_1940_, v___y_1942_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_union___redArg(lean_object* v_inst_1946_, lean_object* v_inst_1947_, lean_object* v_m_u2081_1948_, lean_object* v_m_u2082_1949_){
_start:
{
lean_object* v_size_1950_; lean_object* v_buckets_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; uint8_t v___x_1954_; 
v_size_1950_ = lean_ctor_get(v_m_u2081_1948_, 0);
v_buckets_1951_ = lean_ctor_get(v_m_u2081_1948_, 1);
v___x_1952_ = lean_unsigned_to_nat(0u);
v___x_1953_ = lean_array_get_size(v_buckets_1951_);
v___x_1954_ = lean_nat_dec_lt(v___x_1952_, v___x_1953_);
if (v___x_1954_ == 0)
{
lean_dec_ref(v_m_u2081_1948_);
lean_dec_ref(v_inst_1947_);
lean_dec_ref(v_inst_1946_);
return v_m_u2082_1949_;
}
else
{
lean_object* v_size_1955_; lean_object* v_buckets_1956_; lean_object* v___x_1957_; uint8_t v___x_1958_; 
v_size_1955_ = lean_ctor_get(v_m_u2082_1949_, 0);
v_buckets_1956_ = lean_ctor_get(v_m_u2082_1949_, 1);
v___x_1957_ = lean_array_get_size(v_buckets_1956_);
v___x_1958_ = lean_nat_dec_lt(v___x_1952_, v___x_1957_);
if (v___x_1958_ == 0)
{
lean_dec_ref(v_m_u2082_1949_);
lean_dec_ref(v_inst_1947_);
lean_dec_ref(v_inst_1946_);
return v_m_u2081_1948_;
}
else
{
uint8_t v___x_1959_; 
v___x_1959_ = lean_nat_dec_le(v_size_1950_, v_size_1955_);
if (v___x_1959_ == 0)
{
lean_object* v___f_1960_; lean_object* v___x_1961_; 
v___f_1960_ = ((lean_object*)(l_Std_DHashMap_Raw_union___redArg___closed__0));
v___x_1961_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1960_, v_inst_1946_, v_inst_1947_, v_m_u2081_1948_, v_m_u2082_1949_);
return v___x_1961_;
}
else
{
lean_object* v___f_1962_; lean_object* v___x_1963_; lean_object* v___f_1964_; size_t v_sz_1965_; size_t v___x_1966_; lean_object* v___x_1967_; 
lean_inc_ref(v_buckets_1951_);
lean_dec_ref(v_m_u2081_1948_);
v___f_1962_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1962_, 0, v_inst_1946_);
lean_closure_set(v___f_1962_, 1, v_inst_1947_);
v___x_1963_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___f_1964_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1964_, 0, v___x_1963_);
lean_closure_set(v___f_1964_, 1, v___f_1962_);
v_sz_1965_ = lean_array_size(v_buckets_1951_);
v___x_1966_ = ((size_t)0ULL);
v___x_1967_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1963_, v_buckets_1951_, v___f_1964_, v_sz_1965_, v___x_1966_, v_m_u2082_1949_);
return v___x_1967_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_union(lean_object* v_00_u03b1_1968_, lean_object* v_00_u03b2_1969_, lean_object* v_inst_1970_, lean_object* v_inst_1971_, lean_object* v_m_u2081_1972_, lean_object* v_m_u2082_1973_){
_start:
{
lean_object* v_size_1974_; lean_object* v_buckets_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; uint8_t v___x_1978_; 
v_size_1974_ = lean_ctor_get(v_m_u2081_1972_, 0);
v_buckets_1975_ = lean_ctor_get(v_m_u2081_1972_, 1);
v___x_1976_ = lean_unsigned_to_nat(0u);
v___x_1977_ = lean_array_get_size(v_buckets_1975_);
v___x_1978_ = lean_nat_dec_lt(v___x_1976_, v___x_1977_);
if (v___x_1978_ == 0)
{
lean_dec_ref(v_m_u2081_1972_);
lean_dec_ref(v_inst_1971_);
lean_dec_ref(v_inst_1970_);
return v_m_u2082_1973_;
}
else
{
lean_object* v_size_1979_; lean_object* v_buckets_1980_; lean_object* v___x_1981_; uint8_t v___x_1982_; 
v_size_1979_ = lean_ctor_get(v_m_u2082_1973_, 0);
v_buckets_1980_ = lean_ctor_get(v_m_u2082_1973_, 1);
v___x_1981_ = lean_array_get_size(v_buckets_1980_);
v___x_1982_ = lean_nat_dec_lt(v___x_1976_, v___x_1981_);
if (v___x_1982_ == 0)
{
lean_dec_ref(v_m_u2082_1973_);
lean_dec_ref(v_inst_1971_);
lean_dec_ref(v_inst_1970_);
return v_m_u2081_1972_;
}
else
{
uint8_t v___x_1983_; 
v___x_1983_ = lean_nat_dec_le(v_size_1974_, v_size_1979_);
if (v___x_1983_ == 0)
{
lean_object* v___f_1984_; lean_object* v___x_1985_; 
v___f_1984_ = ((lean_object*)(l_Std_DHashMap_Raw_union___redArg___closed__0));
v___x_1985_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1984_, v_inst_1970_, v_inst_1971_, v_m_u2081_1972_, v_m_u2082_1973_);
return v___x_1985_;
}
else
{
lean_object* v___f_1986_; lean_object* v___x_1987_; lean_object* v___f_1988_; size_t v_sz_1989_; size_t v___x_1990_; lean_object* v___x_1991_; 
lean_inc_ref(v_buckets_1975_);
lean_dec_ref(v_m_u2081_1972_);
v___f_1986_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1986_, 0, v_inst_1970_);
lean_closure_set(v___f_1986_, 1, v_inst_1971_);
v___x_1987_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___f_1988_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1988_, 0, v___x_1987_);
lean_closure_set(v___f_1988_, 1, v___f_1986_);
v_sz_1989_ = lean_array_size(v_buckets_1975_);
v___x_1990_ = ((size_t)0ULL);
v___x_1991_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1987_, v_buckets_1975_, v___f_1988_, v_sz_1989_, v___x_1990_, v_m_u2082_1973_);
return v___x_1991_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instUnionOfBEqOfHashable___redArg(lean_object* v_inst_1992_, lean_object* v_inst_1993_){
_start:
{
lean_object* v___x_1994_; 
v___x_1994_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_union), 6, 4);
lean_closure_set(v___x_1994_, 0, lean_box(0));
lean_closure_set(v___x_1994_, 1, lean_box(0));
lean_closure_set(v___x_1994_, 2, v_inst_1992_);
lean_closure_set(v___x_1994_, 3, v_inst_1993_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instUnionOfBEqOfHashable(lean_object* v_00_u03b1_1995_, lean_object* v_00_u03b2_1996_, lean_object* v_inst_1997_, lean_object* v_inst_1998_){
_start:
{
lean_object* v___x_1999_; 
v___x_1999_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_union), 6, 4);
lean_closure_set(v___x_1999_, 0, lean_box(0));
lean_closure_set(v___x_1999_, 1, lean_box(0));
lean_closure_set(v___x_1999_, 2, v_inst_1997_);
lean_closure_set(v___x_1999_, 3, v_inst_1998_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_inter___redArg(lean_object* v_inst_2000_, lean_object* v_inst_2001_, lean_object* v_m_u2081_2002_, lean_object* v_m_u2082_2003_){
_start:
{
lean_object* v_buckets_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; uint8_t v___x_2007_; 
v_buckets_2004_ = lean_ctor_get(v_m_u2081_2002_, 1);
v___x_2005_ = lean_unsigned_to_nat(0u);
v___x_2006_ = lean_array_get_size(v_buckets_2004_);
v___x_2007_ = lean_nat_dec_lt(v___x_2005_, v___x_2006_);
if (v___x_2007_ == 0)
{
lean_dec_ref(v_m_u2081_2002_);
lean_dec_ref(v_inst_2001_);
lean_dec_ref(v_inst_2000_);
return v_m_u2082_2003_;
}
else
{
lean_object* v_buckets_2008_; lean_object* v___x_2009_; uint8_t v___x_2010_; 
v_buckets_2008_ = lean_ctor_get(v_m_u2082_2003_, 1);
v___x_2009_ = lean_array_get_size(v_buckets_2008_);
v___x_2010_ = lean_nat_dec_lt(v___x_2005_, v___x_2009_);
if (v___x_2010_ == 0)
{
lean_dec_ref(v_m_u2082_2003_);
lean_dec_ref(v_inst_2001_);
lean_dec_ref(v_inst_2000_);
return v_m_u2081_2002_;
}
else
{
lean_object* v___x_2011_; 
v___x_2011_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_2000_, v_inst_2001_, v_m_u2081_2002_, v_m_u2082_2003_);
return v___x_2011_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_inter(lean_object* v_00_u03b1_2012_, lean_object* v_00_u03b2_2013_, lean_object* v_inst_2014_, lean_object* v_inst_2015_, lean_object* v_m_u2081_2016_, lean_object* v_m_u2082_2017_){
_start:
{
lean_object* v_buckets_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; uint8_t v___x_2021_; 
v_buckets_2018_ = lean_ctor_get(v_m_u2081_2016_, 1);
v___x_2019_ = lean_unsigned_to_nat(0u);
v___x_2020_ = lean_array_get_size(v_buckets_2018_);
v___x_2021_ = lean_nat_dec_lt(v___x_2019_, v___x_2020_);
if (v___x_2021_ == 0)
{
lean_dec_ref(v_m_u2081_2016_);
lean_dec_ref(v_inst_2015_);
lean_dec_ref(v_inst_2014_);
return v_m_u2082_2017_;
}
else
{
lean_object* v_buckets_2022_; lean_object* v___x_2023_; uint8_t v___x_2024_; 
v_buckets_2022_ = lean_ctor_get(v_m_u2082_2017_, 1);
v___x_2023_ = lean_array_get_size(v_buckets_2022_);
v___x_2024_ = lean_nat_dec_lt(v___x_2019_, v___x_2023_);
if (v___x_2024_ == 0)
{
lean_dec_ref(v_m_u2082_2017_);
lean_dec_ref(v_inst_2015_);
lean_dec_ref(v_inst_2014_);
return v_m_u2081_2016_;
}
else
{
lean_object* v___x_2025_; 
v___x_2025_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_2014_, v_inst_2015_, v_m_u2081_2016_, v_m_u2082_2017_);
return v___x_2025_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInterOfBEqOfHashable___redArg(lean_object* v_inst_2026_, lean_object* v_inst_2027_){
_start:
{
lean_object* v___x_2028_; 
v___x_2028_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_inter), 6, 4);
lean_closure_set(v___x_2028_, 0, lean_box(0));
lean_closure_set(v___x_2028_, 1, lean_box(0));
lean_closure_set(v___x_2028_, 2, v_inst_2026_);
lean_closure_set(v___x_2028_, 3, v_inst_2027_);
return v___x_2028_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInterOfBEqOfHashable(lean_object* v_00_u03b1_2029_, lean_object* v_00_u03b2_2030_, lean_object* v_inst_2031_, lean_object* v_inst_2032_){
_start:
{
lean_object* v___x_2033_; 
v___x_2033_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_inter), 6, 4);
lean_closure_set(v___x_2033_, 0, lean_box(0));
lean_closure_set(v___x_2033_, 1, lean_box(0));
lean_closure_set(v___x_2033_, 2, v_inst_2031_);
lean_closure_set(v___x_2033_, 3, v_inst_2032_);
return v___x_2033_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_beq___redArg(lean_object* v_inst_2034_, lean_object* v_inst_2035_, lean_object* v_inst_2036_, lean_object* v_m_u2081_2037_, lean_object* v_m_u2082_2038_){
_start:
{
lean_object* v_buckets_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; uint8_t v___x_2042_; 
v_buckets_2039_ = lean_ctor_get(v_m_u2081_2037_, 1);
v___x_2040_ = lean_unsigned_to_nat(0u);
v___x_2041_ = lean_array_get_size(v_buckets_2039_);
v___x_2042_ = lean_nat_dec_lt(v___x_2040_, v___x_2041_);
if (v___x_2042_ == 0)
{
lean_dec_ref(v_m_u2082_2038_);
lean_dec_ref(v_m_u2081_2037_);
lean_dec_ref(v_inst_2036_);
lean_dec_ref(v_inst_2035_);
lean_dec_ref(v_inst_2034_);
return v___x_2042_;
}
else
{
lean_object* v_buckets_2043_; lean_object* v___x_2044_; uint8_t v___x_2045_; 
v_buckets_2043_ = lean_ctor_get(v_m_u2082_2038_, 1);
v___x_2044_ = lean_array_get_size(v_buckets_2043_);
v___x_2045_ = lean_nat_dec_lt(v___x_2040_, v___x_2044_);
if (v___x_2045_ == 0)
{
lean_dec_ref(v_m_u2082_2038_);
lean_dec_ref(v_m_u2081_2037_);
lean_dec_ref(v_inst_2036_);
lean_dec_ref(v_inst_2035_);
lean_dec_ref(v_inst_2034_);
return v___x_2045_;
}
else
{
uint8_t v___x_2046_; 
v___x_2046_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(v_inst_2034_, v_inst_2035_, v_inst_2036_, v_m_u2081_2037_, v_m_u2082_2038_);
return v___x_2046_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_beq___redArg___boxed(lean_object* v_inst_2047_, lean_object* v_inst_2048_, lean_object* v_inst_2049_, lean_object* v_m_u2081_2050_, lean_object* v_m_u2082_2051_){
_start:
{
uint8_t v_res_2052_; lean_object* v_r_2053_; 
v_res_2052_ = l_Std_DHashMap_Raw_beq___redArg(v_inst_2047_, v_inst_2048_, v_inst_2049_, v_m_u2081_2050_, v_m_u2082_2051_);
v_r_2053_ = lean_box(v_res_2052_);
return v_r_2053_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_beq(lean_object* v_00_u03b1_2054_, lean_object* v_00_u03b2_2055_, lean_object* v_inst_2056_, lean_object* v_inst_2057_, lean_object* v_inst_2058_, lean_object* v_inst_2059_, lean_object* v_m_u2081_2060_, lean_object* v_m_u2082_2061_){
_start:
{
uint8_t v___x_2062_; 
v___x_2062_ = l_Std_DHashMap_Raw_beq___redArg(v_inst_2056_, v_inst_2057_, v_inst_2059_, v_m_u2081_2060_, v_m_u2082_2061_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_beq___boxed(lean_object* v_00_u03b1_2063_, lean_object* v_00_u03b2_2064_, lean_object* v_inst_2065_, lean_object* v_inst_2066_, lean_object* v_inst_2067_, lean_object* v_inst_2068_, lean_object* v_m_u2081_2069_, lean_object* v_m_u2082_2070_){
_start:
{
uint8_t v_res_2071_; lean_object* v_r_2072_; 
v_res_2071_ = l_Std_DHashMap_Raw_beq(v_00_u03b1_2063_, v_00_u03b2_2064_, v_inst_2065_, v_inst_2066_, v_inst_2067_, v_inst_2068_, v_m_u2081_2069_, v_m_u2082_2070_);
v_r_2072_ = lean_box(v_res_2071_);
return v_r_2072_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instBEqOfHashableOfLawfulBEq___redArg(lean_object* v_inst_2073_, lean_object* v_inst_2074_, lean_object* v_inst_2075_){
_start:
{
lean_object* v___x_2076_; 
v___x_2076_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_beq___boxed), 8, 6);
lean_closure_set(v___x_2076_, 0, lean_box(0));
lean_closure_set(v___x_2076_, 1, lean_box(0));
lean_closure_set(v___x_2076_, 2, v_inst_2073_);
lean_closure_set(v___x_2076_, 3, v_inst_2074_);
lean_closure_set(v___x_2076_, 4, lean_box(0));
lean_closure_set(v___x_2076_, 5, v_inst_2075_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instBEqOfHashableOfLawfulBEq(lean_object* v_00_u03b1_2077_, lean_object* v_00_u03b2_2078_, lean_object* v_inst_2079_, lean_object* v_inst_2080_, lean_object* v_inst_2081_, lean_object* v_inst_2082_){
_start:
{
lean_object* v___x_2083_; 
v___x_2083_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_beq___boxed), 8, 6);
lean_closure_set(v___x_2083_, 0, lean_box(0));
lean_closure_set(v___x_2083_, 1, lean_box(0));
lean_closure_set(v___x_2083_, 2, v_inst_2079_);
lean_closure_set(v___x_2083_, 3, v_inst_2080_);
lean_closure_set(v___x_2083_, 4, lean_box(0));
lean_closure_set(v___x_2083_, 5, v_inst_2082_);
return v___x_2083_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_Const_beq___redArg(lean_object* v_inst_2084_, lean_object* v_inst_2085_, lean_object* v_inst_2086_, lean_object* v_m_u2081_2087_, lean_object* v_m_u2082_2088_){
_start:
{
lean_object* v_buckets_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; uint8_t v___x_2092_; 
v_buckets_2089_ = lean_ctor_get(v_m_u2081_2087_, 1);
v___x_2090_ = lean_unsigned_to_nat(0u);
v___x_2091_ = lean_array_get_size(v_buckets_2089_);
v___x_2092_ = lean_nat_dec_lt(v___x_2090_, v___x_2091_);
if (v___x_2092_ == 0)
{
lean_dec_ref(v_m_u2082_2088_);
lean_dec_ref(v_m_u2081_2087_);
lean_dec_ref(v_inst_2086_);
lean_dec_ref(v_inst_2085_);
lean_dec_ref(v_inst_2084_);
return v___x_2092_;
}
else
{
lean_object* v_buckets_2093_; lean_object* v___x_2094_; uint8_t v___x_2095_; 
v_buckets_2093_ = lean_ctor_get(v_m_u2082_2088_, 1);
v___x_2094_ = lean_array_get_size(v_buckets_2093_);
v___x_2095_ = lean_nat_dec_lt(v___x_2090_, v___x_2094_);
if (v___x_2095_ == 0)
{
lean_dec_ref(v_m_u2082_2088_);
lean_dec_ref(v_m_u2081_2087_);
lean_dec_ref(v_inst_2086_);
lean_dec_ref(v_inst_2085_);
lean_dec_ref(v_inst_2084_);
return v___x_2095_;
}
else
{
uint8_t v___x_2096_; 
v___x_2096_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_inst_2084_, v_inst_2085_, v_inst_2086_, v_m_u2081_2087_, v_m_u2082_2088_);
return v___x_2096_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_beq___redArg___boxed(lean_object* v_inst_2097_, lean_object* v_inst_2098_, lean_object* v_inst_2099_, lean_object* v_m_u2081_2100_, lean_object* v_m_u2082_2101_){
_start:
{
uint8_t v_res_2102_; lean_object* v_r_2103_; 
v_res_2102_ = l_Std_DHashMap_Raw_Const_beq___redArg(v_inst_2097_, v_inst_2098_, v_inst_2099_, v_m_u2081_2100_, v_m_u2082_2101_);
v_r_2103_ = lean_box(v_res_2102_);
return v_r_2103_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_Const_beq(lean_object* v_00_u03b1_2104_, lean_object* v_00_u03b2_2105_, lean_object* v_inst_2106_, lean_object* v_inst_2107_, lean_object* v_inst_2108_, lean_object* v_m_u2081_2109_, lean_object* v_m_u2082_2110_){
_start:
{
uint8_t v___x_2111_; 
v___x_2111_ = l_Std_DHashMap_Raw_Const_beq___redArg(v_inst_2106_, v_inst_2107_, v_inst_2108_, v_m_u2081_2109_, v_m_u2082_2110_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_beq___boxed(lean_object* v_00_u03b1_2112_, lean_object* v_00_u03b2_2113_, lean_object* v_inst_2114_, lean_object* v_inst_2115_, lean_object* v_inst_2116_, lean_object* v_m_u2081_2117_, lean_object* v_m_u2082_2118_){
_start:
{
uint8_t v_res_2119_; lean_object* v_r_2120_; 
v_res_2119_ = l_Std_DHashMap_Raw_Const_beq(v_00_u03b1_2112_, v_00_u03b2_2113_, v_inst_2114_, v_inst_2115_, v_inst_2116_, v_m_u2081_2117_, v_m_u2082_2118_);
v_r_2120_ = lean_box(v_res_2119_);
return v_r_2120_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_diff___redArg___lam__0(lean_object* v_inst_2121_, lean_object* v_inst_2122_, lean_object* v_m_u2082_2123_, uint8_t v___x_2124_, lean_object* v_k_2125_, lean_object* v_x_2126_){
_start:
{
uint8_t v___x_2127_; 
v___x_2127_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_2121_, v_inst_2122_, v_m_u2082_2123_, v_k_2125_);
if (v___x_2127_ == 0)
{
return v___x_2124_;
}
else
{
uint8_t v___x_2128_; 
v___x_2128_ = 0;
return v___x_2128_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_diff___redArg___lam__0___boxed(lean_object* v_inst_2129_, lean_object* v_inst_2130_, lean_object* v_m_u2082_2131_, lean_object* v___x_2132_, lean_object* v_k_2133_, lean_object* v_x_2134_){
_start:
{
uint8_t v___x_92__boxed_2135_; uint8_t v_res_2136_; lean_object* v_r_2137_; 
v___x_92__boxed_2135_ = lean_unbox(v___x_2132_);
v_res_2136_ = l_Std_DHashMap_Raw_diff___redArg___lam__0(v_inst_2129_, v_inst_2130_, v_m_u2082_2131_, v___x_92__boxed_2135_, v_k_2133_, v_x_2134_);
lean_dec(v_x_2134_);
lean_dec_ref(v_m_u2082_2131_);
v_r_2137_ = lean_box(v_res_2136_);
return v_r_2137_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_diff___redArg(lean_object* v_inst_2138_, lean_object* v_inst_2139_, lean_object* v_m_u2081_2140_, lean_object* v_m_u2082_2141_){
_start:
{
lean_object* v_size_2142_; lean_object* v_buckets_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; uint8_t v___x_2146_; 
v_size_2142_ = lean_ctor_get(v_m_u2081_2140_, 0);
v_buckets_2143_ = lean_ctor_get(v_m_u2081_2140_, 1);
v___x_2144_ = lean_unsigned_to_nat(0u);
v___x_2145_ = lean_array_get_size(v_buckets_2143_);
v___x_2146_ = lean_nat_dec_lt(v___x_2144_, v___x_2145_);
if (v___x_2146_ == 0)
{
lean_dec_ref(v_m_u2081_2140_);
lean_dec_ref(v_inst_2139_);
lean_dec_ref(v_inst_2138_);
return v_m_u2082_2141_;
}
else
{
lean_object* v_size_2147_; lean_object* v_buckets_2148_; lean_object* v___x_2149_; uint8_t v___x_2150_; 
v_size_2147_ = lean_ctor_get(v_m_u2082_2141_, 0);
v_buckets_2148_ = lean_ctor_get(v_m_u2082_2141_, 1);
v___x_2149_ = lean_array_get_size(v_buckets_2148_);
v___x_2150_ = lean_nat_dec_lt(v___x_2144_, v___x_2149_);
if (v___x_2150_ == 0)
{
lean_dec_ref(v_m_u2082_2141_);
lean_dec_ref(v_inst_2139_);
lean_dec_ref(v_inst_2138_);
return v_m_u2081_2140_;
}
else
{
uint8_t v___x_2151_; 
v___x_2151_ = lean_nat_dec_le(v_size_2142_, v_size_2147_);
if (v___x_2151_ == 0)
{
lean_object* v___f_2152_; lean_object* v___x_2153_; 
v___f_2152_ = ((lean_object*)(l_Std_DHashMap_Raw_union___redArg___closed__0));
v___x_2153_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_2152_, v_inst_2138_, v_inst_2139_, v_m_u2081_2140_, v_m_u2082_2141_);
return v___x_2153_;
}
else
{
lean_object* v___x_2154_; lean_object* v___f_2155_; lean_object* v___x_2156_; 
v___x_2154_ = lean_box(v___x_2151_);
v___f_2155_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_2155_, 0, v_inst_2138_);
lean_closure_set(v___f_2155_, 1, v_inst_2139_);
lean_closure_set(v___f_2155_, 2, v_m_u2082_2141_);
lean_closure_set(v___f_2155_, 3, v___x_2154_);
v___x_2156_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_2155_, v_m_u2081_2140_);
return v___x_2156_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_diff(lean_object* v_00_u03b1_2157_, lean_object* v_00_u03b2_2158_, lean_object* v_inst_2159_, lean_object* v_inst_2160_, lean_object* v_m_u2081_2161_, lean_object* v_m_u2082_2162_){
_start:
{
lean_object* v_size_2163_; lean_object* v_buckets_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; uint8_t v___x_2167_; 
v_size_2163_ = lean_ctor_get(v_m_u2081_2161_, 0);
v_buckets_2164_ = lean_ctor_get(v_m_u2081_2161_, 1);
v___x_2165_ = lean_unsigned_to_nat(0u);
v___x_2166_ = lean_array_get_size(v_buckets_2164_);
v___x_2167_ = lean_nat_dec_lt(v___x_2165_, v___x_2166_);
if (v___x_2167_ == 0)
{
lean_dec_ref(v_m_u2081_2161_);
lean_dec_ref(v_inst_2160_);
lean_dec_ref(v_inst_2159_);
return v_m_u2082_2162_;
}
else
{
lean_object* v_size_2168_; lean_object* v_buckets_2169_; lean_object* v___x_2170_; uint8_t v___x_2171_; 
v_size_2168_ = lean_ctor_get(v_m_u2082_2162_, 0);
v_buckets_2169_ = lean_ctor_get(v_m_u2082_2162_, 1);
v___x_2170_ = lean_array_get_size(v_buckets_2169_);
v___x_2171_ = lean_nat_dec_lt(v___x_2165_, v___x_2170_);
if (v___x_2171_ == 0)
{
lean_dec_ref(v_m_u2082_2162_);
lean_dec_ref(v_inst_2160_);
lean_dec_ref(v_inst_2159_);
return v_m_u2081_2161_;
}
else
{
uint8_t v___x_2172_; 
v___x_2172_ = lean_nat_dec_le(v_size_2163_, v_size_2168_);
if (v___x_2172_ == 0)
{
lean_object* v___f_2173_; lean_object* v___x_2174_; 
v___f_2173_ = ((lean_object*)(l_Std_DHashMap_Raw_union___redArg___closed__0));
v___x_2174_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_2173_, v_inst_2159_, v_inst_2160_, v_m_u2081_2161_, v_m_u2082_2162_);
return v___x_2174_;
}
else
{
lean_object* v___x_2175_; lean_object* v___f_2176_; lean_object* v___x_2177_; 
v___x_2175_ = lean_box(v___x_2172_);
v___f_2176_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_2176_, 0, v_inst_2159_);
lean_closure_set(v___f_2176_, 1, v_inst_2160_);
lean_closure_set(v___f_2176_, 2, v_m_u2082_2162_);
lean_closure_set(v___f_2176_, 3, v___x_2175_);
v___x_2177_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_2176_, v_m_u2081_2161_);
return v___x_2177_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instSDiffOfBEqOfHashable___redArg(lean_object* v_inst_2178_, lean_object* v_inst_2179_){
_start:
{
lean_object* v___x_2180_; 
v___x_2180_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_diff), 6, 4);
lean_closure_set(v___x_2180_, 0, lean_box(0));
lean_closure_set(v___x_2180_, 1, lean_box(0));
lean_closure_set(v___x_2180_, 2, v_inst_2178_);
lean_closure_set(v___x_2180_, 3, v_inst_2179_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instSDiffOfBEqOfHashable(lean_object* v_00_u03b1_2181_, lean_object* v_00_u03b2_2182_, lean_object* v_inst_2183_, lean_object* v_inst_2184_){
_start:
{
lean_object* v___x_2185_; 
v___x_2185_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_diff), 6, 4);
lean_closure_set(v___x_2185_, 0, lean_box(0));
lean_closure_set(v___x_2185_, 1, lean_box(0));
lean_closure_set(v___x_2185_, 2, v_inst_2183_);
lean_closure_set(v___x_2185_, 3, v_inst_2184_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_values___redArg___lam__0(lean_object* v_a_2186_, lean_object* v_b_2187_, lean_object* v_d_2188_){
_start:
{
lean_object* v___x_2189_; 
v___x_2189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2189_, 0, v_b_2187_);
lean_ctor_set(v___x_2189_, 1, v_d_2188_);
return v___x_2189_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_values___redArg___lam__0___boxed(lean_object* v_a_2190_, lean_object* v_b_2191_, lean_object* v_d_2192_){
_start:
{
lean_object* v_res_2193_; 
v_res_2193_ = l_Std_DHashMap_Raw_values___redArg___lam__0(v_a_2190_, v_b_2191_, v_d_2192_);
lean_dec(v_a_2190_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_values___redArg___lam__1(lean_object* v___x_2194_, lean_object* v___f_2195_, lean_object* v_l_2196_, lean_object* v_acc_2197_){
_start:
{
lean_object* v___x_2198_; 
v___x_2198_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_2194_, v___f_2195_, v_acc_2197_, v_l_2196_);
return v___x_2198_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_values___redArg(lean_object* v_m_2203_){
_start:
{
lean_object* v___x_2204_; lean_object* v_buckets_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; uint8_t v___x_2209_; 
v___x_2204_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_2205_ = lean_ctor_get(v_m_2203_, 1);
lean_inc_ref(v_buckets_2205_);
lean_dec_ref(v_m_2203_);
v___x_2206_ = lean_box(0);
v___x_2207_ = lean_array_get_size(v_buckets_2205_);
v___x_2208_ = lean_unsigned_to_nat(0u);
v___x_2209_ = lean_nat_dec_lt(v___x_2208_, v___x_2207_);
if (v___x_2209_ == 0)
{
lean_dec_ref(v_buckets_2205_);
return v___x_2206_;
}
else
{
lean_object* v___f_2210_; size_t v___x_2211_; size_t v___x_2212_; lean_object* v___x_2213_; 
v___f_2210_ = ((lean_object*)(l_Std_DHashMap_Raw_values___redArg___closed__1));
v___x_2211_ = lean_usize_of_nat(v___x_2207_);
v___x_2212_ = ((size_t)0ULL);
v___x_2213_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2204_, v___f_2210_, v_buckets_2205_, v___x_2211_, v___x_2212_, v___x_2206_);
return v___x_2213_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_values(lean_object* v_00_u03b1_2214_, lean_object* v_00_u03b2_2215_, lean_object* v_m_2216_){
_start:
{
lean_object* v___x_2217_; lean_object* v_buckets_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; uint8_t v___x_2222_; 
v___x_2217_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_2218_ = lean_ctor_get(v_m_2216_, 1);
lean_inc_ref(v_buckets_2218_);
lean_dec_ref(v_m_2216_);
v___x_2219_ = lean_box(0);
v___x_2220_ = lean_array_get_size(v_buckets_2218_);
v___x_2221_ = lean_unsigned_to_nat(0u);
v___x_2222_ = lean_nat_dec_lt(v___x_2221_, v___x_2220_);
if (v___x_2222_ == 0)
{
lean_dec_ref(v_buckets_2218_);
return v___x_2219_;
}
else
{
lean_object* v___f_2223_; size_t v___x_2224_; size_t v___x_2225_; lean_object* v___x_2226_; 
v___f_2223_ = ((lean_object*)(l_Std_DHashMap_Raw_values___redArg___closed__1));
v___x_2224_ = lean_usize_of_nat(v___x_2220_);
v___x_2225_ = ((size_t)0ULL);
v___x_2226_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2217_, v___f_2223_, v_buckets_2218_, v___x_2224_, v___x_2225_, v___x_2219_);
return v___x_2226_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_valuesArray___redArg___lam__0(lean_object* v_x1_2227_, lean_object* v_x2_2228_, lean_object* v_x3_2229_){
_start:
{
lean_object* v___x_2230_; 
v___x_2230_ = lean_array_push(v_x1_2227_, v_x3_2229_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_valuesArray___redArg___lam__0___boxed(lean_object* v_x1_2231_, lean_object* v_x2_2232_, lean_object* v_x3_2233_){
_start:
{
lean_object* v_res_2234_; 
v_res_2234_ = l_Std_DHashMap_Raw_valuesArray___redArg___lam__0(v_x1_2231_, v_x2_2232_, v_x3_2233_);
lean_dec(v_x2_2232_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_valuesArray___redArg(lean_object* v_m_2239_){
_start:
{
lean_object* v_size_2240_; lean_object* v_buckets_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; uint8_t v___x_2246_; 
v_size_2240_ = lean_ctor_get(v_m_2239_, 0);
lean_inc(v_size_2240_);
v_buckets_2241_ = lean_ctor_get(v_m_2239_, 1);
lean_inc_ref(v_buckets_2241_);
lean_dec_ref(v_m_2239_);
v___x_2242_ = lean_mk_empty_array_with_capacity(v_size_2240_);
lean_dec(v_size_2240_);
v___x_2243_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_2244_ = lean_unsigned_to_nat(0u);
v___x_2245_ = lean_array_get_size(v_buckets_2241_);
v___x_2246_ = lean_nat_dec_lt(v___x_2244_, v___x_2245_);
if (v___x_2246_ == 0)
{
lean_dec_ref(v_buckets_2241_);
return v___x_2242_;
}
else
{
lean_object* v___f_2247_; uint8_t v___x_2248_; 
v___f_2247_ = ((lean_object*)(l_Std_DHashMap_Raw_valuesArray___redArg___closed__1));
v___x_2248_ = lean_nat_dec_le(v___x_2245_, v___x_2245_);
if (v___x_2248_ == 0)
{
if (v___x_2246_ == 0)
{
lean_dec_ref(v_buckets_2241_);
return v___x_2242_;
}
else
{
size_t v___x_2249_; size_t v___x_2250_; lean_object* v___x_2251_; 
v___x_2249_ = ((size_t)0ULL);
v___x_2250_ = lean_usize_of_nat(v___x_2245_);
v___x_2251_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2243_, v___f_2247_, v_buckets_2241_, v___x_2249_, v___x_2250_, v___x_2242_);
return v___x_2251_;
}
}
else
{
size_t v___x_2252_; size_t v___x_2253_; lean_object* v___x_2254_; 
v___x_2252_ = ((size_t)0ULL);
v___x_2253_ = lean_usize_of_nat(v___x_2245_);
v___x_2254_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2243_, v___f_2247_, v_buckets_2241_, v___x_2252_, v___x_2253_, v___x_2242_);
return v___x_2254_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_valuesArray(lean_object* v_00_u03b1_2255_, lean_object* v_00_u03b2_2256_, lean_object* v_m_2257_){
_start:
{
lean_object* v_size_2258_; lean_object* v_buckets_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; uint8_t v___x_2264_; 
v_size_2258_ = lean_ctor_get(v_m_2257_, 0);
lean_inc(v_size_2258_);
v_buckets_2259_ = lean_ctor_get(v_m_2257_, 1);
lean_inc_ref(v_buckets_2259_);
lean_dec_ref(v_m_2257_);
v___x_2260_ = lean_mk_empty_array_with_capacity(v_size_2258_);
lean_dec(v_size_2258_);
v___x_2261_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_2262_ = lean_unsigned_to_nat(0u);
v___x_2263_ = lean_array_get_size(v_buckets_2259_);
v___x_2264_ = lean_nat_dec_lt(v___x_2262_, v___x_2263_);
if (v___x_2264_ == 0)
{
lean_dec_ref(v_buckets_2259_);
return v___x_2260_;
}
else
{
lean_object* v___f_2265_; uint8_t v___x_2266_; 
v___f_2265_ = ((lean_object*)(l_Std_DHashMap_Raw_valuesArray___redArg___closed__1));
v___x_2266_ = lean_nat_dec_le(v___x_2263_, v___x_2263_);
if (v___x_2266_ == 0)
{
if (v___x_2264_ == 0)
{
lean_dec_ref(v_buckets_2259_);
return v___x_2260_;
}
else
{
size_t v___x_2267_; size_t v___x_2268_; lean_object* v___x_2269_; 
v___x_2267_ = ((size_t)0ULL);
v___x_2268_ = lean_usize_of_nat(v___x_2263_);
v___x_2269_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2261_, v___f_2265_, v_buckets_2259_, v___x_2267_, v___x_2268_, v___x_2260_);
return v___x_2269_;
}
}
else
{
size_t v___x_2270_; size_t v___x_2271_; lean_object* v___x_2272_; 
v___x_2270_ = ((size_t)0ULL);
v___x_2271_ = lean_usize_of_nat(v___x_2263_);
v___x_2272_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2261_, v___f_2265_, v_buckets_2259_, v___x_2270_, v___x_2271_, v___x_2260_);
return v___x_2272_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insertMany___redArg(lean_object* v_inst_2273_, lean_object* v_inst_2274_, lean_object* v_inst_2275_, lean_object* v_m_2276_, lean_object* v_l_2277_){
_start:
{
lean_object* v_buckets_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; uint8_t v___x_2281_; 
v_buckets_2278_ = lean_ctor_get(v_m_2276_, 1);
v___x_2279_ = lean_unsigned_to_nat(0u);
v___x_2280_ = lean_array_get_size(v_buckets_2278_);
v___x_2281_ = lean_nat_dec_lt(v___x_2279_, v___x_2280_);
if (v___x_2281_ == 0)
{
lean_dec(v_l_2277_);
lean_dec(v_inst_2275_);
lean_dec_ref(v_inst_2274_);
lean_dec_ref(v_inst_2273_);
return v_m_2276_;
}
else
{
lean_object* v___x_2282_; 
v___x_2282_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v_inst_2275_, v_inst_2273_, v_inst_2274_, v_m_2276_, v_l_2277_);
return v___x_2282_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insertMany(lean_object* v_00_u03b1_2283_, lean_object* v_00_u03b2_2284_, lean_object* v_inst_2285_, lean_object* v_inst_2286_, lean_object* v_00_u03c1_2287_, lean_object* v_inst_2288_, lean_object* v_m_2289_, lean_object* v_l_2290_){
_start:
{
lean_object* v_buckets_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; uint8_t v___x_2294_; 
v_buckets_2291_ = lean_ctor_get(v_m_2289_, 1);
v___x_2292_ = lean_unsigned_to_nat(0u);
v___x_2293_ = lean_array_get_size(v_buckets_2291_);
v___x_2294_ = lean_nat_dec_lt(v___x_2292_, v___x_2293_);
if (v___x_2294_ == 0)
{
lean_dec(v_l_2290_);
lean_dec(v_inst_2288_);
lean_dec_ref(v_inst_2286_);
lean_dec_ref(v_inst_2285_);
return v_m_2289_;
}
else
{
lean_object* v___x_2295_; 
v___x_2295_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v_inst_2288_, v_inst_2285_, v_inst_2286_, v_m_2289_, v_l_2290_);
return v___x_2295_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_eraseManyEntries___redArg(lean_object* v_inst_2296_, lean_object* v_inst_2297_, lean_object* v_inst_2298_, lean_object* v_m_2299_, lean_object* v_l_2300_){
_start:
{
lean_object* v_buckets_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; uint8_t v___x_2304_; 
v_buckets_2301_ = lean_ctor_get(v_m_2299_, 1);
v___x_2302_ = lean_unsigned_to_nat(0u);
v___x_2303_ = lean_array_get_size(v_buckets_2301_);
v___x_2304_ = lean_nat_dec_lt(v___x_2302_, v___x_2303_);
if (v___x_2304_ == 0)
{
lean_dec(v_l_2300_);
lean_dec(v_inst_2298_);
lean_dec_ref(v_inst_2297_);
lean_dec_ref(v_inst_2296_);
return v_m_2299_;
}
else
{
lean_object* v___x_2305_; 
v___x_2305_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v_inst_2298_, v_inst_2296_, v_inst_2297_, v_m_2299_, v_l_2300_);
return v___x_2305_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_eraseManyEntries(lean_object* v_00_u03b1_2306_, lean_object* v_00_u03b2_2307_, lean_object* v_inst_2308_, lean_object* v_inst_2309_, lean_object* v_00_u03c1_2310_, lean_object* v_inst_2311_, lean_object* v_m_2312_, lean_object* v_l_2313_){
_start:
{
lean_object* v_buckets_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; uint8_t v___x_2317_; 
v_buckets_2314_ = lean_ctor_get(v_m_2312_, 1);
v___x_2315_ = lean_unsigned_to_nat(0u);
v___x_2316_ = lean_array_get_size(v_buckets_2314_);
v___x_2317_ = lean_nat_dec_lt(v___x_2315_, v___x_2316_);
if (v___x_2317_ == 0)
{
lean_dec(v_l_2313_);
lean_dec(v_inst_2311_);
lean_dec_ref(v_inst_2309_);
lean_dec_ref(v_inst_2308_);
return v_m_2312_;
}
else
{
lean_object* v___x_2318_; 
v___x_2318_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v_inst_2311_, v_inst_2308_, v_inst_2309_, v_m_2312_, v_l_2313_);
return v___x_2318_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_insertMany___redArg(lean_object* v_inst_2319_, lean_object* v_inst_2320_, lean_object* v_inst_2321_, lean_object* v_m_2322_, lean_object* v_l_2323_){
_start:
{
lean_object* v_buckets_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; uint8_t v___x_2327_; 
v_buckets_2324_ = lean_ctor_get(v_m_2322_, 1);
v___x_2325_ = lean_unsigned_to_nat(0u);
v___x_2326_ = lean_array_get_size(v_buckets_2324_);
v___x_2327_ = lean_nat_dec_lt(v___x_2325_, v___x_2326_);
if (v___x_2327_ == 0)
{
lean_dec(v_l_2323_);
lean_dec(v_inst_2321_);
lean_dec_ref(v_inst_2320_);
lean_dec_ref(v_inst_2319_);
return v_m_2322_;
}
else
{
lean_object* v___x_2328_; 
v___x_2328_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v_inst_2321_, v_inst_2319_, v_inst_2320_, v_m_2322_, v_l_2323_);
return v___x_2328_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_insertMany(lean_object* v_00_u03b1_2329_, lean_object* v_00_u03b2_2330_, lean_object* v_inst_2331_, lean_object* v_inst_2332_, lean_object* v_00_u03c1_2333_, lean_object* v_inst_2334_, lean_object* v_m_2335_, lean_object* v_l_2336_){
_start:
{
lean_object* v_buckets_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; uint8_t v___x_2340_; 
v_buckets_2337_ = lean_ctor_get(v_m_2335_, 1);
v___x_2338_ = lean_unsigned_to_nat(0u);
v___x_2339_ = lean_array_get_size(v_buckets_2337_);
v___x_2340_ = lean_nat_dec_lt(v___x_2338_, v___x_2339_);
if (v___x_2340_ == 0)
{
lean_dec(v_l_2336_);
lean_dec(v_inst_2334_);
lean_dec_ref(v_inst_2332_);
lean_dec_ref(v_inst_2331_);
return v_m_2335_;
}
else
{
lean_object* v___x_2341_; 
v___x_2341_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v_inst_2334_, v_inst_2331_, v_inst_2332_, v_m_2335_, v_l_2336_);
return v___x_2341_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_insertManyIfNewUnit___redArg(lean_object* v_inst_2342_, lean_object* v_inst_2343_, lean_object* v_inst_2344_, lean_object* v_m_2345_, lean_object* v_l_2346_){
_start:
{
lean_object* v_buckets_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; uint8_t v___x_2350_; 
v_buckets_2347_ = lean_ctor_get(v_m_2345_, 1);
v___x_2348_ = lean_unsigned_to_nat(0u);
v___x_2349_ = lean_array_get_size(v_buckets_2347_);
v___x_2350_ = lean_nat_dec_lt(v___x_2348_, v___x_2349_);
if (v___x_2350_ == 0)
{
lean_dec(v_l_2346_);
lean_dec(v_inst_2344_);
lean_dec_ref(v_inst_2343_);
lean_dec_ref(v_inst_2342_);
return v_m_2345_;
}
else
{
lean_object* v___x_2351_; 
v___x_2351_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_2344_, v_inst_2342_, v_inst_2343_, v_m_2345_, v_l_2346_);
return v___x_2351_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_insertManyIfNewUnit(lean_object* v_00_u03b1_2352_, lean_object* v_inst_2353_, lean_object* v_inst_2354_, lean_object* v_00_u03c1_2355_, lean_object* v_inst_2356_, lean_object* v_m_2357_, lean_object* v_l_2358_){
_start:
{
lean_object* v_buckets_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; uint8_t v___x_2362_; 
v_buckets_2359_ = lean_ctor_get(v_m_2357_, 1);
v___x_2360_ = lean_unsigned_to_nat(0u);
v___x_2361_ = lean_array_get_size(v_buckets_2359_);
v___x_2362_ = lean_nat_dec_lt(v___x_2360_, v___x_2361_);
if (v___x_2362_ == 0)
{
lean_dec(v_l_2358_);
lean_dec(v_inst_2356_);
lean_dec_ref(v_inst_2354_);
lean_dec_ref(v_inst_2353_);
return v_m_2357_;
}
else
{
lean_object* v___x_2363_; 
v___x_2363_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_2356_, v_inst_2353_, v_inst_2354_, v_m_2357_, v_l_2358_);
return v___x_2363_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_unitOfArray___redArg(lean_object* v_inst_2368_, lean_object* v_inst_2369_, lean_object* v_l_2370_){
_start:
{
lean_object* v___x_2371_; uint8_t v___x_2372_; 
v___x_2371_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
v___x_2372_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2372_ == 0)
{
lean_dec_ref(v_l_2370_);
lean_dec_ref(v_inst_2369_);
lean_dec_ref(v_inst_2368_);
return v___x_2371_;
}
else
{
lean_object* v___f_2373_; lean_object* v___x_2374_; 
v___f_2373_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1));
v___x_2374_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2373_, v_inst_2368_, v_inst_2369_, v___x_2371_, v_l_2370_);
return v___x_2374_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_unitOfArray(lean_object* v_00_u03b1_2375_, lean_object* v_inst_2376_, lean_object* v_inst_2377_, lean_object* v_l_2378_){
_start:
{
lean_object* v___x_2379_; uint8_t v___x_2380_; 
v___x_2379_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
v___x_2380_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2380_ == 0)
{
lean_dec_ref(v_l_2378_);
lean_dec_ref(v_inst_2377_);
lean_dec_ref(v_inst_2376_);
return v___x_2379_;
}
else
{
lean_object* v___f_2381_; lean_object* v___x_2382_; 
v___f_2381_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1));
v___x_2382_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2381_, v_inst_2376_, v_inst_2377_, v___x_2379_, v_l_2378_);
return v___x_2382_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_numBuckets___redArg(lean_object* v_m_2383_){
_start:
{
lean_object* v_buckets_2384_; lean_object* v___x_2385_; 
v_buckets_2384_ = lean_ctor_get(v_m_2383_, 1);
v___x_2385_ = lean_array_get_size(v_buckets_2384_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_numBuckets___redArg___boxed(lean_object* v_m_2386_){
_start:
{
lean_object* v_res_2387_; 
v_res_2387_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2386_);
lean_dec_ref(v_m_2386_);
return v_res_2387_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_numBuckets(lean_object* v_00_u03b1_2388_, lean_object* v_00_u03b2_2389_, lean_object* v_m_2390_){
_start:
{
lean_object* v___x_2391_; 
v___x_2391_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2390_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_numBuckets___boxed(lean_object* v_00_u03b1_2392_, lean_object* v_00_u03b2_2393_, lean_object* v_m_2394_){
_start:
{
lean_object* v_res_2395_; 
v_res_2395_ = l_Std_DHashMap_Raw_Internal_numBuckets(v_00_u03b1_2392_, v_00_u03b2_2393_, v_m_2394_);
lean_dec_ref(v_m_2394_);
return v_res_2395_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toList___redArg___lam__0(lean_object* v_a_2396_, lean_object* v_b_2397_, lean_object* v_d_2398_){
_start:
{
lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___x_2399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2399_, 0, v_a_2396_);
lean_ctor_set(v___x_2399_, 1, v_b_2397_);
v___x_2400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2399_);
lean_ctor_set(v___x_2400_, 1, v_d_2398_);
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toList___redArg___lam__1(lean_object* v___x_2401_, lean_object* v___f_2402_, lean_object* v_l_2403_, lean_object* v_acc_2404_){
_start:
{
lean_object* v___x_2405_; 
v___x_2405_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_2401_, v___f_2402_, v_acc_2404_, v_l_2403_);
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toList___redArg(lean_object* v_m_2410_){
_start:
{
lean_object* v___x_2411_; lean_object* v_buckets_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; uint8_t v___x_2416_; 
v___x_2411_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_2412_ = lean_ctor_get(v_m_2410_, 1);
lean_inc_ref(v_buckets_2412_);
lean_dec_ref(v_m_2410_);
v___x_2413_ = lean_box(0);
v___x_2414_ = lean_array_get_size(v_buckets_2412_);
v___x_2415_ = lean_unsigned_to_nat(0u);
v___x_2416_ = lean_nat_dec_lt(v___x_2415_, v___x_2414_);
if (v___x_2416_ == 0)
{
lean_dec_ref(v_buckets_2412_);
return v___x_2413_;
}
else
{
lean_object* v___f_2417_; size_t v___x_2418_; size_t v___x_2419_; lean_object* v___x_2420_; 
v___f_2417_ = ((lean_object*)(l_Std_DHashMap_Raw_toList___redArg___closed__1));
v___x_2418_ = lean_usize_of_nat(v___x_2414_);
v___x_2419_ = ((size_t)0ULL);
v___x_2420_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2411_, v___f_2417_, v_buckets_2412_, v___x_2418_, v___x_2419_, v___x_2413_);
return v___x_2420_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toList(lean_object* v_00_u03b1_2421_, lean_object* v_00_u03b2_2422_, lean_object* v_m_2423_){
_start:
{
lean_object* v___x_2424_; lean_object* v_buckets_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; uint8_t v___x_2429_; 
v___x_2424_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_2425_ = lean_ctor_get(v_m_2423_, 1);
lean_inc_ref(v_buckets_2425_);
lean_dec_ref(v_m_2423_);
v___x_2426_ = lean_box(0);
v___x_2427_ = lean_array_get_size(v_buckets_2425_);
v___x_2428_ = lean_unsigned_to_nat(0u);
v___x_2429_ = lean_nat_dec_lt(v___x_2428_, v___x_2427_);
if (v___x_2429_ == 0)
{
lean_dec_ref(v_buckets_2425_);
return v___x_2426_;
}
else
{
lean_object* v___f_2430_; size_t v___x_2431_; size_t v___x_2432_; lean_object* v___x_2433_; 
v___f_2430_ = ((lean_object*)(l_Std_DHashMap_Raw_toList___redArg___closed__1));
v___x_2431_ = lean_usize_of_nat(v___x_2427_);
v___x_2432_ = ((size_t)0ULL);
v___x_2433_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2424_, v___f_2430_, v_buckets_2425_, v___x_2431_, v___x_2432_, v___x_2426_);
return v___x_2433_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toList___redArg___lam__0(lean_object* v_a_2434_, lean_object* v_b_2435_, lean_object* v_d_2436_){
_start:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2437_, 0, v_a_2434_);
lean_ctor_set(v___x_2437_, 1, v_b_2435_);
v___x_2438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2437_);
lean_ctor_set(v___x_2438_, 1, v_d_2436_);
return v___x_2438_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toList___redArg___lam__1(lean_object* v___x_2439_, lean_object* v___f_2440_, lean_object* v_l_2441_, lean_object* v_acc_2442_){
_start:
{
lean_object* v___x_2443_; 
v___x_2443_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_2439_, v___f_2440_, v_acc_2442_, v_l_2441_);
return v___x_2443_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toList___redArg(lean_object* v_m_2448_){
_start:
{
lean_object* v___x_2449_; lean_object* v_buckets_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; uint8_t v___x_2454_; 
v___x_2449_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_2450_ = lean_ctor_get(v_m_2448_, 1);
lean_inc_ref(v_buckets_2450_);
lean_dec_ref(v_m_2448_);
v___x_2451_ = lean_box(0);
v___x_2452_ = lean_array_get_size(v_buckets_2450_);
v___x_2453_ = lean_unsigned_to_nat(0u);
v___x_2454_ = lean_nat_dec_lt(v___x_2453_, v___x_2452_);
if (v___x_2454_ == 0)
{
lean_dec_ref(v_buckets_2450_);
return v___x_2451_;
}
else
{
lean_object* v___f_2455_; size_t v___x_2456_; size_t v___x_2457_; lean_object* v___x_2458_; 
v___f_2455_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_toList___redArg___closed__1));
v___x_2456_ = lean_usize_of_nat(v___x_2452_);
v___x_2457_ = ((size_t)0ULL);
v___x_2458_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2449_, v___f_2455_, v_buckets_2450_, v___x_2456_, v___x_2457_, v___x_2451_);
return v___x_2458_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toList(lean_object* v_00_u03b1_2459_, lean_object* v_00_u03b2_2460_, lean_object* v_m_2461_){
_start:
{
lean_object* v___x_2462_; lean_object* v_buckets_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; uint8_t v___x_2467_; 
v___x_2462_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_2463_ = lean_ctor_get(v_m_2461_, 1);
lean_inc_ref(v_buckets_2463_);
lean_dec_ref(v_m_2461_);
v___x_2464_ = lean_box(0);
v___x_2465_ = lean_array_get_size(v_buckets_2463_);
v___x_2466_ = lean_unsigned_to_nat(0u);
v___x_2467_ = lean_nat_dec_lt(v___x_2466_, v___x_2465_);
if (v___x_2467_ == 0)
{
lean_dec_ref(v_buckets_2463_);
return v___x_2464_;
}
else
{
lean_object* v___f_2468_; size_t v___x_2469_; size_t v___x_2470_; lean_object* v___x_2471_; 
v___f_2468_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_toList___redArg___closed__1));
v___x_2469_ = lean_usize_of_nat(v___x_2465_);
v___x_2470_ = ((size_t)0ULL);
v___x_2471_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2462_, v___f_2468_, v_buckets_2463_, v___x_2469_, v___x_2470_, v___x_2464_);
return v___x_2471_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instRepr___redArg___lam__2(lean_object* v___x_2475_, lean_object* v___f_2476_, lean_object* v_m_2477_, lean_object* v_prec_2478_){
_start:
{
lean_object* v___x_2479_; lean_object* v_buckets_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2500_; 
v___x_2479_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_2480_ = lean_ctor_get(v_m_2477_, 1);
v_isSharedCheck_2500_ = !lean_is_exclusive(v_m_2477_);
if (v_isSharedCheck_2500_ == 0)
{
lean_object* v_unused_2501_; 
v_unused_2501_ = lean_ctor_get(v_m_2477_, 0);
lean_dec(v_unused_2501_);
v___x_2482_ = v_m_2477_;
v_isShared_2483_ = v_isSharedCheck_2500_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_buckets_2480_);
lean_dec(v_m_2477_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2500_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2484_; lean_object* v___y_2486_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; uint8_t v___x_2495_; 
v___x_2484_ = ((lean_object*)(l_Std_DHashMap_Raw_instRepr___redArg___lam__2___closed__1));
v___x_2492_ = lean_box(0);
v___x_2493_ = lean_array_get_size(v_buckets_2480_);
v___x_2494_ = lean_unsigned_to_nat(0u);
v___x_2495_ = lean_nat_dec_lt(v___x_2494_, v___x_2493_);
if (v___x_2495_ == 0)
{
lean_dec_ref(v_buckets_2480_);
lean_dec_ref(v___f_2476_);
v___y_2486_ = v___x_2492_;
goto v___jp_2485_;
}
else
{
lean_object* v___f_2496_; size_t v___x_2497_; size_t v___x_2498_; lean_object* v___x_2499_; 
v___f_2496_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_toList___redArg___lam__1), 4, 2);
lean_closure_set(v___f_2496_, 0, v___x_2479_);
lean_closure_set(v___f_2496_, 1, v___f_2476_);
v___x_2497_ = lean_usize_of_nat(v___x_2493_);
v___x_2498_ = ((size_t)0ULL);
v___x_2499_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2479_, v___f_2496_, v_buckets_2480_, v___x_2497_, v___x_2498_, v___x_2492_);
v___y_2486_ = v___x_2499_;
goto v___jp_2485_;
}
v___jp_2485_:
{
lean_object* v___x_2487_; lean_object* v___x_2489_; 
v___x_2487_ = l_List_repr___redArg(v___x_2475_, v___y_2486_);
if (v_isShared_2483_ == 0)
{
lean_ctor_set_tag(v___x_2482_, 5);
lean_ctor_set(v___x_2482_, 1, v___x_2487_);
lean_ctor_set(v___x_2482_, 0, v___x_2484_);
v___x_2489_ = v___x_2482_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v___x_2484_);
lean_ctor_set(v_reuseFailAlloc_2491_, 1, v___x_2487_);
v___x_2489_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
lean_object* v___x_2490_; 
v___x_2490_ = l_Repr_addAppParen(v___x_2489_, v_prec_2478_);
return v___x_2490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instRepr___redArg___lam__2___boxed(lean_object* v___x_2502_, lean_object* v___f_2503_, lean_object* v_m_2504_, lean_object* v_prec_2505_){
_start:
{
lean_object* v_res_2506_; 
v_res_2506_ = l_Std_DHashMap_Raw_instRepr___redArg___lam__2(v___x_2502_, v___f_2503_, v_m_2504_, v_prec_2505_);
lean_dec(v_prec_2505_);
return v_res_2506_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instRepr___redArg(lean_object* v_inst_2507_, lean_object* v_inst_2508_){
_start:
{
lean_object* v___f_2509_; lean_object* v___x_2510_; lean_object* v___f_2511_; 
v___f_2509_ = ((lean_object*)(l_Std_DHashMap_Raw_toList___redArg___closed__0));
v___x_2510_ = lean_alloc_closure((void*)(l_Sigma_repr___boxed), 6, 4);
lean_closure_set(v___x_2510_, 0, lean_box(0));
lean_closure_set(v___x_2510_, 1, lean_box(0));
lean_closure_set(v___x_2510_, 2, v_inst_2507_);
lean_closure_set(v___x_2510_, 3, v_inst_2508_);
v___f_2511_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instRepr___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2511_, 0, v___x_2510_);
lean_closure_set(v___f_2511_, 1, v___f_2509_);
return v___f_2511_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instRepr(lean_object* v_00_u03b1_2512_, lean_object* v_00_u03b2_2513_, lean_object* v_inst_2514_, lean_object* v_inst_2515_){
_start:
{
lean_object* v___x_2516_; 
v___x_2516_ = l_Std_DHashMap_Raw_instRepr___redArg(v_inst_2514_, v_inst_2515_);
return v___x_2516_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keys___redArg___lam__0(lean_object* v_a_2517_, lean_object* v_b_2518_, lean_object* v_d_2519_){
_start:
{
lean_object* v___x_2520_; 
v___x_2520_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2520_, 0, v_a_2517_);
lean_ctor_set(v___x_2520_, 1, v_d_2519_);
return v___x_2520_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keys___redArg___lam__0___boxed(lean_object* v_a_2521_, lean_object* v_b_2522_, lean_object* v_d_2523_){
_start:
{
lean_object* v_res_2524_; 
v_res_2524_ = l_Std_DHashMap_Raw_keys___redArg___lam__0(v_a_2521_, v_b_2522_, v_d_2523_);
lean_dec(v_b_2522_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keys___redArg(lean_object* v_m_2529_){
_start:
{
lean_object* v___x_2530_; lean_object* v_buckets_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; uint8_t v___x_2535_; 
v___x_2530_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_2531_ = lean_ctor_get(v_m_2529_, 1);
lean_inc_ref(v_buckets_2531_);
lean_dec_ref(v_m_2529_);
v___x_2532_ = lean_box(0);
v___x_2533_ = lean_array_get_size(v_buckets_2531_);
v___x_2534_ = lean_unsigned_to_nat(0u);
v___x_2535_ = lean_nat_dec_lt(v___x_2534_, v___x_2533_);
if (v___x_2535_ == 0)
{
lean_dec_ref(v_buckets_2531_);
return v___x_2532_;
}
else
{
lean_object* v___f_2536_; size_t v___x_2537_; size_t v___x_2538_; lean_object* v___x_2539_; 
v___f_2536_ = ((lean_object*)(l_Std_DHashMap_Raw_keys___redArg___closed__1));
v___x_2537_ = lean_usize_of_nat(v___x_2533_);
v___x_2538_ = ((size_t)0ULL);
v___x_2539_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2530_, v___f_2536_, v_buckets_2531_, v___x_2537_, v___x_2538_, v___x_2532_);
return v___x_2539_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keys(lean_object* v_00_u03b1_2540_, lean_object* v_00_u03b2_2541_, lean_object* v_m_2542_){
_start:
{
lean_object* v___x_2543_; lean_object* v_buckets_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; uint8_t v___x_2548_; 
v___x_2543_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_2544_ = lean_ctor_get(v_m_2542_, 1);
lean_inc_ref(v_buckets_2544_);
lean_dec_ref(v_m_2542_);
v___x_2545_ = lean_box(0);
v___x_2546_ = lean_array_get_size(v_buckets_2544_);
v___x_2547_ = lean_unsigned_to_nat(0u);
v___x_2548_ = lean_nat_dec_lt(v___x_2547_, v___x_2546_);
if (v___x_2548_ == 0)
{
lean_dec_ref(v_buckets_2544_);
return v___x_2545_;
}
else
{
lean_object* v___f_2549_; size_t v___x_2550_; size_t v___x_2551_; lean_object* v___x_2552_; 
v___f_2549_ = ((lean_object*)(l_Std_DHashMap_Raw_keys___redArg___closed__1));
v___x_2550_ = lean_usize_of_nat(v___x_2546_);
v___x_2551_ = ((size_t)0ULL);
v___x_2552_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2543_, v___f_2549_, v_buckets_2544_, v___x_2550_, v___x_2551_, v___x_2545_);
return v___x_2552_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_ofList___redArg(lean_object* v_inst_2557_, lean_object* v_inst_2558_, lean_object* v_l_2559_){
_start:
{
lean_object* v___x_2560_; uint8_t v___x_2561_; 
v___x_2560_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
v___x_2561_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2561_ == 0)
{
lean_dec(v_l_2559_);
lean_dec_ref(v_inst_2558_);
lean_dec_ref(v_inst_2557_);
return v___x_2560_;
}
else
{
lean_object* v___f_2562_; lean_object* v___x_2563_; 
v___f_2562_ = ((lean_object*)(l_Std_DHashMap_Raw_ofList___redArg___closed__1));
v___x_2563_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_2562_, v_inst_2557_, v_inst_2558_, v___x_2560_, v_l_2559_);
return v___x_2563_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_ofList(lean_object* v_00_u03b1_2564_, lean_object* v_00_u03b2_2565_, lean_object* v_inst_2566_, lean_object* v_inst_2567_, lean_object* v_l_2568_){
_start:
{
lean_object* v___x_2569_; uint8_t v___x_2570_; 
v___x_2569_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
v___x_2570_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2570_ == 0)
{
lean_dec(v_l_2568_);
lean_dec_ref(v_inst_2567_);
lean_dec_ref(v_inst_2566_);
return v___x_2569_;
}
else
{
lean_object* v___f_2571_; lean_object* v___x_2572_; 
v___f_2571_ = ((lean_object*)(l_Std_DHashMap_Raw_ofList___redArg___closed__1));
v___x_2572_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_2571_, v_inst_2566_, v_inst_2567_, v___x_2569_, v_l_2568_);
return v___x_2572_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_ofArray___redArg(lean_object* v_inst_2573_, lean_object* v_inst_2574_, lean_object* v_l_2575_){
_start:
{
lean_object* v___x_2576_; uint8_t v___x_2577_; 
v___x_2576_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
v___x_2577_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2577_ == 0)
{
lean_dec_ref(v_l_2575_);
lean_dec_ref(v_inst_2574_);
lean_dec_ref(v_inst_2573_);
return v___x_2576_;
}
else
{
lean_object* v___f_2578_; lean_object* v___x_2579_; 
v___f_2578_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1));
v___x_2579_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_2578_, v_inst_2573_, v_inst_2574_, v___x_2576_, v_l_2575_);
return v___x_2579_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_ofArray(lean_object* v_00_u03b1_2580_, lean_object* v_00_u03b2_2581_, lean_object* v_inst_2582_, lean_object* v_inst_2583_, lean_object* v_l_2584_){
_start:
{
lean_object* v___x_2585_; uint8_t v___x_2586_; 
v___x_2585_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
v___x_2586_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2586_ == 0)
{
lean_dec_ref(v_l_2584_);
lean_dec_ref(v_inst_2583_);
lean_dec_ref(v_inst_2582_);
return v___x_2585_;
}
else
{
lean_object* v___f_2587_; lean_object* v___x_2588_; 
v___f_2587_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1));
v___x_2588_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_2587_, v_inst_2582_, v_inst_2583_, v___x_2585_, v_l_2584_);
return v___x_2588_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_ofList___redArg(lean_object* v_inst_2589_, lean_object* v_inst_2590_, lean_object* v_l_2591_){
_start:
{
lean_object* v___x_2592_; uint8_t v___x_2593_; 
v___x_2592_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
v___x_2593_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2593_ == 0)
{
lean_dec(v_l_2591_);
lean_dec_ref(v_inst_2590_);
lean_dec_ref(v_inst_2589_);
return v___x_2592_;
}
else
{
lean_object* v___f_2594_; lean_object* v___x_2595_; 
v___f_2594_ = ((lean_object*)(l_Std_DHashMap_Raw_ofList___redArg___closed__1));
v___x_2595_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_2594_, v_inst_2589_, v_inst_2590_, v___x_2592_, v_l_2591_);
return v___x_2595_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_ofList(lean_object* v_00_u03b1_2596_, lean_object* v_00_u03b2_2597_, lean_object* v_inst_2598_, lean_object* v_inst_2599_, lean_object* v_l_2600_){
_start:
{
lean_object* v___x_2601_; uint8_t v___x_2602_; 
v___x_2601_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
v___x_2602_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2602_ == 0)
{
lean_dec(v_l_2600_);
lean_dec_ref(v_inst_2599_);
lean_dec_ref(v_inst_2598_);
return v___x_2601_;
}
else
{
lean_object* v___f_2603_; lean_object* v___x_2604_; 
v___f_2603_ = ((lean_object*)(l_Std_DHashMap_Raw_ofList___redArg___closed__1));
v___x_2604_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_2603_, v_inst_2598_, v_inst_2599_, v___x_2601_, v_l_2600_);
return v___x_2604_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_ofArray___redArg(lean_object* v_inst_2605_, lean_object* v_inst_2606_, lean_object* v_l_2607_){
_start:
{
lean_object* v___x_2608_; uint8_t v___x_2609_; 
v___x_2608_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
v___x_2609_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2609_ == 0)
{
lean_dec_ref(v_l_2607_);
lean_dec_ref(v_inst_2606_);
lean_dec_ref(v_inst_2605_);
return v___x_2608_;
}
else
{
lean_object* v___f_2610_; lean_object* v___x_2611_; 
v___f_2610_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1));
v___x_2611_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_2610_, v_inst_2605_, v_inst_2606_, v___x_2608_, v_l_2607_);
return v___x_2611_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_ofArray(lean_object* v_00_u03b1_2612_, lean_object* v_00_u03b2_2613_, lean_object* v_inst_2614_, lean_object* v_inst_2615_, lean_object* v_l_2616_){
_start:
{
lean_object* v___x_2617_; uint8_t v___x_2618_; 
v___x_2617_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
v___x_2618_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2618_ == 0)
{
lean_dec_ref(v_l_2616_);
lean_dec_ref(v_inst_2615_);
lean_dec_ref(v_inst_2614_);
return v___x_2617_;
}
else
{
lean_object* v___f_2619_; lean_object* v___x_2620_; 
v___f_2619_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1));
v___x_2620_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_2619_, v_inst_2614_, v_inst_2615_, v___x_2617_, v_l_2616_);
return v___x_2620_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_unitOfList___redArg(lean_object* v_inst_2621_, lean_object* v_inst_2622_, lean_object* v_l_2623_){
_start:
{
lean_object* v___x_2624_; uint8_t v___x_2625_; 
v___x_2624_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
v___x_2625_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2625_ == 0)
{
lean_dec(v_l_2623_);
lean_dec_ref(v_inst_2622_);
lean_dec_ref(v_inst_2621_);
return v___x_2624_;
}
else
{
lean_object* v___f_2626_; lean_object* v___x_2627_; 
v___f_2626_ = ((lean_object*)(l_Std_DHashMap_Raw_ofList___redArg___closed__1));
v___x_2627_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2626_, v_inst_2621_, v_inst_2622_, v___x_2624_, v_l_2623_);
return v___x_2627_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_unitOfList(lean_object* v_00_u03b1_2628_, lean_object* v_inst_2629_, lean_object* v_inst_2630_, lean_object* v_l_2631_){
_start:
{
lean_object* v___x_2632_; uint8_t v___x_2633_; 
v___x_2632_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
v___x_2633_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2633_ == 0)
{
lean_dec(v_l_2631_);
lean_dec_ref(v_inst_2630_);
lean_dec_ref(v_inst_2629_);
return v___x_2632_;
}
else
{
lean_object* v___f_2634_; lean_object* v___x_2635_; 
v___f_2634_ = ((lean_object*)(l_Std_DHashMap_Raw_ofList___redArg___closed__1));
v___x_2635_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2634_, v_inst_2629_, v_inst_2630_, v___x_2632_, v_l_2631_);
return v___x_2635_;
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
