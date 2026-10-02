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
static lean_once_cell_t l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__0;
static lean_once_cell_t l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instEmptyCollection___redArg();
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instEmptyCollection___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_DHashMap_Raw_instEmptyCollection___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Raw_instEmptyCollection___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instEmptyCollection(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInhabited___redArg();
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInhabited___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_DHashMap_Raw_instInhabited___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Raw_instInhabited___closed__0;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instMembershipOfBEqOfHashable___redArg();
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instMembershipOfBEqOfHashable___redArg___boxed(lean_object*);
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
static lean_object* _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__0(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = lean_box(0);
v___x_30_ = lean_unsigned_to_nat(16u);
v___x_31_ = lean_mk_array(v___x_30_, v___x_29_);
return v___x_31_;
}
}
static lean_object* _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1(void){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_32_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__0, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__0_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__0);
v___x_33_ = lean_unsigned_to_nat(0u);
v___x_34_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_34_, 0, v___x_33_);
lean_ctor_set(v___x_34_, 1, v___x_32_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instEmptyCollection___redArg___boxed(lean_object* v___dummy_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Std_DHashMap_Raw_instEmptyCollection___redArg();
return v_res_38_;
}
}
static lean_object* _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__0(void){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Std_DHashMap_Raw_instEmptyCollection___redArg();
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instEmptyCollection(lean_object* v_00_u03b1_40_, lean_object* v_00_u03b2_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__0, &l_Std_DHashMap_Raw_instEmptyCollection___closed__0_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__0);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInhabited___redArg(){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInhabited___redArg___boxed(lean_object* v___dummy_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Std_DHashMap_Raw_instInhabited___redArg();
return v_res_46_;
}
}
static lean_object* _init_l_Std_DHashMap_Raw_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Std_DHashMap_Raw_instInhabited___redArg();
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInhabited(lean_object* v_00_u03b1_48_, lean_object* v_00_u03b2_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = lean_obj_once(&l_Std_DHashMap_Raw_instInhabited___closed__0, &l_Std_DHashMap_Raw_instInhabited___closed__0_once, _init_l_Std_DHashMap_Raw_instInhabited___closed__0);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_markLinear___redArg(lean_object* v_m_51_){
_start:
{
lean_object* v_size_52_; lean_object* v_buckets_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_61_; 
v_size_52_ = lean_ctor_get(v_m_51_, 0);
v_buckets_53_ = lean_ctor_get(v_m_51_, 1);
v_isSharedCheck_61_ = !lean_is_exclusive(v_m_51_);
if (v_isSharedCheck_61_ == 0)
{
v___x_55_ = v_m_51_;
v_isShared_56_ = v_isSharedCheck_61_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_buckets_53_);
lean_inc(v_size_52_);
lean_dec(v_m_51_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_61_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v___x_57_; lean_object* v___x_59_; 
v___x_57_ = lean_array_mark_linear(v_buckets_53_);
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 1, v___x_57_);
v___x_59_ = v___x_55_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v_size_52_);
lean_ctor_set(v_reuseFailAlloc_60_, 1, v___x_57_);
v___x_59_ = v_reuseFailAlloc_60_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
return v___x_59_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_markLinear(lean_object* v_00_u03b1_62_, lean_object* v_00_u03b2_63_, lean_object* v_m_64_){
_start:
{
lean_object* v_size_65_; lean_object* v_buckets_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_74_; 
v_size_65_ = lean_ctor_get(v_m_64_, 0);
v_buckets_66_ = lean_ctor_get(v_m_64_, 1);
v_isSharedCheck_74_ = !lean_is_exclusive(v_m_64_);
if (v_isSharedCheck_74_ == 0)
{
v___x_68_ = v_m_64_;
v_isShared_69_ = v_isSharedCheck_74_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_buckets_66_);
lean_inc(v_size_65_);
lean_dec(v_m_64_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_74_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
lean_object* v___x_70_; lean_object* v___x_72_; 
v___x_70_ = lean_array_mark_linear(v_buckets_66_);
if (v_isShared_69_ == 0)
{
lean_ctor_set(v___x_68_, 1, v___x_70_);
v___x_72_ = v___x_68_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_size_65_);
lean_ctor_set(v_reuseFailAlloc_73_, 1, v___x_70_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
}
static lean_object* _init_l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__6(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = ((lean_object*)(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__5));
v___x_116_ = l_String_toRawSubstring_x27(v___x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1(lean_object* v_x_140_, lean_object* v_a_141_, lean_object* v_a_142_){
_start:
{
lean_object* v___x_143_; uint8_t v___x_144_; 
v___x_143_ = ((lean_object*)(l_Std_DHashMap_Raw_term___x7em___00__closed__4));
lean_inc(v_x_140_);
v___x_144_ = l_Lean_Syntax_isOfKind(v_x_140_, v___x_143_);
if (v___x_144_ == 0)
{
lean_object* v___x_145_; lean_object* v___x_146_; 
lean_dec(v_x_140_);
v___x_145_ = lean_box(1);
v___x_146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
lean_ctor_set(v___x_146_, 1, v_a_142_);
return v___x_146_;
}
else
{
lean_object* v_quotContext_147_; lean_object* v_currMacroScope_148_; lean_object* v_ref_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; uint8_t v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v_quotContext_147_ = lean_ctor_get(v_a_141_, 1);
v_currMacroScope_148_ = lean_ctor_get(v_a_141_, 2);
v_ref_149_ = lean_ctor_get(v_a_141_, 5);
v___x_150_ = lean_unsigned_to_nat(0u);
v___x_151_ = l_Lean_Syntax_getArg(v_x_140_, v___x_150_);
v___x_152_ = lean_unsigned_to_nat(2u);
v___x_153_ = l_Lean_Syntax_getArg(v_x_140_, v___x_152_);
lean_dec(v_x_140_);
v___x_154_ = 0;
v___x_155_ = l_Lean_SourceInfo_fromRef(v_ref_149_, v___x_154_);
v___x_156_ = ((lean_object*)(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4));
v___x_157_ = lean_obj_once(&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__6, &l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__6_once, _init_l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__6);
v___x_158_ = ((lean_object*)(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__8));
lean_inc(v_currMacroScope_148_);
lean_inc(v_quotContext_147_);
v___x_159_ = l_Lean_addMacroScope(v_quotContext_147_, v___x_158_, v_currMacroScope_148_);
v___x_160_ = ((lean_object*)(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__13));
lean_inc_n(v___x_155_, 2);
v___x_161_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_161_, 0, v___x_155_);
lean_ctor_set(v___x_161_, 1, v___x_157_);
lean_ctor_set(v___x_161_, 2, v___x_159_);
lean_ctor_set(v___x_161_, 3, v___x_160_);
v___x_162_ = ((lean_object*)(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__15));
v___x_163_ = l_Lean_Syntax_node2(v___x_155_, v___x_162_, v___x_151_, v___x_153_);
v___x_164_ = l_Lean_Syntax_node2(v___x_155_, v___x_156_, v___x_161_, v___x_163_);
v___x_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
lean_ctor_set(v___x_165_, 1, v_a_142_);
return v___x_165_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___boxed(lean_object* v_x_166_, lean_object* v_a_167_, lean_object* v_a_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1(v_x_166_, v_a_167_, v_a_168_);
lean_dec_ref(v_a_167_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1(lean_object* v_x_173_, lean_object* v_a_174_, lean_object* v_a_175_){
_start:
{
lean_object* v___x_176_; uint8_t v___x_177_; 
v___x_176_ = ((lean_object*)(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4));
lean_inc(v_x_173_);
v___x_177_ = l_Lean_Syntax_isOfKind(v_x_173_, v___x_176_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; lean_object* v___x_179_; 
lean_dec(v_x_173_);
v___x_178_ = lean_box(0);
v___x_179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
lean_ctor_set(v___x_179_, 1, v_a_175_);
return v___x_179_;
}
else
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; uint8_t v___x_183_; 
v___x_180_ = lean_unsigned_to_nat(0u);
v___x_181_ = l_Lean_Syntax_getArg(v_x_173_, v___x_180_);
v___x_182_ = ((lean_object*)(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___closed__1));
lean_inc(v___x_181_);
v___x_183_ = l_Lean_Syntax_isOfKind(v___x_181_, v___x_182_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; lean_object* v___x_185_; 
lean_dec(v___x_181_);
lean_dec(v_x_173_);
v___x_184_ = lean_box(0);
v___x_185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
lean_ctor_set(v___x_185_, 1, v_a_175_);
return v___x_185_;
}
else
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; uint8_t v___x_189_; 
v___x_186_ = lean_unsigned_to_nat(1u);
v___x_187_ = l_Lean_Syntax_getArg(v_x_173_, v___x_186_);
lean_dec(v_x_173_);
v___x_188_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_187_);
v___x_189_ = l_Lean_Syntax_matchesNull(v___x_187_, v___x_188_);
if (v___x_189_ == 0)
{
lean_object* v___x_190_; lean_object* v___x_191_; 
lean_dec(v___x_187_);
lean_dec(v___x_181_);
v___x_190_ = lean_box(0);
v___x_191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
lean_ctor_set(v___x_191_, 1, v_a_175_);
return v___x_191_;
}
else
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v_ref_194_; uint8_t v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_192_ = l_Lean_Syntax_getArg(v___x_187_, v___x_180_);
v___x_193_ = l_Lean_Syntax_getArg(v___x_187_, v___x_186_);
lean_dec(v___x_187_);
v_ref_194_ = l_Lean_replaceRef(v___x_181_, v_a_174_);
lean_dec(v___x_181_);
v___x_195_ = 0;
v___x_196_ = l_Lean_SourceInfo_fromRef(v_ref_194_, v___x_195_);
lean_dec(v_ref_194_);
v___x_197_ = ((lean_object*)(l_Std_DHashMap_Raw_term___x7em___00__closed__4));
v___x_198_ = ((lean_object*)(l_Std_DHashMap_Raw_term___x7em___00__closed__7));
lean_inc(v___x_196_);
v___x_199_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_196_);
lean_ctor_set(v___x_199_, 1, v___x_198_);
v___x_200_ = l_Lean_Syntax_node3(v___x_196_, v___x_197_, v___x_192_, v___x_199_, v___x_193_);
v___x_201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
lean_ctor_set(v___x_201_, 1, v_a_175_);
return v___x_201_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___boxed(lean_object* v_x_202_, lean_object* v_a_203_, lean_object* v_a_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1(v_x_202_, v_a_203_, v_a_204_);
lean_dec(v_a_203_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insert___redArg(lean_object* v_inst_206_, lean_object* v_inst_207_, lean_object* v_m_208_, lean_object* v_a_209_, lean_object* v_b_210_){
_start:
{
lean_object* v_buckets_211_; lean_object* v___x_212_; lean_object* v___x_213_; uint8_t v___x_214_; 
v_buckets_211_ = lean_ctor_get(v_m_208_, 1);
v___x_212_ = lean_unsigned_to_nat(0u);
v___x_213_ = lean_array_get_size(v_buckets_211_);
v___x_214_ = lean_nat_dec_lt(v___x_212_, v___x_213_);
if (v___x_214_ == 0)
{
lean_dec(v_b_210_);
lean_dec(v_a_209_);
lean_dec_ref(v_inst_207_);
lean_dec_ref(v_inst_206_);
return v_m_208_;
}
else
{
lean_object* v___x_215_; 
v___x_215_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_206_, v_inst_207_, v_m_208_, v_a_209_, v_b_210_);
return v___x_215_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insert(lean_object* v_00_u03b1_216_, lean_object* v_00_u03b2_217_, lean_object* v_inst_218_, lean_object* v_inst_219_, lean_object* v_m_220_, lean_object* v_a_221_, lean_object* v_b_222_){
_start:
{
lean_object* v_buckets_223_; lean_object* v___x_224_; lean_object* v___x_225_; uint8_t v___x_226_; 
v_buckets_223_ = lean_ctor_get(v_m_220_, 1);
v___x_224_ = lean_unsigned_to_nat(0u);
v___x_225_ = lean_array_get_size(v_buckets_223_);
v___x_226_ = lean_nat_dec_lt(v___x_224_, v___x_225_);
if (v___x_226_ == 0)
{
lean_dec(v_b_222_);
lean_dec(v_a_221_);
lean_dec_ref(v_inst_219_);
lean_dec_ref(v_inst_218_);
return v_m_220_;
}
else
{
lean_object* v___x_227_; 
v___x_227_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_218_, v_inst_219_, v_m_220_, v_a_221_, v_b_222_);
return v___x_227_;
}
}
}
static lean_object* _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__0, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__0_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__0);
v___x_229_ = lean_array_get_size(v___x_228_);
return v___x_229_;
}
}
static uint8_t _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_230_ = lean_obj_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0);
v___x_231_ = lean_unsigned_to_nat(0u);
v___x_232_ = lean_nat_dec_lt(v___x_231_, v___x_230_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0(lean_object* v_inst_233_, lean_object* v_inst_234_, lean_object* v_x_235_){
_start:
{
lean_object* v_fst_236_; lean_object* v_snd_237_; lean_object* v___x_238_; uint8_t v___x_239_; 
v_fst_236_ = lean_ctor_get(v_x_235_, 0);
lean_inc(v_fst_236_);
v_snd_237_ = lean_ctor_get(v_x_235_, 1);
lean_inc(v_snd_237_);
lean_dec_ref(v_x_235_);
v___x_238_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
v___x_239_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_239_ == 0)
{
lean_dec(v_snd_237_);
lean_dec(v_fst_236_);
lean_dec_ref(v_inst_234_);
lean_dec_ref(v_inst_233_);
return v___x_238_;
}
else
{
lean_object* v___x_240_; 
v___x_240_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_233_, v_inst_234_, v___x_238_, v_fst_236_, v_snd_237_);
return v___x_240_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg(lean_object* v_inst_241_, lean_object* v_inst_242_){
_start:
{
lean_object* v___f_243_; 
v___f_243_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_243_, 0, v_inst_241_);
lean_closure_set(v___f_243_, 1, v_inst_242_);
return v___f_243_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable(lean_object* v_00_u03b1_244_, lean_object* v_00_u03b2_245_, lean_object* v_inst_246_, lean_object* v_inst_247_){
_start:
{
lean_object* v___f_248_; 
v___f_248_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_248_, 0, v_inst_246_);
lean_closure_set(v___f_248_, 1, v_inst_247_);
return v___f_248_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable___redArg___lam__0(lean_object* v_inst_249_, lean_object* v_inst_250_, lean_object* v_x_251_, lean_object* v_s_252_){
_start:
{
lean_object* v_fst_253_; lean_object* v_snd_254_; lean_object* v_buckets_255_; lean_object* v___x_256_; lean_object* v___x_257_; uint8_t v___x_258_; 
v_fst_253_ = lean_ctor_get(v_x_251_, 0);
lean_inc(v_fst_253_);
v_snd_254_ = lean_ctor_get(v_x_251_, 1);
lean_inc(v_snd_254_);
lean_dec_ref(v_x_251_);
v_buckets_255_ = lean_ctor_get(v_s_252_, 1);
v___x_256_ = lean_unsigned_to_nat(0u);
v___x_257_ = lean_array_get_size(v_buckets_255_);
v___x_258_ = lean_nat_dec_lt(v___x_256_, v___x_257_);
if (v___x_258_ == 0)
{
lean_dec(v_snd_254_);
lean_dec(v_fst_253_);
lean_dec_ref(v_inst_250_);
lean_dec_ref(v_inst_249_);
return v_s_252_;
}
else
{
lean_object* v___x_259_; 
v___x_259_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_249_, v_inst_250_, v_s_252_, v_fst_253_, v_snd_254_);
return v___x_259_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable___redArg(lean_object* v_inst_260_, lean_object* v_inst_261_){
_start:
{
lean_object* v___f_262_; 
v___f_262_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_262_, 0, v_inst_260_);
lean_closure_set(v___f_262_, 1, v_inst_261_);
return v___f_262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable(lean_object* v_00_u03b1_263_, lean_object* v_00_u03b2_264_, lean_object* v_inst_265_, lean_object* v_inst_266_){
_start:
{
lean_object* v___f_267_; 
v___f_267_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_267_, 0, v_inst_265_);
lean_closure_set(v___f_267_, 1, v_inst_266_);
return v___f_267_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insertIfNew___redArg(lean_object* v_inst_268_, lean_object* v_inst_269_, lean_object* v_m_270_, lean_object* v_a_271_, lean_object* v_b_272_){
_start:
{
lean_object* v_buckets_273_; lean_object* v___x_274_; lean_object* v___x_275_; uint8_t v___x_276_; 
v_buckets_273_ = lean_ctor_get(v_m_270_, 1);
v___x_274_ = lean_unsigned_to_nat(0u);
v___x_275_ = lean_array_get_size(v_buckets_273_);
v___x_276_ = lean_nat_dec_lt(v___x_274_, v___x_275_);
if (v___x_276_ == 0)
{
lean_dec(v_b_272_);
lean_dec(v_a_271_);
lean_dec_ref(v_inst_269_);
lean_dec_ref(v_inst_268_);
return v_m_270_;
}
else
{
lean_object* v___x_277_; 
v___x_277_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_268_, v_inst_269_, v_m_270_, v_a_271_, v_b_272_);
return v___x_277_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insertIfNew(lean_object* v_00_u03b1_278_, lean_object* v_00_u03b2_279_, lean_object* v_inst_280_, lean_object* v_inst_281_, lean_object* v_m_282_, lean_object* v_a_283_, lean_object* v_b_284_){
_start:
{
lean_object* v_buckets_285_; lean_object* v___x_286_; lean_object* v___x_287_; uint8_t v___x_288_; 
v_buckets_285_ = lean_ctor_get(v_m_282_, 1);
v___x_286_ = lean_unsigned_to_nat(0u);
v___x_287_ = lean_array_get_size(v_buckets_285_);
v___x_288_ = lean_nat_dec_lt(v___x_286_, v___x_287_);
if (v___x_288_ == 0)
{
lean_dec(v_b_284_);
lean_dec(v_a_283_);
lean_dec_ref(v_inst_281_);
lean_dec_ref(v_inst_280_);
return v_m_282_;
}
else
{
lean_object* v___x_289_; 
v___x_289_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_280_, v_inst_281_, v_m_282_, v_a_283_, v_b_284_);
return v___x_289_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_containsThenInsert___redArg(lean_object* v_inst_290_, lean_object* v_inst_291_, lean_object* v_m_292_, lean_object* v_a_293_, lean_object* v_b_294_){
_start:
{
lean_object* v_size_295_; lean_object* v_buckets_296_; lean_object* v___x_297_; lean_object* v___x_298_; uint8_t v___x_299_; 
v_size_295_ = lean_ctor_get(v_m_292_, 0);
v_buckets_296_ = lean_ctor_get(v_m_292_, 1);
v___x_297_ = lean_unsigned_to_nat(0u);
v___x_298_ = lean_array_get_size(v_buckets_296_);
v___x_299_ = lean_nat_dec_lt(v___x_297_, v___x_298_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; lean_object* v___x_301_; 
lean_dec(v_b_294_);
lean_dec(v_a_293_);
lean_dec_ref(v_inst_291_);
lean_dec_ref(v_inst_290_);
v___x_300_ = lean_box(v___x_299_);
v___x_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
lean_ctor_set(v___x_301_, 1, v_m_292_);
return v___x_301_;
}
else
{
lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_351_; 
lean_inc_ref(v_buckets_296_);
lean_inc(v_size_295_);
v_isSharedCheck_351_ = !lean_is_exclusive(v_m_292_);
if (v_isSharedCheck_351_ == 0)
{
lean_object* v_unused_352_; lean_object* v_unused_353_; 
v_unused_352_ = lean_ctor_get(v_m_292_, 1);
lean_dec(v_unused_352_);
v_unused_353_ = lean_ctor_get(v_m_292_, 0);
lean_dec(v_unused_353_);
v___x_303_ = v_m_292_;
v_isShared_304_ = v_isSharedCheck_351_;
goto v_resetjp_302_;
}
else
{
lean_dec(v_m_292_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_351_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_305_; uint64_t v___x_306_; uint64_t v___x_307_; uint64_t v___x_308_; uint64_t v___x_309_; uint64_t v_fold_310_; uint64_t v___x_311_; uint64_t v___x_312_; uint64_t v___x_313_; size_t v___x_314_; size_t v___x_315_; size_t v___x_316_; size_t v___x_317_; size_t v___x_318_; lean_object* v_bkt_319_; uint8_t v___x_320_; 
lean_inc_ref(v_inst_291_);
lean_inc_n(v_a_293_, 2);
v___x_305_ = lean_apply_1(v_inst_291_, v_a_293_);
v___x_306_ = 32ULL;
v___x_307_ = lean_unbox_uint64(v___x_305_);
v___x_308_ = lean_uint64_shift_right(v___x_307_, v___x_306_);
v___x_309_ = lean_unbox_uint64(v___x_305_);
lean_dec_ref(v___x_305_);
v_fold_310_ = lean_uint64_xor(v___x_309_, v___x_308_);
v___x_311_ = 16ULL;
v___x_312_ = lean_uint64_shift_right(v_fold_310_, v___x_311_);
v___x_313_ = lean_uint64_xor(v_fold_310_, v___x_312_);
v___x_314_ = lean_uint64_to_usize(v___x_313_);
v___x_315_ = lean_usize_of_nat(v___x_298_);
v___x_316_ = ((size_t)1ULL);
v___x_317_ = lean_usize_sub(v___x_315_, v___x_316_);
v___x_318_ = lean_usize_land(v___x_314_, v___x_317_);
v_bkt_319_ = lean_array_uget_borrowed(v_buckets_296_, v___x_318_);
lean_inc(v_bkt_319_);
lean_inc_ref(v_inst_290_);
v___x_320_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_290_, v_a_293_, v_bkt_319_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; lean_object* v_size_x27_322_; lean_object* v___x_323_; lean_object* v_buckets_x27_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; uint8_t v___x_330_; 
lean_dec_ref(v_inst_290_);
v___x_321_ = lean_unsigned_to_nat(1u);
v_size_x27_322_ = lean_nat_add(v_size_295_, v___x_321_);
lean_dec(v_size_295_);
lean_inc(v_bkt_319_);
v___x_323_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_323_, 0, v_a_293_);
lean_ctor_set(v___x_323_, 1, v_b_294_);
lean_ctor_set(v___x_323_, 2, v_bkt_319_);
v_buckets_x27_324_ = lean_array_uset(v_buckets_296_, v___x_318_, v___x_323_);
v___x_325_ = lean_unsigned_to_nat(4u);
v___x_326_ = lean_nat_mul(v_size_x27_322_, v___x_325_);
v___x_327_ = lean_unsigned_to_nat(3u);
v___x_328_ = lean_nat_div(v___x_326_, v___x_327_);
lean_dec(v___x_326_);
v___x_329_ = lean_array_get_size(v_buckets_x27_324_);
v___x_330_ = lean_nat_dec_le(v___x_328_, v___x_329_);
lean_dec(v___x_328_);
if (v___x_330_ == 0)
{
lean_object* v_val_331_; lean_object* v___x_333_; 
v_val_331_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_291_, v_buckets_x27_324_);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 1, v_val_331_);
lean_ctor_set(v___x_303_, 0, v_size_x27_322_);
v___x_333_ = v___x_303_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_size_x27_322_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v_val_331_);
v___x_333_ = v_reuseFailAlloc_336_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = lean_box(v___x_320_);
v___x_335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set(v___x_335_, 1, v___x_333_);
return v___x_335_;
}
}
else
{
lean_object* v___x_338_; 
lean_dec_ref(v_inst_291_);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 1, v_buckets_x27_324_);
lean_ctor_set(v___x_303_, 0, v_size_x27_322_);
v___x_338_ = v___x_303_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_size_x27_322_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v_buckets_x27_324_);
v___x_338_ = v_reuseFailAlloc_341_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_box(v___x_320_);
v___x_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v___x_338_);
return v___x_340_;
}
}
}
else
{
lean_object* v___x_342_; lean_object* v_buckets_x27_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_347_; 
lean_inc(v_bkt_319_);
lean_dec_ref(v_inst_291_);
v___x_342_ = lean_box(0);
v_buckets_x27_343_ = lean_array_uset(v_buckets_296_, v___x_318_, v___x_342_);
v___x_344_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_inst_290_, v_a_293_, v_b_294_, v_bkt_319_);
v___x_345_ = lean_array_uset(v_buckets_x27_343_, v___x_318_, v___x_344_);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 1, v___x_345_);
v___x_347_ = v___x_303_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_size_295_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v___x_345_);
v___x_347_ = v_reuseFailAlloc_350_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_box(v___x_320_);
v___x_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
lean_ctor_set(v___x_349_, 1, v___x_347_);
return v___x_349_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_containsThenInsert(lean_object* v_00_u03b1_354_, lean_object* v_00_u03b2_355_, lean_object* v_inst_356_, lean_object* v_inst_357_, lean_object* v_m_358_, lean_object* v_a_359_, lean_object* v_b_360_){
_start:
{
lean_object* v_size_361_; lean_object* v_buckets_362_; lean_object* v___x_363_; lean_object* v___x_364_; uint8_t v___x_365_; 
v_size_361_ = lean_ctor_get(v_m_358_, 0);
v_buckets_362_ = lean_ctor_get(v_m_358_, 1);
v___x_363_ = lean_unsigned_to_nat(0u);
v___x_364_ = lean_array_get_size(v_buckets_362_);
v___x_365_ = lean_nat_dec_lt(v___x_363_, v___x_364_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; lean_object* v___x_367_; 
lean_dec(v_b_360_);
lean_dec(v_a_359_);
lean_dec_ref(v_inst_357_);
lean_dec_ref(v_inst_356_);
v___x_366_ = lean_box(v___x_365_);
v___x_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
lean_ctor_set(v___x_367_, 1, v_m_358_);
return v___x_367_;
}
else
{
lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_417_; 
lean_inc_ref(v_buckets_362_);
lean_inc(v_size_361_);
v_isSharedCheck_417_ = !lean_is_exclusive(v_m_358_);
if (v_isSharedCheck_417_ == 0)
{
lean_object* v_unused_418_; lean_object* v_unused_419_; 
v_unused_418_ = lean_ctor_get(v_m_358_, 1);
lean_dec(v_unused_418_);
v_unused_419_ = lean_ctor_get(v_m_358_, 0);
lean_dec(v_unused_419_);
v___x_369_ = v_m_358_;
v_isShared_370_ = v_isSharedCheck_417_;
goto v_resetjp_368_;
}
else
{
lean_dec(v_m_358_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_417_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_371_; uint64_t v___x_372_; uint64_t v___x_373_; uint64_t v___x_374_; uint64_t v___x_375_; uint64_t v_fold_376_; uint64_t v___x_377_; uint64_t v___x_378_; uint64_t v___x_379_; size_t v___x_380_; size_t v___x_381_; size_t v___x_382_; size_t v___x_383_; size_t v___x_384_; lean_object* v_bkt_385_; uint8_t v___x_386_; 
lean_inc_ref(v_inst_357_);
lean_inc_n(v_a_359_, 2);
v___x_371_ = lean_apply_1(v_inst_357_, v_a_359_);
v___x_372_ = 32ULL;
v___x_373_ = lean_unbox_uint64(v___x_371_);
v___x_374_ = lean_uint64_shift_right(v___x_373_, v___x_372_);
v___x_375_ = lean_unbox_uint64(v___x_371_);
lean_dec_ref(v___x_371_);
v_fold_376_ = lean_uint64_xor(v___x_375_, v___x_374_);
v___x_377_ = 16ULL;
v___x_378_ = lean_uint64_shift_right(v_fold_376_, v___x_377_);
v___x_379_ = lean_uint64_xor(v_fold_376_, v___x_378_);
v___x_380_ = lean_uint64_to_usize(v___x_379_);
v___x_381_ = lean_usize_of_nat(v___x_364_);
v___x_382_ = ((size_t)1ULL);
v___x_383_ = lean_usize_sub(v___x_381_, v___x_382_);
v___x_384_ = lean_usize_land(v___x_380_, v___x_383_);
v_bkt_385_ = lean_array_uget_borrowed(v_buckets_362_, v___x_384_);
lean_inc(v_bkt_385_);
lean_inc_ref(v_inst_356_);
v___x_386_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_356_, v_a_359_, v_bkt_385_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; lean_object* v_size_x27_388_; lean_object* v___x_389_; lean_object* v_buckets_x27_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; uint8_t v___x_396_; 
lean_dec_ref(v_inst_356_);
v___x_387_ = lean_unsigned_to_nat(1u);
v_size_x27_388_ = lean_nat_add(v_size_361_, v___x_387_);
lean_dec(v_size_361_);
lean_inc(v_bkt_385_);
v___x_389_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_389_, 0, v_a_359_);
lean_ctor_set(v___x_389_, 1, v_b_360_);
lean_ctor_set(v___x_389_, 2, v_bkt_385_);
v_buckets_x27_390_ = lean_array_uset(v_buckets_362_, v___x_384_, v___x_389_);
v___x_391_ = lean_unsigned_to_nat(4u);
v___x_392_ = lean_nat_mul(v_size_x27_388_, v___x_391_);
v___x_393_ = lean_unsigned_to_nat(3u);
v___x_394_ = lean_nat_div(v___x_392_, v___x_393_);
lean_dec(v___x_392_);
v___x_395_ = lean_array_get_size(v_buckets_x27_390_);
v___x_396_ = lean_nat_dec_le(v___x_394_, v___x_395_);
lean_dec(v___x_394_);
if (v___x_396_ == 0)
{
lean_object* v_val_397_; lean_object* v___x_399_; 
v_val_397_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_357_, v_buckets_x27_390_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 1, v_val_397_);
lean_ctor_set(v___x_369_, 0, v_size_x27_388_);
v___x_399_ = v___x_369_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_size_x27_388_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v_val_397_);
v___x_399_ = v_reuseFailAlloc_402_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_400_ = lean_box(v___x_386_);
v___x_401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_400_);
lean_ctor_set(v___x_401_, 1, v___x_399_);
return v___x_401_;
}
}
else
{
lean_object* v___x_404_; 
lean_dec_ref(v_inst_357_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 1, v_buckets_x27_390_);
lean_ctor_set(v___x_369_, 0, v_size_x27_388_);
v___x_404_ = v___x_369_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_size_x27_388_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v_buckets_x27_390_);
v___x_404_ = v_reuseFailAlloc_407_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = lean_box(v___x_386_);
v___x_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
lean_ctor_set(v___x_406_, 1, v___x_404_);
return v___x_406_;
}
}
}
else
{
lean_object* v___x_408_; lean_object* v_buckets_x27_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_413_; 
lean_inc(v_bkt_385_);
lean_dec_ref(v_inst_357_);
v___x_408_ = lean_box(0);
v_buckets_x27_409_ = lean_array_uset(v_buckets_362_, v___x_384_, v___x_408_);
v___x_410_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_inst_356_, v_a_359_, v_b_360_, v_bkt_385_);
v___x_411_ = lean_array_uset(v_buckets_x27_409_, v___x_384_, v___x_410_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 1, v___x_411_);
v___x_413_ = v___x_369_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_size_361_);
lean_ctor_set(v_reuseFailAlloc_416_, 1, v___x_411_);
v___x_413_ = v_reuseFailAlloc_416_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_414_ = lean_box(v___x_386_);
v___x_415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
lean_ctor_set(v___x_415_, 1, v___x_413_);
return v___x_415_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getThenInsertIfNew_x3f___redArg(lean_object* v_inst_420_, lean_object* v_inst_421_, lean_object* v_m_422_, lean_object* v_a_423_, lean_object* v_b_424_){
_start:
{
lean_object* v_size_425_; lean_object* v_buckets_426_; lean_object* v___x_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v_size_425_ = lean_ctor_get(v_m_422_, 0);
v_buckets_426_ = lean_ctor_get(v_m_422_, 1);
v___x_427_ = lean_unsigned_to_nat(0u);
v___x_428_ = lean_array_get_size(v_buckets_426_);
v___x_429_ = lean_nat_dec_lt(v___x_427_, v___x_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; lean_object* v___x_431_; 
lean_dec(v_b_424_);
lean_dec(v_a_423_);
lean_dec_ref(v_inst_421_);
lean_dec_ref(v_inst_420_);
v___x_430_ = lean_box(0);
v___x_431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
lean_ctor_set(v___x_431_, 1, v_m_422_);
return v___x_431_;
}
else
{
lean_object* v___x_432_; uint64_t v___x_433_; uint64_t v___x_434_; uint64_t v___x_435_; uint64_t v___x_436_; uint64_t v_fold_437_; uint64_t v___x_438_; uint64_t v___x_439_; uint64_t v___x_440_; size_t v___x_441_; size_t v___x_442_; size_t v___x_443_; size_t v___x_444_; size_t v___x_445_; lean_object* v_bkt_446_; lean_object* v___x_447_; 
lean_inc_ref(v_inst_421_);
lean_inc_n(v_a_423_, 2);
v___x_432_ = lean_apply_1(v_inst_421_, v_a_423_);
v___x_433_ = 32ULL;
v___x_434_ = lean_unbox_uint64(v___x_432_);
v___x_435_ = lean_uint64_shift_right(v___x_434_, v___x_433_);
v___x_436_ = lean_unbox_uint64(v___x_432_);
lean_dec_ref(v___x_432_);
v_fold_437_ = lean_uint64_xor(v___x_436_, v___x_435_);
v___x_438_ = 16ULL;
v___x_439_ = lean_uint64_shift_right(v_fold_437_, v___x_438_);
v___x_440_ = lean_uint64_xor(v_fold_437_, v___x_439_);
v___x_441_ = lean_uint64_to_usize(v___x_440_);
v___x_442_ = lean_usize_of_nat(v___x_428_);
v___x_443_ = ((size_t)1ULL);
v___x_444_ = lean_usize_sub(v___x_442_, v___x_443_);
v___x_445_ = lean_usize_land(v___x_441_, v___x_444_);
v_bkt_446_ = lean_array_uget_borrowed(v_buckets_426_, v___x_445_);
lean_inc(v_bkt_446_);
v___x_447_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(v_inst_420_, v_a_423_, v_bkt_446_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_470_; 
lean_inc_ref(v_buckets_426_);
lean_inc(v_size_425_);
v_isSharedCheck_470_ = !lean_is_exclusive(v_m_422_);
if (v_isSharedCheck_470_ == 0)
{
lean_object* v_unused_471_; lean_object* v_unused_472_; 
v_unused_471_ = lean_ctor_get(v_m_422_, 1);
lean_dec(v_unused_471_);
v_unused_472_ = lean_ctor_get(v_m_422_, 0);
lean_dec(v_unused_472_);
v___x_449_ = v_m_422_;
v_isShared_450_ = v_isSharedCheck_470_;
goto v_resetjp_448_;
}
else
{
lean_dec(v_m_422_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_470_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_451_; lean_object* v_size_x27_452_; lean_object* v___x_453_; lean_object* v_buckets_x27_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_451_ = lean_unsigned_to_nat(1u);
v_size_x27_452_ = lean_nat_add(v_size_425_, v___x_451_);
lean_dec(v_size_425_);
lean_inc(v_bkt_446_);
v___x_453_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_453_, 0, v_a_423_);
lean_ctor_set(v___x_453_, 1, v_b_424_);
lean_ctor_set(v___x_453_, 2, v_bkt_446_);
v_buckets_x27_454_ = lean_array_uset(v_buckets_426_, v___x_445_, v___x_453_);
v___x_455_ = lean_unsigned_to_nat(4u);
v___x_456_ = lean_nat_mul(v_size_x27_452_, v___x_455_);
v___x_457_ = lean_unsigned_to_nat(3u);
v___x_458_ = lean_nat_div(v___x_456_, v___x_457_);
lean_dec(v___x_456_);
v___x_459_ = lean_array_get_size(v_buckets_x27_454_);
v___x_460_ = lean_nat_dec_le(v___x_458_, v___x_459_);
lean_dec(v___x_458_);
if (v___x_460_ == 0)
{
lean_object* v_val_461_; lean_object* v___x_463_; 
v_val_461_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_421_, v_buckets_x27_454_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 1, v_val_461_);
lean_ctor_set(v___x_449_, 0, v_size_x27_452_);
v___x_463_ = v___x_449_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_size_x27_452_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v_val_461_);
v___x_463_ = v_reuseFailAlloc_465_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
lean_object* v___x_464_; 
v___x_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_447_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
return v___x_464_;
}
}
else
{
lean_object* v___x_467_; 
lean_dec_ref(v_inst_421_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 1, v_buckets_x27_454_);
lean_ctor_set(v___x_449_, 0, v_size_x27_452_);
v___x_467_ = v___x_449_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_size_x27_452_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v_buckets_x27_454_);
v___x_467_ = v_reuseFailAlloc_469_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
lean_object* v___x_468_; 
v___x_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_447_);
lean_ctor_set(v___x_468_, 1, v___x_467_);
return v___x_468_;
}
}
}
}
else
{
lean_object* v___x_473_; 
lean_dec(v_b_424_);
lean_dec(v_a_423_);
lean_dec_ref(v_inst_421_);
v___x_473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_473_, 0, v___x_447_);
lean_ctor_set(v___x_473_, 1, v_m_422_);
return v___x_473_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_474_, lean_object* v_00_u03b2_475_, lean_object* v_inst_476_, lean_object* v_inst_477_, lean_object* v_inst_478_, lean_object* v_m_479_, lean_object* v_a_480_, lean_object* v_b_481_){
_start:
{
lean_object* v_size_482_; lean_object* v_buckets_483_; lean_object* v___x_484_; lean_object* v___x_485_; uint8_t v___x_486_; 
v_size_482_ = lean_ctor_get(v_m_479_, 0);
v_buckets_483_ = lean_ctor_get(v_m_479_, 1);
v___x_484_ = lean_unsigned_to_nat(0u);
v___x_485_ = lean_array_get_size(v_buckets_483_);
v___x_486_ = lean_nat_dec_lt(v___x_484_, v___x_485_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; lean_object* v___x_488_; 
lean_dec(v_b_481_);
lean_dec(v_a_480_);
lean_dec_ref(v_inst_477_);
lean_dec_ref(v_inst_476_);
v___x_487_ = lean_box(0);
v___x_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
lean_ctor_set(v___x_488_, 1, v_m_479_);
return v___x_488_;
}
else
{
lean_object* v___x_489_; uint64_t v___x_490_; uint64_t v___x_491_; uint64_t v___x_492_; uint64_t v___x_493_; uint64_t v_fold_494_; uint64_t v___x_495_; uint64_t v___x_496_; uint64_t v___x_497_; size_t v___x_498_; size_t v___x_499_; size_t v___x_500_; size_t v___x_501_; size_t v___x_502_; lean_object* v_bkt_503_; lean_object* v___x_504_; 
lean_inc_ref(v_inst_477_);
lean_inc_n(v_a_480_, 2);
v___x_489_ = lean_apply_1(v_inst_477_, v_a_480_);
v___x_490_ = 32ULL;
v___x_491_ = lean_unbox_uint64(v___x_489_);
v___x_492_ = lean_uint64_shift_right(v___x_491_, v___x_490_);
v___x_493_ = lean_unbox_uint64(v___x_489_);
lean_dec_ref(v___x_489_);
v_fold_494_ = lean_uint64_xor(v___x_493_, v___x_492_);
v___x_495_ = 16ULL;
v___x_496_ = lean_uint64_shift_right(v_fold_494_, v___x_495_);
v___x_497_ = lean_uint64_xor(v_fold_494_, v___x_496_);
v___x_498_ = lean_uint64_to_usize(v___x_497_);
v___x_499_ = lean_usize_of_nat(v___x_485_);
v___x_500_ = ((size_t)1ULL);
v___x_501_ = lean_usize_sub(v___x_499_, v___x_500_);
v___x_502_ = lean_usize_land(v___x_498_, v___x_501_);
v_bkt_503_ = lean_array_uget_borrowed(v_buckets_483_, v___x_502_);
lean_inc(v_bkt_503_);
v___x_504_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(v_inst_476_, v_a_480_, v_bkt_503_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_527_; 
lean_inc_ref(v_buckets_483_);
lean_inc(v_size_482_);
v_isSharedCheck_527_ = !lean_is_exclusive(v_m_479_);
if (v_isSharedCheck_527_ == 0)
{
lean_object* v_unused_528_; lean_object* v_unused_529_; 
v_unused_528_ = lean_ctor_get(v_m_479_, 1);
lean_dec(v_unused_528_);
v_unused_529_ = lean_ctor_get(v_m_479_, 0);
lean_dec(v_unused_529_);
v___x_506_ = v_m_479_;
v_isShared_507_ = v_isSharedCheck_527_;
goto v_resetjp_505_;
}
else
{
lean_dec(v_m_479_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_527_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_508_; lean_object* v_size_x27_509_; lean_object* v___x_510_; lean_object* v_buckets_x27_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; uint8_t v___x_517_; 
v___x_508_ = lean_unsigned_to_nat(1u);
v_size_x27_509_ = lean_nat_add(v_size_482_, v___x_508_);
lean_dec(v_size_482_);
lean_inc(v_bkt_503_);
v___x_510_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_510_, 0, v_a_480_);
lean_ctor_set(v___x_510_, 1, v_b_481_);
lean_ctor_set(v___x_510_, 2, v_bkt_503_);
v_buckets_x27_511_ = lean_array_uset(v_buckets_483_, v___x_502_, v___x_510_);
v___x_512_ = lean_unsigned_to_nat(4u);
v___x_513_ = lean_nat_mul(v_size_x27_509_, v___x_512_);
v___x_514_ = lean_unsigned_to_nat(3u);
v___x_515_ = lean_nat_div(v___x_513_, v___x_514_);
lean_dec(v___x_513_);
v___x_516_ = lean_array_get_size(v_buckets_x27_511_);
v___x_517_ = lean_nat_dec_le(v___x_515_, v___x_516_);
lean_dec(v___x_515_);
if (v___x_517_ == 0)
{
lean_object* v_val_518_; lean_object* v___x_520_; 
v_val_518_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_477_, v_buckets_x27_511_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 1, v_val_518_);
lean_ctor_set(v___x_506_, 0, v_size_x27_509_);
v___x_520_ = v___x_506_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_size_x27_509_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v_val_518_);
v___x_520_ = v_reuseFailAlloc_522_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
lean_object* v___x_521_; 
v___x_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_521_, 0, v___x_504_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
return v___x_521_;
}
}
else
{
lean_object* v___x_524_; 
lean_dec_ref(v_inst_477_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 1, v_buckets_x27_511_);
lean_ctor_set(v___x_506_, 0, v_size_x27_509_);
v___x_524_ = v___x_506_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_size_x27_509_);
lean_ctor_set(v_reuseFailAlloc_526_, 1, v_buckets_x27_511_);
v___x_524_ = v_reuseFailAlloc_526_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
lean_object* v___x_525_; 
v___x_525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_504_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
return v___x_525_;
}
}
}
}
else
{
lean_object* v___x_530_; 
lean_dec(v_b_481_);
lean_dec(v_a_480_);
lean_dec_ref(v_inst_477_);
v___x_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_504_);
lean_ctor_set(v___x_530_, 1, v_m_479_);
return v___x_530_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_containsThenInsertIfNew___redArg(lean_object* v_inst_531_, lean_object* v_inst_532_, lean_object* v_m_533_, lean_object* v_a_534_, lean_object* v_b_535_){
_start:
{
lean_object* v_size_536_; lean_object* v_buckets_537_; lean_object* v___x_538_; lean_object* v___x_539_; uint8_t v___x_540_; 
v_size_536_ = lean_ctor_get(v_m_533_, 0);
v_buckets_537_ = lean_ctor_get(v_m_533_, 1);
v___x_538_ = lean_unsigned_to_nat(0u);
v___x_539_ = lean_array_get_size(v_buckets_537_);
v___x_540_ = lean_nat_dec_lt(v___x_538_, v___x_539_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; lean_object* v___x_542_; 
lean_dec(v_b_535_);
lean_dec(v_a_534_);
lean_dec_ref(v_inst_532_);
lean_dec_ref(v_inst_531_);
v___x_541_ = lean_box(v___x_540_);
v___x_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
lean_ctor_set(v___x_542_, 1, v_m_533_);
return v___x_542_;
}
else
{
lean_object* v___x_543_; uint64_t v___x_544_; uint64_t v___x_545_; uint64_t v___x_546_; uint64_t v___x_547_; uint64_t v_fold_548_; uint64_t v___x_549_; uint64_t v___x_550_; uint64_t v___x_551_; size_t v___x_552_; size_t v___x_553_; size_t v___x_554_; size_t v___x_555_; size_t v___x_556_; lean_object* v_bkt_557_; uint8_t v___x_558_; 
lean_inc_ref(v_inst_532_);
lean_inc_n(v_a_534_, 2);
v___x_543_ = lean_apply_1(v_inst_532_, v_a_534_);
v___x_544_ = 32ULL;
v___x_545_ = lean_unbox_uint64(v___x_543_);
v___x_546_ = lean_uint64_shift_right(v___x_545_, v___x_544_);
v___x_547_ = lean_unbox_uint64(v___x_543_);
lean_dec_ref(v___x_543_);
v_fold_548_ = lean_uint64_xor(v___x_547_, v___x_546_);
v___x_549_ = 16ULL;
v___x_550_ = lean_uint64_shift_right(v_fold_548_, v___x_549_);
v___x_551_ = lean_uint64_xor(v_fold_548_, v___x_550_);
v___x_552_ = lean_uint64_to_usize(v___x_551_);
v___x_553_ = lean_usize_of_nat(v___x_539_);
v___x_554_ = ((size_t)1ULL);
v___x_555_ = lean_usize_sub(v___x_553_, v___x_554_);
v___x_556_ = lean_usize_land(v___x_552_, v___x_555_);
v_bkt_557_ = lean_array_uget_borrowed(v_buckets_537_, v___x_556_);
lean_inc(v_bkt_557_);
v___x_558_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_531_, v_a_534_, v_bkt_557_);
if (v___x_558_ == 0)
{
lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_583_; 
lean_inc_ref(v_buckets_537_);
lean_inc(v_size_536_);
v_isSharedCheck_583_ = !lean_is_exclusive(v_m_533_);
if (v_isSharedCheck_583_ == 0)
{
lean_object* v_unused_584_; lean_object* v_unused_585_; 
v_unused_584_ = lean_ctor_get(v_m_533_, 1);
lean_dec(v_unused_584_);
v_unused_585_ = lean_ctor_get(v_m_533_, 0);
lean_dec(v_unused_585_);
v___x_560_ = v_m_533_;
v_isShared_561_ = v_isSharedCheck_583_;
goto v_resetjp_559_;
}
else
{
lean_dec(v_m_533_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_583_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_562_; lean_object* v_size_x27_563_; lean_object* v___x_564_; lean_object* v_buckets_x27_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; uint8_t v___x_571_; 
v___x_562_ = lean_unsigned_to_nat(1u);
v_size_x27_563_ = lean_nat_add(v_size_536_, v___x_562_);
lean_dec(v_size_536_);
lean_inc(v_bkt_557_);
v___x_564_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_564_, 0, v_a_534_);
lean_ctor_set(v___x_564_, 1, v_b_535_);
lean_ctor_set(v___x_564_, 2, v_bkt_557_);
v_buckets_x27_565_ = lean_array_uset(v_buckets_537_, v___x_556_, v___x_564_);
v___x_566_ = lean_unsigned_to_nat(4u);
v___x_567_ = lean_nat_mul(v_size_x27_563_, v___x_566_);
v___x_568_ = lean_unsigned_to_nat(3u);
v___x_569_ = lean_nat_div(v___x_567_, v___x_568_);
lean_dec(v___x_567_);
v___x_570_ = lean_array_get_size(v_buckets_x27_565_);
v___x_571_ = lean_nat_dec_le(v___x_569_, v___x_570_);
lean_dec(v___x_569_);
if (v___x_571_ == 0)
{
lean_object* v_val_572_; lean_object* v___x_574_; 
v_val_572_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_532_, v_buckets_x27_565_);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 1, v_val_572_);
lean_ctor_set(v___x_560_, 0, v_size_x27_563_);
v___x_574_ = v___x_560_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_size_x27_563_);
lean_ctor_set(v_reuseFailAlloc_577_, 1, v_val_572_);
v___x_574_ = v_reuseFailAlloc_577_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = lean_box(v___x_558_);
v___x_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
lean_ctor_set(v___x_576_, 1, v___x_574_);
return v___x_576_;
}
}
else
{
lean_object* v___x_579_; 
lean_dec_ref(v_inst_532_);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 1, v_buckets_x27_565_);
lean_ctor_set(v___x_560_, 0, v_size_x27_563_);
v___x_579_ = v___x_560_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_size_x27_563_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v_buckets_x27_565_);
v___x_579_ = v_reuseFailAlloc_582_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = lean_box(v___x_558_);
v___x_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
lean_ctor_set(v___x_581_, 1, v___x_579_);
return v___x_581_;
}
}
}
}
else
{
lean_object* v___x_586_; lean_object* v___x_587_; 
lean_dec(v_b_535_);
lean_dec(v_a_534_);
lean_dec_ref(v_inst_532_);
v___x_586_ = lean_box(v___x_558_);
v___x_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
lean_ctor_set(v___x_587_, 1, v_m_533_);
return v___x_587_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_containsThenInsertIfNew(lean_object* v_00_u03b1_588_, lean_object* v_00_u03b2_589_, lean_object* v_inst_590_, lean_object* v_inst_591_, lean_object* v_m_592_, lean_object* v_a_593_, lean_object* v_b_594_){
_start:
{
lean_object* v_size_595_; lean_object* v_buckets_596_; lean_object* v___x_597_; lean_object* v___x_598_; uint8_t v___x_599_; 
v_size_595_ = lean_ctor_get(v_m_592_, 0);
v_buckets_596_ = lean_ctor_get(v_m_592_, 1);
v___x_597_ = lean_unsigned_to_nat(0u);
v___x_598_ = lean_array_get_size(v_buckets_596_);
v___x_599_ = lean_nat_dec_lt(v___x_597_, v___x_598_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; lean_object* v___x_601_; 
lean_dec(v_b_594_);
lean_dec(v_a_593_);
lean_dec_ref(v_inst_591_);
lean_dec_ref(v_inst_590_);
v___x_600_ = lean_box(v___x_599_);
v___x_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
lean_ctor_set(v___x_601_, 1, v_m_592_);
return v___x_601_;
}
else
{
lean_object* v___x_602_; uint64_t v___x_603_; uint64_t v___x_604_; uint64_t v___x_605_; uint64_t v___x_606_; uint64_t v_fold_607_; uint64_t v___x_608_; uint64_t v___x_609_; uint64_t v___x_610_; size_t v___x_611_; size_t v___x_612_; size_t v___x_613_; size_t v___x_614_; size_t v___x_615_; lean_object* v_bkt_616_; uint8_t v___x_617_; 
lean_inc_ref(v_inst_591_);
lean_inc_n(v_a_593_, 2);
v___x_602_ = lean_apply_1(v_inst_591_, v_a_593_);
v___x_603_ = 32ULL;
v___x_604_ = lean_unbox_uint64(v___x_602_);
v___x_605_ = lean_uint64_shift_right(v___x_604_, v___x_603_);
v___x_606_ = lean_unbox_uint64(v___x_602_);
lean_dec_ref(v___x_602_);
v_fold_607_ = lean_uint64_xor(v___x_606_, v___x_605_);
v___x_608_ = 16ULL;
v___x_609_ = lean_uint64_shift_right(v_fold_607_, v___x_608_);
v___x_610_ = lean_uint64_xor(v_fold_607_, v___x_609_);
v___x_611_ = lean_uint64_to_usize(v___x_610_);
v___x_612_ = lean_usize_of_nat(v___x_598_);
v___x_613_ = ((size_t)1ULL);
v___x_614_ = lean_usize_sub(v___x_612_, v___x_613_);
v___x_615_ = lean_usize_land(v___x_611_, v___x_614_);
v_bkt_616_ = lean_array_uget_borrowed(v_buckets_596_, v___x_615_);
lean_inc(v_bkt_616_);
v___x_617_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_590_, v_a_593_, v_bkt_616_);
if (v___x_617_ == 0)
{
lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_642_; 
lean_inc_ref(v_buckets_596_);
lean_inc(v_size_595_);
v_isSharedCheck_642_ = !lean_is_exclusive(v_m_592_);
if (v_isSharedCheck_642_ == 0)
{
lean_object* v_unused_643_; lean_object* v_unused_644_; 
v_unused_643_ = lean_ctor_get(v_m_592_, 1);
lean_dec(v_unused_643_);
v_unused_644_ = lean_ctor_get(v_m_592_, 0);
lean_dec(v_unused_644_);
v___x_619_ = v_m_592_;
v_isShared_620_ = v_isSharedCheck_642_;
goto v_resetjp_618_;
}
else
{
lean_dec(v_m_592_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_642_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_621_; lean_object* v_size_x27_622_; lean_object* v___x_623_; lean_object* v_buckets_x27_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; uint8_t v___x_630_; 
v___x_621_ = lean_unsigned_to_nat(1u);
v_size_x27_622_ = lean_nat_add(v_size_595_, v___x_621_);
lean_dec(v_size_595_);
lean_inc(v_bkt_616_);
v___x_623_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_623_, 0, v_a_593_);
lean_ctor_set(v___x_623_, 1, v_b_594_);
lean_ctor_set(v___x_623_, 2, v_bkt_616_);
v_buckets_x27_624_ = lean_array_uset(v_buckets_596_, v___x_615_, v___x_623_);
v___x_625_ = lean_unsigned_to_nat(4u);
v___x_626_ = lean_nat_mul(v_size_x27_622_, v___x_625_);
v___x_627_ = lean_unsigned_to_nat(3u);
v___x_628_ = lean_nat_div(v___x_626_, v___x_627_);
lean_dec(v___x_626_);
v___x_629_ = lean_array_get_size(v_buckets_x27_624_);
v___x_630_ = lean_nat_dec_le(v___x_628_, v___x_629_);
lean_dec(v___x_628_);
if (v___x_630_ == 0)
{
lean_object* v_val_631_; lean_object* v___x_633_; 
v_val_631_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_591_, v_buckets_x27_624_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 1, v_val_631_);
lean_ctor_set(v___x_619_, 0, v_size_x27_622_);
v___x_633_ = v___x_619_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_size_x27_622_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_val_631_);
v___x_633_ = v_reuseFailAlloc_636_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = lean_box(v___x_617_);
v___x_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
lean_ctor_set(v___x_635_, 1, v___x_633_);
return v___x_635_;
}
}
else
{
lean_object* v___x_638_; 
lean_dec_ref(v_inst_591_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 1, v_buckets_x27_624_);
lean_ctor_set(v___x_619_, 0, v_size_x27_622_);
v___x_638_ = v___x_619_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_size_x27_622_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v_buckets_x27_624_);
v___x_638_ = v_reuseFailAlloc_641_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = lean_box(v___x_617_);
v___x_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
lean_ctor_set(v___x_640_, 1, v___x_638_);
return v___x_640_;
}
}
}
}
else
{
lean_object* v___x_645_; lean_object* v___x_646_; 
lean_dec(v_b_594_);
lean_dec(v_a_593_);
lean_dec_ref(v_inst_591_);
v___x_645_ = lean_box(v___x_617_);
v___x_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
lean_ctor_set(v___x_646_, 1, v_m_592_);
return v___x_646_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x3f___redArg(lean_object* v_inst_647_, lean_object* v_inst_648_, lean_object* v_m_649_, lean_object* v_a_650_){
_start:
{
lean_object* v_buckets_651_; lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; 
v_buckets_651_ = lean_ctor_get(v_m_649_, 1);
v___x_652_ = lean_unsigned_to_nat(0u);
v___x_653_ = lean_array_get_size(v_buckets_651_);
v___x_654_ = lean_nat_dec_lt(v___x_652_, v___x_653_);
if (v___x_654_ == 0)
{
lean_object* v___x_655_; 
lean_dec(v_a_650_);
lean_dec_ref(v_inst_648_);
lean_dec_ref(v_inst_647_);
v___x_655_ = lean_box(0);
return v___x_655_;
}
else
{
lean_object* v___x_656_; 
v___x_656_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(v_inst_647_, v_inst_648_, v_m_649_, v_a_650_);
return v___x_656_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x3f___redArg___boxed(lean_object* v_inst_657_, lean_object* v_inst_658_, lean_object* v_m_659_, lean_object* v_a_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Std_DHashMap_Raw_get_x3f___redArg(v_inst_657_, v_inst_658_, v_m_659_, v_a_660_);
lean_dec_ref(v_m_659_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x3f(lean_object* v_00_u03b1_662_, lean_object* v_00_u03b2_663_, lean_object* v_inst_664_, lean_object* v_inst_665_, lean_object* v_inst_666_, lean_object* v_m_667_, lean_object* v_a_668_){
_start:
{
lean_object* v_buckets_669_; lean_object* v___x_670_; lean_object* v___x_671_; uint8_t v___x_672_; 
v_buckets_669_ = lean_ctor_get(v_m_667_, 1);
v___x_670_ = lean_unsigned_to_nat(0u);
v___x_671_ = lean_array_get_size(v_buckets_669_);
v___x_672_ = lean_nat_dec_lt(v___x_670_, v___x_671_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; 
lean_dec(v_a_668_);
lean_dec_ref(v_inst_666_);
lean_dec_ref(v_inst_664_);
v___x_673_ = lean_box(0);
return v___x_673_;
}
else
{
lean_object* v___x_674_; 
v___x_674_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(v_inst_664_, v_inst_666_, v_m_667_, v_a_668_);
return v___x_674_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x3f___boxed(lean_object* v_00_u03b1_675_, lean_object* v_00_u03b2_676_, lean_object* v_inst_677_, lean_object* v_inst_678_, lean_object* v_inst_679_, lean_object* v_m_680_, lean_object* v_a_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Std_DHashMap_Raw_get_x3f(v_00_u03b1_675_, v_00_u03b2_676_, v_inst_677_, v_inst_678_, v_inst_679_, v_m_680_, v_a_681_);
lean_dec_ref(v_m_680_);
return v_res_682_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_contains___redArg(lean_object* v_inst_683_, lean_object* v_inst_684_, lean_object* v_m_685_, lean_object* v_a_686_){
_start:
{
lean_object* v_buckets_687_; lean_object* v___x_688_; lean_object* v___x_689_; uint8_t v___x_690_; 
v_buckets_687_ = lean_ctor_get(v_m_685_, 1);
v___x_688_ = lean_unsigned_to_nat(0u);
v___x_689_ = lean_array_get_size(v_buckets_687_);
v___x_690_ = lean_nat_dec_lt(v___x_688_, v___x_689_);
if (v___x_690_ == 0)
{
lean_dec(v_a_686_);
lean_dec_ref(v_inst_684_);
lean_dec_ref(v_inst_683_);
return v___x_690_;
}
else
{
uint8_t v___x_691_; 
v___x_691_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_683_, v_inst_684_, v_m_685_, v_a_686_);
return v___x_691_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_contains___redArg___boxed(lean_object* v_inst_692_, lean_object* v_inst_693_, lean_object* v_m_694_, lean_object* v_a_695_){
_start:
{
uint8_t v_res_696_; lean_object* v_r_697_; 
v_res_696_ = l_Std_DHashMap_Raw_contains___redArg(v_inst_692_, v_inst_693_, v_m_694_, v_a_695_);
lean_dec_ref(v_m_694_);
v_r_697_ = lean_box(v_res_696_);
return v_r_697_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_contains(lean_object* v_00_u03b1_698_, lean_object* v_00_u03b2_699_, lean_object* v_inst_700_, lean_object* v_inst_701_, lean_object* v_m_702_, lean_object* v_a_703_){
_start:
{
lean_object* v_buckets_704_; lean_object* v___x_705_; lean_object* v___x_706_; uint8_t v___x_707_; 
v_buckets_704_ = lean_ctor_get(v_m_702_, 1);
v___x_705_ = lean_unsigned_to_nat(0u);
v___x_706_ = lean_array_get_size(v_buckets_704_);
v___x_707_ = lean_nat_dec_lt(v___x_705_, v___x_706_);
if (v___x_707_ == 0)
{
lean_dec(v_a_703_);
lean_dec_ref(v_inst_701_);
lean_dec_ref(v_inst_700_);
return v___x_707_;
}
else
{
uint8_t v___x_708_; 
v___x_708_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_700_, v_inst_701_, v_m_702_, v_a_703_);
return v___x_708_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_contains___boxed(lean_object* v_00_u03b1_709_, lean_object* v_00_u03b2_710_, lean_object* v_inst_711_, lean_object* v_inst_712_, lean_object* v_m_713_, lean_object* v_a_714_){
_start:
{
uint8_t v_res_715_; lean_object* v_r_716_; 
v_res_715_ = l_Std_DHashMap_Raw_contains(v_00_u03b1_709_, v_00_u03b2_710_, v_inst_711_, v_inst_712_, v_m_713_, v_a_714_);
lean_dec_ref(v_m_713_);
v_r_716_ = lean_box(v_res_715_);
return v_r_716_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instMembershipOfBEqOfHashable___redArg(){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = lean_box(0);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instMembershipOfBEqOfHashable___redArg___boxed(lean_object* v___dummy_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Std_DHashMap_Raw_instMembershipOfBEqOfHashable___redArg();
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instMembershipOfBEqOfHashable(lean_object* v_00_u03b1_721_, lean_object* v_00_u03b2_722_, lean_object* v_inst_723_, lean_object* v_inst_724_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = lean_box(0);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instMembershipOfBEqOfHashable___boxed(lean_object* v_00_u03b1_726_, lean_object* v_00_u03b2_727_, lean_object* v_inst_728_, lean_object* v_inst_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Std_DHashMap_Raw_instMembershipOfBEqOfHashable(v_00_u03b1_726_, v_00_u03b2_727_, v_inst_728_, v_inst_729_);
lean_dec_ref(v_inst_729_);
lean_dec_ref(v_inst_728_);
return v_res_730_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_instDecidableMem___redArg(lean_object* v_inst_731_, lean_object* v_inst_732_, lean_object* v_m_733_, lean_object* v_a_734_){
_start:
{
lean_object* v_buckets_735_; lean_object* v___x_736_; lean_object* v___x_737_; uint8_t v___x_738_; 
v_buckets_735_ = lean_ctor_get(v_m_733_, 1);
v___x_736_ = lean_unsigned_to_nat(0u);
v___x_737_ = lean_array_get_size(v_buckets_735_);
v___x_738_ = lean_nat_dec_lt(v___x_736_, v___x_737_);
if (v___x_738_ == 0)
{
lean_dec(v_a_734_);
lean_dec_ref(v_inst_732_);
lean_dec_ref(v_inst_731_);
return v___x_738_;
}
else
{
uint8_t v___x_739_; 
v___x_739_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_731_, v_inst_732_, v_m_733_, v_a_734_);
return v___x_739_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instDecidableMem___redArg___boxed(lean_object* v_inst_740_, lean_object* v_inst_741_, lean_object* v_m_742_, lean_object* v_a_743_){
_start:
{
uint8_t v_res_744_; lean_object* v_r_745_; 
v_res_744_ = l_Std_DHashMap_Raw_instDecidableMem___redArg(v_inst_740_, v_inst_741_, v_m_742_, v_a_743_);
lean_dec_ref(v_m_742_);
v_r_745_ = lean_box(v_res_744_);
return v_r_745_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_instDecidableMem(lean_object* v_00_u03b1_746_, lean_object* v_00_u03b2_747_, lean_object* v_inst_748_, lean_object* v_inst_749_, lean_object* v_m_750_, lean_object* v_a_751_){
_start:
{
uint8_t v___x_752_; 
v___x_752_ = l_Std_DHashMap_Raw_instDecidableMem___redArg(v_inst_748_, v_inst_749_, v_m_750_, v_a_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instDecidableMem___boxed(lean_object* v_00_u03b1_753_, lean_object* v_00_u03b2_754_, lean_object* v_inst_755_, lean_object* v_inst_756_, lean_object* v_m_757_, lean_object* v_a_758_){
_start:
{
uint8_t v_res_759_; lean_object* v_r_760_; 
v_res_759_ = l_Std_DHashMap_Raw_instDecidableMem(v_00_u03b1_753_, v_00_u03b2_754_, v_inst_755_, v_inst_756_, v_m_757_, v_a_758_);
lean_dec_ref(v_m_757_);
v_r_760_ = lean_box(v_res_759_);
return v_r_760_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get___redArg(lean_object* v_inst_761_, lean_object* v_inst_762_, lean_object* v_m_763_, lean_object* v_a_764_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_Std_DHashMap_Internal_Raw_u2080_get___redArg(v_inst_761_, v_inst_762_, v_m_763_, v_a_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get___redArg___boxed(lean_object* v_inst_766_, lean_object* v_inst_767_, lean_object* v_m_768_, lean_object* v_a_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Std_DHashMap_Raw_get___redArg(v_inst_766_, v_inst_767_, v_m_768_, v_a_769_);
lean_dec_ref(v_m_768_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get(lean_object* v_00_u03b1_771_, lean_object* v_00_u03b2_772_, lean_object* v_inst_773_, lean_object* v_inst_774_, lean_object* v_inst_775_, lean_object* v_m_776_, lean_object* v_a_777_, lean_object* v_h_778_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l_Std_DHashMap_Internal_Raw_u2080_get___redArg(v_inst_773_, v_inst_774_, v_m_776_, v_a_777_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get___boxed(lean_object* v_00_u03b1_780_, lean_object* v_00_u03b2_781_, lean_object* v_inst_782_, lean_object* v_inst_783_, lean_object* v_inst_784_, lean_object* v_m_785_, lean_object* v_a_786_, lean_object* v_h_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Std_DHashMap_Raw_get(v_00_u03b1_780_, v_00_u03b2_781_, v_inst_782_, v_inst_783_, v_inst_784_, v_m_785_, v_a_786_, v_h_787_);
lean_dec_ref(v_m_785_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getD___redArg(lean_object* v_inst_789_, lean_object* v_inst_790_, lean_object* v_m_791_, lean_object* v_a_792_, lean_object* v_fallback_793_){
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
lean_inc(v_fallback_793_);
return v_fallback_793_;
}
else
{
lean_object* v___x_798_; 
v___x_798_ = l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(v_inst_789_, v_inst_790_, v_m_791_, v_a_792_, v_fallback_793_);
return v___x_798_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getD___redArg___boxed(lean_object* v_inst_799_, lean_object* v_inst_800_, lean_object* v_m_801_, lean_object* v_a_802_, lean_object* v_fallback_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Std_DHashMap_Raw_getD___redArg(v_inst_799_, v_inst_800_, v_m_801_, v_a_802_, v_fallback_803_);
lean_dec(v_fallback_803_);
lean_dec_ref(v_m_801_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getD(lean_object* v_00_u03b1_805_, lean_object* v_00_u03b2_806_, lean_object* v_inst_807_, lean_object* v_inst_808_, lean_object* v_inst_809_, lean_object* v_m_810_, lean_object* v_a_811_, lean_object* v_fallback_812_){
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
lean_inc(v_fallback_812_);
return v_fallback_812_;
}
else
{
lean_object* v___x_817_; 
v___x_817_ = l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(v_inst_807_, v_inst_808_, v_m_810_, v_a_811_, v_fallback_812_);
return v___x_817_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getD___boxed(lean_object* v_00_u03b1_818_, lean_object* v_00_u03b2_819_, lean_object* v_inst_820_, lean_object* v_inst_821_, lean_object* v_inst_822_, lean_object* v_m_823_, lean_object* v_a_824_, lean_object* v_fallback_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Std_DHashMap_Raw_getD(v_00_u03b1_818_, v_00_u03b2_819_, v_inst_820_, v_inst_821_, v_inst_822_, v_m_823_, v_a_824_, v_fallback_825_);
lean_dec(v_fallback_825_);
lean_dec_ref(v_m_823_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x21___redArg(lean_object* v_inst_827_, lean_object* v_inst_828_, lean_object* v_m_829_, lean_object* v_a_830_, lean_object* v_inst_831_){
_start:
{
lean_object* v_buckets_832_; lean_object* v___x_833_; lean_object* v___x_834_; uint8_t v___x_835_; 
v_buckets_832_ = lean_ctor_get(v_m_829_, 1);
v___x_833_ = lean_unsigned_to_nat(0u);
v___x_834_ = lean_array_get_size(v_buckets_832_);
v___x_835_ = lean_nat_dec_lt(v___x_833_, v___x_834_);
if (v___x_835_ == 0)
{
lean_dec(v_a_830_);
lean_dec_ref(v_inst_828_);
lean_dec_ref(v_inst_827_);
lean_inc(v_inst_831_);
return v_inst_831_;
}
else
{
lean_object* v___x_836_; 
v___x_836_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(v_inst_827_, v_inst_828_, v_m_829_, v_a_830_, v_inst_831_);
return v___x_836_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x21___redArg___boxed(lean_object* v_inst_837_, lean_object* v_inst_838_, lean_object* v_m_839_, lean_object* v_a_840_, lean_object* v_inst_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Std_DHashMap_Raw_get_x21___redArg(v_inst_837_, v_inst_838_, v_m_839_, v_a_840_, v_inst_841_);
lean_dec(v_inst_841_);
lean_dec_ref(v_m_839_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x21(lean_object* v_00_u03b1_843_, lean_object* v_00_u03b2_844_, lean_object* v_inst_845_, lean_object* v_inst_846_, lean_object* v_inst_847_, lean_object* v_m_848_, lean_object* v_a_849_, lean_object* v_inst_850_){
_start:
{
lean_object* v_buckets_851_; lean_object* v___x_852_; lean_object* v___x_853_; uint8_t v___x_854_; 
v_buckets_851_ = lean_ctor_get(v_m_848_, 1);
v___x_852_ = lean_unsigned_to_nat(0u);
v___x_853_ = lean_array_get_size(v_buckets_851_);
v___x_854_ = lean_nat_dec_lt(v___x_852_, v___x_853_);
if (v___x_854_ == 0)
{
lean_dec(v_a_849_);
lean_dec_ref(v_inst_846_);
lean_dec_ref(v_inst_845_);
lean_inc(v_inst_850_);
return v_inst_850_;
}
else
{
lean_object* v___x_855_; 
v___x_855_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(v_inst_845_, v_inst_846_, v_m_848_, v_a_849_, v_inst_850_);
return v___x_855_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x21___boxed(lean_object* v_00_u03b1_856_, lean_object* v_00_u03b2_857_, lean_object* v_inst_858_, lean_object* v_inst_859_, lean_object* v_inst_860_, lean_object* v_m_861_, lean_object* v_a_862_, lean_object* v_inst_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_Std_DHashMap_Raw_get_x21(v_00_u03b1_856_, v_00_u03b2_857_, v_inst_858_, v_inst_859_, v_inst_860_, v_m_861_, v_a_862_, v_inst_863_);
lean_dec(v_inst_863_);
lean_dec_ref(v_m_861_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_erase___redArg(lean_object* v_inst_865_, lean_object* v_inst_866_, lean_object* v_m_867_, lean_object* v_a_868_){
_start:
{
lean_object* v_buckets_869_; lean_object* v___x_870_; lean_object* v___x_871_; uint8_t v___x_872_; 
v_buckets_869_ = lean_ctor_get(v_m_867_, 1);
v___x_870_ = lean_unsigned_to_nat(0u);
v___x_871_ = lean_array_get_size(v_buckets_869_);
v___x_872_ = lean_nat_dec_lt(v___x_870_, v___x_871_);
if (v___x_872_ == 0)
{
lean_dec(v_a_868_);
lean_dec_ref(v_inst_866_);
lean_dec_ref(v_inst_865_);
return v_m_867_;
}
else
{
lean_object* v___x_873_; 
v___x_873_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_865_, v_inst_866_, v_m_867_, v_a_868_);
return v___x_873_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_erase(lean_object* v_00_u03b1_874_, lean_object* v_00_u03b2_875_, lean_object* v_inst_876_, lean_object* v_inst_877_, lean_object* v_m_878_, lean_object* v_a_879_){
_start:
{
lean_object* v_buckets_880_; lean_object* v___x_881_; lean_object* v___x_882_; uint8_t v___x_883_; 
v_buckets_880_ = lean_ctor_get(v_m_878_, 1);
v___x_881_ = lean_unsigned_to_nat(0u);
v___x_882_ = lean_array_get_size(v_buckets_880_);
v___x_883_ = lean_nat_dec_lt(v___x_881_, v___x_882_);
if (v___x_883_ == 0)
{
lean_dec(v_a_879_);
lean_dec_ref(v_inst_877_);
lean_dec_ref(v_inst_876_);
return v_m_878_;
}
else
{
lean_object* v___x_884_; 
v___x_884_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_876_, v_inst_877_, v_m_878_, v_a_879_);
return v___x_884_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x3f___redArg(lean_object* v_inst_885_, lean_object* v_inst_886_, lean_object* v_m_887_, lean_object* v_a_888_){
_start:
{
lean_object* v_buckets_889_; lean_object* v___x_890_; lean_object* v___x_891_; uint8_t v___x_892_; 
v_buckets_889_ = lean_ctor_get(v_m_887_, 1);
v___x_890_ = lean_unsigned_to_nat(0u);
v___x_891_ = lean_array_get_size(v_buckets_889_);
v___x_892_ = lean_nat_dec_lt(v___x_890_, v___x_891_);
if (v___x_892_ == 0)
{
lean_object* v___x_893_; 
lean_dec(v_a_888_);
lean_dec_ref(v_inst_886_);
lean_dec_ref(v_inst_885_);
v___x_893_ = lean_box(0);
return v___x_893_;
}
else
{
lean_object* v___x_894_; 
v___x_894_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_885_, v_inst_886_, v_m_887_, v_a_888_);
return v___x_894_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x3f___redArg___boxed(lean_object* v_inst_895_, lean_object* v_inst_896_, lean_object* v_m_897_, lean_object* v_a_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Std_DHashMap_Raw_Const_get_x3f___redArg(v_inst_895_, v_inst_896_, v_m_897_, v_a_898_);
lean_dec_ref(v_m_897_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x3f(lean_object* v_00_u03b1_900_, lean_object* v_00_u03b2_901_, lean_object* v_inst_902_, lean_object* v_inst_903_, lean_object* v_m_904_, lean_object* v_a_905_){
_start:
{
lean_object* v_buckets_906_; lean_object* v___x_907_; lean_object* v___x_908_; uint8_t v___x_909_; 
v_buckets_906_ = lean_ctor_get(v_m_904_, 1);
v___x_907_ = lean_unsigned_to_nat(0u);
v___x_908_ = lean_array_get_size(v_buckets_906_);
v___x_909_ = lean_nat_dec_lt(v___x_907_, v___x_908_);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; 
lean_dec(v_a_905_);
lean_dec_ref(v_inst_903_);
lean_dec_ref(v_inst_902_);
v___x_910_ = lean_box(0);
return v___x_910_;
}
else
{
lean_object* v___x_911_; 
v___x_911_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_902_, v_inst_903_, v_m_904_, v_a_905_);
return v___x_911_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x3f___boxed(lean_object* v_00_u03b1_912_, lean_object* v_00_u03b2_913_, lean_object* v_inst_914_, lean_object* v_inst_915_, lean_object* v_m_916_, lean_object* v_a_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_Std_DHashMap_Raw_Const_get_x3f(v_00_u03b1_912_, v_00_u03b2_913_, v_inst_914_, v_inst_915_, v_m_916_, v_a_917_);
lean_dec_ref(v_m_916_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get___redArg(lean_object* v_inst_919_, lean_object* v_inst_920_, lean_object* v_m_921_, lean_object* v_a_922_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_919_, v_inst_920_, v_m_921_, v_a_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get___redArg___boxed(lean_object* v_inst_924_, lean_object* v_inst_925_, lean_object* v_m_926_, lean_object* v_a_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Std_DHashMap_Raw_Const_get___redArg(v_inst_924_, v_inst_925_, v_m_926_, v_a_927_);
lean_dec_ref(v_m_926_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get(lean_object* v_00_u03b1_929_, lean_object* v_00_u03b2_930_, lean_object* v_inst_931_, lean_object* v_inst_932_, lean_object* v_m_933_, lean_object* v_a_934_, lean_object* v_h_935_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_931_, v_inst_932_, v_m_933_, v_a_934_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get___boxed(lean_object* v_00_u03b1_937_, lean_object* v_00_u03b2_938_, lean_object* v_inst_939_, lean_object* v_inst_940_, lean_object* v_m_941_, lean_object* v_a_942_, lean_object* v_h_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Std_DHashMap_Raw_Const_get(v_00_u03b1_937_, v_00_u03b2_938_, v_inst_939_, v_inst_940_, v_m_941_, v_a_942_, v_h_943_);
lean_dec_ref(v_m_941_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getD___redArg(lean_object* v_inst_945_, lean_object* v_inst_946_, lean_object* v_m_947_, lean_object* v_a_948_, lean_object* v_fallback_949_){
_start:
{
lean_object* v_buckets_950_; lean_object* v___x_951_; lean_object* v___x_952_; uint8_t v___x_953_; 
v_buckets_950_ = lean_ctor_get(v_m_947_, 1);
v___x_951_ = lean_unsigned_to_nat(0u);
v___x_952_ = lean_array_get_size(v_buckets_950_);
v___x_953_ = lean_nat_dec_lt(v___x_951_, v___x_952_);
if (v___x_953_ == 0)
{
lean_dec(v_a_948_);
lean_dec_ref(v_inst_946_);
lean_dec_ref(v_inst_945_);
lean_inc(v_fallback_949_);
return v_fallback_949_;
}
else
{
lean_object* v___x_954_; 
v___x_954_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_inst_945_, v_inst_946_, v_m_947_, v_a_948_, v_fallback_949_);
return v___x_954_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getD___redArg___boxed(lean_object* v_inst_955_, lean_object* v_inst_956_, lean_object* v_m_957_, lean_object* v_a_958_, lean_object* v_fallback_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Std_DHashMap_Raw_Const_getD___redArg(v_inst_955_, v_inst_956_, v_m_957_, v_a_958_, v_fallback_959_);
lean_dec(v_fallback_959_);
lean_dec_ref(v_m_957_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getD(lean_object* v_00_u03b1_961_, lean_object* v_00_u03b2_962_, lean_object* v_inst_963_, lean_object* v_inst_964_, lean_object* v_m_965_, lean_object* v_a_966_, lean_object* v_fallback_967_){
_start:
{
lean_object* v_buckets_968_; lean_object* v___x_969_; lean_object* v___x_970_; uint8_t v___x_971_; 
v_buckets_968_ = lean_ctor_get(v_m_965_, 1);
v___x_969_ = lean_unsigned_to_nat(0u);
v___x_970_ = lean_array_get_size(v_buckets_968_);
v___x_971_ = lean_nat_dec_lt(v___x_969_, v___x_970_);
if (v___x_971_ == 0)
{
lean_dec(v_a_966_);
lean_dec_ref(v_inst_964_);
lean_dec_ref(v_inst_963_);
lean_inc(v_fallback_967_);
return v_fallback_967_;
}
else
{
lean_object* v___x_972_; 
v___x_972_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_inst_963_, v_inst_964_, v_m_965_, v_a_966_, v_fallback_967_);
return v___x_972_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getD___boxed(lean_object* v_00_u03b1_973_, lean_object* v_00_u03b2_974_, lean_object* v_inst_975_, lean_object* v_inst_976_, lean_object* v_m_977_, lean_object* v_a_978_, lean_object* v_fallback_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Std_DHashMap_Raw_Const_getD(v_00_u03b1_973_, v_00_u03b2_974_, v_inst_975_, v_inst_976_, v_m_977_, v_a_978_, v_fallback_979_);
lean_dec(v_fallback_979_);
lean_dec_ref(v_m_977_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x21___redArg(lean_object* v_inst_981_, lean_object* v_inst_982_, lean_object* v_inst_983_, lean_object* v_m_984_, lean_object* v_a_985_){
_start:
{
lean_object* v_buckets_986_; lean_object* v___x_987_; lean_object* v___x_988_; uint8_t v___x_989_; 
v_buckets_986_ = lean_ctor_get(v_m_984_, 1);
v___x_987_ = lean_unsigned_to_nat(0u);
v___x_988_ = lean_array_get_size(v_buckets_986_);
v___x_989_ = lean_nat_dec_lt(v___x_987_, v___x_988_);
if (v___x_989_ == 0)
{
lean_dec(v_a_985_);
lean_dec_ref(v_inst_982_);
lean_dec_ref(v_inst_981_);
lean_inc(v_inst_983_);
return v_inst_983_;
}
else
{
lean_object* v___x_990_; 
v___x_990_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_981_, v_inst_982_, v_inst_983_, v_m_984_, v_a_985_);
return v___x_990_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x21___redArg___boxed(lean_object* v_inst_991_, lean_object* v_inst_992_, lean_object* v_inst_993_, lean_object* v_m_994_, lean_object* v_a_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Std_DHashMap_Raw_Const_get_x21___redArg(v_inst_991_, v_inst_992_, v_inst_993_, v_m_994_, v_a_995_);
lean_dec_ref(v_m_994_);
lean_dec(v_inst_993_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x21(lean_object* v_00_u03b1_997_, lean_object* v_00_u03b2_998_, lean_object* v_inst_999_, lean_object* v_inst_1000_, lean_object* v_inst_1001_, lean_object* v_m_1002_, lean_object* v_a_1003_){
_start:
{
lean_object* v_buckets_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; uint8_t v___x_1007_; 
v_buckets_1004_ = lean_ctor_get(v_m_1002_, 1);
v___x_1005_ = lean_unsigned_to_nat(0u);
v___x_1006_ = lean_array_get_size(v_buckets_1004_);
v___x_1007_ = lean_nat_dec_lt(v___x_1005_, v___x_1006_);
if (v___x_1007_ == 0)
{
lean_dec(v_a_1003_);
lean_dec_ref(v_inst_1000_);
lean_dec_ref(v_inst_999_);
lean_inc(v_inst_1001_);
return v_inst_1001_;
}
else
{
lean_object* v___x_1008_; 
v___x_1008_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_999_, v_inst_1000_, v_inst_1001_, v_m_1002_, v_a_1003_);
return v___x_1008_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x21___boxed(lean_object* v_00_u03b1_1009_, lean_object* v_00_u03b2_1010_, lean_object* v_inst_1011_, lean_object* v_inst_1012_, lean_object* v_inst_1013_, lean_object* v_m_1014_, lean_object* v_a_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Std_DHashMap_Raw_Const_get_x21(v_00_u03b1_1009_, v_00_u03b2_1010_, v_inst_1011_, v_inst_1012_, v_inst_1013_, v_m_1014_, v_a_1015_);
lean_dec_ref(v_m_1014_);
lean_dec(v_inst_1013_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getThenInsertIfNew_x3f___redArg(lean_object* v_inst_1017_, lean_object* v_inst_1018_, lean_object* v_m_1019_, lean_object* v_a_1020_, lean_object* v_b_1021_){
_start:
{
lean_object* v_size_1022_; lean_object* v_buckets_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; uint8_t v___x_1026_; 
v_size_1022_ = lean_ctor_get(v_m_1019_, 0);
v_buckets_1023_ = lean_ctor_get(v_m_1019_, 1);
v___x_1024_ = lean_unsigned_to_nat(0u);
v___x_1025_ = lean_array_get_size(v_buckets_1023_);
v___x_1026_ = lean_nat_dec_lt(v___x_1024_, v___x_1025_);
if (v___x_1026_ == 0)
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
lean_dec(v_b_1021_);
lean_dec(v_a_1020_);
lean_dec_ref(v_inst_1018_);
lean_dec_ref(v_inst_1017_);
v___x_1027_ = lean_box(0);
v___x_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
lean_ctor_set(v___x_1028_, 1, v_m_1019_);
return v___x_1028_;
}
else
{
lean_object* v___x_1029_; uint64_t v___x_1030_; uint64_t v___x_1031_; uint64_t v___x_1032_; uint64_t v___x_1033_; uint64_t v_fold_1034_; uint64_t v___x_1035_; uint64_t v___x_1036_; uint64_t v___x_1037_; size_t v___x_1038_; size_t v___x_1039_; size_t v___x_1040_; size_t v___x_1041_; size_t v___x_1042_; lean_object* v_bkt_1043_; lean_object* v___x_1044_; 
lean_inc_ref(v_inst_1018_);
lean_inc_n(v_a_1020_, 2);
v___x_1029_ = lean_apply_1(v_inst_1018_, v_a_1020_);
v___x_1030_ = 32ULL;
v___x_1031_ = lean_unbox_uint64(v___x_1029_);
v___x_1032_ = lean_uint64_shift_right(v___x_1031_, v___x_1030_);
v___x_1033_ = lean_unbox_uint64(v___x_1029_);
lean_dec_ref(v___x_1029_);
v_fold_1034_ = lean_uint64_xor(v___x_1033_, v___x_1032_);
v___x_1035_ = 16ULL;
v___x_1036_ = lean_uint64_shift_right(v_fold_1034_, v___x_1035_);
v___x_1037_ = lean_uint64_xor(v_fold_1034_, v___x_1036_);
v___x_1038_ = lean_uint64_to_usize(v___x_1037_);
v___x_1039_ = lean_usize_of_nat(v___x_1025_);
v___x_1040_ = ((size_t)1ULL);
v___x_1041_ = lean_usize_sub(v___x_1039_, v___x_1040_);
v___x_1042_ = lean_usize_land(v___x_1038_, v___x_1041_);
v_bkt_1043_ = lean_array_uget_borrowed(v_buckets_1023_, v___x_1042_);
lean_inc(v_bkt_1043_);
v___x_1044_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_inst_1017_, v_a_1020_, v_bkt_1043_);
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1067_; 
lean_inc_ref(v_buckets_1023_);
lean_inc(v_size_1022_);
v_isSharedCheck_1067_ = !lean_is_exclusive(v_m_1019_);
if (v_isSharedCheck_1067_ == 0)
{
lean_object* v_unused_1068_; lean_object* v_unused_1069_; 
v_unused_1068_ = lean_ctor_get(v_m_1019_, 1);
lean_dec(v_unused_1068_);
v_unused_1069_ = lean_ctor_get(v_m_1019_, 0);
lean_dec(v_unused_1069_);
v___x_1046_ = v_m_1019_;
v_isShared_1047_ = v_isSharedCheck_1067_;
goto v_resetjp_1045_;
}
else
{
lean_dec(v_m_1019_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1067_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1048_; lean_object* v_size_x27_1049_; lean_object* v___x_1050_; lean_object* v_buckets_x27_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; uint8_t v___x_1057_; 
v___x_1048_ = lean_unsigned_to_nat(1u);
v_size_x27_1049_ = lean_nat_add(v_size_1022_, v___x_1048_);
lean_dec(v_size_1022_);
lean_inc(v_bkt_1043_);
v___x_1050_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1050_, 0, v_a_1020_);
lean_ctor_set(v___x_1050_, 1, v_b_1021_);
lean_ctor_set(v___x_1050_, 2, v_bkt_1043_);
v_buckets_x27_1051_ = lean_array_uset(v_buckets_1023_, v___x_1042_, v___x_1050_);
v___x_1052_ = lean_unsigned_to_nat(4u);
v___x_1053_ = lean_nat_mul(v_size_x27_1049_, v___x_1052_);
v___x_1054_ = lean_unsigned_to_nat(3u);
v___x_1055_ = lean_nat_div(v___x_1053_, v___x_1054_);
lean_dec(v___x_1053_);
v___x_1056_ = lean_array_get_size(v_buckets_x27_1051_);
v___x_1057_ = lean_nat_dec_le(v___x_1055_, v___x_1056_);
lean_dec(v___x_1055_);
if (v___x_1057_ == 0)
{
lean_object* v_val_1058_; lean_object* v___x_1060_; 
v_val_1058_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1018_, v_buckets_x27_1051_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 1, v_val_1058_);
lean_ctor_set(v___x_1046_, 0, v_size_x27_1049_);
v___x_1060_ = v___x_1046_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_size_x27_1049_);
lean_ctor_set(v_reuseFailAlloc_1062_, 1, v_val_1058_);
v___x_1060_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
lean_object* v___x_1061_; 
v___x_1061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1044_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
return v___x_1061_;
}
}
else
{
lean_object* v___x_1064_; 
lean_dec_ref(v_inst_1018_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 1, v_buckets_x27_1051_);
lean_ctor_set(v___x_1046_, 0, v_size_x27_1049_);
v___x_1064_ = v___x_1046_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_size_x27_1049_);
lean_ctor_set(v_reuseFailAlloc_1066_, 1, v_buckets_x27_1051_);
v___x_1064_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
lean_object* v___x_1065_; 
v___x_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1044_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
return v___x_1065_;
}
}
}
}
else
{
lean_object* v___x_1070_; 
lean_dec(v_b_1021_);
lean_dec(v_a_1020_);
lean_dec_ref(v_inst_1018_);
v___x_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1044_);
lean_ctor_set(v___x_1070_, 1, v_m_1019_);
return v___x_1070_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_1071_, lean_object* v_00_u03b2_1072_, lean_object* v_inst_1073_, lean_object* v_inst_1074_, lean_object* v_m_1075_, lean_object* v_a_1076_, lean_object* v_b_1077_){
_start:
{
lean_object* v_size_1078_; lean_object* v_buckets_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; uint8_t v___x_1082_; 
v_size_1078_ = lean_ctor_get(v_m_1075_, 0);
v_buckets_1079_ = lean_ctor_get(v_m_1075_, 1);
v___x_1080_ = lean_unsigned_to_nat(0u);
v___x_1081_ = lean_array_get_size(v_buckets_1079_);
v___x_1082_ = lean_nat_dec_lt(v___x_1080_, v___x_1081_);
if (v___x_1082_ == 0)
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
lean_dec(v_b_1077_);
lean_dec(v_a_1076_);
lean_dec_ref(v_inst_1074_);
lean_dec_ref(v_inst_1073_);
v___x_1083_ = lean_box(0);
v___x_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
lean_ctor_set(v___x_1084_, 1, v_m_1075_);
return v___x_1084_;
}
else
{
lean_object* v___x_1085_; uint64_t v___x_1086_; uint64_t v___x_1087_; uint64_t v___x_1088_; uint64_t v___x_1089_; uint64_t v_fold_1090_; uint64_t v___x_1091_; uint64_t v___x_1092_; uint64_t v___x_1093_; size_t v___x_1094_; size_t v___x_1095_; size_t v___x_1096_; size_t v___x_1097_; size_t v___x_1098_; lean_object* v_bkt_1099_; lean_object* v___x_1100_; 
lean_inc_ref(v_inst_1074_);
lean_inc_n(v_a_1076_, 2);
v___x_1085_ = lean_apply_1(v_inst_1074_, v_a_1076_);
v___x_1086_ = 32ULL;
v___x_1087_ = lean_unbox_uint64(v___x_1085_);
v___x_1088_ = lean_uint64_shift_right(v___x_1087_, v___x_1086_);
v___x_1089_ = lean_unbox_uint64(v___x_1085_);
lean_dec_ref(v___x_1085_);
v_fold_1090_ = lean_uint64_xor(v___x_1089_, v___x_1088_);
v___x_1091_ = 16ULL;
v___x_1092_ = lean_uint64_shift_right(v_fold_1090_, v___x_1091_);
v___x_1093_ = lean_uint64_xor(v_fold_1090_, v___x_1092_);
v___x_1094_ = lean_uint64_to_usize(v___x_1093_);
v___x_1095_ = lean_usize_of_nat(v___x_1081_);
v___x_1096_ = ((size_t)1ULL);
v___x_1097_ = lean_usize_sub(v___x_1095_, v___x_1096_);
v___x_1098_ = lean_usize_land(v___x_1094_, v___x_1097_);
v_bkt_1099_ = lean_array_uget_borrowed(v_buckets_1079_, v___x_1098_);
lean_inc(v_bkt_1099_);
v___x_1100_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_inst_1073_, v_a_1076_, v_bkt_1099_);
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1123_; 
lean_inc_ref(v_buckets_1079_);
lean_inc(v_size_1078_);
v_isSharedCheck_1123_ = !lean_is_exclusive(v_m_1075_);
if (v_isSharedCheck_1123_ == 0)
{
lean_object* v_unused_1124_; lean_object* v_unused_1125_; 
v_unused_1124_ = lean_ctor_get(v_m_1075_, 1);
lean_dec(v_unused_1124_);
v_unused_1125_ = lean_ctor_get(v_m_1075_, 0);
lean_dec(v_unused_1125_);
v___x_1102_ = v_m_1075_;
v_isShared_1103_ = v_isSharedCheck_1123_;
goto v_resetjp_1101_;
}
else
{
lean_dec(v_m_1075_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1123_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1104_; lean_object* v_size_x27_1105_; lean_object* v___x_1106_; lean_object* v_buckets_x27_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; uint8_t v___x_1113_; 
v___x_1104_ = lean_unsigned_to_nat(1u);
v_size_x27_1105_ = lean_nat_add(v_size_1078_, v___x_1104_);
lean_dec(v_size_1078_);
lean_inc(v_bkt_1099_);
v___x_1106_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1106_, 0, v_a_1076_);
lean_ctor_set(v___x_1106_, 1, v_b_1077_);
lean_ctor_set(v___x_1106_, 2, v_bkt_1099_);
v_buckets_x27_1107_ = lean_array_uset(v_buckets_1079_, v___x_1098_, v___x_1106_);
v___x_1108_ = lean_unsigned_to_nat(4u);
v___x_1109_ = lean_nat_mul(v_size_x27_1105_, v___x_1108_);
v___x_1110_ = lean_unsigned_to_nat(3u);
v___x_1111_ = lean_nat_div(v___x_1109_, v___x_1110_);
lean_dec(v___x_1109_);
v___x_1112_ = lean_array_get_size(v_buckets_x27_1107_);
v___x_1113_ = lean_nat_dec_le(v___x_1111_, v___x_1112_);
lean_dec(v___x_1111_);
if (v___x_1113_ == 0)
{
lean_object* v_val_1114_; lean_object* v___x_1116_; 
v_val_1114_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1074_, v_buckets_x27_1107_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 1, v_val_1114_);
lean_ctor_set(v___x_1102_, 0, v_size_x27_1105_);
v___x_1116_ = v___x_1102_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_size_x27_1105_);
lean_ctor_set(v_reuseFailAlloc_1118_, 1, v_val_1114_);
v___x_1116_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
lean_object* v___x_1117_; 
v___x_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1100_);
lean_ctor_set(v___x_1117_, 1, v___x_1116_);
return v___x_1117_;
}
}
else
{
lean_object* v___x_1120_; 
lean_dec_ref(v_inst_1074_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 1, v_buckets_x27_1107_);
lean_ctor_set(v___x_1102_, 0, v_size_x27_1105_);
v___x_1120_ = v___x_1102_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_size_x27_1105_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v_buckets_x27_1107_);
v___x_1120_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
lean_object* v___x_1121_; 
v___x_1121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1100_);
lean_ctor_set(v___x_1121_, 1, v___x_1120_);
return v___x_1121_;
}
}
}
}
else
{
lean_object* v___x_1126_; 
lean_dec(v_b_1077_);
lean_dec(v_a_1076_);
lean_dec_ref(v_inst_1074_);
v___x_1126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1100_);
lean_ctor_set(v___x_1126_, 1, v_m_1075_);
return v___x_1126_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x3f___redArg(lean_object* v_inst_1127_, lean_object* v_inst_1128_, lean_object* v_m_1129_, lean_object* v_a_1130_){
_start:
{
lean_object* v_buckets_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; uint8_t v___x_1134_; 
v_buckets_1131_ = lean_ctor_get(v_m_1129_, 1);
v___x_1132_ = lean_unsigned_to_nat(0u);
v___x_1133_ = lean_array_get_size(v_buckets_1131_);
v___x_1134_ = lean_nat_dec_lt(v___x_1132_, v___x_1133_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1135_; 
lean_dec(v_a_1130_);
lean_dec_ref(v_inst_1128_);
lean_dec_ref(v_inst_1127_);
v___x_1135_ = lean_box(0);
return v___x_1135_;
}
else
{
lean_object* v___x_1136_; 
v___x_1136_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_1127_, v_inst_1128_, v_m_1129_, v_a_1130_);
return v___x_1136_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x3f___redArg___boxed(lean_object* v_inst_1137_, lean_object* v_inst_1138_, lean_object* v_m_1139_, lean_object* v_a_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Std_DHashMap_Raw_getKey_x3f___redArg(v_inst_1137_, v_inst_1138_, v_m_1139_, v_a_1140_);
lean_dec_ref(v_m_1139_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x3f(lean_object* v_00_u03b1_1142_, lean_object* v_00_u03b2_1143_, lean_object* v_inst_1144_, lean_object* v_inst_1145_, lean_object* v_m_1146_, lean_object* v_a_1147_){
_start:
{
lean_object* v_buckets_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; uint8_t v___x_1151_; 
v_buckets_1148_ = lean_ctor_get(v_m_1146_, 1);
v___x_1149_ = lean_unsigned_to_nat(0u);
v___x_1150_ = lean_array_get_size(v_buckets_1148_);
v___x_1151_ = lean_nat_dec_lt(v___x_1149_, v___x_1150_);
if (v___x_1151_ == 0)
{
lean_object* v___x_1152_; 
lean_dec(v_a_1147_);
lean_dec_ref(v_inst_1145_);
lean_dec_ref(v_inst_1144_);
v___x_1152_ = lean_box(0);
return v___x_1152_;
}
else
{
lean_object* v___x_1153_; 
v___x_1153_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_1144_, v_inst_1145_, v_m_1146_, v_a_1147_);
return v___x_1153_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x3f___boxed(lean_object* v_00_u03b1_1154_, lean_object* v_00_u03b2_1155_, lean_object* v_inst_1156_, lean_object* v_inst_1157_, lean_object* v_m_1158_, lean_object* v_a_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l_Std_DHashMap_Raw_getKey_x3f(v_00_u03b1_1154_, v_00_u03b2_1155_, v_inst_1156_, v_inst_1157_, v_m_1158_, v_a_1159_);
lean_dec_ref(v_m_1158_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey___redArg(lean_object* v_inst_1161_, lean_object* v_inst_1162_, lean_object* v_m_1163_, lean_object* v_a_1164_){
_start:
{
lean_object* v___x_1165_; 
v___x_1165_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_1161_, v_inst_1162_, v_m_1163_, v_a_1164_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey___redArg___boxed(lean_object* v_inst_1166_, lean_object* v_inst_1167_, lean_object* v_m_1168_, lean_object* v_a_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_Std_DHashMap_Raw_getKey___redArg(v_inst_1166_, v_inst_1167_, v_m_1168_, v_a_1169_);
lean_dec_ref(v_m_1168_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey(lean_object* v_00_u03b1_1171_, lean_object* v_00_u03b2_1172_, lean_object* v_inst_1173_, lean_object* v_inst_1174_, lean_object* v_m_1175_, lean_object* v_a_1176_, lean_object* v_h_1177_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_1173_, v_inst_1174_, v_m_1175_, v_a_1176_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey___boxed(lean_object* v_00_u03b1_1179_, lean_object* v_00_u03b2_1180_, lean_object* v_inst_1181_, lean_object* v_inst_1182_, lean_object* v_m_1183_, lean_object* v_a_1184_, lean_object* v_h_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_Std_DHashMap_Raw_getKey(v_00_u03b1_1179_, v_00_u03b2_1180_, v_inst_1181_, v_inst_1182_, v_m_1183_, v_a_1184_, v_h_1185_);
lean_dec_ref(v_m_1183_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKeyD___redArg(lean_object* v_inst_1187_, lean_object* v_inst_1188_, lean_object* v_m_1189_, lean_object* v_a_1190_, lean_object* v_fallback_1191_){
_start:
{
lean_object* v_buckets_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; uint8_t v___x_1195_; 
v_buckets_1192_ = lean_ctor_get(v_m_1189_, 1);
v___x_1193_ = lean_unsigned_to_nat(0u);
v___x_1194_ = lean_array_get_size(v_buckets_1192_);
v___x_1195_ = lean_nat_dec_lt(v___x_1193_, v___x_1194_);
if (v___x_1195_ == 0)
{
lean_dec(v_a_1190_);
lean_dec_ref(v_inst_1188_);
lean_dec_ref(v_inst_1187_);
lean_inc(v_fallback_1191_);
return v_fallback_1191_;
}
else
{
lean_object* v___x_1196_; 
v___x_1196_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_1187_, v_inst_1188_, v_m_1189_, v_a_1190_, v_fallback_1191_);
return v___x_1196_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKeyD___redArg___boxed(lean_object* v_inst_1197_, lean_object* v_inst_1198_, lean_object* v_m_1199_, lean_object* v_a_1200_, lean_object* v_fallback_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Std_DHashMap_Raw_getKeyD___redArg(v_inst_1197_, v_inst_1198_, v_m_1199_, v_a_1200_, v_fallback_1201_);
lean_dec(v_fallback_1201_);
lean_dec_ref(v_m_1199_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKeyD(lean_object* v_00_u03b1_1203_, lean_object* v_00_u03b2_1204_, lean_object* v_inst_1205_, lean_object* v_inst_1206_, lean_object* v_m_1207_, lean_object* v_a_1208_, lean_object* v_fallback_1209_){
_start:
{
lean_object* v_buckets_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; uint8_t v___x_1213_; 
v_buckets_1210_ = lean_ctor_get(v_m_1207_, 1);
v___x_1211_ = lean_unsigned_to_nat(0u);
v___x_1212_ = lean_array_get_size(v_buckets_1210_);
v___x_1213_ = lean_nat_dec_lt(v___x_1211_, v___x_1212_);
if (v___x_1213_ == 0)
{
lean_dec(v_a_1208_);
lean_dec_ref(v_inst_1206_);
lean_dec_ref(v_inst_1205_);
lean_inc(v_fallback_1209_);
return v_fallback_1209_;
}
else
{
lean_object* v___x_1214_; 
v___x_1214_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_1205_, v_inst_1206_, v_m_1207_, v_a_1208_, v_fallback_1209_);
return v___x_1214_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKeyD___boxed(lean_object* v_00_u03b1_1215_, lean_object* v_00_u03b2_1216_, lean_object* v_inst_1217_, lean_object* v_inst_1218_, lean_object* v_m_1219_, lean_object* v_a_1220_, lean_object* v_fallback_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_Std_DHashMap_Raw_getKeyD(v_00_u03b1_1215_, v_00_u03b2_1216_, v_inst_1217_, v_inst_1218_, v_m_1219_, v_a_1220_, v_fallback_1221_);
lean_dec(v_fallback_1221_);
lean_dec_ref(v_m_1219_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x21___redArg(lean_object* v_inst_1223_, lean_object* v_inst_1224_, lean_object* v_inst_1225_, lean_object* v_m_1226_, lean_object* v_a_1227_){
_start:
{
lean_object* v_buckets_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; uint8_t v___x_1231_; 
v_buckets_1228_ = lean_ctor_get(v_m_1226_, 1);
v___x_1229_ = lean_unsigned_to_nat(0u);
v___x_1230_ = lean_array_get_size(v_buckets_1228_);
v___x_1231_ = lean_nat_dec_lt(v___x_1229_, v___x_1230_);
if (v___x_1231_ == 0)
{
lean_dec(v_a_1227_);
lean_dec_ref(v_inst_1224_);
lean_dec_ref(v_inst_1223_);
lean_inc(v_inst_1225_);
return v_inst_1225_;
}
else
{
lean_object* v___x_1232_; 
v___x_1232_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_1223_, v_inst_1224_, v_inst_1225_, v_m_1226_, v_a_1227_);
return v___x_1232_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x21___redArg___boxed(lean_object* v_inst_1233_, lean_object* v_inst_1234_, lean_object* v_inst_1235_, lean_object* v_m_1236_, lean_object* v_a_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Std_DHashMap_Raw_getKey_x21___redArg(v_inst_1233_, v_inst_1234_, v_inst_1235_, v_m_1236_, v_a_1237_);
lean_dec_ref(v_m_1236_);
lean_dec(v_inst_1235_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x21(lean_object* v_00_u03b1_1239_, lean_object* v_00_u03b2_1240_, lean_object* v_inst_1241_, lean_object* v_inst_1242_, lean_object* v_inst_1243_, lean_object* v_m_1244_, lean_object* v_a_1245_){
_start:
{
lean_object* v_buckets_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; uint8_t v___x_1249_; 
v_buckets_1246_ = lean_ctor_get(v_m_1244_, 1);
v___x_1247_ = lean_unsigned_to_nat(0u);
v___x_1248_ = lean_array_get_size(v_buckets_1246_);
v___x_1249_ = lean_nat_dec_lt(v___x_1247_, v___x_1248_);
if (v___x_1249_ == 0)
{
lean_dec(v_a_1245_);
lean_dec_ref(v_inst_1242_);
lean_dec_ref(v_inst_1241_);
lean_inc(v_inst_1243_);
return v_inst_1243_;
}
else
{
lean_object* v___x_1250_; 
v___x_1250_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_1241_, v_inst_1242_, v_inst_1243_, v_m_1244_, v_a_1245_);
return v___x_1250_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x21___boxed(lean_object* v_00_u03b1_1251_, lean_object* v_00_u03b2_1252_, lean_object* v_inst_1253_, lean_object* v_inst_1254_, lean_object* v_inst_1255_, lean_object* v_m_1256_, lean_object* v_a_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_Std_DHashMap_Raw_getKey_x21(v_00_u03b1_1251_, v_00_u03b2_1252_, v_inst_1253_, v_inst_1254_, v_inst_1255_, v_m_1256_, v_a_1257_);
lean_dec_ref(v_m_1256_);
lean_dec(v_inst_1255_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x3f___redArg(lean_object* v_inst_1259_, lean_object* v_inst_1260_, lean_object* v_m_1261_, lean_object* v_a_1262_){
_start:
{
lean_object* v_buckets_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; uint8_t v___x_1266_; 
v_buckets_1263_ = lean_ctor_get(v_m_1261_, 1);
v___x_1264_ = lean_unsigned_to_nat(0u);
v___x_1265_ = lean_array_get_size(v_buckets_1263_);
v___x_1266_ = lean_nat_dec_lt(v___x_1264_, v___x_1265_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1267_; 
lean_dec(v_a_1262_);
lean_dec_ref(v_inst_1260_);
lean_dec_ref(v_inst_1259_);
v___x_1267_ = lean_box(0);
return v___x_1267_;
}
else
{
lean_object* v___x_1268_; 
v___x_1268_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(v_inst_1259_, v_inst_1260_, v_m_1261_, v_a_1262_);
return v___x_1268_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x3f___redArg___boxed(lean_object* v_inst_1269_, lean_object* v_inst_1270_, lean_object* v_m_1271_, lean_object* v_a_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Std_DHashMap_Raw_getEntry_x3f___redArg(v_inst_1269_, v_inst_1270_, v_m_1271_, v_a_1272_);
lean_dec_ref(v_m_1271_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x3f(lean_object* v_00_u03b1_1274_, lean_object* v_00_u03b2_1275_, lean_object* v_inst_1276_, lean_object* v_inst_1277_, lean_object* v_m_1278_, lean_object* v_a_1279_){
_start:
{
lean_object* v_buckets_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; uint8_t v___x_1283_; 
v_buckets_1280_ = lean_ctor_get(v_m_1278_, 1);
v___x_1281_ = lean_unsigned_to_nat(0u);
v___x_1282_ = lean_array_get_size(v_buckets_1280_);
v___x_1283_ = lean_nat_dec_lt(v___x_1281_, v___x_1282_);
if (v___x_1283_ == 0)
{
lean_object* v___x_1284_; 
lean_dec(v_a_1279_);
lean_dec_ref(v_inst_1277_);
lean_dec_ref(v_inst_1276_);
v___x_1284_ = lean_box(0);
return v___x_1284_;
}
else
{
lean_object* v___x_1285_; 
v___x_1285_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(v_inst_1276_, v_inst_1277_, v_m_1278_, v_a_1279_);
return v___x_1285_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x3f___boxed(lean_object* v_00_u03b1_1286_, lean_object* v_00_u03b2_1287_, lean_object* v_inst_1288_, lean_object* v_inst_1289_, lean_object* v_m_1290_, lean_object* v_a_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l_Std_DHashMap_Raw_getEntry_x3f(v_00_u03b1_1286_, v_00_u03b2_1287_, v_inst_1288_, v_inst_1289_, v_m_1290_, v_a_1291_);
lean_dec_ref(v_m_1290_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry___redArg(lean_object* v_inst_1293_, lean_object* v_inst_1294_, lean_object* v_m_1295_, lean_object* v_a_1296_){
_start:
{
lean_object* v___x_1297_; 
v___x_1297_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg(v_inst_1293_, v_inst_1294_, v_m_1295_, v_a_1296_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry___redArg___boxed(lean_object* v_inst_1298_, lean_object* v_inst_1299_, lean_object* v_m_1300_, lean_object* v_a_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Std_DHashMap_Raw_getEntry___redArg(v_inst_1298_, v_inst_1299_, v_m_1300_, v_a_1301_);
lean_dec_ref(v_m_1300_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry(lean_object* v_00_u03b1_1303_, lean_object* v_00_u03b2_1304_, lean_object* v_inst_1305_, lean_object* v_inst_1306_, lean_object* v_m_1307_, lean_object* v_a_1308_, lean_object* v_h_1309_){
_start:
{
lean_object* v___x_1310_; 
v___x_1310_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg(v_inst_1305_, v_inst_1306_, v_m_1307_, v_a_1308_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry___boxed(lean_object* v_00_u03b1_1311_, lean_object* v_00_u03b2_1312_, lean_object* v_inst_1313_, lean_object* v_inst_1314_, lean_object* v_m_1315_, lean_object* v_a_1316_, lean_object* v_h_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Std_DHashMap_Raw_getEntry(v_00_u03b1_1311_, v_00_u03b2_1312_, v_inst_1313_, v_inst_1314_, v_m_1315_, v_a_1316_, v_h_1317_);
lean_dec_ref(v_m_1315_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntryD___redArg(lean_object* v_inst_1319_, lean_object* v_inst_1320_, lean_object* v_m_1321_, lean_object* v_a_1322_, lean_object* v_fallback_1323_){
_start:
{
lean_object* v_buckets_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; uint8_t v___x_1327_; 
v_buckets_1324_ = lean_ctor_get(v_m_1321_, 1);
v___x_1325_ = lean_unsigned_to_nat(0u);
v___x_1326_ = lean_array_get_size(v_buckets_1324_);
v___x_1327_ = lean_nat_dec_lt(v___x_1325_, v___x_1326_);
if (v___x_1327_ == 0)
{
lean_dec(v_a_1322_);
lean_dec_ref(v_inst_1320_);
lean_dec_ref(v_inst_1319_);
lean_inc_ref(v_fallback_1323_);
return v_fallback_1323_;
}
else
{
lean_object* v___x_1328_; 
v___x_1328_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD___redArg(v_inst_1319_, v_inst_1320_, v_m_1321_, v_a_1322_, v_fallback_1323_);
return v___x_1328_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntryD___redArg___boxed(lean_object* v_inst_1329_, lean_object* v_inst_1330_, lean_object* v_m_1331_, lean_object* v_a_1332_, lean_object* v_fallback_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_Std_DHashMap_Raw_getEntryD___redArg(v_inst_1329_, v_inst_1330_, v_m_1331_, v_a_1332_, v_fallback_1333_);
lean_dec_ref(v_fallback_1333_);
lean_dec_ref(v_m_1331_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntryD(lean_object* v_00_u03b1_1335_, lean_object* v_00_u03b2_1336_, lean_object* v_inst_1337_, lean_object* v_inst_1338_, lean_object* v_m_1339_, lean_object* v_a_1340_, lean_object* v_fallback_1341_){
_start:
{
lean_object* v_buckets_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; uint8_t v___x_1345_; 
v_buckets_1342_ = lean_ctor_get(v_m_1339_, 1);
v___x_1343_ = lean_unsigned_to_nat(0u);
v___x_1344_ = lean_array_get_size(v_buckets_1342_);
v___x_1345_ = lean_nat_dec_lt(v___x_1343_, v___x_1344_);
if (v___x_1345_ == 0)
{
lean_dec(v_a_1340_);
lean_dec_ref(v_inst_1338_);
lean_dec_ref(v_inst_1337_);
lean_inc_ref(v_fallback_1341_);
return v_fallback_1341_;
}
else
{
lean_object* v___x_1346_; 
v___x_1346_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD___redArg(v_inst_1337_, v_inst_1338_, v_m_1339_, v_a_1340_, v_fallback_1341_);
return v___x_1346_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntryD___boxed(lean_object* v_00_u03b1_1347_, lean_object* v_00_u03b2_1348_, lean_object* v_inst_1349_, lean_object* v_inst_1350_, lean_object* v_m_1351_, lean_object* v_a_1352_, lean_object* v_fallback_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l_Std_DHashMap_Raw_getEntryD(v_00_u03b1_1347_, v_00_u03b2_1348_, v_inst_1349_, v_inst_1350_, v_m_1351_, v_a_1352_, v_fallback_1353_);
lean_dec_ref(v_fallback_1353_);
lean_dec_ref(v_m_1351_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x21___redArg(lean_object* v_inst_1355_, lean_object* v_inst_1356_, lean_object* v_inst_1357_, lean_object* v_m_1358_, lean_object* v_a_1359_){
_start:
{
lean_object* v_buckets_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; uint8_t v___x_1363_; 
v_buckets_1360_ = lean_ctor_get(v_m_1358_, 1);
v___x_1361_ = lean_unsigned_to_nat(0u);
v___x_1362_ = lean_array_get_size(v_buckets_1360_);
v___x_1363_ = lean_nat_dec_lt(v___x_1361_, v___x_1362_);
if (v___x_1363_ == 0)
{
lean_dec(v_a_1359_);
lean_dec_ref(v_inst_1356_);
lean_dec_ref(v_inst_1355_);
lean_inc_ref(v_inst_1357_);
return v_inst_1357_;
}
else
{
lean_object* v___x_1364_; 
v___x_1364_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___redArg(v_inst_1355_, v_inst_1356_, v_m_1358_, v_a_1359_, v_inst_1357_);
return v___x_1364_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x21___redArg___boxed(lean_object* v_inst_1365_, lean_object* v_inst_1366_, lean_object* v_inst_1367_, lean_object* v_m_1368_, lean_object* v_a_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = l_Std_DHashMap_Raw_getEntry_x21___redArg(v_inst_1365_, v_inst_1366_, v_inst_1367_, v_m_1368_, v_a_1369_);
lean_dec_ref(v_m_1368_);
lean_dec_ref(v_inst_1367_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x21(lean_object* v_00_u03b1_1371_, lean_object* v_00_u03b2_1372_, lean_object* v_inst_1373_, lean_object* v_inst_1374_, lean_object* v_inst_1375_, lean_object* v_m_1376_, lean_object* v_a_1377_){
_start:
{
lean_object* v_buckets_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; uint8_t v___x_1381_; 
v_buckets_1378_ = lean_ctor_get(v_m_1376_, 1);
v___x_1379_ = lean_unsigned_to_nat(0u);
v___x_1380_ = lean_array_get_size(v_buckets_1378_);
v___x_1381_ = lean_nat_dec_lt(v___x_1379_, v___x_1380_);
if (v___x_1381_ == 0)
{
lean_dec(v_a_1377_);
lean_dec_ref(v_inst_1374_);
lean_dec_ref(v_inst_1373_);
lean_inc_ref(v_inst_1375_);
return v_inst_1375_;
}
else
{
lean_object* v___x_1382_; 
v___x_1382_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___redArg(v_inst_1373_, v_inst_1374_, v_m_1376_, v_a_1377_, v_inst_1375_);
return v___x_1382_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x21___boxed(lean_object* v_00_u03b1_1383_, lean_object* v_00_u03b2_1384_, lean_object* v_inst_1385_, lean_object* v_inst_1386_, lean_object* v_inst_1387_, lean_object* v_m_1388_, lean_object* v_a_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_Std_DHashMap_Raw_getEntry_x21(v_00_u03b1_1383_, v_00_u03b2_1384_, v_inst_1385_, v_inst_1386_, v_inst_1387_, v_m_1388_, v_a_1389_);
lean_dec_ref(v_m_1388_);
lean_dec_ref(v_inst_1387_);
return v_res_1390_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_isEmpty___redArg(lean_object* v_m_1391_){
_start:
{
lean_object* v_size_1392_; lean_object* v___x_1393_; uint8_t v___x_1394_; 
v_size_1392_ = lean_ctor_get(v_m_1391_, 0);
v___x_1393_ = lean_unsigned_to_nat(0u);
v___x_1394_ = lean_nat_dec_eq(v_size_1392_, v___x_1393_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_isEmpty___redArg___boxed(lean_object* v_m_1395_){
_start:
{
uint8_t v_res_1396_; lean_object* v_r_1397_; 
v_res_1396_ = l_Std_DHashMap_Raw_isEmpty___redArg(v_m_1395_);
lean_dec_ref(v_m_1395_);
v_r_1397_ = lean_box(v_res_1396_);
return v_r_1397_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_isEmpty(lean_object* v_00_u03b1_1398_, lean_object* v_00_u03b2_1399_, lean_object* v_m_1400_){
_start:
{
lean_object* v_size_1401_; lean_object* v___x_1402_; uint8_t v___x_1403_; 
v_size_1401_ = lean_ctor_get(v_m_1400_, 0);
v___x_1402_ = lean_unsigned_to_nat(0u);
v___x_1403_ = lean_nat_dec_eq(v_size_1401_, v___x_1402_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_isEmpty___boxed(lean_object* v_00_u03b1_1404_, lean_object* v_00_u03b2_1405_, lean_object* v_m_1406_){
_start:
{
uint8_t v_res_1407_; lean_object* v_r_1408_; 
v_res_1407_ = l_Std_DHashMap_Raw_isEmpty(v_00_u03b1_1404_, v_00_u03b2_1405_, v_m_1406_);
lean_dec_ref(v_m_1406_);
v_r_1408_ = lean_box(v_res_1407_);
return v_r_1408_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_modify___redArg(lean_object* v_inst_1409_, lean_object* v_inst_1410_, lean_object* v_m_1411_, lean_object* v_a_1412_, lean_object* v_f_1413_){
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
lean_dec_ref(v_inst_1409_);
v___x_1418_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1418_;
}
else
{
lean_object* v___x_1419_; 
v___x_1419_ = l_Std_DHashMap_Internal_Raw_u2080_modify___redArg(v_inst_1409_, v_inst_1410_, v_m_1411_, v_a_1412_, v_f_1413_);
return v___x_1419_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_modify(lean_object* v_00_u03b1_1420_, lean_object* v_00_u03b2_1421_, lean_object* v_inst_1422_, lean_object* v_inst_1423_, lean_object* v_inst_1424_, lean_object* v_m_1425_, lean_object* v_a_1426_, lean_object* v_f_1427_){
_start:
{
lean_object* v_buckets_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; uint8_t v___x_1431_; 
v_buckets_1428_ = lean_ctor_get(v_m_1425_, 1);
v___x_1429_ = lean_unsigned_to_nat(0u);
v___x_1430_ = lean_array_get_size(v_buckets_1428_);
v___x_1431_ = lean_nat_dec_lt(v___x_1429_, v___x_1430_);
if (v___x_1431_ == 0)
{
lean_object* v___x_1432_; 
lean_dec(v_f_1427_);
lean_dec(v_a_1426_);
lean_dec_ref(v_m_1425_);
lean_dec_ref(v_inst_1424_);
lean_dec_ref(v_inst_1422_);
v___x_1432_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1432_;
}
else
{
lean_object* v___x_1433_; 
v___x_1433_ = l_Std_DHashMap_Internal_Raw_u2080_modify___redArg(v_inst_1422_, v_inst_1424_, v_m_1425_, v_a_1426_, v_f_1427_);
return v___x_1433_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_modify___redArg(lean_object* v_inst_1434_, lean_object* v_inst_1435_, lean_object* v_m_1436_, lean_object* v_a_1437_, lean_object* v_f_1438_){
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
lean_dec_ref(v_inst_1435_);
lean_dec_ref(v_inst_1434_);
v___x_1443_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1443_;
}
else
{
lean_object* v___x_1444_; 
v___x_1444_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_inst_1434_, v_inst_1435_, v_m_1436_, v_a_1437_, v_f_1438_);
return v___x_1444_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_modify(lean_object* v_00_u03b1_1445_, lean_object* v_inst_1446_, lean_object* v_inst_1447_, lean_object* v_inst_1448_, lean_object* v_00_u03b2_1449_, lean_object* v_m_1450_, lean_object* v_a_1451_, lean_object* v_f_1452_){
_start:
{
lean_object* v_buckets_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; uint8_t v___x_1456_; 
v_buckets_1453_ = lean_ctor_get(v_m_1450_, 1);
v___x_1454_ = lean_unsigned_to_nat(0u);
v___x_1455_ = lean_array_get_size(v_buckets_1453_);
v___x_1456_ = lean_nat_dec_lt(v___x_1454_, v___x_1455_);
if (v___x_1456_ == 0)
{
lean_object* v___x_1457_; 
lean_dec(v_f_1452_);
lean_dec(v_a_1451_);
lean_dec_ref(v_m_1450_);
lean_dec_ref(v_inst_1448_);
lean_dec_ref(v_inst_1446_);
v___x_1457_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1457_;
}
else
{
lean_object* v___x_1458_; 
v___x_1458_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_inst_1446_, v_inst_1448_, v_m_1450_, v_a_1451_, v_f_1452_);
return v___x_1458_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_alter___redArg(lean_object* v_inst_1459_, lean_object* v_inst_1460_, lean_object* v_m_1461_, lean_object* v_a_1462_, lean_object* v_f_1463_){
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
lean_dec_ref(v_inst_1459_);
v___x_1468_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1468_;
}
else
{
lean_object* v___x_1469_; 
v___x_1469_ = l_Std_DHashMap_Internal_Raw_u2080_alter___redArg(v_inst_1459_, v_inst_1460_, v_m_1461_, v_a_1462_, v_f_1463_);
return v___x_1469_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_alter(lean_object* v_00_u03b1_1470_, lean_object* v_00_u03b2_1471_, lean_object* v_inst_1472_, lean_object* v_inst_1473_, lean_object* v_inst_1474_, lean_object* v_m_1475_, lean_object* v_a_1476_, lean_object* v_f_1477_){
_start:
{
lean_object* v_buckets_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; uint8_t v___x_1481_; 
v_buckets_1478_ = lean_ctor_get(v_m_1475_, 1);
v___x_1479_ = lean_unsigned_to_nat(0u);
v___x_1480_ = lean_array_get_size(v_buckets_1478_);
v___x_1481_ = lean_nat_dec_lt(v___x_1479_, v___x_1480_);
if (v___x_1481_ == 0)
{
lean_object* v___x_1482_; 
lean_dec_ref(v_f_1477_);
lean_dec(v_a_1476_);
lean_dec_ref(v_m_1475_);
lean_dec_ref(v_inst_1474_);
lean_dec_ref(v_inst_1472_);
v___x_1482_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1482_;
}
else
{
lean_object* v___x_1483_; 
v___x_1483_ = l_Std_DHashMap_Internal_Raw_u2080_alter___redArg(v_inst_1472_, v_inst_1474_, v_m_1475_, v_a_1476_, v_f_1477_);
return v___x_1483_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_alter___redArg(lean_object* v_inst_1484_, lean_object* v_inst_1485_, lean_object* v_m_1486_, lean_object* v_a_1487_, lean_object* v_f_1488_){
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
lean_dec_ref(v_inst_1485_);
lean_dec_ref(v_inst_1484_);
v___x_1493_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1493_;
}
else
{
lean_object* v___x_1494_; 
v___x_1494_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_1484_, v_inst_1485_, v_m_1486_, v_a_1487_, v_f_1488_);
return v___x_1494_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_alter(lean_object* v_00_u03b1_1495_, lean_object* v_inst_1496_, lean_object* v_inst_1497_, lean_object* v_inst_1498_, lean_object* v_00_u03b2_1499_, lean_object* v_m_1500_, lean_object* v_a_1501_, lean_object* v_f_1502_){
_start:
{
lean_object* v_buckets_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; uint8_t v___x_1506_; 
v_buckets_1503_ = lean_ctor_get(v_m_1500_, 1);
v___x_1504_ = lean_unsigned_to_nat(0u);
v___x_1505_ = lean_array_get_size(v_buckets_1503_);
v___x_1506_ = lean_nat_dec_lt(v___x_1504_, v___x_1505_);
if (v___x_1506_ == 0)
{
lean_object* v___x_1507_; 
lean_dec_ref(v_f_1502_);
lean_dec(v_a_1501_);
lean_dec_ref(v_m_1500_);
lean_dec_ref(v_inst_1498_);
lean_dec_ref(v_inst_1496_);
v___x_1507_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1507_;
}
else
{
lean_object* v___x_1508_; 
v___x_1508_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_1496_, v_inst_1498_, v_m_1500_, v_a_1501_, v_f_1502_);
return v___x_1508_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0(lean_object* v_f_1509_, lean_object* v_a_1510_, lean_object* v_b_1511_, lean_object* v_d_1512_){
_start:
{
lean_object* v___x_1513_; 
v___x_1513_ = lean_apply_3(v_f_1509_, v_d_1512_, v_a_1510_, v_b_1511_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__1(lean_object* v_inst_1514_, lean_object* v___f_1515_, lean_object* v_l_1516_, lean_object* v_acc_1517_){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v_inst_1514_, v___f_1515_, v_acc_1517_, v_l_1516_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRevM___redArg(lean_object* v_inst_1519_, lean_object* v_f_1520_, lean_object* v_init_1521_, lean_object* v_b_1522_){
_start:
{
lean_object* v_toApplicative_1523_; lean_object* v_buckets_1524_; lean_object* v_toPure_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; uint8_t v___x_1528_; 
v_toApplicative_1523_ = lean_ctor_get(v_inst_1519_, 0);
v_buckets_1524_ = lean_ctor_get(v_b_1522_, 1);
lean_inc_ref(v_buckets_1524_);
lean_dec_ref(v_b_1522_);
v_toPure_1525_ = lean_ctor_get(v_toApplicative_1523_, 1);
v___x_1526_ = lean_array_get_size(v_buckets_1524_);
v___x_1527_ = lean_unsigned_to_nat(0u);
v___x_1528_ = lean_nat_dec_lt(v___x_1527_, v___x_1526_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; 
lean_inc(v_toPure_1525_);
lean_dec_ref(v_buckets_1524_);
lean_dec(v_f_1520_);
lean_dec_ref(v_inst_1519_);
v___x_1529_ = lean_apply_2(v_toPure_1525_, lean_box(0), v_init_1521_);
return v___x_1529_;
}
else
{
lean_object* v___f_1530_; lean_object* v___f_1531_; size_t v___x_1532_; size_t v___x_1533_; lean_object* v___x_1534_; 
v___f_1530_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1530_, 0, v_f_1520_);
lean_inc_ref(v_inst_1519_);
v___f_1531_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1531_, 0, v_inst_1519_);
lean_closure_set(v___f_1531_, 1, v___f_1530_);
v___x_1532_ = lean_usize_of_nat(v___x_1526_);
v___x_1533_ = ((size_t)0ULL);
v___x_1534_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1519_, v___f_1531_, v_buckets_1524_, v___x_1532_, v___x_1533_, v_init_1521_);
return v___x_1534_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRevM(lean_object* v_00_u03b1_1535_, lean_object* v_00_u03b2_1536_, lean_object* v_00_u03b4_1537_, lean_object* v_m_1538_, lean_object* v_inst_1539_, lean_object* v_f_1540_, lean_object* v_init_1541_, lean_object* v_b_1542_){
_start:
{
lean_object* v_toApplicative_1543_; lean_object* v_buckets_1544_; lean_object* v_toPure_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; 
v_toApplicative_1543_ = lean_ctor_get(v_inst_1539_, 0);
v_buckets_1544_ = lean_ctor_get(v_b_1542_, 1);
lean_inc_ref(v_buckets_1544_);
lean_dec_ref(v_b_1542_);
v_toPure_1545_ = lean_ctor_get(v_toApplicative_1543_, 1);
v___x_1546_ = lean_array_get_size(v_buckets_1544_);
v___x_1547_ = lean_unsigned_to_nat(0u);
v___x_1548_ = lean_nat_dec_lt(v___x_1547_, v___x_1546_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; 
lean_inc(v_toPure_1545_);
lean_dec_ref(v_buckets_1544_);
lean_dec(v_f_1540_);
lean_dec_ref(v_inst_1539_);
v___x_1549_ = lean_apply_2(v_toPure_1545_, lean_box(0), v_init_1541_);
return v___x_1549_;
}
else
{
lean_object* v___f_1550_; lean_object* v___f_1551_; size_t v___x_1552_; size_t v___x_1553_; lean_object* v___x_1554_; 
v___f_1550_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1550_, 0, v_f_1540_);
lean_inc_ref(v_inst_1539_);
v___f_1551_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1551_, 0, v_inst_1539_);
lean_closure_set(v___f_1551_, 1, v___f_1550_);
v___x_1552_ = lean_usize_of_nat(v___x_1546_);
v___x_1553_ = ((size_t)0ULL);
v___x_1554_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1539_, v___f_1551_, v_buckets_1544_, v___x_1552_, v___x_1553_, v_init_1541_);
return v___x_1554_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRev___redArg___lam__1(lean_object* v___x_1555_, lean_object* v___f_1556_, lean_object* v_l_1557_, lean_object* v_acc_1558_){
_start:
{
lean_object* v___x_1559_; 
v___x_1559_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_1555_, v___f_1556_, v_acc_1558_, v_l_1557_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRev___redArg(lean_object* v_f_1579_, lean_object* v_init_1580_, lean_object* v_b_1581_){
_start:
{
lean_object* v___x_1582_; lean_object* v_buckets_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; uint8_t v___x_1586_; 
v___x_1582_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_1583_ = lean_ctor_get(v_b_1581_, 1);
lean_inc_ref(v_buckets_1583_);
lean_dec_ref(v_b_1581_);
v___x_1584_ = lean_array_get_size(v_buckets_1583_);
v___x_1585_ = lean_unsigned_to_nat(0u);
v___x_1586_ = lean_nat_dec_lt(v___x_1585_, v___x_1584_);
if (v___x_1586_ == 0)
{
lean_dec_ref(v_buckets_1583_);
lean_dec(v_f_1579_);
return v_init_1580_;
}
else
{
lean_object* v___f_1587_; lean_object* v___f_1588_; size_t v___x_1589_; size_t v___x_1590_; lean_object* v___x_1591_; 
v___f_1587_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1587_, 0, v_f_1579_);
v___f_1588_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1588_, 0, v___x_1582_);
lean_closure_set(v___f_1588_, 1, v___f_1587_);
v___x_1589_ = lean_usize_of_nat(v___x_1584_);
v___x_1590_ = ((size_t)0ULL);
v___x_1591_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1582_, v___f_1588_, v_buckets_1583_, v___x_1589_, v___x_1590_, v_init_1580_);
return v___x_1591_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRev(lean_object* v_00_u03b1_1592_, lean_object* v_00_u03b2_1593_, lean_object* v_00_u03b4_1594_, lean_object* v_f_1595_, lean_object* v_init_1596_, lean_object* v_b_1597_){
_start:
{
lean_object* v___x_1598_; lean_object* v_buckets_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; uint8_t v___x_1602_; 
v___x_1598_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_1599_ = lean_ctor_get(v_b_1597_, 1);
lean_inc_ref(v_buckets_1599_);
lean_dec_ref(v_b_1597_);
v___x_1600_ = lean_array_get_size(v_buckets_1599_);
v___x_1601_ = lean_unsigned_to_nat(0u);
v___x_1602_ = lean_nat_dec_lt(v___x_1601_, v___x_1600_);
if (v___x_1602_ == 0)
{
lean_dec_ref(v_buckets_1599_);
lean_dec(v_f_1595_);
return v_init_1596_;
}
else
{
lean_object* v___f_1603_; lean_object* v___f_1604_; size_t v___x_1605_; size_t v___x_1606_; lean_object* v___x_1607_; 
v___f_1603_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1603_, 0, v_f_1595_);
v___f_1604_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1604_, 0, v___x_1598_);
lean_closure_set(v___f_1604_, 1, v___f_1603_);
v___x_1605_ = lean_usize_of_nat(v___x_1600_);
v___x_1606_ = ((size_t)0ULL);
v___x_1607_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1598_, v___f_1604_, v_buckets_1599_, v___x_1605_, v___x_1606_, v_init_1596_);
return v___x_1607_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevM___redArg(lean_object* v_inst_1608_, lean_object* v_f_1609_, lean_object* v_init_1610_, lean_object* v_b_1611_){
_start:
{
lean_object* v_toApplicative_1612_; lean_object* v_buckets_1613_; lean_object* v_toPure_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; uint8_t v___x_1617_; 
v_toApplicative_1612_ = lean_ctor_get(v_inst_1608_, 0);
v_buckets_1613_ = lean_ctor_get(v_b_1611_, 1);
lean_inc_ref(v_buckets_1613_);
lean_dec_ref(v_b_1611_);
v_toPure_1614_ = lean_ctor_get(v_toApplicative_1612_, 1);
v___x_1615_ = lean_array_get_size(v_buckets_1613_);
v___x_1616_ = lean_unsigned_to_nat(0u);
v___x_1617_ = lean_nat_dec_lt(v___x_1616_, v___x_1615_);
if (v___x_1617_ == 0)
{
lean_object* v___x_1618_; 
lean_inc(v_toPure_1614_);
lean_dec_ref(v_buckets_1613_);
lean_dec(v_f_1609_);
lean_dec_ref(v_inst_1608_);
v___x_1618_ = lean_apply_2(v_toPure_1614_, lean_box(0), v_init_1610_);
return v___x_1618_;
}
else
{
lean_object* v___f_1619_; lean_object* v___f_1620_; size_t v___x_1621_; size_t v___x_1622_; lean_object* v___x_1623_; 
v___f_1619_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1619_, 0, v_f_1609_);
lean_inc_ref(v_inst_1608_);
v___f_1620_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1620_, 0, v_inst_1608_);
lean_closure_set(v___f_1620_, 1, v___f_1619_);
v___x_1621_ = lean_usize_of_nat(v___x_1615_);
v___x_1622_ = ((size_t)0ULL);
v___x_1623_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1608_, v___f_1620_, v_buckets_1613_, v___x_1621_, v___x_1622_, v_init_1610_);
return v___x_1623_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevM(lean_object* v_00_u03b1_1624_, lean_object* v_00_u03b2_1625_, lean_object* v_00_u03b4_1626_, lean_object* v_m_1627_, lean_object* v_inst_1628_, lean_object* v_f_1629_, lean_object* v_init_1630_, lean_object* v_b_1631_){
_start:
{
lean_object* v_toApplicative_1632_; lean_object* v_buckets_1633_; lean_object* v_toPure_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; uint8_t v___x_1637_; 
v_toApplicative_1632_ = lean_ctor_get(v_inst_1628_, 0);
v_buckets_1633_ = lean_ctor_get(v_b_1631_, 1);
lean_inc_ref(v_buckets_1633_);
lean_dec_ref(v_b_1631_);
v_toPure_1634_ = lean_ctor_get(v_toApplicative_1632_, 1);
v___x_1635_ = lean_array_get_size(v_buckets_1633_);
v___x_1636_ = lean_unsigned_to_nat(0u);
v___x_1637_ = lean_nat_dec_lt(v___x_1636_, v___x_1635_);
if (v___x_1637_ == 0)
{
lean_object* v___x_1638_; 
lean_inc(v_toPure_1634_);
lean_dec_ref(v_buckets_1633_);
lean_dec(v_f_1629_);
lean_dec_ref(v_inst_1628_);
v___x_1638_ = lean_apply_2(v_toPure_1634_, lean_box(0), v_init_1630_);
return v___x_1638_;
}
else
{
lean_object* v___f_1639_; lean_object* v___f_1640_; size_t v___x_1641_; size_t v___x_1642_; lean_object* v___x_1643_; 
v___f_1639_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1639_, 0, v_f_1629_);
lean_inc_ref(v_inst_1628_);
v___f_1640_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1640_, 0, v_inst_1628_);
lean_closure_set(v___f_1640_, 1, v___f_1639_);
v___x_1641_ = lean_usize_of_nat(v___x_1635_);
v___x_1642_ = ((size_t)0ULL);
v___x_1643_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1628_, v___f_1640_, v_buckets_1633_, v___x_1641_, v___x_1642_, v_init_1630_);
return v___x_1643_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRev___redArg(lean_object* v_f_1644_, lean_object* v_init_1645_, lean_object* v_b_1646_){
_start:
{
lean_object* v___x_1647_; lean_object* v_buckets_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; uint8_t v___x_1651_; 
v___x_1647_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_1648_ = lean_ctor_get(v_b_1646_, 1);
lean_inc_ref(v_buckets_1648_);
lean_dec_ref(v_b_1646_);
v___x_1649_ = lean_array_get_size(v_buckets_1648_);
v___x_1650_ = lean_unsigned_to_nat(0u);
v___x_1651_ = lean_nat_dec_lt(v___x_1650_, v___x_1649_);
if (v___x_1651_ == 0)
{
lean_dec_ref(v_buckets_1648_);
lean_dec(v_f_1644_);
return v_init_1645_;
}
else
{
lean_object* v___f_1652_; lean_object* v___f_1653_; size_t v___x_1654_; size_t v___x_1655_; lean_object* v___x_1656_; 
v___f_1652_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1652_, 0, v_f_1644_);
v___f_1653_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1653_, 0, v___x_1647_);
lean_closure_set(v___f_1653_, 1, v___f_1652_);
v___x_1654_ = lean_usize_of_nat(v___x_1649_);
v___x_1655_ = ((size_t)0ULL);
v___x_1656_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1647_, v___f_1653_, v_buckets_1648_, v___x_1654_, v___x_1655_, v_init_1645_);
return v___x_1656_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRev(lean_object* v_00_u03b1_1657_, lean_object* v_00_u03b2_1658_, lean_object* v_00_u03b4_1659_, lean_object* v_f_1660_, lean_object* v_init_1661_, lean_object* v_b_1662_){
_start:
{
lean_object* v___x_1663_; lean_object* v_buckets_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; uint8_t v___x_1667_; 
v___x_1663_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_1664_ = lean_ctor_get(v_b_1662_, 1);
lean_inc_ref(v_buckets_1664_);
lean_dec_ref(v_b_1662_);
v___x_1665_ = lean_array_get_size(v_buckets_1664_);
v___x_1666_ = lean_unsigned_to_nat(0u);
v___x_1667_ = lean_nat_dec_lt(v___x_1666_, v___x_1665_);
if (v___x_1667_ == 0)
{
lean_dec_ref(v_buckets_1664_);
lean_dec(v_f_1660_);
return v_init_1661_;
}
else
{
lean_object* v___f_1668_; lean_object* v___f_1669_; size_t v___x_1670_; size_t v___x_1671_; lean_object* v___x_1672_; 
v___f_1668_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1668_, 0, v_f_1660_);
v___f_1669_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1669_, 0, v___x_1663_);
lean_closure_set(v___f_1669_, 1, v___f_1668_);
v___x_1670_ = lean_usize_of_nat(v___x_1665_);
v___x_1671_ = ((size_t)0ULL);
v___x_1672_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1663_, v___f_1669_, v_buckets_1664_, v___x_1670_, v___x_1671_, v_init_1661_);
return v___x_1672_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__0(lean_object* v_f_1673_, lean_object* v_x_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1677_, 0, v___y_1675_);
lean_ctor_set(v___x_1677_, 1, v___y_1676_);
v___x_1678_ = lean_apply_1(v_f_1673_, v___x_1677_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__1(lean_object* v_inst_1679_, lean_object* v___f_1680_, lean_object* v_x_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1683_ = lean_box(0);
v___x_1684_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_1679_, v___f_1680_, v___x_1683_, v___y_1682_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forMUncurried___redArg(lean_object* v_inst_1685_, lean_object* v_f_1686_, lean_object* v_b_1687_){
_start:
{
lean_object* v_toApplicative_1688_; lean_object* v_buckets_1689_; lean_object* v_toPure_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; uint8_t v___x_1694_; 
v_toApplicative_1688_ = lean_ctor_get(v_inst_1685_, 0);
v_buckets_1689_ = lean_ctor_get(v_b_1687_, 1);
lean_inc_ref(v_buckets_1689_);
lean_dec_ref(v_b_1687_);
v_toPure_1690_ = lean_ctor_get(v_toApplicative_1688_, 1);
v___x_1691_ = lean_unsigned_to_nat(0u);
v___x_1692_ = lean_array_get_size(v_buckets_1689_);
v___x_1693_ = lean_box(0);
v___x_1694_ = lean_nat_dec_lt(v___x_1691_, v___x_1692_);
if (v___x_1694_ == 0)
{
lean_object* v___x_1695_; 
lean_inc(v_toPure_1690_);
lean_dec_ref(v_buckets_1689_);
lean_dec(v_f_1686_);
lean_dec_ref(v_inst_1685_);
v___x_1695_ = lean_apply_2(v_toPure_1690_, lean_box(0), v___x_1693_);
return v___x_1695_;
}
else
{
lean_object* v___f_1696_; lean_object* v___f_1697_; size_t v___x_1698_; size_t v___x_1699_; lean_object* v___x_1700_; 
v___f_1696_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1696_, 0, v_f_1686_);
lean_inc_ref(v_inst_1685_);
v___f_1697_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1697_, 0, v_inst_1685_);
lean_closure_set(v___f_1697_, 1, v___f_1696_);
v___x_1698_ = ((size_t)0ULL);
v___x_1699_ = lean_usize_of_nat(v___x_1692_);
v___x_1700_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1685_, v___f_1697_, v_buckets_1689_, v___x_1698_, v___x_1699_, v___x_1693_);
return v___x_1700_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forMUncurried(lean_object* v_00_u03b1_1701_, lean_object* v_m_1702_, lean_object* v_inst_1703_, lean_object* v_00_u03b2_1704_, lean_object* v_f_1705_, lean_object* v_b_1706_){
_start:
{
lean_object* v_toApplicative_1707_; lean_object* v_buckets_1708_; lean_object* v_toPure_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; uint8_t v___x_1713_; 
v_toApplicative_1707_ = lean_ctor_get(v_inst_1703_, 0);
v_buckets_1708_ = lean_ctor_get(v_b_1706_, 1);
lean_inc_ref(v_buckets_1708_);
lean_dec_ref(v_b_1706_);
v_toPure_1709_ = lean_ctor_get(v_toApplicative_1707_, 1);
v___x_1710_ = lean_unsigned_to_nat(0u);
v___x_1711_ = lean_array_get_size(v_buckets_1708_);
v___x_1712_ = lean_box(0);
v___x_1713_ = lean_nat_dec_lt(v___x_1710_, v___x_1711_);
if (v___x_1713_ == 0)
{
lean_object* v___x_1714_; 
lean_inc(v_toPure_1709_);
lean_dec_ref(v_buckets_1708_);
lean_dec(v_f_1705_);
lean_dec_ref(v_inst_1703_);
v___x_1714_ = lean_apply_2(v_toPure_1709_, lean_box(0), v___x_1712_);
return v___x_1714_;
}
else
{
lean_object* v___f_1715_; lean_object* v___f_1716_; size_t v___x_1717_; size_t v___x_1718_; lean_object* v___x_1719_; 
v___f_1715_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1715_, 0, v_f_1705_);
lean_inc_ref(v_inst_1703_);
v___f_1716_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1716_, 0, v_inst_1703_);
lean_closure_set(v___f_1716_, 1, v___f_1715_);
v___x_1717_ = ((size_t)0ULL);
v___x_1718_ = lean_usize_of_nat(v___x_1711_);
v___x_1719_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1703_, v___f_1716_, v_buckets_1708_, v___x_1717_, v___x_1718_, v___x_1712_);
return v___x_1719_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__0(lean_object* v_f_1720_, lean_object* v_a_1721_, lean_object* v_b_1722_, lean_object* v_d_1723_){
_start:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1724_, 0, v_a_1721_);
lean_ctor_set(v___x_1724_, 1, v_b_1722_);
v___x_1725_ = lean_apply_2(v_f_1720_, v___x_1724_, v_d_1723_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__1(lean_object* v_inst_1726_, lean_object* v___f_1727_, lean_object* v_a_1728_, lean_object* v_x_1729_, lean_object* v___y_1730_){
_start:
{
lean_object* v___x_1731_; 
v___x_1731_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_1726_, v___f_1727_, v_a_1728_, v___y_1730_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forInUncurried___redArg(lean_object* v_inst_1732_, lean_object* v_f_1733_, lean_object* v_init_1734_, lean_object* v_b_1735_){
_start:
{
lean_object* v_buckets_1736_; lean_object* v___f_1737_; lean_object* v___f_1738_; size_t v_sz_1739_; size_t v___x_1740_; lean_object* v___x_1741_; 
v_buckets_1736_ = lean_ctor_get(v_b_1735_, 1);
lean_inc_ref(v_buckets_1736_);
lean_dec_ref(v_b_1735_);
v___f_1737_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1737_, 0, v_f_1733_);
lean_inc_ref(v_inst_1732_);
v___f_1738_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1738_, 0, v_inst_1732_);
lean_closure_set(v___f_1738_, 1, v___f_1737_);
v_sz_1739_ = lean_array_size(v_buckets_1736_);
v___x_1740_ = ((size_t)0ULL);
v___x_1741_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1732_, v_buckets_1736_, v___f_1738_, v_sz_1739_, v___x_1740_, v_init_1734_);
return v___x_1741_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forInUncurried(lean_object* v_00_u03b1_1742_, lean_object* v_00_u03b4_1743_, lean_object* v_m_1744_, lean_object* v_inst_1745_, lean_object* v_00_u03b2_1746_, lean_object* v_f_1747_, lean_object* v_init_1748_, lean_object* v_b_1749_){
_start:
{
lean_object* v_buckets_1750_; lean_object* v___f_1751_; lean_object* v___f_1752_; size_t v_sz_1753_; size_t v___x_1754_; lean_object* v___x_1755_; 
v_buckets_1750_ = lean_ctor_get(v_b_1749_, 1);
lean_inc_ref(v_buckets_1750_);
lean_dec_ref(v_b_1749_);
v___f_1751_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1751_, 0, v_f_1747_);
lean_inc_ref(v_inst_1745_);
v___f_1752_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1752_, 0, v_inst_1745_);
lean_closure_set(v___f_1752_, 1, v___f_1751_);
v_sz_1753_ = lean_array_size(v_buckets_1750_);
v___x_1754_ = ((size_t)0ULL);
v___x_1755_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1745_, v_buckets_1750_, v___f_1752_, v_sz_1753_, v___x_1754_, v_init_1748_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_filterMap___redArg(lean_object* v_f_1756_, lean_object* v_m_1757_){
_start:
{
lean_object* v_buckets_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; uint8_t v___x_1761_; 
v_buckets_1758_ = lean_ctor_get(v_m_1757_, 1);
v___x_1759_ = lean_unsigned_to_nat(0u);
v___x_1760_ = lean_array_get_size(v_buckets_1758_);
v___x_1761_ = lean_nat_dec_lt(v___x_1759_, v___x_1760_);
if (v___x_1761_ == 0)
{
lean_object* v___x_1762_; 
lean_dec_ref(v_m_1757_);
lean_dec_ref(v_f_1756_);
v___x_1762_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1762_;
}
else
{
lean_object* v___x_1763_; 
v___x_1763_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_1756_, v_m_1757_);
return v___x_1763_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_filterMap(lean_object* v_00_u03b1_1764_, lean_object* v_00_u03b2_1765_, lean_object* v_00_u03b3_1766_, lean_object* v_f_1767_, lean_object* v_m_1768_){
_start:
{
lean_object* v_buckets_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; uint8_t v___x_1772_; 
v_buckets_1769_ = lean_ctor_get(v_m_1768_, 1);
v___x_1770_ = lean_unsigned_to_nat(0u);
v___x_1771_ = lean_array_get_size(v_buckets_1769_);
v___x_1772_ = lean_nat_dec_lt(v___x_1770_, v___x_1771_);
if (v___x_1772_ == 0)
{
lean_object* v___x_1773_; 
lean_dec_ref(v_m_1768_);
lean_dec_ref(v_f_1767_);
v___x_1773_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1773_;
}
else
{
lean_object* v___x_1774_; 
v___x_1774_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_1767_, v_m_1768_);
return v___x_1774_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_map___redArg(lean_object* v_f_1775_, lean_object* v_m_1776_){
_start:
{
lean_object* v_buckets_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; uint8_t v___x_1780_; 
v_buckets_1777_ = lean_ctor_get(v_m_1776_, 1);
v___x_1778_ = lean_unsigned_to_nat(0u);
v___x_1779_ = lean_array_get_size(v_buckets_1777_);
v___x_1780_ = lean_nat_dec_lt(v___x_1778_, v___x_1779_);
if (v___x_1780_ == 0)
{
lean_object* v___x_1781_; 
lean_dec_ref(v_m_1776_);
lean_dec(v_f_1775_);
v___x_1781_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1781_;
}
else
{
lean_object* v___x_1782_; 
v___x_1782_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_1775_, v_m_1776_);
return v___x_1782_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_map(lean_object* v_00_u03b1_1783_, lean_object* v_00_u03b2_1784_, lean_object* v_00_u03b3_1785_, lean_object* v_f_1786_, lean_object* v_m_1787_){
_start:
{
lean_object* v_buckets_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; uint8_t v___x_1791_; 
v_buckets_1788_ = lean_ctor_get(v_m_1787_, 1);
v___x_1789_ = lean_unsigned_to_nat(0u);
v___x_1790_ = lean_array_get_size(v_buckets_1788_);
v___x_1791_ = lean_nat_dec_lt(v___x_1789_, v___x_1790_);
if (v___x_1791_ == 0)
{
lean_object* v___x_1792_; 
lean_dec_ref(v_m_1787_);
lean_dec(v_f_1786_);
v___x_1792_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1792_;
}
else
{
lean_object* v___x_1793_; 
v___x_1793_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_1786_, v_m_1787_);
return v___x_1793_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_filter___redArg(lean_object* v_f_1794_, lean_object* v_m_1795_){
_start:
{
lean_object* v_buckets_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; uint8_t v___x_1799_; 
v_buckets_1796_ = lean_ctor_get(v_m_1795_, 1);
v___x_1797_ = lean_unsigned_to_nat(0u);
v___x_1798_ = lean_array_get_size(v_buckets_1796_);
v___x_1799_ = lean_nat_dec_lt(v___x_1797_, v___x_1798_);
if (v___x_1799_ == 0)
{
lean_object* v___x_1800_; 
lean_dec_ref(v_m_1795_);
lean_dec_ref(v_f_1794_);
v___x_1800_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1800_;
}
else
{
lean_object* v___x_1801_; 
v___x_1801_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1794_, v_m_1795_);
return v___x_1801_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_filter(lean_object* v_00_u03b1_1802_, lean_object* v_00_u03b2_1803_, lean_object* v_f_1804_, lean_object* v_m_1805_){
_start:
{
lean_object* v_buckets_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; uint8_t v___x_1809_; 
v_buckets_1806_ = lean_ctor_get(v_m_1805_, 1);
v___x_1807_ = lean_unsigned_to_nat(0u);
v___x_1808_ = lean_array_get_size(v_buckets_1806_);
v___x_1809_ = lean_nat_dec_lt(v___x_1807_, v___x_1808_);
if (v___x_1809_ == 0)
{
lean_object* v___x_1810_; 
lean_dec_ref(v_m_1805_);
lean_dec_ref(v_f_1804_);
v___x_1810_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1810_;
}
else
{
lean_object* v___x_1811_; 
v___x_1811_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1804_, v_m_1805_);
return v___x_1811_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toArray___redArg___lam__0(lean_object* v_x1_1812_, lean_object* v_x2_1813_, lean_object* v_x3_1814_){
_start:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1815_, 0, v_x2_1813_);
lean_ctor_set(v___x_1815_, 1, v_x3_1814_);
v___x_1816_ = lean_array_push(v_x1_1812_, v___x_1815_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toArray___redArg___lam__1(lean_object* v___x_1817_, lean_object* v___f_1818_, lean_object* v_acc_1819_, lean_object* v_l_1820_){
_start:
{
lean_object* v___x_1821_; 
v___x_1821_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1817_, v___f_1818_, v_acc_1819_, v_l_1820_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toArray___redArg(lean_object* v_m_1826_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toArray(lean_object* v_00_u03b1_1838_, lean_object* v_00_u03b2_1839_, lean_object* v_m_1840_){
_start:
{
lean_object* v_size_1841_; lean_object* v_buckets_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; uint8_t v___x_1847_; 
v_size_1841_ = lean_ctor_get(v_m_1840_, 0);
lean_inc(v_size_1841_);
v_buckets_1842_ = lean_ctor_get(v_m_1840_, 1);
lean_inc_ref(v_buckets_1842_);
lean_dec_ref(v_m_1840_);
v___x_1843_ = lean_mk_empty_array_with_capacity(v_size_1841_);
lean_dec(v_size_1841_);
v___x_1844_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_1845_ = lean_unsigned_to_nat(0u);
v___x_1846_ = lean_array_get_size(v_buckets_1842_);
v___x_1847_ = lean_nat_dec_lt(v___x_1845_, v___x_1846_);
if (v___x_1847_ == 0)
{
lean_dec_ref(v_buckets_1842_);
return v___x_1843_;
}
else
{
lean_object* v___f_1848_; size_t v___x_1849_; size_t v___x_1850_; lean_object* v___x_1851_; 
v___f_1848_ = ((lean_object*)(l_Std_DHashMap_Raw_toArray___redArg___closed__1));
v___x_1849_ = ((size_t)0ULL);
v___x_1850_ = lean_usize_of_nat(v___x_1846_);
v___x_1851_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1844_, v___f_1848_, v_buckets_1842_, v___x_1849_, v___x_1850_, v___x_1843_);
return v___x_1851_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toArray___redArg___lam__0(lean_object* v_x1_1852_, lean_object* v_x2_1853_, lean_object* v_x3_1854_){
_start:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1855_, 0, v_x2_1853_);
lean_ctor_set(v___x_1855_, 1, v_x3_1854_);
v___x_1856_ = lean_array_push(v_x1_1852_, v___x_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toArray___redArg___lam__1(lean_object* v___x_1857_, lean_object* v___f_1858_, lean_object* v_acc_1859_, lean_object* v_l_1860_){
_start:
{
lean_object* v___x_1861_; 
v___x_1861_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1857_, v___f_1858_, v_acc_1859_, v_l_1860_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toArray___redArg(lean_object* v_m_1866_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toArray(lean_object* v_00_u03b1_1878_, lean_object* v_00_u03b2_1879_, lean_object* v_m_1880_){
_start:
{
lean_object* v_size_1881_; lean_object* v_buckets_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; uint8_t v___x_1887_; 
v_size_1881_ = lean_ctor_get(v_m_1880_, 0);
lean_inc(v_size_1881_);
v_buckets_1882_ = lean_ctor_get(v_m_1880_, 1);
lean_inc_ref(v_buckets_1882_);
lean_dec_ref(v_m_1880_);
v___x_1883_ = lean_mk_empty_array_with_capacity(v_size_1881_);
lean_dec(v_size_1881_);
v___x_1884_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_1885_ = lean_unsigned_to_nat(0u);
v___x_1886_ = lean_array_get_size(v_buckets_1882_);
v___x_1887_ = lean_nat_dec_lt(v___x_1885_, v___x_1886_);
if (v___x_1887_ == 0)
{
lean_dec_ref(v_buckets_1882_);
return v___x_1883_;
}
else
{
lean_object* v___f_1888_; size_t v___x_1889_; size_t v___x_1890_; lean_object* v___x_1891_; 
v___f_1888_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_toArray___redArg___closed__1));
v___x_1889_ = ((size_t)0ULL);
v___x_1890_ = lean_usize_of_nat(v___x_1886_);
v___x_1891_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1884_, v___f_1888_, v_buckets_1882_, v___x_1889_, v___x_1890_, v___x_1883_);
return v___x_1891_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keysArray___redArg___lam__0(lean_object* v_x1_1892_, lean_object* v_x2_1893_, lean_object* v_x3_1894_){
_start:
{
lean_object* v___x_1895_; 
v___x_1895_ = lean_array_push(v_x1_1892_, v_x2_1893_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keysArray___redArg___lam__0___boxed(lean_object* v_x1_1896_, lean_object* v_x2_1897_, lean_object* v_x3_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l_Std_DHashMap_Raw_keysArray___redArg___lam__0(v_x1_1896_, v_x2_1897_, v_x3_1898_);
lean_dec(v_x3_1898_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keysArray___redArg___lam__1(lean_object* v___x_1900_, lean_object* v___f_1901_, lean_object* v_acc_1902_, lean_object* v_l_1903_){
_start:
{
lean_object* v___x_1904_; 
v___x_1904_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1900_, v___f_1901_, v_acc_1902_, v_l_1903_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keysArray___redArg(lean_object* v_m_1909_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keysArray(lean_object* v_00_u03b1_1921_, lean_object* v_00_u03b2_1922_, lean_object* v_m_1923_){
_start:
{
lean_object* v_size_1924_; lean_object* v_buckets_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; uint8_t v___x_1930_; 
v_size_1924_ = lean_ctor_get(v_m_1923_, 0);
lean_inc(v_size_1924_);
v_buckets_1925_ = lean_ctor_get(v_m_1923_, 1);
lean_inc_ref(v_buckets_1925_);
lean_dec_ref(v_m_1923_);
v___x_1926_ = lean_mk_empty_array_with_capacity(v_size_1924_);
lean_dec(v_size_1924_);
v___x_1927_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_1928_ = lean_unsigned_to_nat(0u);
v___x_1929_ = lean_array_get_size(v_buckets_1925_);
v___x_1930_ = lean_nat_dec_lt(v___x_1928_, v___x_1929_);
if (v___x_1930_ == 0)
{
lean_dec_ref(v_buckets_1925_);
return v___x_1926_;
}
else
{
lean_object* v___f_1931_; size_t v___x_1932_; size_t v___x_1933_; lean_object* v___x_1934_; 
v___f_1931_ = ((lean_object*)(l_Std_DHashMap_Raw_keysArray___redArg___closed__1));
v___x_1932_ = ((size_t)0ULL);
v___x_1933_ = lean_usize_of_nat(v___x_1929_);
v___x_1934_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1927_, v___f_1931_, v_buckets_1925_, v___x_1932_, v___x_1933_, v___x_1926_);
return v___x_1934_;
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
lean_object* v___x_1963_; uint8_t v___x_1964_; 
v___x_1963_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_1964_ = lean_nat_dec_le(v_size_1954_, v_size_1959_);
if (v___x_1964_ == 0)
{
lean_object* v___f_1965_; lean_object* v___x_1966_; 
v___f_1965_ = ((lean_object*)(l_Std_DHashMap_Raw_union___redArg___closed__0));
v___x_1966_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1965_, v_inst_1950_, v_inst_1951_, v_m_u2081_1952_, v_m_u2082_1953_);
return v___x_1966_;
}
else
{
lean_object* v___f_1967_; lean_object* v___f_1968_; size_t v_sz_1969_; size_t v___x_1970_; lean_object* v___x_1971_; 
lean_inc_ref(v_buckets_1955_);
lean_dec_ref(v_m_u2081_1952_);
v___f_1967_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1967_, 0, v_inst_1950_);
lean_closure_set(v___f_1967_, 1, v_inst_1951_);
v___f_1968_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1968_, 0, v___x_1963_);
lean_closure_set(v___f_1968_, 1, v___f_1967_);
v_sz_1969_ = lean_array_size(v_buckets_1955_);
v___x_1970_ = ((size_t)0ULL);
v___x_1971_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1963_, v_buckets_1955_, v___f_1968_, v_sz_1969_, v___x_1970_, v_m_u2082_1953_);
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
lean_object* v___x_1987_; uint8_t v___x_1988_; 
v___x_1987_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_1988_ = lean_nat_dec_le(v_size_1978_, v_size_1983_);
if (v___x_1988_ == 0)
{
lean_object* v___f_1989_; lean_object* v___x_1990_; 
v___f_1989_ = ((lean_object*)(l_Std_DHashMap_Raw_union___redArg___closed__0));
v___x_1990_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1989_, v_inst_1974_, v_inst_1975_, v_m_u2081_1976_, v_m_u2082_1977_);
return v___x_1990_;
}
else
{
lean_object* v___f_1991_; lean_object* v___f_1992_; size_t v_sz_1993_; size_t v___x_1994_; lean_object* v___x_1995_; 
lean_inc_ref(v_buckets_1979_);
lean_dec_ref(v_m_u2081_1976_);
v___f_1991_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1991_, 0, v_inst_1974_);
lean_closure_set(v___f_1991_, 1, v_inst_1975_);
v___f_1992_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1992_, 0, v___x_1987_);
lean_closure_set(v___f_1992_, 1, v___f_1991_);
v_sz_1993_ = lean_array_size(v_buckets_1979_);
v___x_1994_ = ((size_t)0ULL);
v___x_1995_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1987_, v_buckets_1979_, v___f_1992_, v_sz_1993_, v___x_1994_, v_m_u2082_1977_);
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
uint8_t v___y_2044_; lean_object* v_buckets_2046_; lean_object* v_buckets_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; uint8_t v___x_2050_; 
v_buckets_2046_ = lean_ctor_get(v_m_u2081_2041_, 1);
v_buckets_2047_ = lean_ctor_get(v_m_u2082_2042_, 1);
v___x_2048_ = lean_unsigned_to_nat(0u);
v___x_2049_ = lean_array_get_size(v_buckets_2046_);
v___x_2050_ = lean_nat_dec_lt(v___x_2048_, v___x_2049_);
if (v___x_2050_ == 0)
{
v___y_2044_ = v___x_2050_;
goto v___jp_2043_;
}
else
{
lean_object* v___x_2051_; uint8_t v___x_2052_; 
v___x_2051_ = lean_array_get_size(v_buckets_2047_);
v___x_2052_ = lean_nat_dec_lt(v___x_2048_, v___x_2051_);
v___y_2044_ = v___x_2052_;
goto v___jp_2043_;
}
v___jp_2043_:
{
if (v___y_2044_ == 0)
{
lean_dec_ref(v_m_u2082_2042_);
lean_dec_ref(v_m_u2081_2041_);
lean_dec_ref(v_inst_2040_);
lean_dec_ref(v_inst_2039_);
lean_dec_ref(v_inst_2038_);
return v___y_2044_;
}
else
{
uint8_t v___x_2045_; 
v___x_2045_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(v_inst_2038_, v_inst_2039_, v_inst_2040_, v_m_u2081_2041_, v_m_u2082_2042_);
return v___x_2045_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_beq___redArg___boxed(lean_object* v_inst_2053_, lean_object* v_inst_2054_, lean_object* v_inst_2055_, lean_object* v_m_u2081_2056_, lean_object* v_m_u2082_2057_){
_start:
{
uint8_t v_res_2058_; lean_object* v_r_2059_; 
v_res_2058_ = l_Std_DHashMap_Raw_beq___redArg(v_inst_2053_, v_inst_2054_, v_inst_2055_, v_m_u2081_2056_, v_m_u2082_2057_);
v_r_2059_ = lean_box(v_res_2058_);
return v_r_2059_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_beq(lean_object* v_00_u03b1_2060_, lean_object* v_00_u03b2_2061_, lean_object* v_inst_2062_, lean_object* v_inst_2063_, lean_object* v_inst_2064_, lean_object* v_inst_2065_, lean_object* v_m_u2081_2066_, lean_object* v_m_u2082_2067_){
_start:
{
uint8_t v___x_2068_; 
v___x_2068_ = l_Std_DHashMap_Raw_beq___redArg(v_inst_2062_, v_inst_2063_, v_inst_2065_, v_m_u2081_2066_, v_m_u2082_2067_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_beq___boxed(lean_object* v_00_u03b1_2069_, lean_object* v_00_u03b2_2070_, lean_object* v_inst_2071_, lean_object* v_inst_2072_, lean_object* v_inst_2073_, lean_object* v_inst_2074_, lean_object* v_m_u2081_2075_, lean_object* v_m_u2082_2076_){
_start:
{
uint8_t v_res_2077_; lean_object* v_r_2078_; 
v_res_2077_ = l_Std_DHashMap_Raw_beq(v_00_u03b1_2069_, v_00_u03b2_2070_, v_inst_2071_, v_inst_2072_, v_inst_2073_, v_inst_2074_, v_m_u2081_2075_, v_m_u2082_2076_);
v_r_2078_ = lean_box(v_res_2077_);
return v_r_2078_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instBEqOfHashableOfLawfulBEq___redArg(lean_object* v_inst_2079_, lean_object* v_inst_2080_, lean_object* v_inst_2081_){
_start:
{
lean_object* v___x_2082_; 
v___x_2082_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_beq___boxed), 8, 6);
lean_closure_set(v___x_2082_, 0, lean_box(0));
lean_closure_set(v___x_2082_, 1, lean_box(0));
lean_closure_set(v___x_2082_, 2, v_inst_2079_);
lean_closure_set(v___x_2082_, 3, v_inst_2080_);
lean_closure_set(v___x_2082_, 4, lean_box(0));
lean_closure_set(v___x_2082_, 5, v_inst_2081_);
return v___x_2082_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instBEqOfHashableOfLawfulBEq(lean_object* v_00_u03b1_2083_, lean_object* v_00_u03b2_2084_, lean_object* v_inst_2085_, lean_object* v_inst_2086_, lean_object* v_inst_2087_, lean_object* v_inst_2088_){
_start:
{
lean_object* v___x_2089_; 
v___x_2089_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_beq___boxed), 8, 6);
lean_closure_set(v___x_2089_, 0, lean_box(0));
lean_closure_set(v___x_2089_, 1, lean_box(0));
lean_closure_set(v___x_2089_, 2, v_inst_2085_);
lean_closure_set(v___x_2089_, 3, v_inst_2086_);
lean_closure_set(v___x_2089_, 4, lean_box(0));
lean_closure_set(v___x_2089_, 5, v_inst_2088_);
return v___x_2089_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_Const_beq___redArg(lean_object* v_inst_2090_, lean_object* v_inst_2091_, lean_object* v_inst_2092_, lean_object* v_m_u2081_2093_, lean_object* v_m_u2082_2094_){
_start:
{
uint8_t v___y_2096_; lean_object* v_buckets_2098_; lean_object* v_buckets_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; uint8_t v___x_2102_; 
v_buckets_2098_ = lean_ctor_get(v_m_u2081_2093_, 1);
v_buckets_2099_ = lean_ctor_get(v_m_u2082_2094_, 1);
v___x_2100_ = lean_unsigned_to_nat(0u);
v___x_2101_ = lean_array_get_size(v_buckets_2098_);
v___x_2102_ = lean_nat_dec_lt(v___x_2100_, v___x_2101_);
if (v___x_2102_ == 0)
{
v___y_2096_ = v___x_2102_;
goto v___jp_2095_;
}
else
{
lean_object* v___x_2103_; uint8_t v___x_2104_; 
v___x_2103_ = lean_array_get_size(v_buckets_2099_);
v___x_2104_ = lean_nat_dec_lt(v___x_2100_, v___x_2103_);
v___y_2096_ = v___x_2104_;
goto v___jp_2095_;
}
v___jp_2095_:
{
if (v___y_2096_ == 0)
{
lean_dec_ref(v_m_u2082_2094_);
lean_dec_ref(v_m_u2081_2093_);
lean_dec_ref(v_inst_2092_);
lean_dec_ref(v_inst_2091_);
lean_dec_ref(v_inst_2090_);
return v___y_2096_;
}
else
{
uint8_t v___x_2097_; 
v___x_2097_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_inst_2090_, v_inst_2091_, v_inst_2092_, v_m_u2081_2093_, v_m_u2082_2094_);
return v___x_2097_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_beq___redArg___boxed(lean_object* v_inst_2105_, lean_object* v_inst_2106_, lean_object* v_inst_2107_, lean_object* v_m_u2081_2108_, lean_object* v_m_u2082_2109_){
_start:
{
uint8_t v_res_2110_; lean_object* v_r_2111_; 
v_res_2110_ = l_Std_DHashMap_Raw_Const_beq___redArg(v_inst_2105_, v_inst_2106_, v_inst_2107_, v_m_u2081_2108_, v_m_u2082_2109_);
v_r_2111_ = lean_box(v_res_2110_);
return v_r_2111_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_Const_beq(lean_object* v_00_u03b1_2112_, lean_object* v_00_u03b2_2113_, lean_object* v_inst_2114_, lean_object* v_inst_2115_, lean_object* v_inst_2116_, lean_object* v_m_u2081_2117_, lean_object* v_m_u2082_2118_){
_start:
{
uint8_t v___x_2119_; 
v___x_2119_ = l_Std_DHashMap_Raw_Const_beq___redArg(v_inst_2114_, v_inst_2115_, v_inst_2116_, v_m_u2081_2117_, v_m_u2082_2118_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_beq___boxed(lean_object* v_00_u03b1_2120_, lean_object* v_00_u03b2_2121_, lean_object* v_inst_2122_, lean_object* v_inst_2123_, lean_object* v_inst_2124_, lean_object* v_m_u2081_2125_, lean_object* v_m_u2082_2126_){
_start:
{
uint8_t v_res_2127_; lean_object* v_r_2128_; 
v_res_2127_ = l_Std_DHashMap_Raw_Const_beq(v_00_u03b1_2120_, v_00_u03b2_2121_, v_inst_2122_, v_inst_2123_, v_inst_2124_, v_m_u2081_2125_, v_m_u2082_2126_);
v_r_2128_ = lean_box(v_res_2127_);
return v_r_2128_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_diff___redArg___lam__0(lean_object* v_inst_2129_, lean_object* v_inst_2130_, lean_object* v_m_u2082_2131_, uint8_t v___x_2132_, lean_object* v_k_2133_, lean_object* v_x_2134_){
_start:
{
uint8_t v___x_2135_; 
v___x_2135_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_2129_, v_inst_2130_, v_m_u2082_2131_, v_k_2133_);
if (v___x_2135_ == 0)
{
return v___x_2132_;
}
else
{
uint8_t v___x_2136_; 
v___x_2136_ = 0;
return v___x_2136_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_diff___redArg___lam__0___boxed(lean_object* v_inst_2137_, lean_object* v_inst_2138_, lean_object* v_m_u2082_2139_, lean_object* v___x_2140_, lean_object* v_k_2141_, lean_object* v_x_2142_){
_start:
{
uint8_t v___x_95__boxed_2143_; uint8_t v_res_2144_; lean_object* v_r_2145_; 
v___x_95__boxed_2143_ = lean_unbox(v___x_2140_);
v_res_2144_ = l_Std_DHashMap_Raw_diff___redArg___lam__0(v_inst_2137_, v_inst_2138_, v_m_u2082_2139_, v___x_95__boxed_2143_, v_k_2141_, v_x_2142_);
lean_dec(v_x_2142_);
lean_dec_ref(v_m_u2082_2139_);
v_r_2145_ = lean_box(v_res_2144_);
return v_r_2145_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_diff___redArg(lean_object* v_inst_2146_, lean_object* v_inst_2147_, lean_object* v_m_u2081_2148_, lean_object* v_m_u2082_2149_){
_start:
{
lean_object* v_size_2150_; lean_object* v_buckets_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; uint8_t v___x_2154_; 
v_size_2150_ = lean_ctor_get(v_m_u2081_2148_, 0);
v_buckets_2151_ = lean_ctor_get(v_m_u2081_2148_, 1);
v___x_2152_ = lean_unsigned_to_nat(0u);
v___x_2153_ = lean_array_get_size(v_buckets_2151_);
v___x_2154_ = lean_nat_dec_lt(v___x_2152_, v___x_2153_);
if (v___x_2154_ == 0)
{
lean_dec_ref(v_m_u2081_2148_);
lean_dec_ref(v_inst_2147_);
lean_dec_ref(v_inst_2146_);
return v_m_u2082_2149_;
}
else
{
lean_object* v_size_2155_; lean_object* v_buckets_2156_; lean_object* v___x_2157_; uint8_t v___x_2158_; 
v_size_2155_ = lean_ctor_get(v_m_u2082_2149_, 0);
v_buckets_2156_ = lean_ctor_get(v_m_u2082_2149_, 1);
v___x_2157_ = lean_array_get_size(v_buckets_2156_);
v___x_2158_ = lean_nat_dec_lt(v___x_2152_, v___x_2157_);
if (v___x_2158_ == 0)
{
lean_dec_ref(v_m_u2082_2149_);
lean_dec_ref(v_inst_2147_);
lean_dec_ref(v_inst_2146_);
return v_m_u2081_2148_;
}
else
{
uint8_t v___x_2159_; 
v___x_2159_ = lean_nat_dec_le(v_size_2150_, v_size_2155_);
if (v___x_2159_ == 0)
{
lean_object* v___f_2160_; lean_object* v___x_2161_; 
v___f_2160_ = ((lean_object*)(l_Std_DHashMap_Raw_union___redArg___closed__0));
v___x_2161_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_2160_, v_inst_2146_, v_inst_2147_, v_m_u2081_2148_, v_m_u2082_2149_);
return v___x_2161_;
}
else
{
lean_object* v___x_2162_; lean_object* v___f_2163_; lean_object* v___x_2164_; 
v___x_2162_ = lean_box(v___x_2159_);
v___f_2163_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_2163_, 0, v_inst_2146_);
lean_closure_set(v___f_2163_, 1, v_inst_2147_);
lean_closure_set(v___f_2163_, 2, v_m_u2082_2149_);
lean_closure_set(v___f_2163_, 3, v___x_2162_);
v___x_2164_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_2163_, v_m_u2081_2148_);
return v___x_2164_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_diff(lean_object* v_00_u03b1_2165_, lean_object* v_00_u03b2_2166_, lean_object* v_inst_2167_, lean_object* v_inst_2168_, lean_object* v_m_u2081_2169_, lean_object* v_m_u2082_2170_){
_start:
{
lean_object* v_size_2171_; lean_object* v_buckets_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; uint8_t v___x_2175_; 
v_size_2171_ = lean_ctor_get(v_m_u2081_2169_, 0);
v_buckets_2172_ = lean_ctor_get(v_m_u2081_2169_, 1);
v___x_2173_ = lean_unsigned_to_nat(0u);
v___x_2174_ = lean_array_get_size(v_buckets_2172_);
v___x_2175_ = lean_nat_dec_lt(v___x_2173_, v___x_2174_);
if (v___x_2175_ == 0)
{
lean_dec_ref(v_m_u2081_2169_);
lean_dec_ref(v_inst_2168_);
lean_dec_ref(v_inst_2167_);
return v_m_u2082_2170_;
}
else
{
lean_object* v_size_2176_; lean_object* v_buckets_2177_; lean_object* v___x_2178_; uint8_t v___x_2179_; 
v_size_2176_ = lean_ctor_get(v_m_u2082_2170_, 0);
v_buckets_2177_ = lean_ctor_get(v_m_u2082_2170_, 1);
v___x_2178_ = lean_array_get_size(v_buckets_2177_);
v___x_2179_ = lean_nat_dec_lt(v___x_2173_, v___x_2178_);
if (v___x_2179_ == 0)
{
lean_dec_ref(v_m_u2082_2170_);
lean_dec_ref(v_inst_2168_);
lean_dec_ref(v_inst_2167_);
return v_m_u2081_2169_;
}
else
{
uint8_t v___x_2180_; 
v___x_2180_ = lean_nat_dec_le(v_size_2171_, v_size_2176_);
if (v___x_2180_ == 0)
{
lean_object* v___f_2181_; lean_object* v___x_2182_; 
v___f_2181_ = ((lean_object*)(l_Std_DHashMap_Raw_union___redArg___closed__0));
v___x_2182_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_2181_, v_inst_2167_, v_inst_2168_, v_m_u2081_2169_, v_m_u2082_2170_);
return v___x_2182_;
}
else
{
lean_object* v___x_2183_; lean_object* v___f_2184_; lean_object* v___x_2185_; 
v___x_2183_ = lean_box(v___x_2180_);
v___f_2184_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_2184_, 0, v_inst_2167_);
lean_closure_set(v___f_2184_, 1, v_inst_2168_);
lean_closure_set(v___f_2184_, 2, v_m_u2082_2170_);
lean_closure_set(v___f_2184_, 3, v___x_2183_);
v___x_2185_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_2184_, v_m_u2081_2169_);
return v___x_2185_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instSDiffOfBEqOfHashable___redArg(lean_object* v_inst_2186_, lean_object* v_inst_2187_){
_start:
{
lean_object* v___x_2188_; 
v___x_2188_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_diff), 6, 4);
lean_closure_set(v___x_2188_, 0, lean_box(0));
lean_closure_set(v___x_2188_, 1, lean_box(0));
lean_closure_set(v___x_2188_, 2, v_inst_2186_);
lean_closure_set(v___x_2188_, 3, v_inst_2187_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instSDiffOfBEqOfHashable(lean_object* v_00_u03b1_2189_, lean_object* v_00_u03b2_2190_, lean_object* v_inst_2191_, lean_object* v_inst_2192_){
_start:
{
lean_object* v___x_2193_; 
v___x_2193_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_diff), 6, 4);
lean_closure_set(v___x_2193_, 0, lean_box(0));
lean_closure_set(v___x_2193_, 1, lean_box(0));
lean_closure_set(v___x_2193_, 2, v_inst_2191_);
lean_closure_set(v___x_2193_, 3, v_inst_2192_);
return v___x_2193_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_values___redArg___lam__0(lean_object* v_a_2194_, lean_object* v_b_2195_, lean_object* v_d_2196_){
_start:
{
lean_object* v___x_2197_; 
v___x_2197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2197_, 0, v_b_2195_);
lean_ctor_set(v___x_2197_, 1, v_d_2196_);
return v___x_2197_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_values___redArg___lam__0___boxed(lean_object* v_a_2198_, lean_object* v_b_2199_, lean_object* v_d_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l_Std_DHashMap_Raw_values___redArg___lam__0(v_a_2198_, v_b_2199_, v_d_2200_);
lean_dec(v_a_2198_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_values___redArg___lam__1(lean_object* v___x_2202_, lean_object* v___f_2203_, lean_object* v_l_2204_, lean_object* v_acc_2205_){
_start:
{
lean_object* v___x_2206_; 
v___x_2206_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_2202_, v___f_2203_, v_acc_2205_, v_l_2204_);
return v___x_2206_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_values___redArg(lean_object* v_m_2211_){
_start:
{
lean_object* v___x_2212_; lean_object* v_buckets_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; uint8_t v___x_2217_; 
v___x_2212_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_2213_ = lean_ctor_get(v_m_2211_, 1);
lean_inc_ref(v_buckets_2213_);
lean_dec_ref(v_m_2211_);
v___x_2214_ = lean_box(0);
v___x_2215_ = lean_array_get_size(v_buckets_2213_);
v___x_2216_ = lean_unsigned_to_nat(0u);
v___x_2217_ = lean_nat_dec_lt(v___x_2216_, v___x_2215_);
if (v___x_2217_ == 0)
{
lean_dec_ref(v_buckets_2213_);
return v___x_2214_;
}
else
{
lean_object* v___f_2218_; size_t v___x_2219_; size_t v___x_2220_; lean_object* v___x_2221_; 
v___f_2218_ = ((lean_object*)(l_Std_DHashMap_Raw_values___redArg___closed__1));
v___x_2219_ = lean_usize_of_nat(v___x_2215_);
v___x_2220_ = ((size_t)0ULL);
v___x_2221_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2212_, v___f_2218_, v_buckets_2213_, v___x_2219_, v___x_2220_, v___x_2214_);
return v___x_2221_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_values(lean_object* v_00_u03b1_2222_, lean_object* v_00_u03b2_2223_, lean_object* v_m_2224_){
_start:
{
lean_object* v___x_2225_; lean_object* v_buckets_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; uint8_t v___x_2230_; 
v___x_2225_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_2226_ = lean_ctor_get(v_m_2224_, 1);
lean_inc_ref(v_buckets_2226_);
lean_dec_ref(v_m_2224_);
v___x_2227_ = lean_box(0);
v___x_2228_ = lean_array_get_size(v_buckets_2226_);
v___x_2229_ = lean_unsigned_to_nat(0u);
v___x_2230_ = lean_nat_dec_lt(v___x_2229_, v___x_2228_);
if (v___x_2230_ == 0)
{
lean_dec_ref(v_buckets_2226_);
return v___x_2227_;
}
else
{
lean_object* v___f_2231_; size_t v___x_2232_; size_t v___x_2233_; lean_object* v___x_2234_; 
v___f_2231_ = ((lean_object*)(l_Std_DHashMap_Raw_values___redArg___closed__1));
v___x_2232_ = lean_usize_of_nat(v___x_2228_);
v___x_2233_ = ((size_t)0ULL);
v___x_2234_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2225_, v___f_2231_, v_buckets_2226_, v___x_2232_, v___x_2233_, v___x_2227_);
return v___x_2234_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_valuesArray___redArg___lam__0(lean_object* v_x1_2235_, lean_object* v_x2_2236_, lean_object* v_x3_2237_){
_start:
{
lean_object* v___x_2238_; 
v___x_2238_ = lean_array_push(v_x1_2235_, v_x3_2237_);
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_valuesArray___redArg___lam__0___boxed(lean_object* v_x1_2239_, lean_object* v_x2_2240_, lean_object* v_x3_2241_){
_start:
{
lean_object* v_res_2242_; 
v_res_2242_ = l_Std_DHashMap_Raw_valuesArray___redArg___lam__0(v_x1_2239_, v_x2_2240_, v_x3_2241_);
lean_dec(v_x2_2240_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_valuesArray___redArg(lean_object* v_m_2247_){
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
lean_object* v___f_2269_; size_t v___x_2270_; size_t v___x_2271_; lean_object* v___x_2272_; 
v___f_2269_ = ((lean_object*)(l_Std_DHashMap_Raw_valuesArray___redArg___closed__1));
v___x_2270_ = ((size_t)0ULL);
v___x_2271_ = lean_usize_of_nat(v___x_2267_);
v___x_2272_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2265_, v___f_2269_, v_buckets_2263_, v___x_2270_, v___x_2271_, v___x_2264_);
return v___x_2272_;
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
v___x_2371_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
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
v___x_2379_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
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
v___x_2560_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
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
v___x_2569_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
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
v___x_2576_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
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
v___x_2585_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
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
v___x_2592_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
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
v___x_2601_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
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
v___x_2608_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
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
v___x_2617_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
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
v___x_2624_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
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
v___x_2632_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
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
