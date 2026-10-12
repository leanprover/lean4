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
lean_object* l_Std_DHashMap_Raw_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_36_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Raw_instEmptyCollection___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_37_;
v_res_37_ = l_Std_DHashMap_Raw_instEmptyCollection___redArg();
stack->m_obj
 = v_res_37_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instEmptyCollection___redArg___boxed(lean_object* v___dummy_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Std_DHashMap_Raw_instEmptyCollection___redArg();
return v_res_39_;
}
}
static lean_object* _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__0(void){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Std_DHashMap_Raw_instEmptyCollection___redArg();
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instEmptyCollection(lean_object* v_00_u03b1_41_, lean_object* v_00_u03b2_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__0, &l_Std_DHashMap_Raw_instEmptyCollection___closed__0_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__0);
return v___x_43_;
}
}
lean_object* l_Std_DHashMap_Raw_instInhabited___redArg(){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_45_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Raw_instInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_46_;
v_res_46_ = l_Std_DHashMap_Raw_instInhabited___redArg();
stack->m_obj
 = v_res_46_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInhabited___redArg___boxed(lean_object* v___dummy_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Std_DHashMap_Raw_instInhabited___redArg();
return v_res_48_;
}
}
static lean_object* _init_l_Std_DHashMap_Raw_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Std_DHashMap_Raw_instInhabited___redArg();
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInhabited(lean_object* v_00_u03b1_50_, lean_object* v_00_u03b2_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = lean_obj_once(&l_Std_DHashMap_Raw_instInhabited___closed__0, &l_Std_DHashMap_Raw_instInhabited___closed__0_once, _init_l_Std_DHashMap_Raw_instInhabited___closed__0);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_markLinear___redArg(lean_object* v_m_53_){
_start:
{
lean_object* v_size_54_; lean_object* v_buckets_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_63_; 
v_size_54_ = lean_ctor_get(v_m_53_, 0);
v_buckets_55_ = lean_ctor_get(v_m_53_, 1);
v_isSharedCheck_63_ = !lean_is_exclusive(v_m_53_);
if (v_isSharedCheck_63_ == 0)
{
v___x_57_ = v_m_53_;
v_isShared_58_ = v_isSharedCheck_63_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_buckets_55_);
lean_inc(v_size_54_);
lean_dec(v_m_53_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_63_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v___x_59_; lean_object* v___x_61_; 
v___x_59_ = lean_array_mark_linear(v_buckets_55_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 1, v___x_59_);
v___x_61_ = v___x_57_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v_size_54_);
lean_ctor_set(v_reuseFailAlloc_62_, 1, v___x_59_);
v___x_61_ = v_reuseFailAlloc_62_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
return v___x_61_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_markLinear(lean_object* v_00_u03b1_64_, lean_object* v_00_u03b2_65_, lean_object* v_m_66_){
_start:
{
lean_object* v_size_67_; lean_object* v_buckets_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_76_; 
v_size_67_ = lean_ctor_get(v_m_66_, 0);
v_buckets_68_ = lean_ctor_get(v_m_66_, 1);
v_isSharedCheck_76_ = !lean_is_exclusive(v_m_66_);
if (v_isSharedCheck_76_ == 0)
{
v___x_70_ = v_m_66_;
v_isShared_71_ = v_isSharedCheck_76_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_buckets_68_);
lean_inc(v_size_67_);
lean_dec(v_m_66_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_76_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
lean_object* v___x_72_; lean_object* v___x_74_; 
v___x_72_ = lean_array_mark_linear(v_buckets_68_);
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 1, v___x_72_);
v___x_74_ = v___x_70_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v_size_67_);
lean_ctor_set(v_reuseFailAlloc_75_, 1, v___x_72_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
return v___x_74_;
}
}
}
}
static lean_object* _init_l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__6(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = ((lean_object*)(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__5));
v___x_118_ = l_String_toRawSubstring_x27(v___x_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1(lean_object* v_x_142_, lean_object* v_a_143_, lean_object* v_a_144_){
_start:
{
lean_object* v___x_145_; uint8_t v___x_146_; 
v___x_145_ = ((lean_object*)(l_Std_DHashMap_Raw_term___x7em___00__closed__4));
lean_inc(v_x_142_);
v___x_146_ = l_Lean_Syntax_isOfKind(v_x_142_, v___x_145_);
if (v___x_146_ == 0)
{
lean_object* v___x_147_; lean_object* v___x_148_; 
lean_dec(v_x_142_);
v___x_147_ = lean_box(1);
v___x_148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
lean_ctor_set(v___x_148_, 1, v_a_144_);
return v___x_148_;
}
else
{
lean_object* v_quotContext_149_; lean_object* v_currMacroScope_150_; lean_object* v_ref_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; uint8_t v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v_quotContext_149_ = lean_ctor_get(v_a_143_, 1);
v_currMacroScope_150_ = lean_ctor_get(v_a_143_, 2);
v_ref_151_ = lean_ctor_get(v_a_143_, 5);
v___x_152_ = lean_unsigned_to_nat(0u);
v___x_153_ = l_Lean_Syntax_getArg(v_x_142_, v___x_152_);
v___x_154_ = lean_unsigned_to_nat(2u);
v___x_155_ = l_Lean_Syntax_getArg(v_x_142_, v___x_154_);
lean_dec(v_x_142_);
v___x_156_ = 0;
v___x_157_ = l_Lean_SourceInfo_fromRef(v_ref_151_, v___x_156_);
v___x_158_ = ((lean_object*)(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4));
v___x_159_ = lean_obj_once(&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__6, &l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__6_once, _init_l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__6);
v___x_160_ = ((lean_object*)(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__8));
lean_inc(v_currMacroScope_150_);
lean_inc(v_quotContext_149_);
v___x_161_ = l_Lean_addMacroScope(v_quotContext_149_, v___x_160_, v_currMacroScope_150_);
v___x_162_ = ((lean_object*)(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__13));
lean_inc_n(v___x_157_, 2);
v___x_163_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_163_, 0, v___x_157_);
lean_ctor_set(v___x_163_, 1, v___x_159_);
lean_ctor_set(v___x_163_, 2, v___x_161_);
lean_ctor_set(v___x_163_, 3, v___x_162_);
v___x_164_ = ((lean_object*)(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__15));
v___x_165_ = l_Lean_Syntax_node2(v___x_157_, v___x_164_, v___x_153_, v___x_155_);
v___x_166_ = l_Lean_Syntax_node2(v___x_157_, v___x_158_, v___x_163_, v___x_165_);
v___x_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
lean_ctor_set(v___x_167_, 1, v_a_144_);
return v___x_167_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___boxed(lean_object* v_x_168_, lean_object* v_a_169_, lean_object* v_a_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1(v_x_168_, v_a_169_, v_a_170_);
lean_dec_ref(v_a_169_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1(lean_object* v_x_175_, lean_object* v_a_176_, lean_object* v_a_177_){
_start:
{
lean_object* v___x_178_; uint8_t v___x_179_; 
v___x_178_ = ((lean_object*)(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4));
lean_inc(v_x_175_);
v___x_179_ = l_Lean_Syntax_isOfKind(v_x_175_, v___x_178_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; lean_object* v___x_181_; 
lean_dec(v_x_175_);
v___x_180_ = lean_box(0);
v___x_181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set(v___x_181_, 1, v_a_177_);
return v___x_181_;
}
else
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_182_ = lean_unsigned_to_nat(0u);
v___x_183_ = l_Lean_Syntax_getArg(v_x_175_, v___x_182_);
v___x_184_ = ((lean_object*)(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___closed__1));
lean_inc(v___x_183_);
v___x_185_ = l_Lean_Syntax_isOfKind(v___x_183_, v___x_184_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; lean_object* v___x_187_; 
lean_dec(v___x_183_);
lean_dec(v_x_175_);
v___x_186_ = lean_box(0);
v___x_187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
lean_ctor_set(v___x_187_, 1, v_a_177_);
return v___x_187_;
}
else
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; uint8_t v___x_191_; 
v___x_188_ = lean_unsigned_to_nat(1u);
v___x_189_ = l_Lean_Syntax_getArg(v_x_175_, v___x_188_);
lean_dec(v_x_175_);
v___x_190_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_189_);
v___x_191_ = l_Lean_Syntax_matchesNull(v___x_189_, v___x_190_);
if (v___x_191_ == 0)
{
lean_object* v___x_192_; lean_object* v___x_193_; 
lean_dec(v___x_189_);
lean_dec(v___x_183_);
v___x_192_ = lean_box(0);
v___x_193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
lean_ctor_set(v___x_193_, 1, v_a_177_);
return v___x_193_;
}
else
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v_ref_196_; uint8_t v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_194_ = l_Lean_Syntax_getArg(v___x_189_, v___x_182_);
v___x_195_ = l_Lean_Syntax_getArg(v___x_189_, v___x_188_);
lean_dec(v___x_189_);
v_ref_196_ = l_Lean_replaceRef(v___x_183_, v_a_176_);
lean_dec(v___x_183_);
v___x_197_ = 0;
v___x_198_ = l_Lean_SourceInfo_fromRef(v_ref_196_, v___x_197_);
lean_dec(v_ref_196_);
v___x_199_ = ((lean_object*)(l_Std_DHashMap_Raw_term___x7em___00__closed__4));
v___x_200_ = ((lean_object*)(l_Std_DHashMap_Raw_term___x7em___00__closed__7));
lean_inc(v___x_198_);
v___x_201_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_198_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
v___x_202_ = l_Lean_Syntax_node3(v___x_198_, v___x_199_, v___x_194_, v___x_201_, v___x_195_);
v___x_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
lean_ctor_set(v___x_203_, 1, v_a_177_);
return v___x_203_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___boxed(lean_object* v_x_204_, lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1(v_x_204_, v_a_205_, v_a_206_);
lean_dec(v_a_205_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insert___redArg(lean_object* v_inst_208_, lean_object* v_inst_209_, lean_object* v_m_210_, lean_object* v_a_211_, lean_object* v_b_212_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insert(lean_object* v_00_u03b1_218_, lean_object* v_00_u03b2_219_, lean_object* v_inst_220_, lean_object* v_inst_221_, lean_object* v_m_222_, lean_object* v_a_223_, lean_object* v_b_224_){
_start:
{
lean_object* v_buckets_225_; lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v___x_228_; 
v_buckets_225_ = lean_ctor_get(v_m_222_, 1);
v___x_226_ = lean_unsigned_to_nat(0u);
v___x_227_ = lean_array_get_size(v_buckets_225_);
v___x_228_ = lean_nat_dec_lt(v___x_226_, v___x_227_);
if (v___x_228_ == 0)
{
lean_dec(v_b_224_);
lean_dec(v_a_223_);
lean_dec_ref(v_inst_221_);
lean_dec_ref(v_inst_220_);
return v_m_222_;
}
else
{
lean_object* v___x_229_; 
v___x_229_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_220_, v_inst_221_, v_m_222_, v_a_223_, v_b_224_);
return v___x_229_;
}
}
}
static lean_object* _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__0, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__0_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__0);
v___x_231_ = lean_array_get_size(v___x_230_);
return v___x_231_;
}
}
static uint8_t _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; uint8_t v___x_234_; 
v___x_232_ = lean_obj_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0);
v___x_233_ = lean_unsigned_to_nat(0u);
v___x_234_ = lean_nat_dec_lt(v___x_233_, v___x_232_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0(lean_object* v_inst_235_, lean_object* v_inst_236_, lean_object* v_x_237_){
_start:
{
lean_object* v_fst_238_; lean_object* v_snd_239_; lean_object* v___x_240_; uint8_t v___x_241_; 
v_fst_238_ = lean_ctor_get(v_x_237_, 0);
lean_inc(v_fst_238_);
v_snd_239_ = lean_ctor_get(v_x_237_, 1);
lean_inc(v_snd_239_);
lean_dec_ref(v_x_237_);
v___x_240_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
v___x_241_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_241_ == 0)
{
lean_dec(v_snd_239_);
lean_dec(v_fst_238_);
lean_dec_ref(v_inst_236_);
lean_dec_ref(v_inst_235_);
return v___x_240_;
}
else
{
lean_object* v___x_242_; 
v___x_242_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_235_, v_inst_236_, v___x_240_, v_fst_238_, v_snd_239_);
return v___x_242_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg(lean_object* v_inst_243_, lean_object* v_inst_244_){
_start:
{
lean_object* v___f_245_; 
v___f_245_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_245_, 0, v_inst_243_);
lean_closure_set(v___f_245_, 1, v_inst_244_);
return v___f_245_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable(lean_object* v_00_u03b1_246_, lean_object* v_00_u03b2_247_, lean_object* v_inst_248_, lean_object* v_inst_249_){
_start:
{
lean_object* v___f_250_; 
v___f_250_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_250_, 0, v_inst_248_);
lean_closure_set(v___f_250_, 1, v_inst_249_);
return v___f_250_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable___redArg___lam__0(lean_object* v_inst_251_, lean_object* v_inst_252_, lean_object* v_x_253_, lean_object* v_s_254_){
_start:
{
lean_object* v_fst_255_; lean_object* v_snd_256_; lean_object* v_buckets_257_; lean_object* v___x_258_; lean_object* v___x_259_; uint8_t v___x_260_; 
v_fst_255_ = lean_ctor_get(v_x_253_, 0);
lean_inc(v_fst_255_);
v_snd_256_ = lean_ctor_get(v_x_253_, 1);
lean_inc(v_snd_256_);
lean_dec_ref(v_x_253_);
v_buckets_257_ = lean_ctor_get(v_s_254_, 1);
v___x_258_ = lean_unsigned_to_nat(0u);
v___x_259_ = lean_array_get_size(v_buckets_257_);
v___x_260_ = lean_nat_dec_lt(v___x_258_, v___x_259_);
if (v___x_260_ == 0)
{
lean_dec(v_snd_256_);
lean_dec(v_fst_255_);
lean_dec_ref(v_inst_252_);
lean_dec_ref(v_inst_251_);
return v_s_254_;
}
else
{
lean_object* v___x_261_; 
v___x_261_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_251_, v_inst_252_, v_s_254_, v_fst_255_, v_snd_256_);
return v___x_261_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable___redArg(lean_object* v_inst_262_, lean_object* v_inst_263_){
_start:
{
lean_object* v___f_264_; 
v___f_264_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_264_, 0, v_inst_262_);
lean_closure_set(v___f_264_, 1, v_inst_263_);
return v___f_264_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable(lean_object* v_00_u03b1_265_, lean_object* v_00_u03b2_266_, lean_object* v_inst_267_, lean_object* v_inst_268_){
_start:
{
lean_object* v___f_269_; 
v___f_269_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_269_, 0, v_inst_267_);
lean_closure_set(v___f_269_, 1, v_inst_268_);
return v___f_269_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insertIfNew___redArg(lean_object* v_inst_270_, lean_object* v_inst_271_, lean_object* v_m_272_, lean_object* v_a_273_, lean_object* v_b_274_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insertIfNew(lean_object* v_00_u03b1_280_, lean_object* v_00_u03b2_281_, lean_object* v_inst_282_, lean_object* v_inst_283_, lean_object* v_m_284_, lean_object* v_a_285_, lean_object* v_b_286_){
_start:
{
lean_object* v_buckets_287_; lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; 
v_buckets_287_ = lean_ctor_get(v_m_284_, 1);
v___x_288_ = lean_unsigned_to_nat(0u);
v___x_289_ = lean_array_get_size(v_buckets_287_);
v___x_290_ = lean_nat_dec_lt(v___x_288_, v___x_289_);
if (v___x_290_ == 0)
{
lean_dec(v_b_286_);
lean_dec(v_a_285_);
lean_dec_ref(v_inst_283_);
lean_dec_ref(v_inst_282_);
return v_m_284_;
}
else
{
lean_object* v___x_291_; 
v___x_291_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_282_, v_inst_283_, v_m_284_, v_a_285_, v_b_286_);
return v___x_291_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_containsThenInsert___redArg(lean_object* v_inst_292_, lean_object* v_inst_293_, lean_object* v_m_294_, lean_object* v_a_295_, lean_object* v_b_296_){
_start:
{
lean_object* v_size_297_; lean_object* v_buckets_298_; lean_object* v___x_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
v_size_297_ = lean_ctor_get(v_m_294_, 0);
v_buckets_298_ = lean_ctor_get(v_m_294_, 1);
v___x_299_ = lean_unsigned_to_nat(0u);
v___x_300_ = lean_array_get_size(v_buckets_298_);
v___x_301_ = lean_nat_dec_lt(v___x_299_, v___x_300_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; lean_object* v___x_303_; 
lean_dec(v_b_296_);
lean_dec(v_a_295_);
lean_dec_ref(v_inst_293_);
lean_dec_ref(v_inst_292_);
v___x_302_ = lean_box(v___x_301_);
v___x_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
lean_ctor_set(v___x_303_, 1, v_m_294_);
return v___x_303_;
}
else
{
lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_353_; 
lean_inc_ref(v_buckets_298_);
lean_inc(v_size_297_);
v_isSharedCheck_353_ = !lean_is_exclusive(v_m_294_);
if (v_isSharedCheck_353_ == 0)
{
lean_object* v_unused_354_; lean_object* v_unused_355_; 
v_unused_354_ = lean_ctor_get(v_m_294_, 1);
lean_dec(v_unused_354_);
v_unused_355_ = lean_ctor_get(v_m_294_, 0);
lean_dec(v_unused_355_);
v___x_305_ = v_m_294_;
v_isShared_306_ = v_isSharedCheck_353_;
goto v_resetjp_304_;
}
else
{
lean_dec(v_m_294_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_353_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_307_; uint64_t v___x_308_; uint64_t v___x_309_; uint64_t v___x_310_; uint64_t v___x_311_; uint64_t v_fold_312_; uint64_t v___x_313_; uint64_t v___x_314_; uint64_t v___x_315_; size_t v___x_316_; size_t v___x_317_; size_t v___x_318_; size_t v___x_319_; size_t v___x_320_; lean_object* v_bkt_321_; uint8_t v___x_322_; 
lean_inc_ref(v_inst_293_);
lean_inc_n(v_a_295_, 2);
v___x_307_ = lean_apply_1(v_inst_293_, v_a_295_);
v___x_308_ = 32ULL;
v___x_309_ = lean_unbox_uint64(v___x_307_);
v___x_310_ = lean_uint64_shift_right(v___x_309_, v___x_308_);
v___x_311_ = lean_unbox_uint64(v___x_307_);
lean_dec_ref(v___x_307_);
v_fold_312_ = lean_uint64_xor(v___x_311_, v___x_310_);
v___x_313_ = 16ULL;
v___x_314_ = lean_uint64_shift_right(v_fold_312_, v___x_313_);
v___x_315_ = lean_uint64_xor(v_fold_312_, v___x_314_);
v___x_316_ = lean_uint64_to_usize(v___x_315_);
v___x_317_ = lean_usize_of_nat(v___x_300_);
v___x_318_ = ((size_t)1ULL);
v___x_319_ = lean_usize_sub(v___x_317_, v___x_318_);
v___x_320_ = lean_usize_land(v___x_316_, v___x_319_);
v_bkt_321_ = lean_array_uget_borrowed(v_buckets_298_, v___x_320_);
lean_inc(v_bkt_321_);
lean_inc_ref(v_inst_292_);
v___x_322_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_292_, v_a_295_, v_bkt_321_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; lean_object* v_size_x27_324_; lean_object* v___x_325_; lean_object* v_buckets_x27_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; uint8_t v___x_332_; 
lean_dec_ref(v_inst_292_);
v___x_323_ = lean_unsigned_to_nat(1u);
v_size_x27_324_ = lean_nat_add(v_size_297_, v___x_323_);
lean_dec(v_size_297_);
lean_inc(v_bkt_321_);
v___x_325_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_325_, 0, v_a_295_);
lean_ctor_set(v___x_325_, 1, v_b_296_);
lean_ctor_set(v___x_325_, 2, v_bkt_321_);
v_buckets_x27_326_ = lean_array_uset(v_buckets_298_, v___x_320_, v___x_325_);
v___x_327_ = lean_unsigned_to_nat(4u);
v___x_328_ = lean_nat_mul(v_size_x27_324_, v___x_327_);
v___x_329_ = lean_unsigned_to_nat(3u);
v___x_330_ = lean_nat_div(v___x_328_, v___x_329_);
lean_dec(v___x_328_);
v___x_331_ = lean_array_get_size(v_buckets_x27_326_);
v___x_332_ = lean_nat_dec_le(v___x_330_, v___x_331_);
lean_dec(v___x_330_);
if (v___x_332_ == 0)
{
lean_object* v_val_333_; lean_object* v___x_335_; 
v_val_333_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_293_, v_buckets_x27_326_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 1, v_val_333_);
lean_ctor_set(v___x_305_, 0, v_size_x27_324_);
v___x_335_ = v___x_305_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_size_x27_324_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v_val_333_);
v___x_335_ = v_reuseFailAlloc_338_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = lean_box(v___x_322_);
v___x_337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
lean_ctor_set(v___x_337_, 1, v___x_335_);
return v___x_337_;
}
}
else
{
lean_object* v___x_340_; 
lean_dec_ref(v_inst_293_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 1, v_buckets_x27_326_);
lean_ctor_set(v___x_305_, 0, v_size_x27_324_);
v___x_340_ = v___x_305_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_size_x27_324_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v_buckets_x27_326_);
v___x_340_ = v_reuseFailAlloc_343_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = lean_box(v___x_322_);
v___x_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
lean_ctor_set(v___x_342_, 1, v___x_340_);
return v___x_342_;
}
}
}
else
{
lean_object* v___x_344_; lean_object* v_buckets_x27_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_349_; 
lean_inc(v_bkt_321_);
lean_dec_ref(v_inst_293_);
v___x_344_ = lean_box(0);
v_buckets_x27_345_ = lean_array_uset(v_buckets_298_, v___x_320_, v___x_344_);
v___x_346_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_inst_292_, v_a_295_, v_b_296_, v_bkt_321_);
v___x_347_ = lean_array_uset(v_buckets_x27_345_, v___x_320_, v___x_346_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 1, v___x_347_);
v___x_349_ = v___x_305_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_size_297_);
lean_ctor_set(v_reuseFailAlloc_352_, 1, v___x_347_);
v___x_349_ = v_reuseFailAlloc_352_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = lean_box(v___x_322_);
v___x_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
lean_ctor_set(v___x_351_, 1, v___x_349_);
return v___x_351_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_containsThenInsert(lean_object* v_00_u03b1_356_, lean_object* v_00_u03b2_357_, lean_object* v_inst_358_, lean_object* v_inst_359_, lean_object* v_m_360_, lean_object* v_a_361_, lean_object* v_b_362_){
_start:
{
lean_object* v_size_363_; lean_object* v_buckets_364_; lean_object* v___x_365_; lean_object* v___x_366_; uint8_t v___x_367_; 
v_size_363_ = lean_ctor_get(v_m_360_, 0);
v_buckets_364_ = lean_ctor_get(v_m_360_, 1);
v___x_365_ = lean_unsigned_to_nat(0u);
v___x_366_ = lean_array_get_size(v_buckets_364_);
v___x_367_ = lean_nat_dec_lt(v___x_365_, v___x_366_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; lean_object* v___x_369_; 
lean_dec(v_b_362_);
lean_dec(v_a_361_);
lean_dec_ref(v_inst_359_);
lean_dec_ref(v_inst_358_);
v___x_368_ = lean_box(v___x_367_);
v___x_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_369_, 0, v___x_368_);
lean_ctor_set(v___x_369_, 1, v_m_360_);
return v___x_369_;
}
else
{
lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_419_; 
lean_inc_ref(v_buckets_364_);
lean_inc(v_size_363_);
v_isSharedCheck_419_ = !lean_is_exclusive(v_m_360_);
if (v_isSharedCheck_419_ == 0)
{
lean_object* v_unused_420_; lean_object* v_unused_421_; 
v_unused_420_ = lean_ctor_get(v_m_360_, 1);
lean_dec(v_unused_420_);
v_unused_421_ = lean_ctor_get(v_m_360_, 0);
lean_dec(v_unused_421_);
v___x_371_ = v_m_360_;
v_isShared_372_ = v_isSharedCheck_419_;
goto v_resetjp_370_;
}
else
{
lean_dec(v_m_360_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_419_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_373_; uint64_t v___x_374_; uint64_t v___x_375_; uint64_t v___x_376_; uint64_t v___x_377_; uint64_t v_fold_378_; uint64_t v___x_379_; uint64_t v___x_380_; uint64_t v___x_381_; size_t v___x_382_; size_t v___x_383_; size_t v___x_384_; size_t v___x_385_; size_t v___x_386_; lean_object* v_bkt_387_; uint8_t v___x_388_; 
lean_inc_ref(v_inst_359_);
lean_inc_n(v_a_361_, 2);
v___x_373_ = lean_apply_1(v_inst_359_, v_a_361_);
v___x_374_ = 32ULL;
v___x_375_ = lean_unbox_uint64(v___x_373_);
v___x_376_ = lean_uint64_shift_right(v___x_375_, v___x_374_);
v___x_377_ = lean_unbox_uint64(v___x_373_);
lean_dec_ref(v___x_373_);
v_fold_378_ = lean_uint64_xor(v___x_377_, v___x_376_);
v___x_379_ = 16ULL;
v___x_380_ = lean_uint64_shift_right(v_fold_378_, v___x_379_);
v___x_381_ = lean_uint64_xor(v_fold_378_, v___x_380_);
v___x_382_ = lean_uint64_to_usize(v___x_381_);
v___x_383_ = lean_usize_of_nat(v___x_366_);
v___x_384_ = ((size_t)1ULL);
v___x_385_ = lean_usize_sub(v___x_383_, v___x_384_);
v___x_386_ = lean_usize_land(v___x_382_, v___x_385_);
v_bkt_387_ = lean_array_uget_borrowed(v_buckets_364_, v___x_386_);
lean_inc(v_bkt_387_);
lean_inc_ref(v_inst_358_);
v___x_388_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_358_, v_a_361_, v_bkt_387_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; lean_object* v_size_x27_390_; lean_object* v___x_391_; lean_object* v_buckets_x27_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; uint8_t v___x_398_; 
lean_dec_ref(v_inst_358_);
v___x_389_ = lean_unsigned_to_nat(1u);
v_size_x27_390_ = lean_nat_add(v_size_363_, v___x_389_);
lean_dec(v_size_363_);
lean_inc(v_bkt_387_);
v___x_391_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_391_, 0, v_a_361_);
lean_ctor_set(v___x_391_, 1, v_b_362_);
lean_ctor_set(v___x_391_, 2, v_bkt_387_);
v_buckets_x27_392_ = lean_array_uset(v_buckets_364_, v___x_386_, v___x_391_);
v___x_393_ = lean_unsigned_to_nat(4u);
v___x_394_ = lean_nat_mul(v_size_x27_390_, v___x_393_);
v___x_395_ = lean_unsigned_to_nat(3u);
v___x_396_ = lean_nat_div(v___x_394_, v___x_395_);
lean_dec(v___x_394_);
v___x_397_ = lean_array_get_size(v_buckets_x27_392_);
v___x_398_ = lean_nat_dec_le(v___x_396_, v___x_397_);
lean_dec(v___x_396_);
if (v___x_398_ == 0)
{
lean_object* v_val_399_; lean_object* v___x_401_; 
v_val_399_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_359_, v_buckets_x27_392_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 1, v_val_399_);
lean_ctor_set(v___x_371_, 0, v_size_x27_390_);
v___x_401_ = v___x_371_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_size_x27_390_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v_val_399_);
v___x_401_ = v_reuseFailAlloc_404_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = lean_box(v___x_388_);
v___x_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
lean_ctor_set(v___x_403_, 1, v___x_401_);
return v___x_403_;
}
}
else
{
lean_object* v___x_406_; 
lean_dec_ref(v_inst_359_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 1, v_buckets_x27_392_);
lean_ctor_set(v___x_371_, 0, v_size_x27_390_);
v___x_406_ = v___x_371_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_size_x27_390_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v_buckets_x27_392_);
v___x_406_ = v_reuseFailAlloc_409_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = lean_box(v___x_388_);
v___x_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
lean_ctor_set(v___x_408_, 1, v___x_406_);
return v___x_408_;
}
}
}
else
{
lean_object* v___x_410_; lean_object* v_buckets_x27_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_415_; 
lean_inc(v_bkt_387_);
lean_dec_ref(v_inst_359_);
v___x_410_ = lean_box(0);
v_buckets_x27_411_ = lean_array_uset(v_buckets_364_, v___x_386_, v___x_410_);
v___x_412_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_inst_358_, v_a_361_, v_b_362_, v_bkt_387_);
v___x_413_ = lean_array_uset(v_buckets_x27_411_, v___x_386_, v___x_412_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 1, v___x_413_);
v___x_415_ = v___x_371_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_size_363_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v___x_413_);
v___x_415_ = v_reuseFailAlloc_418_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = lean_box(v___x_388_);
v___x_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
lean_ctor_set(v___x_417_, 1, v___x_415_);
return v___x_417_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getThenInsertIfNew_x3f___redArg(lean_object* v_inst_422_, lean_object* v_inst_423_, lean_object* v_m_424_, lean_object* v_a_425_, lean_object* v_b_426_){
_start:
{
lean_object* v_size_427_; lean_object* v_buckets_428_; lean_object* v___x_429_; lean_object* v___x_430_; uint8_t v___x_431_; 
v_size_427_ = lean_ctor_get(v_m_424_, 0);
v_buckets_428_ = lean_ctor_get(v_m_424_, 1);
v___x_429_ = lean_unsigned_to_nat(0u);
v___x_430_ = lean_array_get_size(v_buckets_428_);
v___x_431_ = lean_nat_dec_lt(v___x_429_, v___x_430_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; lean_object* v___x_433_; 
lean_dec(v_b_426_);
lean_dec(v_a_425_);
lean_dec_ref(v_inst_423_);
lean_dec_ref(v_inst_422_);
v___x_432_ = lean_box(0);
v___x_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
lean_ctor_set(v___x_433_, 1, v_m_424_);
return v___x_433_;
}
else
{
lean_object* v___x_434_; uint64_t v___x_435_; uint64_t v___x_436_; uint64_t v___x_437_; uint64_t v___x_438_; uint64_t v_fold_439_; uint64_t v___x_440_; uint64_t v___x_441_; uint64_t v___x_442_; size_t v___x_443_; size_t v___x_444_; size_t v___x_445_; size_t v___x_446_; size_t v___x_447_; lean_object* v_bkt_448_; lean_object* v___x_449_; 
lean_inc_ref(v_inst_423_);
lean_inc_n(v_a_425_, 2);
v___x_434_ = lean_apply_1(v_inst_423_, v_a_425_);
v___x_435_ = 32ULL;
v___x_436_ = lean_unbox_uint64(v___x_434_);
v___x_437_ = lean_uint64_shift_right(v___x_436_, v___x_435_);
v___x_438_ = lean_unbox_uint64(v___x_434_);
lean_dec_ref(v___x_434_);
v_fold_439_ = lean_uint64_xor(v___x_438_, v___x_437_);
v___x_440_ = 16ULL;
v___x_441_ = lean_uint64_shift_right(v_fold_439_, v___x_440_);
v___x_442_ = lean_uint64_xor(v_fold_439_, v___x_441_);
v___x_443_ = lean_uint64_to_usize(v___x_442_);
v___x_444_ = lean_usize_of_nat(v___x_430_);
v___x_445_ = ((size_t)1ULL);
v___x_446_ = lean_usize_sub(v___x_444_, v___x_445_);
v___x_447_ = lean_usize_land(v___x_443_, v___x_446_);
v_bkt_448_ = lean_array_uget_borrowed(v_buckets_428_, v___x_447_);
lean_inc(v_bkt_448_);
v___x_449_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(v_inst_422_, v_a_425_, v_bkt_448_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_472_; 
lean_inc_ref(v_buckets_428_);
lean_inc(v_size_427_);
v_isSharedCheck_472_ = !lean_is_exclusive(v_m_424_);
if (v_isSharedCheck_472_ == 0)
{
lean_object* v_unused_473_; lean_object* v_unused_474_; 
v_unused_473_ = lean_ctor_get(v_m_424_, 1);
lean_dec(v_unused_473_);
v_unused_474_ = lean_ctor_get(v_m_424_, 0);
lean_dec(v_unused_474_);
v___x_451_ = v_m_424_;
v_isShared_452_ = v_isSharedCheck_472_;
goto v_resetjp_450_;
}
else
{
lean_dec(v_m_424_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_472_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_453_; lean_object* v_size_x27_454_; lean_object* v___x_455_; lean_object* v_buckets_x27_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_453_ = lean_unsigned_to_nat(1u);
v_size_x27_454_ = lean_nat_add(v_size_427_, v___x_453_);
lean_dec(v_size_427_);
lean_inc(v_bkt_448_);
v___x_455_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_455_, 0, v_a_425_);
lean_ctor_set(v___x_455_, 1, v_b_426_);
lean_ctor_set(v___x_455_, 2, v_bkt_448_);
v_buckets_x27_456_ = lean_array_uset(v_buckets_428_, v___x_447_, v___x_455_);
v___x_457_ = lean_unsigned_to_nat(4u);
v___x_458_ = lean_nat_mul(v_size_x27_454_, v___x_457_);
v___x_459_ = lean_unsigned_to_nat(3u);
v___x_460_ = lean_nat_div(v___x_458_, v___x_459_);
lean_dec(v___x_458_);
v___x_461_ = lean_array_get_size(v_buckets_x27_456_);
v___x_462_ = lean_nat_dec_le(v___x_460_, v___x_461_);
lean_dec(v___x_460_);
if (v___x_462_ == 0)
{
lean_object* v_val_463_; lean_object* v___x_465_; 
v_val_463_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_423_, v_buckets_x27_456_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 1, v_val_463_);
lean_ctor_set(v___x_451_, 0, v_size_x27_454_);
v___x_465_ = v___x_451_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_size_x27_454_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v_val_463_);
v___x_465_ = v_reuseFailAlloc_467_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
lean_object* v___x_466_; 
v___x_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_466_, 0, v___x_449_);
lean_ctor_set(v___x_466_, 1, v___x_465_);
return v___x_466_;
}
}
else
{
lean_object* v___x_469_; 
lean_dec_ref(v_inst_423_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 1, v_buckets_x27_456_);
lean_ctor_set(v___x_451_, 0, v_size_x27_454_);
v___x_469_ = v___x_451_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_size_x27_454_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v_buckets_x27_456_);
v___x_469_ = v_reuseFailAlloc_471_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v___x_470_; 
v___x_470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_470_, 0, v___x_449_);
lean_ctor_set(v___x_470_, 1, v___x_469_);
return v___x_470_;
}
}
}
}
else
{
lean_object* v___x_475_; 
lean_dec(v_b_426_);
lean_dec(v_a_425_);
lean_dec_ref(v_inst_423_);
v___x_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_475_, 0, v___x_449_);
lean_ctor_set(v___x_475_, 1, v_m_424_);
return v___x_475_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_476_, lean_object* v_00_u03b2_477_, lean_object* v_inst_478_, lean_object* v_inst_479_, lean_object* v_inst_480_, lean_object* v_m_481_, lean_object* v_a_482_, lean_object* v_b_483_){
_start:
{
lean_object* v_size_484_; lean_object* v_buckets_485_; lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v_size_484_ = lean_ctor_get(v_m_481_, 0);
v_buckets_485_ = lean_ctor_get(v_m_481_, 1);
v___x_486_ = lean_unsigned_to_nat(0u);
v___x_487_ = lean_array_get_size(v_buckets_485_);
v___x_488_ = lean_nat_dec_lt(v___x_486_, v___x_487_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; lean_object* v___x_490_; 
lean_dec(v_b_483_);
lean_dec(v_a_482_);
lean_dec_ref(v_inst_479_);
lean_dec_ref(v_inst_478_);
v___x_489_ = lean_box(0);
v___x_490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
lean_ctor_set(v___x_490_, 1, v_m_481_);
return v___x_490_;
}
else
{
lean_object* v___x_491_; uint64_t v___x_492_; uint64_t v___x_493_; uint64_t v___x_494_; uint64_t v___x_495_; uint64_t v_fold_496_; uint64_t v___x_497_; uint64_t v___x_498_; uint64_t v___x_499_; size_t v___x_500_; size_t v___x_501_; size_t v___x_502_; size_t v___x_503_; size_t v___x_504_; lean_object* v_bkt_505_; lean_object* v___x_506_; 
lean_inc_ref(v_inst_479_);
lean_inc_n(v_a_482_, 2);
v___x_491_ = lean_apply_1(v_inst_479_, v_a_482_);
v___x_492_ = 32ULL;
v___x_493_ = lean_unbox_uint64(v___x_491_);
v___x_494_ = lean_uint64_shift_right(v___x_493_, v___x_492_);
v___x_495_ = lean_unbox_uint64(v___x_491_);
lean_dec_ref(v___x_491_);
v_fold_496_ = lean_uint64_xor(v___x_495_, v___x_494_);
v___x_497_ = 16ULL;
v___x_498_ = lean_uint64_shift_right(v_fold_496_, v___x_497_);
v___x_499_ = lean_uint64_xor(v_fold_496_, v___x_498_);
v___x_500_ = lean_uint64_to_usize(v___x_499_);
v___x_501_ = lean_usize_of_nat(v___x_487_);
v___x_502_ = ((size_t)1ULL);
v___x_503_ = lean_usize_sub(v___x_501_, v___x_502_);
v___x_504_ = lean_usize_land(v___x_500_, v___x_503_);
v_bkt_505_ = lean_array_uget_borrowed(v_buckets_485_, v___x_504_);
lean_inc(v_bkt_505_);
v___x_506_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(v_inst_478_, v_a_482_, v_bkt_505_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_529_; 
lean_inc_ref(v_buckets_485_);
lean_inc(v_size_484_);
v_isSharedCheck_529_ = !lean_is_exclusive(v_m_481_);
if (v_isSharedCheck_529_ == 0)
{
lean_object* v_unused_530_; lean_object* v_unused_531_; 
v_unused_530_ = lean_ctor_get(v_m_481_, 1);
lean_dec(v_unused_530_);
v_unused_531_ = lean_ctor_get(v_m_481_, 0);
lean_dec(v_unused_531_);
v___x_508_ = v_m_481_;
v_isShared_509_ = v_isSharedCheck_529_;
goto v_resetjp_507_;
}
else
{
lean_dec(v_m_481_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_529_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v_size_x27_511_; lean_object* v___x_512_; lean_object* v_buckets_x27_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_510_ = lean_unsigned_to_nat(1u);
v_size_x27_511_ = lean_nat_add(v_size_484_, v___x_510_);
lean_dec(v_size_484_);
lean_inc(v_bkt_505_);
v___x_512_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_512_, 0, v_a_482_);
lean_ctor_set(v___x_512_, 1, v_b_483_);
lean_ctor_set(v___x_512_, 2, v_bkt_505_);
v_buckets_x27_513_ = lean_array_uset(v_buckets_485_, v___x_504_, v___x_512_);
v___x_514_ = lean_unsigned_to_nat(4u);
v___x_515_ = lean_nat_mul(v_size_x27_511_, v___x_514_);
v___x_516_ = lean_unsigned_to_nat(3u);
v___x_517_ = lean_nat_div(v___x_515_, v___x_516_);
lean_dec(v___x_515_);
v___x_518_ = lean_array_get_size(v_buckets_x27_513_);
v___x_519_ = lean_nat_dec_le(v___x_517_, v___x_518_);
lean_dec(v___x_517_);
if (v___x_519_ == 0)
{
lean_object* v_val_520_; lean_object* v___x_522_; 
v_val_520_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_479_, v_buckets_x27_513_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 1, v_val_520_);
lean_ctor_set(v___x_508_, 0, v_size_x27_511_);
v___x_522_ = v___x_508_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_size_x27_511_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v_val_520_);
v___x_522_ = v_reuseFailAlloc_524_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_523_; 
v___x_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_506_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
return v___x_523_;
}
}
else
{
lean_object* v___x_526_; 
lean_dec_ref(v_inst_479_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 1, v_buckets_x27_513_);
lean_ctor_set(v___x_508_, 0, v_size_x27_511_);
v___x_526_ = v___x_508_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_size_x27_511_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v_buckets_x27_513_);
v___x_526_ = v_reuseFailAlloc_528_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
lean_object* v___x_527_; 
v___x_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_506_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
return v___x_527_;
}
}
}
}
else
{
lean_object* v___x_532_; 
lean_dec(v_b_483_);
lean_dec(v_a_482_);
lean_dec_ref(v_inst_479_);
v___x_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_506_);
lean_ctor_set(v___x_532_, 1, v_m_481_);
return v___x_532_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_containsThenInsertIfNew___redArg(lean_object* v_inst_533_, lean_object* v_inst_534_, lean_object* v_m_535_, lean_object* v_a_536_, lean_object* v_b_537_){
_start:
{
lean_object* v_size_538_; lean_object* v_buckets_539_; lean_object* v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; 
v_size_538_ = lean_ctor_get(v_m_535_, 0);
v_buckets_539_ = lean_ctor_get(v_m_535_, 1);
v___x_540_ = lean_unsigned_to_nat(0u);
v___x_541_ = lean_array_get_size(v_buckets_539_);
v___x_542_ = lean_nat_dec_lt(v___x_540_, v___x_541_);
if (v___x_542_ == 0)
{
lean_object* v___x_543_; lean_object* v___x_544_; 
lean_dec(v_b_537_);
lean_dec(v_a_536_);
lean_dec_ref(v_inst_534_);
lean_dec_ref(v_inst_533_);
v___x_543_ = lean_box(v___x_542_);
v___x_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
lean_ctor_set(v___x_544_, 1, v_m_535_);
return v___x_544_;
}
else
{
lean_object* v___x_545_; uint64_t v___x_546_; uint64_t v___x_547_; uint64_t v___x_548_; uint64_t v___x_549_; uint64_t v_fold_550_; uint64_t v___x_551_; uint64_t v___x_552_; uint64_t v___x_553_; size_t v___x_554_; size_t v___x_555_; size_t v___x_556_; size_t v___x_557_; size_t v___x_558_; lean_object* v_bkt_559_; uint8_t v___x_560_; 
lean_inc_ref(v_inst_534_);
lean_inc_n(v_a_536_, 2);
v___x_545_ = lean_apply_1(v_inst_534_, v_a_536_);
v___x_546_ = 32ULL;
v___x_547_ = lean_unbox_uint64(v___x_545_);
v___x_548_ = lean_uint64_shift_right(v___x_547_, v___x_546_);
v___x_549_ = lean_unbox_uint64(v___x_545_);
lean_dec_ref(v___x_545_);
v_fold_550_ = lean_uint64_xor(v___x_549_, v___x_548_);
v___x_551_ = 16ULL;
v___x_552_ = lean_uint64_shift_right(v_fold_550_, v___x_551_);
v___x_553_ = lean_uint64_xor(v_fold_550_, v___x_552_);
v___x_554_ = lean_uint64_to_usize(v___x_553_);
v___x_555_ = lean_usize_of_nat(v___x_541_);
v___x_556_ = ((size_t)1ULL);
v___x_557_ = lean_usize_sub(v___x_555_, v___x_556_);
v___x_558_ = lean_usize_land(v___x_554_, v___x_557_);
v_bkt_559_ = lean_array_uget_borrowed(v_buckets_539_, v___x_558_);
lean_inc(v_bkt_559_);
v___x_560_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_533_, v_a_536_, v_bkt_559_);
if (v___x_560_ == 0)
{
lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_585_; 
lean_inc_ref(v_buckets_539_);
lean_inc(v_size_538_);
v_isSharedCheck_585_ = !lean_is_exclusive(v_m_535_);
if (v_isSharedCheck_585_ == 0)
{
lean_object* v_unused_586_; lean_object* v_unused_587_; 
v_unused_586_ = lean_ctor_get(v_m_535_, 1);
lean_dec(v_unused_586_);
v_unused_587_ = lean_ctor_get(v_m_535_, 0);
lean_dec(v_unused_587_);
v___x_562_ = v_m_535_;
v_isShared_563_ = v_isSharedCheck_585_;
goto v_resetjp_561_;
}
else
{
lean_dec(v_m_535_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_585_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_564_; lean_object* v_size_x27_565_; lean_object* v___x_566_; lean_object* v_buckets_x27_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; uint8_t v___x_573_; 
v___x_564_ = lean_unsigned_to_nat(1u);
v_size_x27_565_ = lean_nat_add(v_size_538_, v___x_564_);
lean_dec(v_size_538_);
lean_inc(v_bkt_559_);
v___x_566_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_566_, 0, v_a_536_);
lean_ctor_set(v___x_566_, 1, v_b_537_);
lean_ctor_set(v___x_566_, 2, v_bkt_559_);
v_buckets_x27_567_ = lean_array_uset(v_buckets_539_, v___x_558_, v___x_566_);
v___x_568_ = lean_unsigned_to_nat(4u);
v___x_569_ = lean_nat_mul(v_size_x27_565_, v___x_568_);
v___x_570_ = lean_unsigned_to_nat(3u);
v___x_571_ = lean_nat_div(v___x_569_, v___x_570_);
lean_dec(v___x_569_);
v___x_572_ = lean_array_get_size(v_buckets_x27_567_);
v___x_573_ = lean_nat_dec_le(v___x_571_, v___x_572_);
lean_dec(v___x_571_);
if (v___x_573_ == 0)
{
lean_object* v_val_574_; lean_object* v___x_576_; 
v_val_574_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_534_, v_buckets_x27_567_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 1, v_val_574_);
lean_ctor_set(v___x_562_, 0, v_size_x27_565_);
v___x_576_ = v___x_562_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_size_x27_565_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v_val_574_);
v___x_576_ = v_reuseFailAlloc_579_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = lean_box(v___x_560_);
v___x_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
lean_ctor_set(v___x_578_, 1, v___x_576_);
return v___x_578_;
}
}
else
{
lean_object* v___x_581_; 
lean_dec_ref(v_inst_534_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 1, v_buckets_x27_567_);
lean_ctor_set(v___x_562_, 0, v_size_x27_565_);
v___x_581_ = v___x_562_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_size_x27_565_);
lean_ctor_set(v_reuseFailAlloc_584_, 1, v_buckets_x27_567_);
v___x_581_ = v_reuseFailAlloc_584_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = lean_box(v___x_560_);
v___x_583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
lean_ctor_set(v___x_583_, 1, v___x_581_);
return v___x_583_;
}
}
}
}
else
{
lean_object* v___x_588_; lean_object* v___x_589_; 
lean_dec(v_b_537_);
lean_dec(v_a_536_);
lean_dec_ref(v_inst_534_);
v___x_588_ = lean_box(v___x_560_);
v___x_589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_589_, 0, v___x_588_);
lean_ctor_set(v___x_589_, 1, v_m_535_);
return v___x_589_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_containsThenInsertIfNew(lean_object* v_00_u03b1_590_, lean_object* v_00_u03b2_591_, lean_object* v_inst_592_, lean_object* v_inst_593_, lean_object* v_m_594_, lean_object* v_a_595_, lean_object* v_b_596_){
_start:
{
lean_object* v_size_597_; lean_object* v_buckets_598_; lean_object* v___x_599_; lean_object* v___x_600_; uint8_t v___x_601_; 
v_size_597_ = lean_ctor_get(v_m_594_, 0);
v_buckets_598_ = lean_ctor_get(v_m_594_, 1);
v___x_599_ = lean_unsigned_to_nat(0u);
v___x_600_ = lean_array_get_size(v_buckets_598_);
v___x_601_ = lean_nat_dec_lt(v___x_599_, v___x_600_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; lean_object* v___x_603_; 
lean_dec(v_b_596_);
lean_dec(v_a_595_);
lean_dec_ref(v_inst_593_);
lean_dec_ref(v_inst_592_);
v___x_602_ = lean_box(v___x_601_);
v___x_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
lean_ctor_set(v___x_603_, 1, v_m_594_);
return v___x_603_;
}
else
{
lean_object* v___x_604_; uint64_t v___x_605_; uint64_t v___x_606_; uint64_t v___x_607_; uint64_t v___x_608_; uint64_t v_fold_609_; uint64_t v___x_610_; uint64_t v___x_611_; uint64_t v___x_612_; size_t v___x_613_; size_t v___x_614_; size_t v___x_615_; size_t v___x_616_; size_t v___x_617_; lean_object* v_bkt_618_; uint8_t v___x_619_; 
lean_inc_ref(v_inst_593_);
lean_inc_n(v_a_595_, 2);
v___x_604_ = lean_apply_1(v_inst_593_, v_a_595_);
v___x_605_ = 32ULL;
v___x_606_ = lean_unbox_uint64(v___x_604_);
v___x_607_ = lean_uint64_shift_right(v___x_606_, v___x_605_);
v___x_608_ = lean_unbox_uint64(v___x_604_);
lean_dec_ref(v___x_604_);
v_fold_609_ = lean_uint64_xor(v___x_608_, v___x_607_);
v___x_610_ = 16ULL;
v___x_611_ = lean_uint64_shift_right(v_fold_609_, v___x_610_);
v___x_612_ = lean_uint64_xor(v_fold_609_, v___x_611_);
v___x_613_ = lean_uint64_to_usize(v___x_612_);
v___x_614_ = lean_usize_of_nat(v___x_600_);
v___x_615_ = ((size_t)1ULL);
v___x_616_ = lean_usize_sub(v___x_614_, v___x_615_);
v___x_617_ = lean_usize_land(v___x_613_, v___x_616_);
v_bkt_618_ = lean_array_uget_borrowed(v_buckets_598_, v___x_617_);
lean_inc(v_bkt_618_);
v___x_619_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_592_, v_a_595_, v_bkt_618_);
if (v___x_619_ == 0)
{
lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_644_; 
lean_inc_ref(v_buckets_598_);
lean_inc(v_size_597_);
v_isSharedCheck_644_ = !lean_is_exclusive(v_m_594_);
if (v_isSharedCheck_644_ == 0)
{
lean_object* v_unused_645_; lean_object* v_unused_646_; 
v_unused_645_ = lean_ctor_get(v_m_594_, 1);
lean_dec(v_unused_645_);
v_unused_646_ = lean_ctor_get(v_m_594_, 0);
lean_dec(v_unused_646_);
v___x_621_ = v_m_594_;
v_isShared_622_ = v_isSharedCheck_644_;
goto v_resetjp_620_;
}
else
{
lean_dec(v_m_594_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_644_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_623_; lean_object* v_size_x27_624_; lean_object* v___x_625_; lean_object* v_buckets_x27_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; uint8_t v___x_632_; 
v___x_623_ = lean_unsigned_to_nat(1u);
v_size_x27_624_ = lean_nat_add(v_size_597_, v___x_623_);
lean_dec(v_size_597_);
lean_inc(v_bkt_618_);
v___x_625_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_625_, 0, v_a_595_);
lean_ctor_set(v___x_625_, 1, v_b_596_);
lean_ctor_set(v___x_625_, 2, v_bkt_618_);
v_buckets_x27_626_ = lean_array_uset(v_buckets_598_, v___x_617_, v___x_625_);
v___x_627_ = lean_unsigned_to_nat(4u);
v___x_628_ = lean_nat_mul(v_size_x27_624_, v___x_627_);
v___x_629_ = lean_unsigned_to_nat(3u);
v___x_630_ = lean_nat_div(v___x_628_, v___x_629_);
lean_dec(v___x_628_);
v___x_631_ = lean_array_get_size(v_buckets_x27_626_);
v___x_632_ = lean_nat_dec_le(v___x_630_, v___x_631_);
lean_dec(v___x_630_);
if (v___x_632_ == 0)
{
lean_object* v_val_633_; lean_object* v___x_635_; 
v_val_633_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_593_, v_buckets_x27_626_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 1, v_val_633_);
lean_ctor_set(v___x_621_, 0, v_size_x27_624_);
v___x_635_ = v___x_621_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_size_x27_624_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v_val_633_);
v___x_635_ = v_reuseFailAlloc_638_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = lean_box(v___x_619_);
v___x_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
lean_ctor_set(v___x_637_, 1, v___x_635_);
return v___x_637_;
}
}
else
{
lean_object* v___x_640_; 
lean_dec_ref(v_inst_593_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 1, v_buckets_x27_626_);
lean_ctor_set(v___x_621_, 0, v_size_x27_624_);
v___x_640_ = v___x_621_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_size_x27_624_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v_buckets_x27_626_);
v___x_640_ = v_reuseFailAlloc_643_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = lean_box(v___x_619_);
v___x_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
lean_ctor_set(v___x_642_, 1, v___x_640_);
return v___x_642_;
}
}
}
}
else
{
lean_object* v___x_647_; lean_object* v___x_648_; 
lean_dec(v_b_596_);
lean_dec(v_a_595_);
lean_dec_ref(v_inst_593_);
v___x_647_ = lean_box(v___x_619_);
v___x_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_647_);
lean_ctor_set(v___x_648_, 1, v_m_594_);
return v___x_648_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x3f___redArg(lean_object* v_inst_649_, lean_object* v_inst_650_, lean_object* v_m_651_, lean_object* v_a_652_){
_start:
{
lean_object* v_buckets_653_; lean_object* v___x_654_; lean_object* v___x_655_; uint8_t v___x_656_; 
v_buckets_653_ = lean_ctor_get(v_m_651_, 1);
v___x_654_ = lean_unsigned_to_nat(0u);
v___x_655_ = lean_array_get_size(v_buckets_653_);
v___x_656_ = lean_nat_dec_lt(v___x_654_, v___x_655_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; 
lean_dec(v_a_652_);
lean_dec_ref(v_inst_650_);
lean_dec_ref(v_inst_649_);
v___x_657_ = lean_box(0);
return v___x_657_;
}
else
{
lean_object* v___x_658_; 
v___x_658_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(v_inst_649_, v_inst_650_, v_m_651_, v_a_652_);
return v___x_658_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x3f___redArg___boxed(lean_object* v_inst_659_, lean_object* v_inst_660_, lean_object* v_m_661_, lean_object* v_a_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Std_DHashMap_Raw_get_x3f___redArg(v_inst_659_, v_inst_660_, v_m_661_, v_a_662_);
lean_dec_ref(v_m_661_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x3f(lean_object* v_00_u03b1_664_, lean_object* v_00_u03b2_665_, lean_object* v_inst_666_, lean_object* v_inst_667_, lean_object* v_inst_668_, lean_object* v_m_669_, lean_object* v_a_670_){
_start:
{
lean_object* v_buckets_671_; lean_object* v___x_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
v_buckets_671_ = lean_ctor_get(v_m_669_, 1);
v___x_672_ = lean_unsigned_to_nat(0u);
v___x_673_ = lean_array_get_size(v_buckets_671_);
v___x_674_ = lean_nat_dec_lt(v___x_672_, v___x_673_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; 
lean_dec(v_a_670_);
lean_dec_ref(v_inst_668_);
lean_dec_ref(v_inst_666_);
v___x_675_ = lean_box(0);
return v___x_675_;
}
else
{
lean_object* v___x_676_; 
v___x_676_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(v_inst_666_, v_inst_668_, v_m_669_, v_a_670_);
return v___x_676_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x3f___boxed(lean_object* v_00_u03b1_677_, lean_object* v_00_u03b2_678_, lean_object* v_inst_679_, lean_object* v_inst_680_, lean_object* v_inst_681_, lean_object* v_m_682_, lean_object* v_a_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Std_DHashMap_Raw_get_x3f(v_00_u03b1_677_, v_00_u03b2_678_, v_inst_679_, v_inst_680_, v_inst_681_, v_m_682_, v_a_683_);
lean_dec_ref(v_m_682_);
return v_res_684_;
}
}
uint8_t l_Std_DHashMap_Raw_contains___redArg(lean_object* v_inst_685_, lean_object* v_inst_686_, lean_object* v_m_687_, lean_object* v_a_688_){
_start:
{
lean_object* v_buckets_689_; lean_object* v___x_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
v_buckets_689_ = lean_ctor_get(v_m_687_, 1);
v___x_690_ = lean_unsigned_to_nat(0u);
v___x_691_ = lean_array_get_size(v_buckets_689_);
v___x_692_ = lean_nat_dec_lt(v___x_690_, v___x_691_);
if (v___x_692_ == 0)
{
lean_dec(v_a_688_);
lean_dec_ref(v_inst_686_);
lean_dec_ref(v_inst_685_);
return v___x_692_;
}
else
{
uint8_t v___x_693_; 
v___x_693_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_685_, v_inst_686_, v_m_687_, v_a_688_);
return v___x_693_;
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Raw_contains___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_685_ = stack[0].m_obj;
lean_object* v_inst_686_ = stack[1].m_obj;
lean_object* v_m_687_ = stack[2].m_obj;
lean_object* v_a_688_ = stack[3].m_obj;
uint8_t v_res_694_;
v_res_694_ = l_Std_DHashMap_Raw_contains___redArg(v_inst_685_, v_inst_686_, v_m_687_, v_a_688_);
stack->m_num = v_res_694_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_contains___redArg___boxed(lean_object* v_inst_695_, lean_object* v_inst_696_, lean_object* v_m_697_, lean_object* v_a_698_){
_start:
{
uint8_t v_res_699_; lean_object* v_r_700_; 
v_res_699_ = l_Std_DHashMap_Raw_contains___redArg(v_inst_695_, v_inst_696_, v_m_697_, v_a_698_);
lean_dec_ref(v_m_697_);
v_r_700_ = lean_box(v_res_699_);
return v_r_700_;
}
}
uint8_t l_Std_DHashMap_Raw_contains(lean_object* v_00_u03b1_701_, lean_object* v_00_u03b2_702_, lean_object* v_inst_703_, lean_object* v_inst_704_, lean_object* v_m_705_, lean_object* v_a_706_){
_start:
{
lean_object* v_buckets_707_; lean_object* v___x_708_; lean_object* v___x_709_; uint8_t v___x_710_; 
v_buckets_707_ = lean_ctor_get(v_m_705_, 1);
v___x_708_ = lean_unsigned_to_nat(0u);
v___x_709_ = lean_array_get_size(v_buckets_707_);
v___x_710_ = lean_nat_dec_lt(v___x_708_, v___x_709_);
if (v___x_710_ == 0)
{
lean_dec(v_a_706_);
lean_dec_ref(v_inst_704_);
lean_dec_ref(v_inst_703_);
return v___x_710_;
}
else
{
uint8_t v___x_711_; 
v___x_711_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_703_, v_inst_704_, v_m_705_, v_a_706_);
return v___x_711_;
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Raw_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_703_ = stack[2].m_obj;
lean_object* v_inst_704_ = stack[3].m_obj;
lean_object* v_m_705_ = stack[4].m_obj;
lean_object* v_a_706_ = stack[5].m_obj;
uint8_t v_res_712_;
v_res_712_ = l_Std_DHashMap_Raw_contains(lean_box(0), lean_box(0), v_inst_703_, v_inst_704_, v_m_705_, v_a_706_);
stack->m_num = v_res_712_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_contains___boxed(lean_object* v_00_u03b1_713_, lean_object* v_00_u03b2_714_, lean_object* v_inst_715_, lean_object* v_inst_716_, lean_object* v_m_717_, lean_object* v_a_718_){
_start:
{
uint8_t v_res_719_; lean_object* v_r_720_; 
v_res_719_ = l_Std_DHashMap_Raw_contains(v_00_u03b1_713_, v_00_u03b2_714_, v_inst_715_, v_inst_716_, v_m_717_, v_a_718_);
lean_dec_ref(v_m_717_);
v_r_720_ = lean_box(v_res_719_);
return v_r_720_;
}
}
lean_object* l_Std_DHashMap_Raw_instMembershipOfBEqOfHashable___redArg(){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = lean_box(0);
return v___x_722_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Raw_instMembershipOfBEqOfHashable___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_723_;
v_res_723_ = l_Std_DHashMap_Raw_instMembershipOfBEqOfHashable___redArg();
stack->m_obj
 = v_res_723_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instMembershipOfBEqOfHashable___redArg___boxed(lean_object* v___dummy_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Std_DHashMap_Raw_instMembershipOfBEqOfHashable___redArg();
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instMembershipOfBEqOfHashable(lean_object* v_00_u03b1_726_, lean_object* v_00_u03b2_727_, lean_object* v_inst_728_, lean_object* v_inst_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = lean_box(0);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instMembershipOfBEqOfHashable___boxed(lean_object* v_00_u03b1_731_, lean_object* v_00_u03b2_732_, lean_object* v_inst_733_, lean_object* v_inst_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Std_DHashMap_Raw_instMembershipOfBEqOfHashable(v_00_u03b1_731_, v_00_u03b2_732_, v_inst_733_, v_inst_734_);
lean_dec_ref(v_inst_734_);
lean_dec_ref(v_inst_733_);
return v_res_735_;
}
}
uint8_t l_Std_DHashMap_Raw_instDecidableMem___redArg(lean_object* v_inst_736_, lean_object* v_inst_737_, lean_object* v_m_738_, lean_object* v_a_739_){
_start:
{
lean_object* v_buckets_740_; lean_object* v___x_741_; lean_object* v___x_742_; uint8_t v___x_743_; 
v_buckets_740_ = lean_ctor_get(v_m_738_, 1);
v___x_741_ = lean_unsigned_to_nat(0u);
v___x_742_ = lean_array_get_size(v_buckets_740_);
v___x_743_ = lean_nat_dec_lt(v___x_741_, v___x_742_);
if (v___x_743_ == 0)
{
lean_dec(v_a_739_);
lean_dec_ref(v_inst_737_);
lean_dec_ref(v_inst_736_);
return v___x_743_;
}
else
{
uint8_t v___x_744_; 
v___x_744_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_736_, v_inst_737_, v_m_738_, v_a_739_);
return v___x_744_;
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Raw_instDecidableMem___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_736_ = stack[0].m_obj;
lean_object* v_inst_737_ = stack[1].m_obj;
lean_object* v_m_738_ = stack[2].m_obj;
lean_object* v_a_739_ = stack[3].m_obj;
uint8_t v_res_745_;
v_res_745_ = l_Std_DHashMap_Raw_instDecidableMem___redArg(v_inst_736_, v_inst_737_, v_m_738_, v_a_739_);
stack->m_num = v_res_745_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instDecidableMem___redArg___boxed(lean_object* v_inst_746_, lean_object* v_inst_747_, lean_object* v_m_748_, lean_object* v_a_749_){
_start:
{
uint8_t v_res_750_; lean_object* v_r_751_; 
v_res_750_ = l_Std_DHashMap_Raw_instDecidableMem___redArg(v_inst_746_, v_inst_747_, v_m_748_, v_a_749_);
lean_dec_ref(v_m_748_);
v_r_751_ = lean_box(v_res_750_);
return v_r_751_;
}
}
uint8_t l_Std_DHashMap_Raw_instDecidableMem(lean_object* v_00_u03b1_752_, lean_object* v_00_u03b2_753_, lean_object* v_inst_754_, lean_object* v_inst_755_, lean_object* v_m_756_, lean_object* v_a_757_){
_start:
{
uint8_t v___x_758_; 
v___x_758_ = l_Std_DHashMap_Raw_instDecidableMem___redArg(v_inst_754_, v_inst_755_, v_m_756_, v_a_757_);
return v___x_758_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Raw_instDecidableMem_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_754_ = stack[2].m_obj;
lean_object* v_inst_755_ = stack[3].m_obj;
lean_object* v_m_756_ = stack[4].m_obj;
lean_object* v_a_757_ = stack[5].m_obj;
uint8_t v_res_759_;
v_res_759_ = l_Std_DHashMap_Raw_instDecidableMem(lean_box(0), lean_box(0), v_inst_754_, v_inst_755_, v_m_756_, v_a_757_);
stack->m_num = v_res_759_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instDecidableMem___boxed(lean_object* v_00_u03b1_760_, lean_object* v_00_u03b2_761_, lean_object* v_inst_762_, lean_object* v_inst_763_, lean_object* v_m_764_, lean_object* v_a_765_){
_start:
{
uint8_t v_res_766_; lean_object* v_r_767_; 
v_res_766_ = l_Std_DHashMap_Raw_instDecidableMem(v_00_u03b1_760_, v_00_u03b2_761_, v_inst_762_, v_inst_763_, v_m_764_, v_a_765_);
lean_dec_ref(v_m_764_);
v_r_767_ = lean_box(v_res_766_);
return v_r_767_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get___redArg(lean_object* v_inst_768_, lean_object* v_inst_769_, lean_object* v_m_770_, lean_object* v_a_771_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l_Std_DHashMap_Internal_Raw_u2080_get___redArg(v_inst_768_, v_inst_769_, v_m_770_, v_a_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get___redArg___boxed(lean_object* v_inst_773_, lean_object* v_inst_774_, lean_object* v_m_775_, lean_object* v_a_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Std_DHashMap_Raw_get___redArg(v_inst_773_, v_inst_774_, v_m_775_, v_a_776_);
lean_dec_ref(v_m_775_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get(lean_object* v_00_u03b1_778_, lean_object* v_00_u03b2_779_, lean_object* v_inst_780_, lean_object* v_inst_781_, lean_object* v_inst_782_, lean_object* v_m_783_, lean_object* v_a_784_, lean_object* v_h_785_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l_Std_DHashMap_Internal_Raw_u2080_get___redArg(v_inst_780_, v_inst_781_, v_m_783_, v_a_784_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get___boxed(lean_object* v_00_u03b1_787_, lean_object* v_00_u03b2_788_, lean_object* v_inst_789_, lean_object* v_inst_790_, lean_object* v_inst_791_, lean_object* v_m_792_, lean_object* v_a_793_, lean_object* v_h_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_Std_DHashMap_Raw_get(v_00_u03b1_787_, v_00_u03b2_788_, v_inst_789_, v_inst_790_, v_inst_791_, v_m_792_, v_a_793_, v_h_794_);
lean_dec_ref(v_m_792_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getD___redArg(lean_object* v_inst_796_, lean_object* v_inst_797_, lean_object* v_m_798_, lean_object* v_a_799_, lean_object* v_fallback_800_){
_start:
{
lean_object* v_buckets_801_; lean_object* v___x_802_; lean_object* v___x_803_; uint8_t v___x_804_; 
v_buckets_801_ = lean_ctor_get(v_m_798_, 1);
v___x_802_ = lean_unsigned_to_nat(0u);
v___x_803_ = lean_array_get_size(v_buckets_801_);
v___x_804_ = lean_nat_dec_lt(v___x_802_, v___x_803_);
if (v___x_804_ == 0)
{
lean_dec(v_a_799_);
lean_dec_ref(v_inst_797_);
lean_dec_ref(v_inst_796_);
lean_inc(v_fallback_800_);
return v_fallback_800_;
}
else
{
lean_object* v___x_805_; 
v___x_805_ = l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(v_inst_796_, v_inst_797_, v_m_798_, v_a_799_, v_fallback_800_);
return v___x_805_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getD___redArg___boxed(lean_object* v_inst_806_, lean_object* v_inst_807_, lean_object* v_m_808_, lean_object* v_a_809_, lean_object* v_fallback_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_Std_DHashMap_Raw_getD___redArg(v_inst_806_, v_inst_807_, v_m_808_, v_a_809_, v_fallback_810_);
lean_dec(v_fallback_810_);
lean_dec_ref(v_m_808_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getD(lean_object* v_00_u03b1_812_, lean_object* v_00_u03b2_813_, lean_object* v_inst_814_, lean_object* v_inst_815_, lean_object* v_inst_816_, lean_object* v_m_817_, lean_object* v_a_818_, lean_object* v_fallback_819_){
_start:
{
lean_object* v_buckets_820_; lean_object* v___x_821_; lean_object* v___x_822_; uint8_t v___x_823_; 
v_buckets_820_ = lean_ctor_get(v_m_817_, 1);
v___x_821_ = lean_unsigned_to_nat(0u);
v___x_822_ = lean_array_get_size(v_buckets_820_);
v___x_823_ = lean_nat_dec_lt(v___x_821_, v___x_822_);
if (v___x_823_ == 0)
{
lean_dec(v_a_818_);
lean_dec_ref(v_inst_815_);
lean_dec_ref(v_inst_814_);
lean_inc(v_fallback_819_);
return v_fallback_819_;
}
else
{
lean_object* v___x_824_; 
v___x_824_ = l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(v_inst_814_, v_inst_815_, v_m_817_, v_a_818_, v_fallback_819_);
return v___x_824_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getD___boxed(lean_object* v_00_u03b1_825_, lean_object* v_00_u03b2_826_, lean_object* v_inst_827_, lean_object* v_inst_828_, lean_object* v_inst_829_, lean_object* v_m_830_, lean_object* v_a_831_, lean_object* v_fallback_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Std_DHashMap_Raw_getD(v_00_u03b1_825_, v_00_u03b2_826_, v_inst_827_, v_inst_828_, v_inst_829_, v_m_830_, v_a_831_, v_fallback_832_);
lean_dec(v_fallback_832_);
lean_dec_ref(v_m_830_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x21___redArg(lean_object* v_inst_834_, lean_object* v_inst_835_, lean_object* v_m_836_, lean_object* v_a_837_, lean_object* v_inst_838_){
_start:
{
lean_object* v_buckets_839_; lean_object* v___x_840_; lean_object* v___x_841_; uint8_t v___x_842_; 
v_buckets_839_ = lean_ctor_get(v_m_836_, 1);
v___x_840_ = lean_unsigned_to_nat(0u);
v___x_841_ = lean_array_get_size(v_buckets_839_);
v___x_842_ = lean_nat_dec_lt(v___x_840_, v___x_841_);
if (v___x_842_ == 0)
{
lean_dec(v_a_837_);
lean_dec_ref(v_inst_835_);
lean_dec_ref(v_inst_834_);
lean_inc(v_inst_838_);
return v_inst_838_;
}
else
{
lean_object* v___x_843_; 
v___x_843_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(v_inst_834_, v_inst_835_, v_m_836_, v_a_837_, v_inst_838_);
return v___x_843_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x21___redArg___boxed(lean_object* v_inst_844_, lean_object* v_inst_845_, lean_object* v_m_846_, lean_object* v_a_847_, lean_object* v_inst_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Std_DHashMap_Raw_get_x21___redArg(v_inst_844_, v_inst_845_, v_m_846_, v_a_847_, v_inst_848_);
lean_dec(v_inst_848_);
lean_dec_ref(v_m_846_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x21(lean_object* v_00_u03b1_850_, lean_object* v_00_u03b2_851_, lean_object* v_inst_852_, lean_object* v_inst_853_, lean_object* v_inst_854_, lean_object* v_m_855_, lean_object* v_a_856_, lean_object* v_inst_857_){
_start:
{
lean_object* v_buckets_858_; lean_object* v___x_859_; lean_object* v___x_860_; uint8_t v___x_861_; 
v_buckets_858_ = lean_ctor_get(v_m_855_, 1);
v___x_859_ = lean_unsigned_to_nat(0u);
v___x_860_ = lean_array_get_size(v_buckets_858_);
v___x_861_ = lean_nat_dec_lt(v___x_859_, v___x_860_);
if (v___x_861_ == 0)
{
lean_dec(v_a_856_);
lean_dec_ref(v_inst_853_);
lean_dec_ref(v_inst_852_);
lean_inc(v_inst_857_);
return v_inst_857_;
}
else
{
lean_object* v___x_862_; 
v___x_862_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(v_inst_852_, v_inst_853_, v_m_855_, v_a_856_, v_inst_857_);
return v___x_862_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x21___boxed(lean_object* v_00_u03b1_863_, lean_object* v_00_u03b2_864_, lean_object* v_inst_865_, lean_object* v_inst_866_, lean_object* v_inst_867_, lean_object* v_m_868_, lean_object* v_a_869_, lean_object* v_inst_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Std_DHashMap_Raw_get_x21(v_00_u03b1_863_, v_00_u03b2_864_, v_inst_865_, v_inst_866_, v_inst_867_, v_m_868_, v_a_869_, v_inst_870_);
lean_dec(v_inst_870_);
lean_dec_ref(v_m_868_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_erase___redArg(lean_object* v_inst_872_, lean_object* v_inst_873_, lean_object* v_m_874_, lean_object* v_a_875_){
_start:
{
lean_object* v_buckets_876_; lean_object* v___x_877_; lean_object* v___x_878_; uint8_t v___x_879_; 
v_buckets_876_ = lean_ctor_get(v_m_874_, 1);
v___x_877_ = lean_unsigned_to_nat(0u);
v___x_878_ = lean_array_get_size(v_buckets_876_);
v___x_879_ = lean_nat_dec_lt(v___x_877_, v___x_878_);
if (v___x_879_ == 0)
{
lean_dec(v_a_875_);
lean_dec_ref(v_inst_873_);
lean_dec_ref(v_inst_872_);
return v_m_874_;
}
else
{
lean_object* v___x_880_; 
v___x_880_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_872_, v_inst_873_, v_m_874_, v_a_875_);
return v___x_880_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_erase(lean_object* v_00_u03b1_881_, lean_object* v_00_u03b2_882_, lean_object* v_inst_883_, lean_object* v_inst_884_, lean_object* v_m_885_, lean_object* v_a_886_){
_start:
{
lean_object* v_buckets_887_; lean_object* v___x_888_; lean_object* v___x_889_; uint8_t v___x_890_; 
v_buckets_887_ = lean_ctor_get(v_m_885_, 1);
v___x_888_ = lean_unsigned_to_nat(0u);
v___x_889_ = lean_array_get_size(v_buckets_887_);
v___x_890_ = lean_nat_dec_lt(v___x_888_, v___x_889_);
if (v___x_890_ == 0)
{
lean_dec(v_a_886_);
lean_dec_ref(v_inst_884_);
lean_dec_ref(v_inst_883_);
return v_m_885_;
}
else
{
lean_object* v___x_891_; 
v___x_891_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_883_, v_inst_884_, v_m_885_, v_a_886_);
return v___x_891_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x3f___redArg(lean_object* v_inst_892_, lean_object* v_inst_893_, lean_object* v_m_894_, lean_object* v_a_895_){
_start:
{
lean_object* v_buckets_896_; lean_object* v___x_897_; lean_object* v___x_898_; uint8_t v___x_899_; 
v_buckets_896_ = lean_ctor_get(v_m_894_, 1);
v___x_897_ = lean_unsigned_to_nat(0u);
v___x_898_ = lean_array_get_size(v_buckets_896_);
v___x_899_ = lean_nat_dec_lt(v___x_897_, v___x_898_);
if (v___x_899_ == 0)
{
lean_object* v___x_900_; 
lean_dec(v_a_895_);
lean_dec_ref(v_inst_893_);
lean_dec_ref(v_inst_892_);
v___x_900_ = lean_box(0);
return v___x_900_;
}
else
{
lean_object* v___x_901_; 
v___x_901_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_892_, v_inst_893_, v_m_894_, v_a_895_);
return v___x_901_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x3f___redArg___boxed(lean_object* v_inst_902_, lean_object* v_inst_903_, lean_object* v_m_904_, lean_object* v_a_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Std_DHashMap_Raw_Const_get_x3f___redArg(v_inst_902_, v_inst_903_, v_m_904_, v_a_905_);
lean_dec_ref(v_m_904_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x3f(lean_object* v_00_u03b1_907_, lean_object* v_00_u03b2_908_, lean_object* v_inst_909_, lean_object* v_inst_910_, lean_object* v_m_911_, lean_object* v_a_912_){
_start:
{
lean_object* v_buckets_913_; lean_object* v___x_914_; lean_object* v___x_915_; uint8_t v___x_916_; 
v_buckets_913_ = lean_ctor_get(v_m_911_, 1);
v___x_914_ = lean_unsigned_to_nat(0u);
v___x_915_ = lean_array_get_size(v_buckets_913_);
v___x_916_ = lean_nat_dec_lt(v___x_914_, v___x_915_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; 
lean_dec(v_a_912_);
lean_dec_ref(v_inst_910_);
lean_dec_ref(v_inst_909_);
v___x_917_ = lean_box(0);
return v___x_917_;
}
else
{
lean_object* v___x_918_; 
v___x_918_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_909_, v_inst_910_, v_m_911_, v_a_912_);
return v___x_918_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x3f___boxed(lean_object* v_00_u03b1_919_, lean_object* v_00_u03b2_920_, lean_object* v_inst_921_, lean_object* v_inst_922_, lean_object* v_m_923_, lean_object* v_a_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Std_DHashMap_Raw_Const_get_x3f(v_00_u03b1_919_, v_00_u03b2_920_, v_inst_921_, v_inst_922_, v_m_923_, v_a_924_);
lean_dec_ref(v_m_923_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get___redArg(lean_object* v_inst_926_, lean_object* v_inst_927_, lean_object* v_m_928_, lean_object* v_a_929_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_926_, v_inst_927_, v_m_928_, v_a_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get___redArg___boxed(lean_object* v_inst_931_, lean_object* v_inst_932_, lean_object* v_m_933_, lean_object* v_a_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Std_DHashMap_Raw_Const_get___redArg(v_inst_931_, v_inst_932_, v_m_933_, v_a_934_);
lean_dec_ref(v_m_933_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get(lean_object* v_00_u03b1_936_, lean_object* v_00_u03b2_937_, lean_object* v_inst_938_, lean_object* v_inst_939_, lean_object* v_m_940_, lean_object* v_a_941_, lean_object* v_h_942_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_938_, v_inst_939_, v_m_940_, v_a_941_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get___boxed(lean_object* v_00_u03b1_944_, lean_object* v_00_u03b2_945_, lean_object* v_inst_946_, lean_object* v_inst_947_, lean_object* v_m_948_, lean_object* v_a_949_, lean_object* v_h_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Std_DHashMap_Raw_Const_get(v_00_u03b1_944_, v_00_u03b2_945_, v_inst_946_, v_inst_947_, v_m_948_, v_a_949_, v_h_950_);
lean_dec_ref(v_m_948_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getD___redArg(lean_object* v_inst_952_, lean_object* v_inst_953_, lean_object* v_m_954_, lean_object* v_a_955_, lean_object* v_fallback_956_){
_start:
{
lean_object* v_buckets_957_; lean_object* v___x_958_; lean_object* v___x_959_; uint8_t v___x_960_; 
v_buckets_957_ = lean_ctor_get(v_m_954_, 1);
v___x_958_ = lean_unsigned_to_nat(0u);
v___x_959_ = lean_array_get_size(v_buckets_957_);
v___x_960_ = lean_nat_dec_lt(v___x_958_, v___x_959_);
if (v___x_960_ == 0)
{
lean_dec(v_a_955_);
lean_dec_ref(v_inst_953_);
lean_dec_ref(v_inst_952_);
lean_inc(v_fallback_956_);
return v_fallback_956_;
}
else
{
lean_object* v___x_961_; 
v___x_961_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_inst_952_, v_inst_953_, v_m_954_, v_a_955_, v_fallback_956_);
return v___x_961_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getD___redArg___boxed(lean_object* v_inst_962_, lean_object* v_inst_963_, lean_object* v_m_964_, lean_object* v_a_965_, lean_object* v_fallback_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_Std_DHashMap_Raw_Const_getD___redArg(v_inst_962_, v_inst_963_, v_m_964_, v_a_965_, v_fallback_966_);
lean_dec(v_fallback_966_);
lean_dec_ref(v_m_964_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getD(lean_object* v_00_u03b1_968_, lean_object* v_00_u03b2_969_, lean_object* v_inst_970_, lean_object* v_inst_971_, lean_object* v_m_972_, lean_object* v_a_973_, lean_object* v_fallback_974_){
_start:
{
lean_object* v_buckets_975_; lean_object* v___x_976_; lean_object* v___x_977_; uint8_t v___x_978_; 
v_buckets_975_ = lean_ctor_get(v_m_972_, 1);
v___x_976_ = lean_unsigned_to_nat(0u);
v___x_977_ = lean_array_get_size(v_buckets_975_);
v___x_978_ = lean_nat_dec_lt(v___x_976_, v___x_977_);
if (v___x_978_ == 0)
{
lean_dec(v_a_973_);
lean_dec_ref(v_inst_971_);
lean_dec_ref(v_inst_970_);
lean_inc(v_fallback_974_);
return v_fallback_974_;
}
else
{
lean_object* v___x_979_; 
v___x_979_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_inst_970_, v_inst_971_, v_m_972_, v_a_973_, v_fallback_974_);
return v___x_979_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getD___boxed(lean_object* v_00_u03b1_980_, lean_object* v_00_u03b2_981_, lean_object* v_inst_982_, lean_object* v_inst_983_, lean_object* v_m_984_, lean_object* v_a_985_, lean_object* v_fallback_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_Std_DHashMap_Raw_Const_getD(v_00_u03b1_980_, v_00_u03b2_981_, v_inst_982_, v_inst_983_, v_m_984_, v_a_985_, v_fallback_986_);
lean_dec(v_fallback_986_);
lean_dec_ref(v_m_984_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x21___redArg(lean_object* v_inst_988_, lean_object* v_inst_989_, lean_object* v_inst_990_, lean_object* v_m_991_, lean_object* v_a_992_){
_start:
{
lean_object* v_buckets_993_; lean_object* v___x_994_; lean_object* v___x_995_; uint8_t v___x_996_; 
v_buckets_993_ = lean_ctor_get(v_m_991_, 1);
v___x_994_ = lean_unsigned_to_nat(0u);
v___x_995_ = lean_array_get_size(v_buckets_993_);
v___x_996_ = lean_nat_dec_lt(v___x_994_, v___x_995_);
if (v___x_996_ == 0)
{
lean_dec(v_a_992_);
lean_dec_ref(v_inst_989_);
lean_dec_ref(v_inst_988_);
lean_inc(v_inst_990_);
return v_inst_990_;
}
else
{
lean_object* v___x_997_; 
v___x_997_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_988_, v_inst_989_, v_inst_990_, v_m_991_, v_a_992_);
return v___x_997_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x21___redArg___boxed(lean_object* v_inst_998_, lean_object* v_inst_999_, lean_object* v_inst_1000_, lean_object* v_m_1001_, lean_object* v_a_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_Std_DHashMap_Raw_Const_get_x21___redArg(v_inst_998_, v_inst_999_, v_inst_1000_, v_m_1001_, v_a_1002_);
lean_dec_ref(v_m_1001_);
lean_dec(v_inst_1000_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x21(lean_object* v_00_u03b1_1004_, lean_object* v_00_u03b2_1005_, lean_object* v_inst_1006_, lean_object* v_inst_1007_, lean_object* v_inst_1008_, lean_object* v_m_1009_, lean_object* v_a_1010_){
_start:
{
lean_object* v_buckets_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; uint8_t v___x_1014_; 
v_buckets_1011_ = lean_ctor_get(v_m_1009_, 1);
v___x_1012_ = lean_unsigned_to_nat(0u);
v___x_1013_ = lean_array_get_size(v_buckets_1011_);
v___x_1014_ = lean_nat_dec_lt(v___x_1012_, v___x_1013_);
if (v___x_1014_ == 0)
{
lean_dec(v_a_1010_);
lean_dec_ref(v_inst_1007_);
lean_dec_ref(v_inst_1006_);
lean_inc(v_inst_1008_);
return v_inst_1008_;
}
else
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_1006_, v_inst_1007_, v_inst_1008_, v_m_1009_, v_a_1010_);
return v___x_1015_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x21___boxed(lean_object* v_00_u03b1_1016_, lean_object* v_00_u03b2_1017_, lean_object* v_inst_1018_, lean_object* v_inst_1019_, lean_object* v_inst_1020_, lean_object* v_m_1021_, lean_object* v_a_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Std_DHashMap_Raw_Const_get_x21(v_00_u03b1_1016_, v_00_u03b2_1017_, v_inst_1018_, v_inst_1019_, v_inst_1020_, v_m_1021_, v_a_1022_);
lean_dec_ref(v_m_1021_);
lean_dec(v_inst_1020_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getThenInsertIfNew_x3f___redArg(lean_object* v_inst_1024_, lean_object* v_inst_1025_, lean_object* v_m_1026_, lean_object* v_a_1027_, lean_object* v_b_1028_){
_start:
{
lean_object* v_size_1029_; lean_object* v_buckets_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; uint8_t v___x_1033_; 
v_size_1029_ = lean_ctor_get(v_m_1026_, 0);
v_buckets_1030_ = lean_ctor_get(v_m_1026_, 1);
v___x_1031_ = lean_unsigned_to_nat(0u);
v___x_1032_ = lean_array_get_size(v_buckets_1030_);
v___x_1033_ = lean_nat_dec_lt(v___x_1031_, v___x_1032_);
if (v___x_1033_ == 0)
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
lean_dec(v_b_1028_);
lean_dec(v_a_1027_);
lean_dec_ref(v_inst_1025_);
lean_dec_ref(v_inst_1024_);
v___x_1034_ = lean_box(0);
v___x_1035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1034_);
lean_ctor_set(v___x_1035_, 1, v_m_1026_);
return v___x_1035_;
}
else
{
lean_object* v___x_1036_; uint64_t v___x_1037_; uint64_t v___x_1038_; uint64_t v___x_1039_; uint64_t v___x_1040_; uint64_t v_fold_1041_; uint64_t v___x_1042_; uint64_t v___x_1043_; uint64_t v___x_1044_; size_t v___x_1045_; size_t v___x_1046_; size_t v___x_1047_; size_t v___x_1048_; size_t v___x_1049_; lean_object* v_bkt_1050_; lean_object* v___x_1051_; 
lean_inc_ref(v_inst_1025_);
lean_inc_n(v_a_1027_, 2);
v___x_1036_ = lean_apply_1(v_inst_1025_, v_a_1027_);
v___x_1037_ = 32ULL;
v___x_1038_ = lean_unbox_uint64(v___x_1036_);
v___x_1039_ = lean_uint64_shift_right(v___x_1038_, v___x_1037_);
v___x_1040_ = lean_unbox_uint64(v___x_1036_);
lean_dec_ref(v___x_1036_);
v_fold_1041_ = lean_uint64_xor(v___x_1040_, v___x_1039_);
v___x_1042_ = 16ULL;
v___x_1043_ = lean_uint64_shift_right(v_fold_1041_, v___x_1042_);
v___x_1044_ = lean_uint64_xor(v_fold_1041_, v___x_1043_);
v___x_1045_ = lean_uint64_to_usize(v___x_1044_);
v___x_1046_ = lean_usize_of_nat(v___x_1032_);
v___x_1047_ = ((size_t)1ULL);
v___x_1048_ = lean_usize_sub(v___x_1046_, v___x_1047_);
v___x_1049_ = lean_usize_land(v___x_1045_, v___x_1048_);
v_bkt_1050_ = lean_array_uget_borrowed(v_buckets_1030_, v___x_1049_);
lean_inc(v_bkt_1050_);
v___x_1051_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_inst_1024_, v_a_1027_, v_bkt_1050_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1074_; 
lean_inc_ref(v_buckets_1030_);
lean_inc(v_size_1029_);
v_isSharedCheck_1074_ = !lean_is_exclusive(v_m_1026_);
if (v_isSharedCheck_1074_ == 0)
{
lean_object* v_unused_1075_; lean_object* v_unused_1076_; 
v_unused_1075_ = lean_ctor_get(v_m_1026_, 1);
lean_dec(v_unused_1075_);
v_unused_1076_ = lean_ctor_get(v_m_1026_, 0);
lean_dec(v_unused_1076_);
v___x_1053_ = v_m_1026_;
v_isShared_1054_ = v_isSharedCheck_1074_;
goto v_resetjp_1052_;
}
else
{
lean_dec(v_m_1026_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1074_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1055_; lean_object* v_size_x27_1056_; lean_object* v___x_1057_; lean_object* v_buckets_x27_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; uint8_t v___x_1064_; 
v___x_1055_ = lean_unsigned_to_nat(1u);
v_size_x27_1056_ = lean_nat_add(v_size_1029_, v___x_1055_);
lean_dec(v_size_1029_);
lean_inc(v_bkt_1050_);
v___x_1057_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1057_, 0, v_a_1027_);
lean_ctor_set(v___x_1057_, 1, v_b_1028_);
lean_ctor_set(v___x_1057_, 2, v_bkt_1050_);
v_buckets_x27_1058_ = lean_array_uset(v_buckets_1030_, v___x_1049_, v___x_1057_);
v___x_1059_ = lean_unsigned_to_nat(4u);
v___x_1060_ = lean_nat_mul(v_size_x27_1056_, v___x_1059_);
v___x_1061_ = lean_unsigned_to_nat(3u);
v___x_1062_ = lean_nat_div(v___x_1060_, v___x_1061_);
lean_dec(v___x_1060_);
v___x_1063_ = lean_array_get_size(v_buckets_x27_1058_);
v___x_1064_ = lean_nat_dec_le(v___x_1062_, v___x_1063_);
lean_dec(v___x_1062_);
if (v___x_1064_ == 0)
{
lean_object* v_val_1065_; lean_object* v___x_1067_; 
v_val_1065_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1025_, v_buckets_x27_1058_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 1, v_val_1065_);
lean_ctor_set(v___x_1053_, 0, v_size_x27_1056_);
v___x_1067_ = v___x_1053_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_size_x27_1056_);
lean_ctor_set(v_reuseFailAlloc_1069_, 1, v_val_1065_);
v___x_1067_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
lean_object* v___x_1068_; 
v___x_1068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1051_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
return v___x_1068_;
}
}
else
{
lean_object* v___x_1071_; 
lean_dec_ref(v_inst_1025_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 1, v_buckets_x27_1058_);
lean_ctor_set(v___x_1053_, 0, v_size_x27_1056_);
v___x_1071_ = v___x_1053_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_size_x27_1056_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v_buckets_x27_1058_);
v___x_1071_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
lean_object* v___x_1072_; 
v___x_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1051_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
return v___x_1072_;
}
}
}
}
else
{
lean_object* v___x_1077_; 
lean_dec(v_b_1028_);
lean_dec(v_a_1027_);
lean_dec_ref(v_inst_1025_);
v___x_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1051_);
lean_ctor_set(v___x_1077_, 1, v_m_1026_);
return v___x_1077_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_1078_, lean_object* v_00_u03b2_1079_, lean_object* v_inst_1080_, lean_object* v_inst_1081_, lean_object* v_m_1082_, lean_object* v_a_1083_, lean_object* v_b_1084_){
_start:
{
lean_object* v_size_1085_; lean_object* v_buckets_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; uint8_t v___x_1089_; 
v_size_1085_ = lean_ctor_get(v_m_1082_, 0);
v_buckets_1086_ = lean_ctor_get(v_m_1082_, 1);
v___x_1087_ = lean_unsigned_to_nat(0u);
v___x_1088_ = lean_array_get_size(v_buckets_1086_);
v___x_1089_ = lean_nat_dec_lt(v___x_1087_, v___x_1088_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
lean_dec(v_b_1084_);
lean_dec(v_a_1083_);
lean_dec_ref(v_inst_1081_);
lean_dec_ref(v_inst_1080_);
v___x_1090_ = lean_box(0);
v___x_1091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1090_);
lean_ctor_set(v___x_1091_, 1, v_m_1082_);
return v___x_1091_;
}
else
{
lean_object* v___x_1092_; uint64_t v___x_1093_; uint64_t v___x_1094_; uint64_t v___x_1095_; uint64_t v___x_1096_; uint64_t v_fold_1097_; uint64_t v___x_1098_; uint64_t v___x_1099_; uint64_t v___x_1100_; size_t v___x_1101_; size_t v___x_1102_; size_t v___x_1103_; size_t v___x_1104_; size_t v___x_1105_; lean_object* v_bkt_1106_; lean_object* v___x_1107_; 
lean_inc_ref(v_inst_1081_);
lean_inc_n(v_a_1083_, 2);
v___x_1092_ = lean_apply_1(v_inst_1081_, v_a_1083_);
v___x_1093_ = 32ULL;
v___x_1094_ = lean_unbox_uint64(v___x_1092_);
v___x_1095_ = lean_uint64_shift_right(v___x_1094_, v___x_1093_);
v___x_1096_ = lean_unbox_uint64(v___x_1092_);
lean_dec_ref(v___x_1092_);
v_fold_1097_ = lean_uint64_xor(v___x_1096_, v___x_1095_);
v___x_1098_ = 16ULL;
v___x_1099_ = lean_uint64_shift_right(v_fold_1097_, v___x_1098_);
v___x_1100_ = lean_uint64_xor(v_fold_1097_, v___x_1099_);
v___x_1101_ = lean_uint64_to_usize(v___x_1100_);
v___x_1102_ = lean_usize_of_nat(v___x_1088_);
v___x_1103_ = ((size_t)1ULL);
v___x_1104_ = lean_usize_sub(v___x_1102_, v___x_1103_);
v___x_1105_ = lean_usize_land(v___x_1101_, v___x_1104_);
v_bkt_1106_ = lean_array_uget_borrowed(v_buckets_1086_, v___x_1105_);
lean_inc(v_bkt_1106_);
v___x_1107_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_inst_1080_, v_a_1083_, v_bkt_1106_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1130_; 
lean_inc_ref(v_buckets_1086_);
lean_inc(v_size_1085_);
v_isSharedCheck_1130_ = !lean_is_exclusive(v_m_1082_);
if (v_isSharedCheck_1130_ == 0)
{
lean_object* v_unused_1131_; lean_object* v_unused_1132_; 
v_unused_1131_ = lean_ctor_get(v_m_1082_, 1);
lean_dec(v_unused_1131_);
v_unused_1132_ = lean_ctor_get(v_m_1082_, 0);
lean_dec(v_unused_1132_);
v___x_1109_ = v_m_1082_;
v_isShared_1110_ = v_isSharedCheck_1130_;
goto v_resetjp_1108_;
}
else
{
lean_dec(v_m_1082_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1130_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1111_; lean_object* v_size_x27_1112_; lean_object* v___x_1113_; lean_object* v_buckets_x27_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; uint8_t v___x_1120_; 
v___x_1111_ = lean_unsigned_to_nat(1u);
v_size_x27_1112_ = lean_nat_add(v_size_1085_, v___x_1111_);
lean_dec(v_size_1085_);
lean_inc(v_bkt_1106_);
v___x_1113_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1113_, 0, v_a_1083_);
lean_ctor_set(v___x_1113_, 1, v_b_1084_);
lean_ctor_set(v___x_1113_, 2, v_bkt_1106_);
v_buckets_x27_1114_ = lean_array_uset(v_buckets_1086_, v___x_1105_, v___x_1113_);
v___x_1115_ = lean_unsigned_to_nat(4u);
v___x_1116_ = lean_nat_mul(v_size_x27_1112_, v___x_1115_);
v___x_1117_ = lean_unsigned_to_nat(3u);
v___x_1118_ = lean_nat_div(v___x_1116_, v___x_1117_);
lean_dec(v___x_1116_);
v___x_1119_ = lean_array_get_size(v_buckets_x27_1114_);
v___x_1120_ = lean_nat_dec_le(v___x_1118_, v___x_1119_);
lean_dec(v___x_1118_);
if (v___x_1120_ == 0)
{
lean_object* v_val_1121_; lean_object* v___x_1123_; 
v_val_1121_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1081_, v_buckets_x27_1114_);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 1, v_val_1121_);
lean_ctor_set(v___x_1109_, 0, v_size_x27_1112_);
v___x_1123_ = v___x_1109_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_size_x27_1112_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v_val_1121_);
v___x_1123_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
lean_object* v___x_1124_; 
v___x_1124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1107_);
lean_ctor_set(v___x_1124_, 1, v___x_1123_);
return v___x_1124_;
}
}
else
{
lean_object* v___x_1127_; 
lean_dec_ref(v_inst_1081_);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 1, v_buckets_x27_1114_);
lean_ctor_set(v___x_1109_, 0, v_size_x27_1112_);
v___x_1127_ = v___x_1109_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_size_x27_1112_);
lean_ctor_set(v_reuseFailAlloc_1129_, 1, v_buckets_x27_1114_);
v___x_1127_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
lean_object* v___x_1128_; 
v___x_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1107_);
lean_ctor_set(v___x_1128_, 1, v___x_1127_);
return v___x_1128_;
}
}
}
}
else
{
lean_object* v___x_1133_; 
lean_dec(v_b_1084_);
lean_dec(v_a_1083_);
lean_dec_ref(v_inst_1081_);
v___x_1133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1107_);
lean_ctor_set(v___x_1133_, 1, v_m_1082_);
return v___x_1133_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x3f___redArg(lean_object* v_inst_1134_, lean_object* v_inst_1135_, lean_object* v_m_1136_, lean_object* v_a_1137_){
_start:
{
lean_object* v_buckets_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; uint8_t v___x_1141_; 
v_buckets_1138_ = lean_ctor_get(v_m_1136_, 1);
v___x_1139_ = lean_unsigned_to_nat(0u);
v___x_1140_ = lean_array_get_size(v_buckets_1138_);
v___x_1141_ = lean_nat_dec_lt(v___x_1139_, v___x_1140_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1142_; 
lean_dec(v_a_1137_);
lean_dec_ref(v_inst_1135_);
lean_dec_ref(v_inst_1134_);
v___x_1142_ = lean_box(0);
return v___x_1142_;
}
else
{
lean_object* v___x_1143_; 
v___x_1143_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_1134_, v_inst_1135_, v_m_1136_, v_a_1137_);
return v___x_1143_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x3f___redArg___boxed(lean_object* v_inst_1144_, lean_object* v_inst_1145_, lean_object* v_m_1146_, lean_object* v_a_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Std_DHashMap_Raw_getKey_x3f___redArg(v_inst_1144_, v_inst_1145_, v_m_1146_, v_a_1147_);
lean_dec_ref(v_m_1146_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x3f(lean_object* v_00_u03b1_1149_, lean_object* v_00_u03b2_1150_, lean_object* v_inst_1151_, lean_object* v_inst_1152_, lean_object* v_m_1153_, lean_object* v_a_1154_){
_start:
{
lean_object* v_buckets_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; uint8_t v___x_1158_; 
v_buckets_1155_ = lean_ctor_get(v_m_1153_, 1);
v___x_1156_ = lean_unsigned_to_nat(0u);
v___x_1157_ = lean_array_get_size(v_buckets_1155_);
v___x_1158_ = lean_nat_dec_lt(v___x_1156_, v___x_1157_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; 
lean_dec(v_a_1154_);
lean_dec_ref(v_inst_1152_);
lean_dec_ref(v_inst_1151_);
v___x_1159_ = lean_box(0);
return v___x_1159_;
}
else
{
lean_object* v___x_1160_; 
v___x_1160_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_1151_, v_inst_1152_, v_m_1153_, v_a_1154_);
return v___x_1160_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x3f___boxed(lean_object* v_00_u03b1_1161_, lean_object* v_00_u03b2_1162_, lean_object* v_inst_1163_, lean_object* v_inst_1164_, lean_object* v_m_1165_, lean_object* v_a_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_Std_DHashMap_Raw_getKey_x3f(v_00_u03b1_1161_, v_00_u03b2_1162_, v_inst_1163_, v_inst_1164_, v_m_1165_, v_a_1166_);
lean_dec_ref(v_m_1165_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey___redArg(lean_object* v_inst_1168_, lean_object* v_inst_1169_, lean_object* v_m_1170_, lean_object* v_a_1171_){
_start:
{
lean_object* v___x_1172_; 
v___x_1172_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_1168_, v_inst_1169_, v_m_1170_, v_a_1171_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey___redArg___boxed(lean_object* v_inst_1173_, lean_object* v_inst_1174_, lean_object* v_m_1175_, lean_object* v_a_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Std_DHashMap_Raw_getKey___redArg(v_inst_1173_, v_inst_1174_, v_m_1175_, v_a_1176_);
lean_dec_ref(v_m_1175_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey(lean_object* v_00_u03b1_1178_, lean_object* v_00_u03b2_1179_, lean_object* v_inst_1180_, lean_object* v_inst_1181_, lean_object* v_m_1182_, lean_object* v_a_1183_, lean_object* v_h_1184_){
_start:
{
lean_object* v___x_1185_; 
v___x_1185_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_1180_, v_inst_1181_, v_m_1182_, v_a_1183_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey___boxed(lean_object* v_00_u03b1_1186_, lean_object* v_00_u03b2_1187_, lean_object* v_inst_1188_, lean_object* v_inst_1189_, lean_object* v_m_1190_, lean_object* v_a_1191_, lean_object* v_h_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Std_DHashMap_Raw_getKey(v_00_u03b1_1186_, v_00_u03b2_1187_, v_inst_1188_, v_inst_1189_, v_m_1190_, v_a_1191_, v_h_1192_);
lean_dec_ref(v_m_1190_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKeyD___redArg(lean_object* v_inst_1194_, lean_object* v_inst_1195_, lean_object* v_m_1196_, lean_object* v_a_1197_, lean_object* v_fallback_1198_){
_start:
{
lean_object* v_buckets_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; uint8_t v___x_1202_; 
v_buckets_1199_ = lean_ctor_get(v_m_1196_, 1);
v___x_1200_ = lean_unsigned_to_nat(0u);
v___x_1201_ = lean_array_get_size(v_buckets_1199_);
v___x_1202_ = lean_nat_dec_lt(v___x_1200_, v___x_1201_);
if (v___x_1202_ == 0)
{
lean_dec(v_a_1197_);
lean_dec_ref(v_inst_1195_);
lean_dec_ref(v_inst_1194_);
lean_inc(v_fallback_1198_);
return v_fallback_1198_;
}
else
{
lean_object* v___x_1203_; 
v___x_1203_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_1194_, v_inst_1195_, v_m_1196_, v_a_1197_, v_fallback_1198_);
return v___x_1203_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKeyD___redArg___boxed(lean_object* v_inst_1204_, lean_object* v_inst_1205_, lean_object* v_m_1206_, lean_object* v_a_1207_, lean_object* v_fallback_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Std_DHashMap_Raw_getKeyD___redArg(v_inst_1204_, v_inst_1205_, v_m_1206_, v_a_1207_, v_fallback_1208_);
lean_dec(v_fallback_1208_);
lean_dec_ref(v_m_1206_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKeyD(lean_object* v_00_u03b1_1210_, lean_object* v_00_u03b2_1211_, lean_object* v_inst_1212_, lean_object* v_inst_1213_, lean_object* v_m_1214_, lean_object* v_a_1215_, lean_object* v_fallback_1216_){
_start:
{
lean_object* v_buckets_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; uint8_t v___x_1220_; 
v_buckets_1217_ = lean_ctor_get(v_m_1214_, 1);
v___x_1218_ = lean_unsigned_to_nat(0u);
v___x_1219_ = lean_array_get_size(v_buckets_1217_);
v___x_1220_ = lean_nat_dec_lt(v___x_1218_, v___x_1219_);
if (v___x_1220_ == 0)
{
lean_dec(v_a_1215_);
lean_dec_ref(v_inst_1213_);
lean_dec_ref(v_inst_1212_);
lean_inc(v_fallback_1216_);
return v_fallback_1216_;
}
else
{
lean_object* v___x_1221_; 
v___x_1221_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_1212_, v_inst_1213_, v_m_1214_, v_a_1215_, v_fallback_1216_);
return v___x_1221_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKeyD___boxed(lean_object* v_00_u03b1_1222_, lean_object* v_00_u03b2_1223_, lean_object* v_inst_1224_, lean_object* v_inst_1225_, lean_object* v_m_1226_, lean_object* v_a_1227_, lean_object* v_fallback_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l_Std_DHashMap_Raw_getKeyD(v_00_u03b1_1222_, v_00_u03b2_1223_, v_inst_1224_, v_inst_1225_, v_m_1226_, v_a_1227_, v_fallback_1228_);
lean_dec(v_fallback_1228_);
lean_dec_ref(v_m_1226_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x21___redArg(lean_object* v_inst_1230_, lean_object* v_inst_1231_, lean_object* v_inst_1232_, lean_object* v_m_1233_, lean_object* v_a_1234_){
_start:
{
lean_object* v_buckets_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; uint8_t v___x_1238_; 
v_buckets_1235_ = lean_ctor_get(v_m_1233_, 1);
v___x_1236_ = lean_unsigned_to_nat(0u);
v___x_1237_ = lean_array_get_size(v_buckets_1235_);
v___x_1238_ = lean_nat_dec_lt(v___x_1236_, v___x_1237_);
if (v___x_1238_ == 0)
{
lean_dec(v_a_1234_);
lean_dec_ref(v_inst_1231_);
lean_dec_ref(v_inst_1230_);
lean_inc(v_inst_1232_);
return v_inst_1232_;
}
else
{
lean_object* v___x_1239_; 
v___x_1239_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_1230_, v_inst_1231_, v_inst_1232_, v_m_1233_, v_a_1234_);
return v___x_1239_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x21___redArg___boxed(lean_object* v_inst_1240_, lean_object* v_inst_1241_, lean_object* v_inst_1242_, lean_object* v_m_1243_, lean_object* v_a_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Std_DHashMap_Raw_getKey_x21___redArg(v_inst_1240_, v_inst_1241_, v_inst_1242_, v_m_1243_, v_a_1244_);
lean_dec_ref(v_m_1243_);
lean_dec(v_inst_1242_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x21(lean_object* v_00_u03b1_1246_, lean_object* v_00_u03b2_1247_, lean_object* v_inst_1248_, lean_object* v_inst_1249_, lean_object* v_inst_1250_, lean_object* v_m_1251_, lean_object* v_a_1252_){
_start:
{
lean_object* v_buckets_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; uint8_t v___x_1256_; 
v_buckets_1253_ = lean_ctor_get(v_m_1251_, 1);
v___x_1254_ = lean_unsigned_to_nat(0u);
v___x_1255_ = lean_array_get_size(v_buckets_1253_);
v___x_1256_ = lean_nat_dec_lt(v___x_1254_, v___x_1255_);
if (v___x_1256_ == 0)
{
lean_dec(v_a_1252_);
lean_dec_ref(v_inst_1249_);
lean_dec_ref(v_inst_1248_);
lean_inc(v_inst_1250_);
return v_inst_1250_;
}
else
{
lean_object* v___x_1257_; 
v___x_1257_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_1248_, v_inst_1249_, v_inst_1250_, v_m_1251_, v_a_1252_);
return v___x_1257_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x21___boxed(lean_object* v_00_u03b1_1258_, lean_object* v_00_u03b2_1259_, lean_object* v_inst_1260_, lean_object* v_inst_1261_, lean_object* v_inst_1262_, lean_object* v_m_1263_, lean_object* v_a_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l_Std_DHashMap_Raw_getKey_x21(v_00_u03b1_1258_, v_00_u03b2_1259_, v_inst_1260_, v_inst_1261_, v_inst_1262_, v_m_1263_, v_a_1264_);
lean_dec_ref(v_m_1263_);
lean_dec(v_inst_1262_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x3f___redArg(lean_object* v_inst_1266_, lean_object* v_inst_1267_, lean_object* v_m_1268_, lean_object* v_a_1269_){
_start:
{
lean_object* v_buckets_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; uint8_t v___x_1273_; 
v_buckets_1270_ = lean_ctor_get(v_m_1268_, 1);
v___x_1271_ = lean_unsigned_to_nat(0u);
v___x_1272_ = lean_array_get_size(v_buckets_1270_);
v___x_1273_ = lean_nat_dec_lt(v___x_1271_, v___x_1272_);
if (v___x_1273_ == 0)
{
lean_object* v___x_1274_; 
lean_dec(v_a_1269_);
lean_dec_ref(v_inst_1267_);
lean_dec_ref(v_inst_1266_);
v___x_1274_ = lean_box(0);
return v___x_1274_;
}
else
{
lean_object* v___x_1275_; 
v___x_1275_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(v_inst_1266_, v_inst_1267_, v_m_1268_, v_a_1269_);
return v___x_1275_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x3f___redArg___boxed(lean_object* v_inst_1276_, lean_object* v_inst_1277_, lean_object* v_m_1278_, lean_object* v_a_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_Std_DHashMap_Raw_getEntry_x3f___redArg(v_inst_1276_, v_inst_1277_, v_m_1278_, v_a_1279_);
lean_dec_ref(v_m_1278_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x3f(lean_object* v_00_u03b1_1281_, lean_object* v_00_u03b2_1282_, lean_object* v_inst_1283_, lean_object* v_inst_1284_, lean_object* v_m_1285_, lean_object* v_a_1286_){
_start:
{
lean_object* v_buckets_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; uint8_t v___x_1290_; 
v_buckets_1287_ = lean_ctor_get(v_m_1285_, 1);
v___x_1288_ = lean_unsigned_to_nat(0u);
v___x_1289_ = lean_array_get_size(v_buckets_1287_);
v___x_1290_ = lean_nat_dec_lt(v___x_1288_, v___x_1289_);
if (v___x_1290_ == 0)
{
lean_object* v___x_1291_; 
lean_dec(v_a_1286_);
lean_dec_ref(v_inst_1284_);
lean_dec_ref(v_inst_1283_);
v___x_1291_ = lean_box(0);
return v___x_1291_;
}
else
{
lean_object* v___x_1292_; 
v___x_1292_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(v_inst_1283_, v_inst_1284_, v_m_1285_, v_a_1286_);
return v___x_1292_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x3f___boxed(lean_object* v_00_u03b1_1293_, lean_object* v_00_u03b2_1294_, lean_object* v_inst_1295_, lean_object* v_inst_1296_, lean_object* v_m_1297_, lean_object* v_a_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Std_DHashMap_Raw_getEntry_x3f(v_00_u03b1_1293_, v_00_u03b2_1294_, v_inst_1295_, v_inst_1296_, v_m_1297_, v_a_1298_);
lean_dec_ref(v_m_1297_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry___redArg(lean_object* v_inst_1300_, lean_object* v_inst_1301_, lean_object* v_m_1302_, lean_object* v_a_1303_){
_start:
{
lean_object* v___x_1304_; 
v___x_1304_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg(v_inst_1300_, v_inst_1301_, v_m_1302_, v_a_1303_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry___redArg___boxed(lean_object* v_inst_1305_, lean_object* v_inst_1306_, lean_object* v_m_1307_, lean_object* v_a_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Std_DHashMap_Raw_getEntry___redArg(v_inst_1305_, v_inst_1306_, v_m_1307_, v_a_1308_);
lean_dec_ref(v_m_1307_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry(lean_object* v_00_u03b1_1310_, lean_object* v_00_u03b2_1311_, lean_object* v_inst_1312_, lean_object* v_inst_1313_, lean_object* v_m_1314_, lean_object* v_a_1315_, lean_object* v_h_1316_){
_start:
{
lean_object* v___x_1317_; 
v___x_1317_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg(v_inst_1312_, v_inst_1313_, v_m_1314_, v_a_1315_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry___boxed(lean_object* v_00_u03b1_1318_, lean_object* v_00_u03b2_1319_, lean_object* v_inst_1320_, lean_object* v_inst_1321_, lean_object* v_m_1322_, lean_object* v_a_1323_, lean_object* v_h_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l_Std_DHashMap_Raw_getEntry(v_00_u03b1_1318_, v_00_u03b2_1319_, v_inst_1320_, v_inst_1321_, v_m_1322_, v_a_1323_, v_h_1324_);
lean_dec_ref(v_m_1322_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntryD___redArg(lean_object* v_inst_1326_, lean_object* v_inst_1327_, lean_object* v_m_1328_, lean_object* v_a_1329_, lean_object* v_fallback_1330_){
_start:
{
lean_object* v_buckets_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; uint8_t v___x_1334_; 
v_buckets_1331_ = lean_ctor_get(v_m_1328_, 1);
v___x_1332_ = lean_unsigned_to_nat(0u);
v___x_1333_ = lean_array_get_size(v_buckets_1331_);
v___x_1334_ = lean_nat_dec_lt(v___x_1332_, v___x_1333_);
if (v___x_1334_ == 0)
{
lean_dec(v_a_1329_);
lean_dec_ref(v_inst_1327_);
lean_dec_ref(v_inst_1326_);
lean_inc_ref(v_fallback_1330_);
return v_fallback_1330_;
}
else
{
lean_object* v___x_1335_; 
v___x_1335_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD___redArg(v_inst_1326_, v_inst_1327_, v_m_1328_, v_a_1329_, v_fallback_1330_);
return v___x_1335_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntryD___redArg___boxed(lean_object* v_inst_1336_, lean_object* v_inst_1337_, lean_object* v_m_1338_, lean_object* v_a_1339_, lean_object* v_fallback_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Std_DHashMap_Raw_getEntryD___redArg(v_inst_1336_, v_inst_1337_, v_m_1338_, v_a_1339_, v_fallback_1340_);
lean_dec_ref(v_fallback_1340_);
lean_dec_ref(v_m_1338_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntryD(lean_object* v_00_u03b1_1342_, lean_object* v_00_u03b2_1343_, lean_object* v_inst_1344_, lean_object* v_inst_1345_, lean_object* v_m_1346_, lean_object* v_a_1347_, lean_object* v_fallback_1348_){
_start:
{
lean_object* v_buckets_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; uint8_t v___x_1352_; 
v_buckets_1349_ = lean_ctor_get(v_m_1346_, 1);
v___x_1350_ = lean_unsigned_to_nat(0u);
v___x_1351_ = lean_array_get_size(v_buckets_1349_);
v___x_1352_ = lean_nat_dec_lt(v___x_1350_, v___x_1351_);
if (v___x_1352_ == 0)
{
lean_dec(v_a_1347_);
lean_dec_ref(v_inst_1345_);
lean_dec_ref(v_inst_1344_);
lean_inc_ref(v_fallback_1348_);
return v_fallback_1348_;
}
else
{
lean_object* v___x_1353_; 
v___x_1353_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD___redArg(v_inst_1344_, v_inst_1345_, v_m_1346_, v_a_1347_, v_fallback_1348_);
return v___x_1353_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntryD___boxed(lean_object* v_00_u03b1_1354_, lean_object* v_00_u03b2_1355_, lean_object* v_inst_1356_, lean_object* v_inst_1357_, lean_object* v_m_1358_, lean_object* v_a_1359_, lean_object* v_fallback_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Std_DHashMap_Raw_getEntryD(v_00_u03b1_1354_, v_00_u03b2_1355_, v_inst_1356_, v_inst_1357_, v_m_1358_, v_a_1359_, v_fallback_1360_);
lean_dec_ref(v_fallback_1360_);
lean_dec_ref(v_m_1358_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x21___redArg(lean_object* v_inst_1362_, lean_object* v_inst_1363_, lean_object* v_inst_1364_, lean_object* v_m_1365_, lean_object* v_a_1366_){
_start:
{
lean_object* v_buckets_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; uint8_t v___x_1370_; 
v_buckets_1367_ = lean_ctor_get(v_m_1365_, 1);
v___x_1368_ = lean_unsigned_to_nat(0u);
v___x_1369_ = lean_array_get_size(v_buckets_1367_);
v___x_1370_ = lean_nat_dec_lt(v___x_1368_, v___x_1369_);
if (v___x_1370_ == 0)
{
lean_dec(v_a_1366_);
lean_dec_ref(v_inst_1363_);
lean_dec_ref(v_inst_1362_);
lean_inc_ref(v_inst_1364_);
return v_inst_1364_;
}
else
{
lean_object* v___x_1371_; 
v___x_1371_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___redArg(v_inst_1362_, v_inst_1363_, v_m_1365_, v_a_1366_, v_inst_1364_);
return v___x_1371_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x21___redArg___boxed(lean_object* v_inst_1372_, lean_object* v_inst_1373_, lean_object* v_inst_1374_, lean_object* v_m_1375_, lean_object* v_a_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l_Std_DHashMap_Raw_getEntry_x21___redArg(v_inst_1372_, v_inst_1373_, v_inst_1374_, v_m_1375_, v_a_1376_);
lean_dec_ref(v_m_1375_);
lean_dec_ref(v_inst_1374_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x21(lean_object* v_00_u03b1_1378_, lean_object* v_00_u03b2_1379_, lean_object* v_inst_1380_, lean_object* v_inst_1381_, lean_object* v_inst_1382_, lean_object* v_m_1383_, lean_object* v_a_1384_){
_start:
{
lean_object* v_buckets_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; uint8_t v___x_1388_; 
v_buckets_1385_ = lean_ctor_get(v_m_1383_, 1);
v___x_1386_ = lean_unsigned_to_nat(0u);
v___x_1387_ = lean_array_get_size(v_buckets_1385_);
v___x_1388_ = lean_nat_dec_lt(v___x_1386_, v___x_1387_);
if (v___x_1388_ == 0)
{
lean_dec(v_a_1384_);
lean_dec_ref(v_inst_1381_);
lean_dec_ref(v_inst_1380_);
lean_inc_ref(v_inst_1382_);
return v_inst_1382_;
}
else
{
lean_object* v___x_1389_; 
v___x_1389_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___redArg(v_inst_1380_, v_inst_1381_, v_m_1383_, v_a_1384_, v_inst_1382_);
return v___x_1389_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x21___boxed(lean_object* v_00_u03b1_1390_, lean_object* v_00_u03b2_1391_, lean_object* v_inst_1392_, lean_object* v_inst_1393_, lean_object* v_inst_1394_, lean_object* v_m_1395_, lean_object* v_a_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Std_DHashMap_Raw_getEntry_x21(v_00_u03b1_1390_, v_00_u03b2_1391_, v_inst_1392_, v_inst_1393_, v_inst_1394_, v_m_1395_, v_a_1396_);
lean_dec_ref(v_m_1395_);
lean_dec_ref(v_inst_1394_);
return v_res_1397_;
}
}
uint8_t l_Std_DHashMap_Raw_isEmpty___redArg(lean_object* v_m_1398_){
_start:
{
lean_object* v_size_1399_; lean_object* v___x_1400_; uint8_t v___x_1401_; 
v_size_1399_ = lean_ctor_get(v_m_1398_, 0);
v___x_1400_ = lean_unsigned_to_nat(0u);
v___x_1401_ = lean_nat_dec_eq(v_size_1399_, v___x_1400_);
return v___x_1401_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Raw_isEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1398_ = stack[0].m_obj;
uint8_t v_res_1402_;
v_res_1402_ = l_Std_DHashMap_Raw_isEmpty___redArg(v_m_1398_);
stack->m_num = v_res_1402_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_isEmpty___redArg___boxed(lean_object* v_m_1403_){
_start:
{
uint8_t v_res_1404_; lean_object* v_r_1405_; 
v_res_1404_ = l_Std_DHashMap_Raw_isEmpty___redArg(v_m_1403_);
lean_dec_ref(v_m_1403_);
v_r_1405_ = lean_box(v_res_1404_);
return v_r_1405_;
}
}
uint8_t l_Std_DHashMap_Raw_isEmpty(lean_object* v_00_u03b1_1406_, lean_object* v_00_u03b2_1407_, lean_object* v_m_1408_){
_start:
{
lean_object* v_size_1409_; lean_object* v___x_1410_; uint8_t v___x_1411_; 
v_size_1409_ = lean_ctor_get(v_m_1408_, 0);
v___x_1410_ = lean_unsigned_to_nat(0u);
v___x_1411_ = lean_nat_dec_eq(v_size_1409_, v___x_1410_);
return v___x_1411_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Raw_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1408_ = stack[2].m_obj;
uint8_t v_res_1412_;
v_res_1412_ = l_Std_DHashMap_Raw_isEmpty(lean_box(0), lean_box(0), v_m_1408_);
stack->m_num = v_res_1412_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_isEmpty___boxed(lean_object* v_00_u03b1_1413_, lean_object* v_00_u03b2_1414_, lean_object* v_m_1415_){
_start:
{
uint8_t v_res_1416_; lean_object* v_r_1417_; 
v_res_1416_ = l_Std_DHashMap_Raw_isEmpty(v_00_u03b1_1413_, v_00_u03b2_1414_, v_m_1415_);
lean_dec_ref(v_m_1415_);
v_r_1417_ = lean_box(v_res_1416_);
return v_r_1417_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_modify___redArg(lean_object* v_inst_1418_, lean_object* v_inst_1419_, lean_object* v_m_1420_, lean_object* v_a_1421_, lean_object* v_f_1422_){
_start:
{
lean_object* v_buckets_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; uint8_t v___x_1426_; 
v_buckets_1423_ = lean_ctor_get(v_m_1420_, 1);
v___x_1424_ = lean_unsigned_to_nat(0u);
v___x_1425_ = lean_array_get_size(v_buckets_1423_);
v___x_1426_ = lean_nat_dec_lt(v___x_1424_, v___x_1425_);
if (v___x_1426_ == 0)
{
lean_object* v___x_1427_; 
lean_dec(v_f_1422_);
lean_dec(v_a_1421_);
lean_dec_ref(v_m_1420_);
lean_dec_ref(v_inst_1419_);
lean_dec_ref(v_inst_1418_);
v___x_1427_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1427_;
}
else
{
lean_object* v___x_1428_; 
v___x_1428_ = l_Std_DHashMap_Internal_Raw_u2080_modify___redArg(v_inst_1418_, v_inst_1419_, v_m_1420_, v_a_1421_, v_f_1422_);
return v___x_1428_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_modify(lean_object* v_00_u03b1_1429_, lean_object* v_00_u03b2_1430_, lean_object* v_inst_1431_, lean_object* v_inst_1432_, lean_object* v_inst_1433_, lean_object* v_m_1434_, lean_object* v_a_1435_, lean_object* v_f_1436_){
_start:
{
lean_object* v_buckets_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; uint8_t v___x_1440_; 
v_buckets_1437_ = lean_ctor_get(v_m_1434_, 1);
v___x_1438_ = lean_unsigned_to_nat(0u);
v___x_1439_ = lean_array_get_size(v_buckets_1437_);
v___x_1440_ = lean_nat_dec_lt(v___x_1438_, v___x_1439_);
if (v___x_1440_ == 0)
{
lean_object* v___x_1441_; 
lean_dec(v_f_1436_);
lean_dec(v_a_1435_);
lean_dec_ref(v_m_1434_);
lean_dec_ref(v_inst_1433_);
lean_dec_ref(v_inst_1431_);
v___x_1441_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1441_;
}
else
{
lean_object* v___x_1442_; 
v___x_1442_ = l_Std_DHashMap_Internal_Raw_u2080_modify___redArg(v_inst_1431_, v_inst_1433_, v_m_1434_, v_a_1435_, v_f_1436_);
return v___x_1442_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_modify___redArg(lean_object* v_inst_1443_, lean_object* v_inst_1444_, lean_object* v_m_1445_, lean_object* v_a_1446_, lean_object* v_f_1447_){
_start:
{
lean_object* v_buckets_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; uint8_t v___x_1451_; 
v_buckets_1448_ = lean_ctor_get(v_m_1445_, 1);
v___x_1449_ = lean_unsigned_to_nat(0u);
v___x_1450_ = lean_array_get_size(v_buckets_1448_);
v___x_1451_ = lean_nat_dec_lt(v___x_1449_, v___x_1450_);
if (v___x_1451_ == 0)
{
lean_object* v___x_1452_; 
lean_dec(v_f_1447_);
lean_dec(v_a_1446_);
lean_dec_ref(v_m_1445_);
lean_dec_ref(v_inst_1444_);
lean_dec_ref(v_inst_1443_);
v___x_1452_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1452_;
}
else
{
lean_object* v___x_1453_; 
v___x_1453_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_inst_1443_, v_inst_1444_, v_m_1445_, v_a_1446_, v_f_1447_);
return v___x_1453_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_modify(lean_object* v_00_u03b1_1454_, lean_object* v_inst_1455_, lean_object* v_inst_1456_, lean_object* v_inst_1457_, lean_object* v_00_u03b2_1458_, lean_object* v_m_1459_, lean_object* v_a_1460_, lean_object* v_f_1461_){
_start:
{
lean_object* v_buckets_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; uint8_t v___x_1465_; 
v_buckets_1462_ = lean_ctor_get(v_m_1459_, 1);
v___x_1463_ = lean_unsigned_to_nat(0u);
v___x_1464_ = lean_array_get_size(v_buckets_1462_);
v___x_1465_ = lean_nat_dec_lt(v___x_1463_, v___x_1464_);
if (v___x_1465_ == 0)
{
lean_object* v___x_1466_; 
lean_dec(v_f_1461_);
lean_dec(v_a_1460_);
lean_dec_ref(v_m_1459_);
lean_dec_ref(v_inst_1457_);
lean_dec_ref(v_inst_1455_);
v___x_1466_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1466_;
}
else
{
lean_object* v___x_1467_; 
v___x_1467_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_inst_1455_, v_inst_1457_, v_m_1459_, v_a_1460_, v_f_1461_);
return v___x_1467_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_alter___redArg(lean_object* v_inst_1468_, lean_object* v_inst_1469_, lean_object* v_m_1470_, lean_object* v_a_1471_, lean_object* v_f_1472_){
_start:
{
lean_object* v_buckets_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; uint8_t v___x_1476_; 
v_buckets_1473_ = lean_ctor_get(v_m_1470_, 1);
v___x_1474_ = lean_unsigned_to_nat(0u);
v___x_1475_ = lean_array_get_size(v_buckets_1473_);
v___x_1476_ = lean_nat_dec_lt(v___x_1474_, v___x_1475_);
if (v___x_1476_ == 0)
{
lean_object* v___x_1477_; 
lean_dec_ref(v_f_1472_);
lean_dec(v_a_1471_);
lean_dec_ref(v_m_1470_);
lean_dec_ref(v_inst_1469_);
lean_dec_ref(v_inst_1468_);
v___x_1477_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1477_;
}
else
{
lean_object* v___x_1478_; 
v___x_1478_ = l_Std_DHashMap_Internal_Raw_u2080_alter___redArg(v_inst_1468_, v_inst_1469_, v_m_1470_, v_a_1471_, v_f_1472_);
return v___x_1478_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_alter(lean_object* v_00_u03b1_1479_, lean_object* v_00_u03b2_1480_, lean_object* v_inst_1481_, lean_object* v_inst_1482_, lean_object* v_inst_1483_, lean_object* v_m_1484_, lean_object* v_a_1485_, lean_object* v_f_1486_){
_start:
{
lean_object* v_buckets_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; uint8_t v___x_1490_; 
v_buckets_1487_ = lean_ctor_get(v_m_1484_, 1);
v___x_1488_ = lean_unsigned_to_nat(0u);
v___x_1489_ = lean_array_get_size(v_buckets_1487_);
v___x_1490_ = lean_nat_dec_lt(v___x_1488_, v___x_1489_);
if (v___x_1490_ == 0)
{
lean_object* v___x_1491_; 
lean_dec_ref(v_f_1486_);
lean_dec(v_a_1485_);
lean_dec_ref(v_m_1484_);
lean_dec_ref(v_inst_1483_);
lean_dec_ref(v_inst_1481_);
v___x_1491_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1491_;
}
else
{
lean_object* v___x_1492_; 
v___x_1492_ = l_Std_DHashMap_Internal_Raw_u2080_alter___redArg(v_inst_1481_, v_inst_1483_, v_m_1484_, v_a_1485_, v_f_1486_);
return v___x_1492_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_alter___redArg(lean_object* v_inst_1493_, lean_object* v_inst_1494_, lean_object* v_m_1495_, lean_object* v_a_1496_, lean_object* v_f_1497_){
_start:
{
lean_object* v_buckets_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; uint8_t v___x_1501_; 
v_buckets_1498_ = lean_ctor_get(v_m_1495_, 1);
v___x_1499_ = lean_unsigned_to_nat(0u);
v___x_1500_ = lean_array_get_size(v_buckets_1498_);
v___x_1501_ = lean_nat_dec_lt(v___x_1499_, v___x_1500_);
if (v___x_1501_ == 0)
{
lean_object* v___x_1502_; 
lean_dec_ref(v_f_1497_);
lean_dec(v_a_1496_);
lean_dec_ref(v_m_1495_);
lean_dec_ref(v_inst_1494_);
lean_dec_ref(v_inst_1493_);
v___x_1502_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1502_;
}
else
{
lean_object* v___x_1503_; 
v___x_1503_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_1493_, v_inst_1494_, v_m_1495_, v_a_1496_, v_f_1497_);
return v___x_1503_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_alter(lean_object* v_00_u03b1_1504_, lean_object* v_inst_1505_, lean_object* v_inst_1506_, lean_object* v_inst_1507_, lean_object* v_00_u03b2_1508_, lean_object* v_m_1509_, lean_object* v_a_1510_, lean_object* v_f_1511_){
_start:
{
lean_object* v_buckets_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; uint8_t v___x_1515_; 
v_buckets_1512_ = lean_ctor_get(v_m_1509_, 1);
v___x_1513_ = lean_unsigned_to_nat(0u);
v___x_1514_ = lean_array_get_size(v_buckets_1512_);
v___x_1515_ = lean_nat_dec_lt(v___x_1513_, v___x_1514_);
if (v___x_1515_ == 0)
{
lean_object* v___x_1516_; 
lean_dec_ref(v_f_1511_);
lean_dec(v_a_1510_);
lean_dec_ref(v_m_1509_);
lean_dec_ref(v_inst_1507_);
lean_dec_ref(v_inst_1505_);
v___x_1516_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1516_;
}
else
{
lean_object* v___x_1517_; 
v___x_1517_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_1505_, v_inst_1507_, v_m_1509_, v_a_1510_, v_f_1511_);
return v___x_1517_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0(lean_object* v_f_1518_, lean_object* v_a_1519_, lean_object* v_b_1520_, lean_object* v_d_1521_){
_start:
{
lean_object* v___x_1522_; 
v___x_1522_ = lean_apply_3(v_f_1518_, v_d_1521_, v_a_1519_, v_b_1520_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__1(lean_object* v_inst_1523_, lean_object* v___f_1524_, lean_object* v_l_1525_, lean_object* v_acc_1526_){
_start:
{
lean_object* v___x_1527_; 
v___x_1527_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v_inst_1523_, v___f_1524_, v_acc_1526_, v_l_1525_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRevM___redArg(lean_object* v_inst_1528_, lean_object* v_f_1529_, lean_object* v_init_1530_, lean_object* v_b_1531_){
_start:
{
lean_object* v_toApplicative_1532_; lean_object* v_buckets_1533_; lean_object* v_toPure_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; uint8_t v___x_1537_; 
v_toApplicative_1532_ = lean_ctor_get(v_inst_1528_, 0);
v_buckets_1533_ = lean_ctor_get(v_b_1531_, 1);
lean_inc_ref(v_buckets_1533_);
lean_dec_ref(v_b_1531_);
v_toPure_1534_ = lean_ctor_get(v_toApplicative_1532_, 1);
v___x_1535_ = lean_array_get_size(v_buckets_1533_);
v___x_1536_ = lean_unsigned_to_nat(0u);
v___x_1537_ = lean_nat_dec_lt(v___x_1536_, v___x_1535_);
if (v___x_1537_ == 0)
{
lean_object* v___x_1538_; 
lean_inc(v_toPure_1534_);
lean_dec_ref(v_buckets_1533_);
lean_dec(v_f_1529_);
lean_dec_ref(v_inst_1528_);
v___x_1538_ = lean_apply_2(v_toPure_1534_, lean_box(0), v_init_1530_);
return v___x_1538_;
}
else
{
lean_object* v___f_1539_; lean_object* v___f_1540_; size_t v___x_1541_; size_t v___x_1542_; lean_object* v___x_1543_; 
v___f_1539_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1539_, 0, v_f_1529_);
lean_inc_ref(v_inst_1528_);
v___f_1540_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1540_, 0, v_inst_1528_);
lean_closure_set(v___f_1540_, 1, v___f_1539_);
v___x_1541_ = lean_usize_of_nat(v___x_1535_);
v___x_1542_ = ((size_t)0ULL);
v___x_1543_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1528_, v___f_1540_, v_buckets_1533_, v___x_1541_, v___x_1542_, v_init_1530_);
return v___x_1543_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRevM(lean_object* v_00_u03b1_1544_, lean_object* v_00_u03b2_1545_, lean_object* v_00_u03b4_1546_, lean_object* v_m_1547_, lean_object* v_inst_1548_, lean_object* v_f_1549_, lean_object* v_init_1550_, lean_object* v_b_1551_){
_start:
{
lean_object* v_toApplicative_1552_; lean_object* v_buckets_1553_; lean_object* v_toPure_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; uint8_t v___x_1557_; 
v_toApplicative_1552_ = lean_ctor_get(v_inst_1548_, 0);
v_buckets_1553_ = lean_ctor_get(v_b_1551_, 1);
lean_inc_ref(v_buckets_1553_);
lean_dec_ref(v_b_1551_);
v_toPure_1554_ = lean_ctor_get(v_toApplicative_1552_, 1);
v___x_1555_ = lean_array_get_size(v_buckets_1553_);
v___x_1556_ = lean_unsigned_to_nat(0u);
v___x_1557_ = lean_nat_dec_lt(v___x_1556_, v___x_1555_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1558_; 
lean_inc(v_toPure_1554_);
lean_dec_ref(v_buckets_1553_);
lean_dec(v_f_1549_);
lean_dec_ref(v_inst_1548_);
v___x_1558_ = lean_apply_2(v_toPure_1554_, lean_box(0), v_init_1550_);
return v___x_1558_;
}
else
{
lean_object* v___f_1559_; lean_object* v___f_1560_; size_t v___x_1561_; size_t v___x_1562_; lean_object* v___x_1563_; 
v___f_1559_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1559_, 0, v_f_1549_);
lean_inc_ref(v_inst_1548_);
v___f_1560_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1560_, 0, v_inst_1548_);
lean_closure_set(v___f_1560_, 1, v___f_1559_);
v___x_1561_ = lean_usize_of_nat(v___x_1555_);
v___x_1562_ = ((size_t)0ULL);
v___x_1563_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1548_, v___f_1560_, v_buckets_1553_, v___x_1561_, v___x_1562_, v_init_1550_);
return v___x_1563_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRev___redArg___lam__1(lean_object* v___x_1564_, lean_object* v___f_1565_, lean_object* v_l_1566_, lean_object* v_acc_1567_){
_start:
{
lean_object* v___x_1568_; 
v___x_1568_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_1564_, v___f_1565_, v_acc_1567_, v_l_1566_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRev___redArg(lean_object* v_f_1588_, lean_object* v_init_1589_, lean_object* v_b_1590_){
_start:
{
lean_object* v___x_1591_; lean_object* v_buckets_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; uint8_t v___x_1595_; 
v___x_1591_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_1592_ = lean_ctor_get(v_b_1590_, 1);
lean_inc_ref(v_buckets_1592_);
lean_dec_ref(v_b_1590_);
v___x_1593_ = lean_array_get_size(v_buckets_1592_);
v___x_1594_ = lean_unsigned_to_nat(0u);
v___x_1595_ = lean_nat_dec_lt(v___x_1594_, v___x_1593_);
if (v___x_1595_ == 0)
{
lean_dec_ref(v_buckets_1592_);
lean_dec(v_f_1588_);
return v_init_1589_;
}
else
{
lean_object* v___f_1596_; lean_object* v___f_1597_; size_t v___x_1598_; size_t v___x_1599_; lean_object* v___x_1600_; 
v___f_1596_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1596_, 0, v_f_1588_);
v___f_1597_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1597_, 0, v___x_1591_);
lean_closure_set(v___f_1597_, 1, v___f_1596_);
v___x_1598_ = lean_usize_of_nat(v___x_1593_);
v___x_1599_ = ((size_t)0ULL);
v___x_1600_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1591_, v___f_1597_, v_buckets_1592_, v___x_1598_, v___x_1599_, v_init_1589_);
return v___x_1600_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRev(lean_object* v_00_u03b1_1601_, lean_object* v_00_u03b2_1602_, lean_object* v_00_u03b4_1603_, lean_object* v_f_1604_, lean_object* v_init_1605_, lean_object* v_b_1606_){
_start:
{
lean_object* v___x_1607_; lean_object* v_buckets_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; uint8_t v___x_1611_; 
v___x_1607_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_1608_ = lean_ctor_get(v_b_1606_, 1);
lean_inc_ref(v_buckets_1608_);
lean_dec_ref(v_b_1606_);
v___x_1609_ = lean_array_get_size(v_buckets_1608_);
v___x_1610_ = lean_unsigned_to_nat(0u);
v___x_1611_ = lean_nat_dec_lt(v___x_1610_, v___x_1609_);
if (v___x_1611_ == 0)
{
lean_dec_ref(v_buckets_1608_);
lean_dec(v_f_1604_);
return v_init_1605_;
}
else
{
lean_object* v___f_1612_; lean_object* v___f_1613_; size_t v___x_1614_; size_t v___x_1615_; lean_object* v___x_1616_; 
v___f_1612_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1612_, 0, v_f_1604_);
v___f_1613_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1613_, 0, v___x_1607_);
lean_closure_set(v___f_1613_, 1, v___f_1612_);
v___x_1614_ = lean_usize_of_nat(v___x_1609_);
v___x_1615_ = ((size_t)0ULL);
v___x_1616_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1607_, v___f_1613_, v_buckets_1608_, v___x_1614_, v___x_1615_, v_init_1605_);
return v___x_1616_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevM___redArg(lean_object* v_inst_1617_, lean_object* v_f_1618_, lean_object* v_init_1619_, lean_object* v_b_1620_){
_start:
{
lean_object* v_toApplicative_1621_; lean_object* v_buckets_1622_; lean_object* v_toPure_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; uint8_t v___x_1626_; 
v_toApplicative_1621_ = lean_ctor_get(v_inst_1617_, 0);
v_buckets_1622_ = lean_ctor_get(v_b_1620_, 1);
lean_inc_ref(v_buckets_1622_);
lean_dec_ref(v_b_1620_);
v_toPure_1623_ = lean_ctor_get(v_toApplicative_1621_, 1);
v___x_1624_ = lean_array_get_size(v_buckets_1622_);
v___x_1625_ = lean_unsigned_to_nat(0u);
v___x_1626_ = lean_nat_dec_lt(v___x_1625_, v___x_1624_);
if (v___x_1626_ == 0)
{
lean_object* v___x_1627_; 
lean_inc(v_toPure_1623_);
lean_dec_ref(v_buckets_1622_);
lean_dec(v_f_1618_);
lean_dec_ref(v_inst_1617_);
v___x_1627_ = lean_apply_2(v_toPure_1623_, lean_box(0), v_init_1619_);
return v___x_1627_;
}
else
{
lean_object* v___f_1628_; lean_object* v___f_1629_; size_t v___x_1630_; size_t v___x_1631_; lean_object* v___x_1632_; 
v___f_1628_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1628_, 0, v_f_1618_);
lean_inc_ref(v_inst_1617_);
v___f_1629_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1629_, 0, v_inst_1617_);
lean_closure_set(v___f_1629_, 1, v___f_1628_);
v___x_1630_ = lean_usize_of_nat(v___x_1624_);
v___x_1631_ = ((size_t)0ULL);
v___x_1632_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1617_, v___f_1629_, v_buckets_1622_, v___x_1630_, v___x_1631_, v_init_1619_);
return v___x_1632_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevM(lean_object* v_00_u03b1_1633_, lean_object* v_00_u03b2_1634_, lean_object* v_00_u03b4_1635_, lean_object* v_m_1636_, lean_object* v_inst_1637_, lean_object* v_f_1638_, lean_object* v_init_1639_, lean_object* v_b_1640_){
_start:
{
lean_object* v_toApplicative_1641_; lean_object* v_buckets_1642_; lean_object* v_toPure_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; uint8_t v___x_1646_; 
v_toApplicative_1641_ = lean_ctor_get(v_inst_1637_, 0);
v_buckets_1642_ = lean_ctor_get(v_b_1640_, 1);
lean_inc_ref(v_buckets_1642_);
lean_dec_ref(v_b_1640_);
v_toPure_1643_ = lean_ctor_get(v_toApplicative_1641_, 1);
v___x_1644_ = lean_array_get_size(v_buckets_1642_);
v___x_1645_ = lean_unsigned_to_nat(0u);
v___x_1646_ = lean_nat_dec_lt(v___x_1645_, v___x_1644_);
if (v___x_1646_ == 0)
{
lean_object* v___x_1647_; 
lean_inc(v_toPure_1643_);
lean_dec_ref(v_buckets_1642_);
lean_dec(v_f_1638_);
lean_dec_ref(v_inst_1637_);
v___x_1647_ = lean_apply_2(v_toPure_1643_, lean_box(0), v_init_1639_);
return v___x_1647_;
}
else
{
lean_object* v___f_1648_; lean_object* v___f_1649_; size_t v___x_1650_; size_t v___x_1651_; lean_object* v___x_1652_; 
v___f_1648_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1648_, 0, v_f_1638_);
lean_inc_ref(v_inst_1637_);
v___f_1649_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1649_, 0, v_inst_1637_);
lean_closure_set(v___f_1649_, 1, v___f_1648_);
v___x_1650_ = lean_usize_of_nat(v___x_1644_);
v___x_1651_ = ((size_t)0ULL);
v___x_1652_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1637_, v___f_1649_, v_buckets_1642_, v___x_1650_, v___x_1651_, v_init_1639_);
return v___x_1652_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRev___redArg(lean_object* v_f_1653_, lean_object* v_init_1654_, lean_object* v_b_1655_){
_start:
{
lean_object* v___x_1656_; lean_object* v_buckets_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; uint8_t v___x_1660_; 
v___x_1656_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_1657_ = lean_ctor_get(v_b_1655_, 1);
lean_inc_ref(v_buckets_1657_);
lean_dec_ref(v_b_1655_);
v___x_1658_ = lean_array_get_size(v_buckets_1657_);
v___x_1659_ = lean_unsigned_to_nat(0u);
v___x_1660_ = lean_nat_dec_lt(v___x_1659_, v___x_1658_);
if (v___x_1660_ == 0)
{
lean_dec_ref(v_buckets_1657_);
lean_dec(v_f_1653_);
return v_init_1654_;
}
else
{
lean_object* v___f_1661_; lean_object* v___f_1662_; size_t v___x_1663_; size_t v___x_1664_; lean_object* v___x_1665_; 
v___f_1661_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1661_, 0, v_f_1653_);
v___f_1662_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1662_, 0, v___x_1656_);
lean_closure_set(v___f_1662_, 1, v___f_1661_);
v___x_1663_ = lean_usize_of_nat(v___x_1658_);
v___x_1664_ = ((size_t)0ULL);
v___x_1665_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1656_, v___f_1662_, v_buckets_1657_, v___x_1663_, v___x_1664_, v_init_1654_);
return v___x_1665_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRev(lean_object* v_00_u03b1_1666_, lean_object* v_00_u03b2_1667_, lean_object* v_00_u03b4_1668_, lean_object* v_f_1669_, lean_object* v_init_1670_, lean_object* v_b_1671_){
_start:
{
lean_object* v___x_1672_; lean_object* v_buckets_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; uint8_t v___x_1676_; 
v___x_1672_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_1673_ = lean_ctor_get(v_b_1671_, 1);
lean_inc_ref(v_buckets_1673_);
lean_dec_ref(v_b_1671_);
v___x_1674_ = lean_array_get_size(v_buckets_1673_);
v___x_1675_ = lean_unsigned_to_nat(0u);
v___x_1676_ = lean_nat_dec_lt(v___x_1675_, v___x_1674_);
if (v___x_1676_ == 0)
{
lean_dec_ref(v_buckets_1673_);
lean_dec(v_f_1669_);
return v_init_1670_;
}
else
{
lean_object* v___f_1677_; lean_object* v___f_1678_; size_t v___x_1679_; size_t v___x_1680_; lean_object* v___x_1681_; 
v___f_1677_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1677_, 0, v_f_1669_);
v___f_1678_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1678_, 0, v___x_1672_);
lean_closure_set(v___f_1678_, 1, v___f_1677_);
v___x_1679_ = lean_usize_of_nat(v___x_1674_);
v___x_1680_ = ((size_t)0ULL);
v___x_1681_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1672_, v___f_1678_, v_buckets_1673_, v___x_1679_, v___x_1680_, v_init_1670_);
return v___x_1681_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__0(lean_object* v_f_1682_, lean_object* v_x_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1686_, 0, v___y_1684_);
lean_ctor_set(v___x_1686_, 1, v___y_1685_);
v___x_1687_ = lean_apply_1(v_f_1682_, v___x_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__1(lean_object* v_inst_1688_, lean_object* v___f_1689_, lean_object* v_x_1690_, lean_object* v___y_1691_){
_start:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1692_ = lean_box(0);
v___x_1693_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_1688_, v___f_1689_, v___x_1692_, v___y_1691_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forMUncurried___redArg(lean_object* v_inst_1694_, lean_object* v_f_1695_, lean_object* v_b_1696_){
_start:
{
lean_object* v_toApplicative_1697_; lean_object* v_buckets_1698_; lean_object* v_toPure_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; uint8_t v___x_1703_; 
v_toApplicative_1697_ = lean_ctor_get(v_inst_1694_, 0);
v_buckets_1698_ = lean_ctor_get(v_b_1696_, 1);
lean_inc_ref(v_buckets_1698_);
lean_dec_ref(v_b_1696_);
v_toPure_1699_ = lean_ctor_get(v_toApplicative_1697_, 1);
v___x_1700_ = lean_unsigned_to_nat(0u);
v___x_1701_ = lean_array_get_size(v_buckets_1698_);
v___x_1702_ = lean_box(0);
v___x_1703_ = lean_nat_dec_lt(v___x_1700_, v___x_1701_);
if (v___x_1703_ == 0)
{
lean_object* v___x_1704_; 
lean_inc(v_toPure_1699_);
lean_dec_ref(v_buckets_1698_);
lean_dec(v_f_1695_);
lean_dec_ref(v_inst_1694_);
v___x_1704_ = lean_apply_2(v_toPure_1699_, lean_box(0), v___x_1702_);
return v___x_1704_;
}
else
{
lean_object* v___f_1705_; lean_object* v___f_1706_; size_t v___x_1707_; size_t v___x_1708_; lean_object* v___x_1709_; 
v___f_1705_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1705_, 0, v_f_1695_);
lean_inc_ref(v_inst_1694_);
v___f_1706_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1706_, 0, v_inst_1694_);
lean_closure_set(v___f_1706_, 1, v___f_1705_);
v___x_1707_ = ((size_t)0ULL);
v___x_1708_ = lean_usize_of_nat(v___x_1701_);
v___x_1709_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1694_, v___f_1706_, v_buckets_1698_, v___x_1707_, v___x_1708_, v___x_1702_);
return v___x_1709_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forMUncurried(lean_object* v_00_u03b1_1710_, lean_object* v_m_1711_, lean_object* v_inst_1712_, lean_object* v_00_u03b2_1713_, lean_object* v_f_1714_, lean_object* v_b_1715_){
_start:
{
lean_object* v_toApplicative_1716_; lean_object* v_buckets_1717_; lean_object* v_toPure_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; uint8_t v___x_1722_; 
v_toApplicative_1716_ = lean_ctor_get(v_inst_1712_, 0);
v_buckets_1717_ = lean_ctor_get(v_b_1715_, 1);
lean_inc_ref(v_buckets_1717_);
lean_dec_ref(v_b_1715_);
v_toPure_1718_ = lean_ctor_get(v_toApplicative_1716_, 1);
v___x_1719_ = lean_unsigned_to_nat(0u);
v___x_1720_ = lean_array_get_size(v_buckets_1717_);
v___x_1721_ = lean_box(0);
v___x_1722_ = lean_nat_dec_lt(v___x_1719_, v___x_1720_);
if (v___x_1722_ == 0)
{
lean_object* v___x_1723_; 
lean_inc(v_toPure_1718_);
lean_dec_ref(v_buckets_1717_);
lean_dec(v_f_1714_);
lean_dec_ref(v_inst_1712_);
v___x_1723_ = lean_apply_2(v_toPure_1718_, lean_box(0), v___x_1721_);
return v___x_1723_;
}
else
{
lean_object* v___f_1724_; lean_object* v___f_1725_; size_t v___x_1726_; size_t v___x_1727_; lean_object* v___x_1728_; 
v___f_1724_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1724_, 0, v_f_1714_);
lean_inc_ref(v_inst_1712_);
v___f_1725_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1725_, 0, v_inst_1712_);
lean_closure_set(v___f_1725_, 1, v___f_1724_);
v___x_1726_ = ((size_t)0ULL);
v___x_1727_ = lean_usize_of_nat(v___x_1720_);
v___x_1728_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1712_, v___f_1725_, v_buckets_1717_, v___x_1726_, v___x_1727_, v___x_1721_);
return v___x_1728_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__0(lean_object* v_f_1729_, lean_object* v_a_1730_, lean_object* v_b_1731_, lean_object* v_d_1732_){
_start:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1733_, 0, v_a_1730_);
lean_ctor_set(v___x_1733_, 1, v_b_1731_);
v___x_1734_ = lean_apply_2(v_f_1729_, v___x_1733_, v_d_1732_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__1(lean_object* v_inst_1735_, lean_object* v___f_1736_, lean_object* v_a_1737_, lean_object* v_x_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_1735_, v___f_1736_, v_a_1737_, v___y_1739_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forInUncurried___redArg(lean_object* v_inst_1741_, lean_object* v_f_1742_, lean_object* v_init_1743_, lean_object* v_b_1744_){
_start:
{
lean_object* v_buckets_1745_; lean_object* v___f_1746_; lean_object* v___f_1747_; size_t v_sz_1748_; size_t v___x_1749_; lean_object* v___x_1750_; 
v_buckets_1745_ = lean_ctor_get(v_b_1744_, 1);
lean_inc_ref(v_buckets_1745_);
lean_dec_ref(v_b_1744_);
v___f_1746_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1746_, 0, v_f_1742_);
lean_inc_ref(v_inst_1741_);
v___f_1747_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1747_, 0, v_inst_1741_);
lean_closure_set(v___f_1747_, 1, v___f_1746_);
v_sz_1748_ = lean_array_size(v_buckets_1745_);
v___x_1749_ = ((size_t)0ULL);
v___x_1750_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1741_, v_buckets_1745_, v___f_1747_, v_sz_1748_, v___x_1749_, v_init_1743_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forInUncurried(lean_object* v_00_u03b1_1751_, lean_object* v_00_u03b4_1752_, lean_object* v_m_1753_, lean_object* v_inst_1754_, lean_object* v_00_u03b2_1755_, lean_object* v_f_1756_, lean_object* v_init_1757_, lean_object* v_b_1758_){
_start:
{
lean_object* v_buckets_1759_; lean_object* v___f_1760_; lean_object* v___f_1761_; size_t v_sz_1762_; size_t v___x_1763_; lean_object* v___x_1764_; 
v_buckets_1759_ = lean_ctor_get(v_b_1758_, 1);
lean_inc_ref(v_buckets_1759_);
lean_dec_ref(v_b_1758_);
v___f_1760_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1760_, 0, v_f_1756_);
lean_inc_ref(v_inst_1754_);
v___f_1761_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1761_, 0, v_inst_1754_);
lean_closure_set(v___f_1761_, 1, v___f_1760_);
v_sz_1762_ = lean_array_size(v_buckets_1759_);
v___x_1763_ = ((size_t)0ULL);
v___x_1764_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1754_, v_buckets_1759_, v___f_1761_, v_sz_1762_, v___x_1763_, v_init_1757_);
return v___x_1764_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_filterMap___redArg(lean_object* v_f_1765_, lean_object* v_m_1766_){
_start:
{
lean_object* v_buckets_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; uint8_t v___x_1770_; 
v_buckets_1767_ = lean_ctor_get(v_m_1766_, 1);
v___x_1768_ = lean_unsigned_to_nat(0u);
v___x_1769_ = lean_array_get_size(v_buckets_1767_);
v___x_1770_ = lean_nat_dec_lt(v___x_1768_, v___x_1769_);
if (v___x_1770_ == 0)
{
lean_object* v___x_1771_; 
lean_dec_ref(v_m_1766_);
lean_dec_ref(v_f_1765_);
v___x_1771_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1771_;
}
else
{
lean_object* v___x_1772_; 
v___x_1772_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_1765_, v_m_1766_);
return v___x_1772_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_filterMap(lean_object* v_00_u03b1_1773_, lean_object* v_00_u03b2_1774_, lean_object* v_00_u03b3_1775_, lean_object* v_f_1776_, lean_object* v_m_1777_){
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
v___x_1782_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1782_;
}
else
{
lean_object* v___x_1783_; 
v___x_1783_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_1776_, v_m_1777_);
return v___x_1783_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_map___redArg(lean_object* v_f_1784_, lean_object* v_m_1785_){
_start:
{
lean_object* v_buckets_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; uint8_t v___x_1789_; 
v_buckets_1786_ = lean_ctor_get(v_m_1785_, 1);
v___x_1787_ = lean_unsigned_to_nat(0u);
v___x_1788_ = lean_array_get_size(v_buckets_1786_);
v___x_1789_ = lean_nat_dec_lt(v___x_1787_, v___x_1788_);
if (v___x_1789_ == 0)
{
lean_object* v___x_1790_; 
lean_dec_ref(v_m_1785_);
lean_dec(v_f_1784_);
v___x_1790_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1790_;
}
else
{
lean_object* v___x_1791_; 
v___x_1791_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_1784_, v_m_1785_);
return v___x_1791_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_map(lean_object* v_00_u03b1_1792_, lean_object* v_00_u03b2_1793_, lean_object* v_00_u03b3_1794_, lean_object* v_f_1795_, lean_object* v_m_1796_){
_start:
{
lean_object* v_buckets_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; uint8_t v___x_1800_; 
v_buckets_1797_ = lean_ctor_get(v_m_1796_, 1);
v___x_1798_ = lean_unsigned_to_nat(0u);
v___x_1799_ = lean_array_get_size(v_buckets_1797_);
v___x_1800_ = lean_nat_dec_lt(v___x_1798_, v___x_1799_);
if (v___x_1800_ == 0)
{
lean_object* v___x_1801_; 
lean_dec_ref(v_m_1796_);
lean_dec(v_f_1795_);
v___x_1801_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1801_;
}
else
{
lean_object* v___x_1802_; 
v___x_1802_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_1795_, v_m_1796_);
return v___x_1802_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_filter___redArg(lean_object* v_f_1803_, lean_object* v_m_1804_){
_start:
{
lean_object* v_buckets_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; uint8_t v___x_1808_; 
v_buckets_1805_ = lean_ctor_get(v_m_1804_, 1);
v___x_1806_ = lean_unsigned_to_nat(0u);
v___x_1807_ = lean_array_get_size(v_buckets_1805_);
v___x_1808_ = lean_nat_dec_lt(v___x_1806_, v___x_1807_);
if (v___x_1808_ == 0)
{
lean_object* v___x_1809_; 
lean_dec_ref(v_m_1804_);
lean_dec_ref(v_f_1803_);
v___x_1809_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1809_;
}
else
{
lean_object* v___x_1810_; 
v___x_1810_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1803_, v_m_1804_);
return v___x_1810_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_filter(lean_object* v_00_u03b1_1811_, lean_object* v_00_u03b2_1812_, lean_object* v_f_1813_, lean_object* v_m_1814_){
_start:
{
lean_object* v_buckets_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; uint8_t v___x_1818_; 
v_buckets_1815_ = lean_ctor_get(v_m_1814_, 1);
v___x_1816_ = lean_unsigned_to_nat(0u);
v___x_1817_ = lean_array_get_size(v_buckets_1815_);
v___x_1818_ = lean_nat_dec_lt(v___x_1816_, v___x_1817_);
if (v___x_1818_ == 0)
{
lean_object* v___x_1819_; 
lean_dec_ref(v_m_1814_);
lean_dec_ref(v_f_1813_);
v___x_1819_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1819_;
}
else
{
lean_object* v___x_1820_; 
v___x_1820_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1813_, v_m_1814_);
return v___x_1820_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toArray___redArg___lam__0(lean_object* v_x1_1821_, lean_object* v_x2_1822_, lean_object* v_x3_1823_){
_start:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1824_, 0, v_x2_1822_);
lean_ctor_set(v___x_1824_, 1, v_x3_1823_);
v___x_1825_ = lean_array_push(v_x1_1821_, v___x_1824_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toArray___redArg___lam__1(lean_object* v___x_1826_, lean_object* v___f_1827_, lean_object* v_acc_1828_, lean_object* v_l_1829_){
_start:
{
lean_object* v___x_1830_; 
v___x_1830_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1826_, v___f_1827_, v_acc_1828_, v_l_1829_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toArray___redArg(lean_object* v_m_1835_){
_start:
{
lean_object* v_size_1836_; lean_object* v_buckets_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; uint8_t v___x_1842_; 
v_size_1836_ = lean_ctor_get(v_m_1835_, 0);
lean_inc(v_size_1836_);
v_buckets_1837_ = lean_ctor_get(v_m_1835_, 1);
lean_inc_ref(v_buckets_1837_);
lean_dec_ref(v_m_1835_);
v___x_1838_ = lean_mk_empty_array_with_capacity(v_size_1836_);
lean_dec(v_size_1836_);
v___x_1839_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_1840_ = lean_unsigned_to_nat(0u);
v___x_1841_ = lean_array_get_size(v_buckets_1837_);
v___x_1842_ = lean_nat_dec_lt(v___x_1840_, v___x_1841_);
if (v___x_1842_ == 0)
{
lean_dec_ref(v_buckets_1837_);
return v___x_1838_;
}
else
{
lean_object* v___f_1843_; size_t v___x_1844_; size_t v___x_1845_; lean_object* v___x_1846_; 
v___f_1843_ = ((lean_object*)(l_Std_DHashMap_Raw_toArray___redArg___closed__1));
v___x_1844_ = ((size_t)0ULL);
v___x_1845_ = lean_usize_of_nat(v___x_1841_);
v___x_1846_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1839_, v___f_1843_, v_buckets_1837_, v___x_1844_, v___x_1845_, v___x_1838_);
return v___x_1846_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toArray(lean_object* v_00_u03b1_1847_, lean_object* v_00_u03b2_1848_, lean_object* v_m_1849_){
_start:
{
lean_object* v_size_1850_; lean_object* v_buckets_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; uint8_t v___x_1856_; 
v_size_1850_ = lean_ctor_get(v_m_1849_, 0);
lean_inc(v_size_1850_);
v_buckets_1851_ = lean_ctor_get(v_m_1849_, 1);
lean_inc_ref(v_buckets_1851_);
lean_dec_ref(v_m_1849_);
v___x_1852_ = lean_mk_empty_array_with_capacity(v_size_1850_);
lean_dec(v_size_1850_);
v___x_1853_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_1854_ = lean_unsigned_to_nat(0u);
v___x_1855_ = lean_array_get_size(v_buckets_1851_);
v___x_1856_ = lean_nat_dec_lt(v___x_1854_, v___x_1855_);
if (v___x_1856_ == 0)
{
lean_dec_ref(v_buckets_1851_);
return v___x_1852_;
}
else
{
lean_object* v___f_1857_; size_t v___x_1858_; size_t v___x_1859_; lean_object* v___x_1860_; 
v___f_1857_ = ((lean_object*)(l_Std_DHashMap_Raw_toArray___redArg___closed__1));
v___x_1858_ = ((size_t)0ULL);
v___x_1859_ = lean_usize_of_nat(v___x_1855_);
v___x_1860_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1853_, v___f_1857_, v_buckets_1851_, v___x_1858_, v___x_1859_, v___x_1852_);
return v___x_1860_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toArray___redArg___lam__0(lean_object* v_x1_1861_, lean_object* v_x2_1862_, lean_object* v_x3_1863_){
_start:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1864_, 0, v_x2_1862_);
lean_ctor_set(v___x_1864_, 1, v_x3_1863_);
v___x_1865_ = lean_array_push(v_x1_1861_, v___x_1864_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toArray___redArg___lam__1(lean_object* v___x_1866_, lean_object* v___f_1867_, lean_object* v_acc_1868_, lean_object* v_l_1869_){
_start:
{
lean_object* v___x_1870_; 
v___x_1870_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1866_, v___f_1867_, v_acc_1868_, v_l_1869_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toArray___redArg(lean_object* v_m_1875_){
_start:
{
lean_object* v_size_1876_; lean_object* v_buckets_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; uint8_t v___x_1882_; 
v_size_1876_ = lean_ctor_get(v_m_1875_, 0);
lean_inc(v_size_1876_);
v_buckets_1877_ = lean_ctor_get(v_m_1875_, 1);
lean_inc_ref(v_buckets_1877_);
lean_dec_ref(v_m_1875_);
v___x_1878_ = lean_mk_empty_array_with_capacity(v_size_1876_);
lean_dec(v_size_1876_);
v___x_1879_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_1880_ = lean_unsigned_to_nat(0u);
v___x_1881_ = lean_array_get_size(v_buckets_1877_);
v___x_1882_ = lean_nat_dec_lt(v___x_1880_, v___x_1881_);
if (v___x_1882_ == 0)
{
lean_dec_ref(v_buckets_1877_);
return v___x_1878_;
}
else
{
lean_object* v___f_1883_; size_t v___x_1884_; size_t v___x_1885_; lean_object* v___x_1886_; 
v___f_1883_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_toArray___redArg___closed__1));
v___x_1884_ = ((size_t)0ULL);
v___x_1885_ = lean_usize_of_nat(v___x_1881_);
v___x_1886_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1879_, v___f_1883_, v_buckets_1877_, v___x_1884_, v___x_1885_, v___x_1878_);
return v___x_1886_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toArray(lean_object* v_00_u03b1_1887_, lean_object* v_00_u03b2_1888_, lean_object* v_m_1889_){
_start:
{
lean_object* v_size_1890_; lean_object* v_buckets_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; uint8_t v___x_1896_; 
v_size_1890_ = lean_ctor_get(v_m_1889_, 0);
lean_inc(v_size_1890_);
v_buckets_1891_ = lean_ctor_get(v_m_1889_, 1);
lean_inc_ref(v_buckets_1891_);
lean_dec_ref(v_m_1889_);
v___x_1892_ = lean_mk_empty_array_with_capacity(v_size_1890_);
lean_dec(v_size_1890_);
v___x_1893_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_1894_ = lean_unsigned_to_nat(0u);
v___x_1895_ = lean_array_get_size(v_buckets_1891_);
v___x_1896_ = lean_nat_dec_lt(v___x_1894_, v___x_1895_);
if (v___x_1896_ == 0)
{
lean_dec_ref(v_buckets_1891_);
return v___x_1892_;
}
else
{
lean_object* v___f_1897_; size_t v___x_1898_; size_t v___x_1899_; lean_object* v___x_1900_; 
v___f_1897_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_toArray___redArg___closed__1));
v___x_1898_ = ((size_t)0ULL);
v___x_1899_ = lean_usize_of_nat(v___x_1895_);
v___x_1900_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1893_, v___f_1897_, v_buckets_1891_, v___x_1898_, v___x_1899_, v___x_1892_);
return v___x_1900_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keysArray___redArg___lam__0(lean_object* v_x1_1901_, lean_object* v_x2_1902_, lean_object* v_x3_1903_){
_start:
{
lean_object* v___x_1904_; 
v___x_1904_ = lean_array_push(v_x1_1901_, v_x2_1902_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keysArray___redArg___lam__0___boxed(lean_object* v_x1_1905_, lean_object* v_x2_1906_, lean_object* v_x3_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_Std_DHashMap_Raw_keysArray___redArg___lam__0(v_x1_1905_, v_x2_1906_, v_x3_1907_);
lean_dec(v_x3_1907_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keysArray___redArg___lam__1(lean_object* v___x_1909_, lean_object* v___f_1910_, lean_object* v_acc_1911_, lean_object* v_l_1912_){
_start:
{
lean_object* v___x_1913_; 
v___x_1913_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1909_, v___f_1910_, v_acc_1911_, v_l_1912_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keysArray___redArg(lean_object* v_m_1918_){
_start:
{
lean_object* v_size_1919_; lean_object* v_buckets_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; uint8_t v___x_1925_; 
v_size_1919_ = lean_ctor_get(v_m_1918_, 0);
lean_inc(v_size_1919_);
v_buckets_1920_ = lean_ctor_get(v_m_1918_, 1);
lean_inc_ref(v_buckets_1920_);
lean_dec_ref(v_m_1918_);
v___x_1921_ = lean_mk_empty_array_with_capacity(v_size_1919_);
lean_dec(v_size_1919_);
v___x_1922_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_1923_ = lean_unsigned_to_nat(0u);
v___x_1924_ = lean_array_get_size(v_buckets_1920_);
v___x_1925_ = lean_nat_dec_lt(v___x_1923_, v___x_1924_);
if (v___x_1925_ == 0)
{
lean_dec_ref(v_buckets_1920_);
return v___x_1921_;
}
else
{
lean_object* v___f_1926_; size_t v___x_1927_; size_t v___x_1928_; lean_object* v___x_1929_; 
v___f_1926_ = ((lean_object*)(l_Std_DHashMap_Raw_keysArray___redArg___closed__1));
v___x_1927_ = ((size_t)0ULL);
v___x_1928_ = lean_usize_of_nat(v___x_1924_);
v___x_1929_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1922_, v___f_1926_, v_buckets_1920_, v___x_1927_, v___x_1928_, v___x_1921_);
return v___x_1929_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keysArray(lean_object* v_00_u03b1_1930_, lean_object* v_00_u03b2_1931_, lean_object* v_m_1932_){
_start:
{
lean_object* v_size_1933_; lean_object* v_buckets_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; uint8_t v___x_1939_; 
v_size_1933_ = lean_ctor_get(v_m_1932_, 0);
lean_inc(v_size_1933_);
v_buckets_1934_ = lean_ctor_get(v_m_1932_, 1);
lean_inc_ref(v_buckets_1934_);
lean_dec_ref(v_m_1932_);
v___x_1935_ = lean_mk_empty_array_with_capacity(v_size_1933_);
lean_dec(v_size_1933_);
v___x_1936_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_1937_ = lean_unsigned_to_nat(0u);
v___x_1938_ = lean_array_get_size(v_buckets_1934_);
v___x_1939_ = lean_nat_dec_lt(v___x_1937_, v___x_1938_);
if (v___x_1939_ == 0)
{
lean_dec_ref(v_buckets_1934_);
return v___x_1935_;
}
else
{
lean_object* v___f_1940_; size_t v___x_1941_; size_t v___x_1942_; lean_object* v___x_1943_; 
v___f_1940_ = ((lean_object*)(l_Std_DHashMap_Raw_keysArray___redArg___closed__1));
v___x_1941_ = ((size_t)0ULL);
v___x_1942_ = lean_usize_of_nat(v___x_1938_);
v___x_1943_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1936_, v___f_1940_, v_buckets_1934_, v___x_1941_, v___x_1942_, v___x_1935_);
return v___x_1943_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_union___redArg___lam__0(lean_object* v_inst_1944_, lean_object* v_inst_1945_, lean_object* v_a_1946_, lean_object* v_b_1947_, lean_object* v_acc_1948_){
_start:
{
lean_object* v_r_1949_; lean_object* v___x_1950_; 
v_r_1949_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_1944_, v_inst_1945_, v_acc_1948_, v_a_1946_, v_b_1947_);
v___x_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1950_, 0, v_r_1949_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_union___redArg___lam__1(lean_object* v___x_1951_, lean_object* v___f_1952_, lean_object* v_a_1953_, lean_object* v_x_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v___x_1956_; 
v___x_1956_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1951_, v___f_1952_, v_a_1953_, v___y_1955_);
return v___x_1956_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_union___redArg(lean_object* v_inst_1959_, lean_object* v_inst_1960_, lean_object* v_m_u2081_1961_, lean_object* v_m_u2082_1962_){
_start:
{
lean_object* v_size_1963_; lean_object* v_buckets_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; uint8_t v___x_1967_; 
v_size_1963_ = lean_ctor_get(v_m_u2081_1961_, 0);
v_buckets_1964_ = lean_ctor_get(v_m_u2081_1961_, 1);
v___x_1965_ = lean_unsigned_to_nat(0u);
v___x_1966_ = lean_array_get_size(v_buckets_1964_);
v___x_1967_ = lean_nat_dec_lt(v___x_1965_, v___x_1966_);
if (v___x_1967_ == 0)
{
lean_dec_ref(v_m_u2081_1961_);
lean_dec_ref(v_inst_1960_);
lean_dec_ref(v_inst_1959_);
return v_m_u2082_1962_;
}
else
{
lean_object* v_size_1968_; lean_object* v_buckets_1969_; lean_object* v___x_1970_; uint8_t v___x_1971_; 
v_size_1968_ = lean_ctor_get(v_m_u2082_1962_, 0);
v_buckets_1969_ = lean_ctor_get(v_m_u2082_1962_, 1);
v___x_1970_ = lean_array_get_size(v_buckets_1969_);
v___x_1971_ = lean_nat_dec_lt(v___x_1965_, v___x_1970_);
if (v___x_1971_ == 0)
{
lean_dec_ref(v_m_u2082_1962_);
lean_dec_ref(v_inst_1960_);
lean_dec_ref(v_inst_1959_);
return v_m_u2081_1961_;
}
else
{
lean_object* v___x_1972_; uint8_t v___x_1973_; 
v___x_1972_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_1973_ = lean_nat_dec_le(v_size_1963_, v_size_1968_);
if (v___x_1973_ == 0)
{
lean_object* v___f_1974_; lean_object* v___x_1975_; 
v___f_1974_ = ((lean_object*)(l_Std_DHashMap_Raw_union___redArg___closed__0));
v___x_1975_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1974_, v_inst_1959_, v_inst_1960_, v_m_u2081_1961_, v_m_u2082_1962_);
return v___x_1975_;
}
else
{
lean_object* v___f_1976_; lean_object* v___f_1977_; size_t v_sz_1978_; size_t v___x_1979_; lean_object* v___x_1980_; 
lean_inc_ref(v_buckets_1964_);
lean_dec_ref(v_m_u2081_1961_);
v___f_1976_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1976_, 0, v_inst_1959_);
lean_closure_set(v___f_1976_, 1, v_inst_1960_);
v___f_1977_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1977_, 0, v___x_1972_);
lean_closure_set(v___f_1977_, 1, v___f_1976_);
v_sz_1978_ = lean_array_size(v_buckets_1964_);
v___x_1979_ = ((size_t)0ULL);
v___x_1980_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1972_, v_buckets_1964_, v___f_1977_, v_sz_1978_, v___x_1979_, v_m_u2082_1962_);
return v___x_1980_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_union(lean_object* v_00_u03b1_1981_, lean_object* v_00_u03b2_1982_, lean_object* v_inst_1983_, lean_object* v_inst_1984_, lean_object* v_m_u2081_1985_, lean_object* v_m_u2082_1986_){
_start:
{
lean_object* v_size_1987_; lean_object* v_buckets_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; uint8_t v___x_1991_; 
v_size_1987_ = lean_ctor_get(v_m_u2081_1985_, 0);
v_buckets_1988_ = lean_ctor_get(v_m_u2081_1985_, 1);
v___x_1989_ = lean_unsigned_to_nat(0u);
v___x_1990_ = lean_array_get_size(v_buckets_1988_);
v___x_1991_ = lean_nat_dec_lt(v___x_1989_, v___x_1990_);
if (v___x_1991_ == 0)
{
lean_dec_ref(v_m_u2081_1985_);
lean_dec_ref(v_inst_1984_);
lean_dec_ref(v_inst_1983_);
return v_m_u2082_1986_;
}
else
{
lean_object* v_size_1992_; lean_object* v_buckets_1993_; lean_object* v___x_1994_; uint8_t v___x_1995_; 
v_size_1992_ = lean_ctor_get(v_m_u2082_1986_, 0);
v_buckets_1993_ = lean_ctor_get(v_m_u2082_1986_, 1);
v___x_1994_ = lean_array_get_size(v_buckets_1993_);
v___x_1995_ = lean_nat_dec_lt(v___x_1989_, v___x_1994_);
if (v___x_1995_ == 0)
{
lean_dec_ref(v_m_u2082_1986_);
lean_dec_ref(v_inst_1984_);
lean_dec_ref(v_inst_1983_);
return v_m_u2081_1985_;
}
else
{
lean_object* v___x_1996_; uint8_t v___x_1997_; 
v___x_1996_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_1997_ = lean_nat_dec_le(v_size_1987_, v_size_1992_);
if (v___x_1997_ == 0)
{
lean_object* v___f_1998_; lean_object* v___x_1999_; 
v___f_1998_ = ((lean_object*)(l_Std_DHashMap_Raw_union___redArg___closed__0));
v___x_1999_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1998_, v_inst_1983_, v_inst_1984_, v_m_u2081_1985_, v_m_u2082_1986_);
return v___x_1999_;
}
else
{
lean_object* v___f_2000_; lean_object* v___f_2001_; size_t v_sz_2002_; size_t v___x_2003_; lean_object* v___x_2004_; 
lean_inc_ref(v_buckets_1988_);
lean_dec_ref(v_m_u2081_1985_);
v___f_2000_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_2000_, 0, v_inst_1983_);
lean_closure_set(v___f_2000_, 1, v_inst_1984_);
v___f_2001_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_2001_, 0, v___x_1996_);
lean_closure_set(v___f_2001_, 1, v___f_2000_);
v_sz_2002_ = lean_array_size(v_buckets_1988_);
v___x_2003_ = ((size_t)0ULL);
v___x_2004_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1996_, v_buckets_1988_, v___f_2001_, v_sz_2002_, v___x_2003_, v_m_u2082_1986_);
return v___x_2004_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instUnionOfBEqOfHashable___redArg(lean_object* v_inst_2005_, lean_object* v_inst_2006_){
_start:
{
lean_object* v___x_2007_; 
v___x_2007_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_union), 6, 4);
lean_closure_set(v___x_2007_, 0, lean_box(0));
lean_closure_set(v___x_2007_, 1, lean_box(0));
lean_closure_set(v___x_2007_, 2, v_inst_2005_);
lean_closure_set(v___x_2007_, 3, v_inst_2006_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instUnionOfBEqOfHashable(lean_object* v_00_u03b1_2008_, lean_object* v_00_u03b2_2009_, lean_object* v_inst_2010_, lean_object* v_inst_2011_){
_start:
{
lean_object* v___x_2012_; 
v___x_2012_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_union), 6, 4);
lean_closure_set(v___x_2012_, 0, lean_box(0));
lean_closure_set(v___x_2012_, 1, lean_box(0));
lean_closure_set(v___x_2012_, 2, v_inst_2010_);
lean_closure_set(v___x_2012_, 3, v_inst_2011_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_inter___redArg(lean_object* v_inst_2013_, lean_object* v_inst_2014_, lean_object* v_m_u2081_2015_, lean_object* v_m_u2082_2016_){
_start:
{
lean_object* v_buckets_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; uint8_t v___x_2020_; 
v_buckets_2017_ = lean_ctor_get(v_m_u2081_2015_, 1);
v___x_2018_ = lean_unsigned_to_nat(0u);
v___x_2019_ = lean_array_get_size(v_buckets_2017_);
v___x_2020_ = lean_nat_dec_lt(v___x_2018_, v___x_2019_);
if (v___x_2020_ == 0)
{
lean_dec_ref(v_m_u2081_2015_);
lean_dec_ref(v_inst_2014_);
lean_dec_ref(v_inst_2013_);
return v_m_u2082_2016_;
}
else
{
lean_object* v_buckets_2021_; lean_object* v___x_2022_; uint8_t v___x_2023_; 
v_buckets_2021_ = lean_ctor_get(v_m_u2082_2016_, 1);
v___x_2022_ = lean_array_get_size(v_buckets_2021_);
v___x_2023_ = lean_nat_dec_lt(v___x_2018_, v___x_2022_);
if (v___x_2023_ == 0)
{
lean_dec_ref(v_m_u2082_2016_);
lean_dec_ref(v_inst_2014_);
lean_dec_ref(v_inst_2013_);
return v_m_u2081_2015_;
}
else
{
lean_object* v___x_2024_; 
v___x_2024_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_2013_, v_inst_2014_, v_m_u2081_2015_, v_m_u2082_2016_);
return v___x_2024_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_inter(lean_object* v_00_u03b1_2025_, lean_object* v_00_u03b2_2026_, lean_object* v_inst_2027_, lean_object* v_inst_2028_, lean_object* v_m_u2081_2029_, lean_object* v_m_u2082_2030_){
_start:
{
lean_object* v_buckets_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; uint8_t v___x_2034_; 
v_buckets_2031_ = lean_ctor_get(v_m_u2081_2029_, 1);
v___x_2032_ = lean_unsigned_to_nat(0u);
v___x_2033_ = lean_array_get_size(v_buckets_2031_);
v___x_2034_ = lean_nat_dec_lt(v___x_2032_, v___x_2033_);
if (v___x_2034_ == 0)
{
lean_dec_ref(v_m_u2081_2029_);
lean_dec_ref(v_inst_2028_);
lean_dec_ref(v_inst_2027_);
return v_m_u2082_2030_;
}
else
{
lean_object* v_buckets_2035_; lean_object* v___x_2036_; uint8_t v___x_2037_; 
v_buckets_2035_ = lean_ctor_get(v_m_u2082_2030_, 1);
v___x_2036_ = lean_array_get_size(v_buckets_2035_);
v___x_2037_ = lean_nat_dec_lt(v___x_2032_, v___x_2036_);
if (v___x_2037_ == 0)
{
lean_dec_ref(v_m_u2082_2030_);
lean_dec_ref(v_inst_2028_);
lean_dec_ref(v_inst_2027_);
return v_m_u2081_2029_;
}
else
{
lean_object* v___x_2038_; 
v___x_2038_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_2027_, v_inst_2028_, v_m_u2081_2029_, v_m_u2082_2030_);
return v___x_2038_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInterOfBEqOfHashable___redArg(lean_object* v_inst_2039_, lean_object* v_inst_2040_){
_start:
{
lean_object* v___x_2041_; 
v___x_2041_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_inter), 6, 4);
lean_closure_set(v___x_2041_, 0, lean_box(0));
lean_closure_set(v___x_2041_, 1, lean_box(0));
lean_closure_set(v___x_2041_, 2, v_inst_2039_);
lean_closure_set(v___x_2041_, 3, v_inst_2040_);
return v___x_2041_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInterOfBEqOfHashable(lean_object* v_00_u03b1_2042_, lean_object* v_00_u03b2_2043_, lean_object* v_inst_2044_, lean_object* v_inst_2045_){
_start:
{
lean_object* v___x_2046_; 
v___x_2046_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_inter), 6, 4);
lean_closure_set(v___x_2046_, 0, lean_box(0));
lean_closure_set(v___x_2046_, 1, lean_box(0));
lean_closure_set(v___x_2046_, 2, v_inst_2044_);
lean_closure_set(v___x_2046_, 3, v_inst_2045_);
return v___x_2046_;
}
}
uint8_t l_Std_DHashMap_Raw_beq___redArg(lean_object* v_inst_2047_, lean_object* v_inst_2048_, lean_object* v_inst_2049_, lean_object* v_m_u2081_2050_, lean_object* v_m_u2082_2051_){
_start:
{
lean_object* v_buckets_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; uint8_t v___x_2055_; 
v_buckets_2052_ = lean_ctor_get(v_m_u2081_2050_, 1);
v___x_2053_ = lean_unsigned_to_nat(0u);
v___x_2054_ = lean_array_get_size(v_buckets_2052_);
v___x_2055_ = lean_nat_dec_lt(v___x_2053_, v___x_2054_);
if (v___x_2055_ == 0)
{
lean_dec_ref(v_m_u2082_2051_);
lean_dec_ref(v_m_u2081_2050_);
lean_dec_ref(v_inst_2049_);
lean_dec_ref(v_inst_2048_);
lean_dec_ref(v_inst_2047_);
return v___x_2055_;
}
else
{
lean_object* v_buckets_2056_; lean_object* v___x_2057_; uint8_t v___x_2058_; 
v_buckets_2056_ = lean_ctor_get(v_m_u2082_2051_, 1);
v___x_2057_ = lean_array_get_size(v_buckets_2056_);
v___x_2058_ = lean_nat_dec_lt(v___x_2053_, v___x_2057_);
if (v___x_2058_ == 0)
{
lean_dec_ref(v_m_u2082_2051_);
lean_dec_ref(v_m_u2081_2050_);
lean_dec_ref(v_inst_2049_);
lean_dec_ref(v_inst_2048_);
lean_dec_ref(v_inst_2047_);
return v___x_2058_;
}
else
{
uint8_t v___x_2059_; 
v___x_2059_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(v_inst_2047_, v_inst_2048_, v_inst_2049_, v_m_u2081_2050_, v_m_u2082_2051_);
return v___x_2059_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Raw_beq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2047_ = stack[0].m_obj;
lean_object* v_inst_2048_ = stack[1].m_obj;
lean_object* v_inst_2049_ = stack[2].m_obj;
lean_object* v_m_u2081_2050_ = stack[3].m_obj;
lean_object* v_m_u2082_2051_ = stack[4].m_obj;
uint8_t v_res_2060_;
v_res_2060_ = l_Std_DHashMap_Raw_beq___redArg(v_inst_2047_, v_inst_2048_, v_inst_2049_, v_m_u2081_2050_, v_m_u2082_2051_);
stack->m_num = v_res_2060_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_beq___redArg___boxed(lean_object* v_inst_2061_, lean_object* v_inst_2062_, lean_object* v_inst_2063_, lean_object* v_m_u2081_2064_, lean_object* v_m_u2082_2065_){
_start:
{
uint8_t v_res_2066_; lean_object* v_r_2067_; 
v_res_2066_ = l_Std_DHashMap_Raw_beq___redArg(v_inst_2061_, v_inst_2062_, v_inst_2063_, v_m_u2081_2064_, v_m_u2082_2065_);
v_r_2067_ = lean_box(v_res_2066_);
return v_r_2067_;
}
}
uint8_t l_Std_DHashMap_Raw_beq(lean_object* v_00_u03b1_2068_, lean_object* v_00_u03b2_2069_, lean_object* v_inst_2070_, lean_object* v_inst_2071_, lean_object* v_inst_2072_, lean_object* v_inst_2073_, lean_object* v_m_u2081_2074_, lean_object* v_m_u2082_2075_){
_start:
{
uint8_t v___x_2076_; 
v___x_2076_ = l_Std_DHashMap_Raw_beq___redArg(v_inst_2070_, v_inst_2071_, v_inst_2073_, v_m_u2081_2074_, v_m_u2082_2075_);
return v___x_2076_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Raw_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2070_ = stack[2].m_obj;
lean_object* v_inst_2071_ = stack[3].m_obj;
lean_object* v_inst_2073_ = stack[5].m_obj;
lean_object* v_m_u2081_2074_ = stack[6].m_obj;
lean_object* v_m_u2082_2075_ = stack[7].m_obj;
uint8_t v_res_2077_;
v_res_2077_ = l_Std_DHashMap_Raw_beq(lean_box(0), lean_box(0), v_inst_2070_, v_inst_2071_, lean_box(0), v_inst_2073_, v_m_u2081_2074_, v_m_u2082_2075_);
stack->m_num = v_res_2077_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_beq___boxed(lean_object* v_00_u03b1_2078_, lean_object* v_00_u03b2_2079_, lean_object* v_inst_2080_, lean_object* v_inst_2081_, lean_object* v_inst_2082_, lean_object* v_inst_2083_, lean_object* v_m_u2081_2084_, lean_object* v_m_u2082_2085_){
_start:
{
uint8_t v_res_2086_; lean_object* v_r_2087_; 
v_res_2086_ = l_Std_DHashMap_Raw_beq(v_00_u03b1_2078_, v_00_u03b2_2079_, v_inst_2080_, v_inst_2081_, v_inst_2082_, v_inst_2083_, v_m_u2081_2084_, v_m_u2082_2085_);
v_r_2087_ = lean_box(v_res_2086_);
return v_r_2087_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instBEqOfHashableOfLawfulBEq___redArg(lean_object* v_inst_2088_, lean_object* v_inst_2089_, lean_object* v_inst_2090_){
_start:
{
lean_object* v___x_2091_; 
v___x_2091_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_beq___boxed), 8, 6);
lean_closure_set(v___x_2091_, 0, lean_box(0));
lean_closure_set(v___x_2091_, 1, lean_box(0));
lean_closure_set(v___x_2091_, 2, v_inst_2088_);
lean_closure_set(v___x_2091_, 3, v_inst_2089_);
lean_closure_set(v___x_2091_, 4, lean_box(0));
lean_closure_set(v___x_2091_, 5, v_inst_2090_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instBEqOfHashableOfLawfulBEq(lean_object* v_00_u03b1_2092_, lean_object* v_00_u03b2_2093_, lean_object* v_inst_2094_, lean_object* v_inst_2095_, lean_object* v_inst_2096_, lean_object* v_inst_2097_){
_start:
{
lean_object* v___x_2098_; 
v___x_2098_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_beq___boxed), 8, 6);
lean_closure_set(v___x_2098_, 0, lean_box(0));
lean_closure_set(v___x_2098_, 1, lean_box(0));
lean_closure_set(v___x_2098_, 2, v_inst_2094_);
lean_closure_set(v___x_2098_, 3, v_inst_2095_);
lean_closure_set(v___x_2098_, 4, lean_box(0));
lean_closure_set(v___x_2098_, 5, v_inst_2097_);
return v___x_2098_;
}
}
uint8_t l_Std_DHashMap_Raw_Const_beq___redArg(lean_object* v_inst_2099_, lean_object* v_inst_2100_, lean_object* v_inst_2101_, lean_object* v_m_u2081_2102_, lean_object* v_m_u2082_2103_){
_start:
{
lean_object* v_buckets_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; uint8_t v___x_2107_; 
v_buckets_2104_ = lean_ctor_get(v_m_u2081_2102_, 1);
v___x_2105_ = lean_unsigned_to_nat(0u);
v___x_2106_ = lean_array_get_size(v_buckets_2104_);
v___x_2107_ = lean_nat_dec_lt(v___x_2105_, v___x_2106_);
if (v___x_2107_ == 0)
{
lean_dec_ref(v_m_u2082_2103_);
lean_dec_ref(v_m_u2081_2102_);
lean_dec_ref(v_inst_2101_);
lean_dec_ref(v_inst_2100_);
lean_dec_ref(v_inst_2099_);
return v___x_2107_;
}
else
{
lean_object* v_buckets_2108_; lean_object* v___x_2109_; uint8_t v___x_2110_; 
v_buckets_2108_ = lean_ctor_get(v_m_u2082_2103_, 1);
v___x_2109_ = lean_array_get_size(v_buckets_2108_);
v___x_2110_ = lean_nat_dec_lt(v___x_2105_, v___x_2109_);
if (v___x_2110_ == 0)
{
lean_dec_ref(v_m_u2082_2103_);
lean_dec_ref(v_m_u2081_2102_);
lean_dec_ref(v_inst_2101_);
lean_dec_ref(v_inst_2100_);
lean_dec_ref(v_inst_2099_);
return v___x_2110_;
}
else
{
uint8_t v___x_2111_; 
v___x_2111_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_inst_2099_, v_inst_2100_, v_inst_2101_, v_m_u2081_2102_, v_m_u2082_2103_);
return v___x_2111_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Raw_Const_beq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2099_ = stack[0].m_obj;
lean_object* v_inst_2100_ = stack[1].m_obj;
lean_object* v_inst_2101_ = stack[2].m_obj;
lean_object* v_m_u2081_2102_ = stack[3].m_obj;
lean_object* v_m_u2082_2103_ = stack[4].m_obj;
uint8_t v_res_2112_;
v_res_2112_ = l_Std_DHashMap_Raw_Const_beq___redArg(v_inst_2099_, v_inst_2100_, v_inst_2101_, v_m_u2081_2102_, v_m_u2082_2103_);
stack->m_num = v_res_2112_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_beq___redArg___boxed(lean_object* v_inst_2113_, lean_object* v_inst_2114_, lean_object* v_inst_2115_, lean_object* v_m_u2081_2116_, lean_object* v_m_u2082_2117_){
_start:
{
uint8_t v_res_2118_; lean_object* v_r_2119_; 
v_res_2118_ = l_Std_DHashMap_Raw_Const_beq___redArg(v_inst_2113_, v_inst_2114_, v_inst_2115_, v_m_u2081_2116_, v_m_u2082_2117_);
v_r_2119_ = lean_box(v_res_2118_);
return v_r_2119_;
}
}
uint8_t l_Std_DHashMap_Raw_Const_beq(lean_object* v_00_u03b1_2120_, lean_object* v_00_u03b2_2121_, lean_object* v_inst_2122_, lean_object* v_inst_2123_, lean_object* v_inst_2124_, lean_object* v_m_u2081_2125_, lean_object* v_m_u2082_2126_){
_start:
{
uint8_t v___x_2127_; 
v___x_2127_ = l_Std_DHashMap_Raw_Const_beq___redArg(v_inst_2122_, v_inst_2123_, v_inst_2124_, v_m_u2081_2125_, v_m_u2082_2126_);
return v___x_2127_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Raw_Const_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2122_ = stack[2].m_obj;
lean_object* v_inst_2123_ = stack[3].m_obj;
lean_object* v_inst_2124_ = stack[4].m_obj;
lean_object* v_m_u2081_2125_ = stack[5].m_obj;
lean_object* v_m_u2082_2126_ = stack[6].m_obj;
uint8_t v_res_2128_;
v_res_2128_ = l_Std_DHashMap_Raw_Const_beq(lean_box(0), lean_box(0), v_inst_2122_, v_inst_2123_, v_inst_2124_, v_m_u2081_2125_, v_m_u2082_2126_);
stack->m_num = v_res_2128_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_beq___boxed(lean_object* v_00_u03b1_2129_, lean_object* v_00_u03b2_2130_, lean_object* v_inst_2131_, lean_object* v_inst_2132_, lean_object* v_inst_2133_, lean_object* v_m_u2081_2134_, lean_object* v_m_u2082_2135_){
_start:
{
uint8_t v_res_2136_; lean_object* v_r_2137_; 
v_res_2136_ = l_Std_DHashMap_Raw_Const_beq(v_00_u03b1_2129_, v_00_u03b2_2130_, v_inst_2131_, v_inst_2132_, v_inst_2133_, v_m_u2081_2134_, v_m_u2082_2135_);
v_r_2137_ = lean_box(v_res_2136_);
return v_r_2137_;
}
}
uint8_t l_Std_DHashMap_Raw_diff___redArg___lam__0(lean_object* v_inst_2138_, lean_object* v_inst_2139_, lean_object* v_m_u2082_2140_, uint8_t v___x_2141_, lean_object* v_k_2142_, lean_object* v_x_2143_){
_start:
{
uint8_t v___x_2144_; 
v___x_2144_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_2138_, v_inst_2139_, v_m_u2082_2140_, v_k_2142_);
if (v___x_2144_ == 0)
{
return v___x_2141_;
}
else
{
uint8_t v___x_2145_; 
v___x_2145_ = 0;
return v___x_2145_;
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Raw_diff___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2138_ = stack[0].m_obj;
lean_object* v_inst_2139_ = stack[1].m_obj;
lean_object* v_m_u2082_2140_ = stack[2].m_obj;
uint8_t v___x_2141_ = stack[3].m_num;
lean_object* v_k_2142_ = stack[4].m_obj;
lean_object* v_x_2143_ = stack[5].m_obj;
uint8_t v_res_2146_;
v_res_2146_ = l_Std_DHashMap_Raw_diff___redArg___lam__0(v_inst_2138_, v_inst_2139_, v_m_u2082_2140_, v___x_2141_, v_k_2142_, v_x_2143_);
stack->m_num = v_res_2146_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_diff___redArg___lam__0___boxed(lean_object* v_inst_2147_, lean_object* v_inst_2148_, lean_object* v_m_u2082_2149_, lean_object* v___x_2150_, lean_object* v_k_2151_, lean_object* v_x_2152_){
_start:
{
uint8_t v___x_95__boxed_2153_; uint8_t v_res_2154_; lean_object* v_r_2155_; 
v___x_95__boxed_2153_ = lean_unbox(v___x_2150_);
v_res_2154_ = l_Std_DHashMap_Raw_diff___redArg___lam__0(v_inst_2147_, v_inst_2148_, v_m_u2082_2149_, v___x_95__boxed_2153_, v_k_2151_, v_x_2152_);
lean_dec(v_x_2152_);
lean_dec_ref(v_m_u2082_2149_);
v_r_2155_ = lean_box(v_res_2154_);
return v_r_2155_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_diff___redArg(lean_object* v_inst_2156_, lean_object* v_inst_2157_, lean_object* v_m_u2081_2158_, lean_object* v_m_u2082_2159_){
_start:
{
lean_object* v_size_2160_; lean_object* v_buckets_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; uint8_t v___x_2164_; 
v_size_2160_ = lean_ctor_get(v_m_u2081_2158_, 0);
v_buckets_2161_ = lean_ctor_get(v_m_u2081_2158_, 1);
v___x_2162_ = lean_unsigned_to_nat(0u);
v___x_2163_ = lean_array_get_size(v_buckets_2161_);
v___x_2164_ = lean_nat_dec_lt(v___x_2162_, v___x_2163_);
if (v___x_2164_ == 0)
{
lean_dec_ref(v_m_u2081_2158_);
lean_dec_ref(v_inst_2157_);
lean_dec_ref(v_inst_2156_);
return v_m_u2082_2159_;
}
else
{
lean_object* v_size_2165_; lean_object* v_buckets_2166_; lean_object* v___x_2167_; uint8_t v___x_2168_; 
v_size_2165_ = lean_ctor_get(v_m_u2082_2159_, 0);
v_buckets_2166_ = lean_ctor_get(v_m_u2082_2159_, 1);
v___x_2167_ = lean_array_get_size(v_buckets_2166_);
v___x_2168_ = lean_nat_dec_lt(v___x_2162_, v___x_2167_);
if (v___x_2168_ == 0)
{
lean_dec_ref(v_m_u2082_2159_);
lean_dec_ref(v_inst_2157_);
lean_dec_ref(v_inst_2156_);
return v_m_u2081_2158_;
}
else
{
uint8_t v___x_2169_; 
v___x_2169_ = lean_nat_dec_le(v_size_2160_, v_size_2165_);
if (v___x_2169_ == 0)
{
lean_object* v___f_2170_; lean_object* v___x_2171_; 
v___f_2170_ = ((lean_object*)(l_Std_DHashMap_Raw_union___redArg___closed__0));
v___x_2171_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_2170_, v_inst_2156_, v_inst_2157_, v_m_u2081_2158_, v_m_u2082_2159_);
return v___x_2171_;
}
else
{
lean_object* v___x_2172_; lean_object* v___f_2173_; lean_object* v___x_2174_; 
v___x_2172_ = lean_box(v___x_2169_);
v___f_2173_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_2173_, 0, v_inst_2156_);
lean_closure_set(v___f_2173_, 1, v_inst_2157_);
lean_closure_set(v___f_2173_, 2, v_m_u2082_2159_);
lean_closure_set(v___f_2173_, 3, v___x_2172_);
v___x_2174_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_2173_, v_m_u2081_2158_);
return v___x_2174_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_diff(lean_object* v_00_u03b1_2175_, lean_object* v_00_u03b2_2176_, lean_object* v_inst_2177_, lean_object* v_inst_2178_, lean_object* v_m_u2081_2179_, lean_object* v_m_u2082_2180_){
_start:
{
lean_object* v_size_2181_; lean_object* v_buckets_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; uint8_t v___x_2185_; 
v_size_2181_ = lean_ctor_get(v_m_u2081_2179_, 0);
v_buckets_2182_ = lean_ctor_get(v_m_u2081_2179_, 1);
v___x_2183_ = lean_unsigned_to_nat(0u);
v___x_2184_ = lean_array_get_size(v_buckets_2182_);
v___x_2185_ = lean_nat_dec_lt(v___x_2183_, v___x_2184_);
if (v___x_2185_ == 0)
{
lean_dec_ref(v_m_u2081_2179_);
lean_dec_ref(v_inst_2178_);
lean_dec_ref(v_inst_2177_);
return v_m_u2082_2180_;
}
else
{
lean_object* v_size_2186_; lean_object* v_buckets_2187_; lean_object* v___x_2188_; uint8_t v___x_2189_; 
v_size_2186_ = lean_ctor_get(v_m_u2082_2180_, 0);
v_buckets_2187_ = lean_ctor_get(v_m_u2082_2180_, 1);
v___x_2188_ = lean_array_get_size(v_buckets_2187_);
v___x_2189_ = lean_nat_dec_lt(v___x_2183_, v___x_2188_);
if (v___x_2189_ == 0)
{
lean_dec_ref(v_m_u2082_2180_);
lean_dec_ref(v_inst_2178_);
lean_dec_ref(v_inst_2177_);
return v_m_u2081_2179_;
}
else
{
uint8_t v___x_2190_; 
v___x_2190_ = lean_nat_dec_le(v_size_2181_, v_size_2186_);
if (v___x_2190_ == 0)
{
lean_object* v___f_2191_; lean_object* v___x_2192_; 
v___f_2191_ = ((lean_object*)(l_Std_DHashMap_Raw_union___redArg___closed__0));
v___x_2192_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_2191_, v_inst_2177_, v_inst_2178_, v_m_u2081_2179_, v_m_u2082_2180_);
return v___x_2192_;
}
else
{
lean_object* v___x_2193_; lean_object* v___f_2194_; lean_object* v___x_2195_; 
v___x_2193_ = lean_box(v___x_2190_);
v___f_2194_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_2194_, 0, v_inst_2177_);
lean_closure_set(v___f_2194_, 1, v_inst_2178_);
lean_closure_set(v___f_2194_, 2, v_m_u2082_2180_);
lean_closure_set(v___f_2194_, 3, v___x_2193_);
v___x_2195_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_2194_, v_m_u2081_2179_);
return v___x_2195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instSDiffOfBEqOfHashable___redArg(lean_object* v_inst_2196_, lean_object* v_inst_2197_){
_start:
{
lean_object* v___x_2198_; 
v___x_2198_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_diff), 6, 4);
lean_closure_set(v___x_2198_, 0, lean_box(0));
lean_closure_set(v___x_2198_, 1, lean_box(0));
lean_closure_set(v___x_2198_, 2, v_inst_2196_);
lean_closure_set(v___x_2198_, 3, v_inst_2197_);
return v___x_2198_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instSDiffOfBEqOfHashable(lean_object* v_00_u03b1_2199_, lean_object* v_00_u03b2_2200_, lean_object* v_inst_2201_, lean_object* v_inst_2202_){
_start:
{
lean_object* v___x_2203_; 
v___x_2203_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_diff), 6, 4);
lean_closure_set(v___x_2203_, 0, lean_box(0));
lean_closure_set(v___x_2203_, 1, lean_box(0));
lean_closure_set(v___x_2203_, 2, v_inst_2201_);
lean_closure_set(v___x_2203_, 3, v_inst_2202_);
return v___x_2203_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_values___redArg___lam__0(lean_object* v_a_2204_, lean_object* v_b_2205_, lean_object* v_d_2206_){
_start:
{
lean_object* v___x_2207_; 
v___x_2207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2207_, 0, v_b_2205_);
lean_ctor_set(v___x_2207_, 1, v_d_2206_);
return v___x_2207_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_values___redArg___lam__0___boxed(lean_object* v_a_2208_, lean_object* v_b_2209_, lean_object* v_d_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l_Std_DHashMap_Raw_values___redArg___lam__0(v_a_2208_, v_b_2209_, v_d_2210_);
lean_dec(v_a_2208_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_values___redArg___lam__1(lean_object* v___x_2212_, lean_object* v___f_2213_, lean_object* v_l_2214_, lean_object* v_acc_2215_){
_start:
{
lean_object* v___x_2216_; 
v___x_2216_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_2212_, v___f_2213_, v_acc_2215_, v_l_2214_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_values___redArg(lean_object* v_m_2221_){
_start:
{
lean_object* v___x_2222_; lean_object* v_buckets_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; uint8_t v___x_2227_; 
v___x_2222_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_2223_ = lean_ctor_get(v_m_2221_, 1);
lean_inc_ref(v_buckets_2223_);
lean_dec_ref(v_m_2221_);
v___x_2224_ = lean_box(0);
v___x_2225_ = lean_array_get_size(v_buckets_2223_);
v___x_2226_ = lean_unsigned_to_nat(0u);
v___x_2227_ = lean_nat_dec_lt(v___x_2226_, v___x_2225_);
if (v___x_2227_ == 0)
{
lean_dec_ref(v_buckets_2223_);
return v___x_2224_;
}
else
{
lean_object* v___f_2228_; size_t v___x_2229_; size_t v___x_2230_; lean_object* v___x_2231_; 
v___f_2228_ = ((lean_object*)(l_Std_DHashMap_Raw_values___redArg___closed__1));
v___x_2229_ = lean_usize_of_nat(v___x_2225_);
v___x_2230_ = ((size_t)0ULL);
v___x_2231_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2222_, v___f_2228_, v_buckets_2223_, v___x_2229_, v___x_2230_, v___x_2224_);
return v___x_2231_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_values(lean_object* v_00_u03b1_2232_, lean_object* v_00_u03b2_2233_, lean_object* v_m_2234_){
_start:
{
lean_object* v___x_2235_; lean_object* v_buckets_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; uint8_t v___x_2240_; 
v___x_2235_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_2236_ = lean_ctor_get(v_m_2234_, 1);
lean_inc_ref(v_buckets_2236_);
lean_dec_ref(v_m_2234_);
v___x_2237_ = lean_box(0);
v___x_2238_ = lean_array_get_size(v_buckets_2236_);
v___x_2239_ = lean_unsigned_to_nat(0u);
v___x_2240_ = lean_nat_dec_lt(v___x_2239_, v___x_2238_);
if (v___x_2240_ == 0)
{
lean_dec_ref(v_buckets_2236_);
return v___x_2237_;
}
else
{
lean_object* v___f_2241_; size_t v___x_2242_; size_t v___x_2243_; lean_object* v___x_2244_; 
v___f_2241_ = ((lean_object*)(l_Std_DHashMap_Raw_values___redArg___closed__1));
v___x_2242_ = lean_usize_of_nat(v___x_2238_);
v___x_2243_ = ((size_t)0ULL);
v___x_2244_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2235_, v___f_2241_, v_buckets_2236_, v___x_2242_, v___x_2243_, v___x_2237_);
return v___x_2244_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_valuesArray___redArg___lam__0(lean_object* v_x1_2245_, lean_object* v_x2_2246_, lean_object* v_x3_2247_){
_start:
{
lean_object* v___x_2248_; 
v___x_2248_ = lean_array_push(v_x1_2245_, v_x3_2247_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_valuesArray___redArg___lam__0___boxed(lean_object* v_x1_2249_, lean_object* v_x2_2250_, lean_object* v_x3_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l_Std_DHashMap_Raw_valuesArray___redArg___lam__0(v_x1_2249_, v_x2_2250_, v_x3_2251_);
lean_dec(v_x2_2250_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_valuesArray___redArg(lean_object* v_m_2257_){
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
lean_object* v___f_2265_; size_t v___x_2266_; size_t v___x_2267_; lean_object* v___x_2268_; 
v___f_2265_ = ((lean_object*)(l_Std_DHashMap_Raw_valuesArray___redArg___closed__1));
v___x_2266_ = ((size_t)0ULL);
v___x_2267_ = lean_usize_of_nat(v___x_2263_);
v___x_2268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2261_, v___f_2265_, v_buckets_2259_, v___x_2266_, v___x_2267_, v___x_2260_);
return v___x_2268_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_valuesArray(lean_object* v_00_u03b1_2269_, lean_object* v_00_u03b2_2270_, lean_object* v_m_2271_){
_start:
{
lean_object* v_size_2272_; lean_object* v_buckets_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; uint8_t v___x_2278_; 
v_size_2272_ = lean_ctor_get(v_m_2271_, 0);
lean_inc(v_size_2272_);
v_buckets_2273_ = lean_ctor_get(v_m_2271_, 1);
lean_inc_ref(v_buckets_2273_);
lean_dec_ref(v_m_2271_);
v___x_2274_ = lean_mk_empty_array_with_capacity(v_size_2272_);
lean_dec(v_size_2272_);
v___x_2275_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_2276_ = lean_unsigned_to_nat(0u);
v___x_2277_ = lean_array_get_size(v_buckets_2273_);
v___x_2278_ = lean_nat_dec_lt(v___x_2276_, v___x_2277_);
if (v___x_2278_ == 0)
{
lean_dec_ref(v_buckets_2273_);
return v___x_2274_;
}
else
{
lean_object* v___f_2279_; size_t v___x_2280_; size_t v___x_2281_; lean_object* v___x_2282_; 
v___f_2279_ = ((lean_object*)(l_Std_DHashMap_Raw_valuesArray___redArg___closed__1));
v___x_2280_ = ((size_t)0ULL);
v___x_2281_ = lean_usize_of_nat(v___x_2277_);
v___x_2282_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2275_, v___f_2279_, v_buckets_2273_, v___x_2280_, v___x_2281_, v___x_2274_);
return v___x_2282_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insertMany___redArg(lean_object* v_inst_2283_, lean_object* v_inst_2284_, lean_object* v_inst_2285_, lean_object* v_m_2286_, lean_object* v_l_2287_){
_start:
{
lean_object* v_buckets_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; uint8_t v___x_2291_; 
v_buckets_2288_ = lean_ctor_get(v_m_2286_, 1);
v___x_2289_ = lean_unsigned_to_nat(0u);
v___x_2290_ = lean_array_get_size(v_buckets_2288_);
v___x_2291_ = lean_nat_dec_lt(v___x_2289_, v___x_2290_);
if (v___x_2291_ == 0)
{
lean_dec(v_l_2287_);
lean_dec(v_inst_2285_);
lean_dec_ref(v_inst_2284_);
lean_dec_ref(v_inst_2283_);
return v_m_2286_;
}
else
{
lean_object* v___x_2292_; 
v___x_2292_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v_inst_2285_, v_inst_2283_, v_inst_2284_, v_m_2286_, v_l_2287_);
return v___x_2292_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insertMany(lean_object* v_00_u03b1_2293_, lean_object* v_00_u03b2_2294_, lean_object* v_inst_2295_, lean_object* v_inst_2296_, lean_object* v_00_u03c1_2297_, lean_object* v_inst_2298_, lean_object* v_m_2299_, lean_object* v_l_2300_){
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
lean_dec_ref(v_inst_2296_);
lean_dec_ref(v_inst_2295_);
return v_m_2299_;
}
else
{
lean_object* v___x_2305_; 
v___x_2305_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v_inst_2298_, v_inst_2295_, v_inst_2296_, v_m_2299_, v_l_2300_);
return v___x_2305_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_eraseManyEntries___redArg(lean_object* v_inst_2306_, lean_object* v_inst_2307_, lean_object* v_inst_2308_, lean_object* v_m_2309_, lean_object* v_l_2310_){
_start:
{
lean_object* v_buckets_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; uint8_t v___x_2314_; 
v_buckets_2311_ = lean_ctor_get(v_m_2309_, 1);
v___x_2312_ = lean_unsigned_to_nat(0u);
v___x_2313_ = lean_array_get_size(v_buckets_2311_);
v___x_2314_ = lean_nat_dec_lt(v___x_2312_, v___x_2313_);
if (v___x_2314_ == 0)
{
lean_dec(v_l_2310_);
lean_dec(v_inst_2308_);
lean_dec_ref(v_inst_2307_);
lean_dec_ref(v_inst_2306_);
return v_m_2309_;
}
else
{
lean_object* v___x_2315_; 
v___x_2315_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v_inst_2308_, v_inst_2306_, v_inst_2307_, v_m_2309_, v_l_2310_);
return v___x_2315_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_eraseManyEntries(lean_object* v_00_u03b1_2316_, lean_object* v_00_u03b2_2317_, lean_object* v_inst_2318_, lean_object* v_inst_2319_, lean_object* v_00_u03c1_2320_, lean_object* v_inst_2321_, lean_object* v_m_2322_, lean_object* v_l_2323_){
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
lean_dec_ref(v_inst_2319_);
lean_dec_ref(v_inst_2318_);
return v_m_2322_;
}
else
{
lean_object* v___x_2328_; 
v___x_2328_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v_inst_2321_, v_inst_2318_, v_inst_2319_, v_m_2322_, v_l_2323_);
return v___x_2328_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_insertMany___redArg(lean_object* v_inst_2329_, lean_object* v_inst_2330_, lean_object* v_inst_2331_, lean_object* v_m_2332_, lean_object* v_l_2333_){
_start:
{
lean_object* v_buckets_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; uint8_t v___x_2337_; 
v_buckets_2334_ = lean_ctor_get(v_m_2332_, 1);
v___x_2335_ = lean_unsigned_to_nat(0u);
v___x_2336_ = lean_array_get_size(v_buckets_2334_);
v___x_2337_ = lean_nat_dec_lt(v___x_2335_, v___x_2336_);
if (v___x_2337_ == 0)
{
lean_dec(v_l_2333_);
lean_dec(v_inst_2331_);
lean_dec_ref(v_inst_2330_);
lean_dec_ref(v_inst_2329_);
return v_m_2332_;
}
else
{
lean_object* v___x_2338_; 
v___x_2338_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v_inst_2331_, v_inst_2329_, v_inst_2330_, v_m_2332_, v_l_2333_);
return v___x_2338_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_insertMany(lean_object* v_00_u03b1_2339_, lean_object* v_00_u03b2_2340_, lean_object* v_inst_2341_, lean_object* v_inst_2342_, lean_object* v_00_u03c1_2343_, lean_object* v_inst_2344_, lean_object* v_m_2345_, lean_object* v_l_2346_){
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
lean_dec_ref(v_inst_2342_);
lean_dec_ref(v_inst_2341_);
return v_m_2345_;
}
else
{
lean_object* v___x_2351_; 
v___x_2351_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v_inst_2344_, v_inst_2341_, v_inst_2342_, v_m_2345_, v_l_2346_);
return v___x_2351_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_insertManyIfNewUnit___redArg(lean_object* v_inst_2352_, lean_object* v_inst_2353_, lean_object* v_inst_2354_, lean_object* v_m_2355_, lean_object* v_l_2356_){
_start:
{
lean_object* v_buckets_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; uint8_t v___x_2360_; 
v_buckets_2357_ = lean_ctor_get(v_m_2355_, 1);
v___x_2358_ = lean_unsigned_to_nat(0u);
v___x_2359_ = lean_array_get_size(v_buckets_2357_);
v___x_2360_ = lean_nat_dec_lt(v___x_2358_, v___x_2359_);
if (v___x_2360_ == 0)
{
lean_dec(v_l_2356_);
lean_dec(v_inst_2354_);
lean_dec_ref(v_inst_2353_);
lean_dec_ref(v_inst_2352_);
return v_m_2355_;
}
else
{
lean_object* v___x_2361_; 
v___x_2361_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_2354_, v_inst_2352_, v_inst_2353_, v_m_2355_, v_l_2356_);
return v___x_2361_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_insertManyIfNewUnit(lean_object* v_00_u03b1_2362_, lean_object* v_inst_2363_, lean_object* v_inst_2364_, lean_object* v_00_u03c1_2365_, lean_object* v_inst_2366_, lean_object* v_m_2367_, lean_object* v_l_2368_){
_start:
{
lean_object* v_buckets_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; uint8_t v___x_2372_; 
v_buckets_2369_ = lean_ctor_get(v_m_2367_, 1);
v___x_2370_ = lean_unsigned_to_nat(0u);
v___x_2371_ = lean_array_get_size(v_buckets_2369_);
v___x_2372_ = lean_nat_dec_lt(v___x_2370_, v___x_2371_);
if (v___x_2372_ == 0)
{
lean_dec(v_l_2368_);
lean_dec(v_inst_2366_);
lean_dec_ref(v_inst_2364_);
lean_dec_ref(v_inst_2363_);
return v_m_2367_;
}
else
{
lean_object* v___x_2373_; 
v___x_2373_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_2366_, v_inst_2363_, v_inst_2364_, v_m_2367_, v_l_2368_);
return v___x_2373_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_unitOfArray___redArg(lean_object* v_inst_2378_, lean_object* v_inst_2379_, lean_object* v_l_2380_){
_start:
{
lean_object* v___x_2381_; uint8_t v___x_2382_; 
v___x_2381_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
v___x_2382_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2382_ == 0)
{
lean_dec_ref(v_l_2380_);
lean_dec_ref(v_inst_2379_);
lean_dec_ref(v_inst_2378_);
return v___x_2381_;
}
else
{
lean_object* v___f_2383_; lean_object* v___x_2384_; 
v___f_2383_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1));
v___x_2384_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2383_, v_inst_2378_, v_inst_2379_, v___x_2381_, v_l_2380_);
return v___x_2384_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_unitOfArray(lean_object* v_00_u03b1_2385_, lean_object* v_inst_2386_, lean_object* v_inst_2387_, lean_object* v_l_2388_){
_start:
{
lean_object* v___x_2389_; uint8_t v___x_2390_; 
v___x_2389_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
v___x_2390_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2390_ == 0)
{
lean_dec_ref(v_l_2388_);
lean_dec_ref(v_inst_2387_);
lean_dec_ref(v_inst_2386_);
return v___x_2389_;
}
else
{
lean_object* v___f_2391_; lean_object* v___x_2392_; 
v___f_2391_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1));
v___x_2392_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2391_, v_inst_2386_, v_inst_2387_, v___x_2389_, v_l_2388_);
return v___x_2392_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_numBuckets___redArg(lean_object* v_m_2393_){
_start:
{
lean_object* v_buckets_2394_; lean_object* v___x_2395_; 
v_buckets_2394_ = lean_ctor_get(v_m_2393_, 1);
v___x_2395_ = lean_array_get_size(v_buckets_2394_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_numBuckets___redArg___boxed(lean_object* v_m_2396_){
_start:
{
lean_object* v_res_2397_; 
v_res_2397_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2396_);
lean_dec_ref(v_m_2396_);
return v_res_2397_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_numBuckets(lean_object* v_00_u03b1_2398_, lean_object* v_00_u03b2_2399_, lean_object* v_m_2400_){
_start:
{
lean_object* v___x_2401_; 
v___x_2401_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2400_);
return v___x_2401_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_numBuckets___boxed(lean_object* v_00_u03b1_2402_, lean_object* v_00_u03b2_2403_, lean_object* v_m_2404_){
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l_Std_DHashMap_Raw_Internal_numBuckets(v_00_u03b1_2402_, v_00_u03b2_2403_, v_m_2404_);
lean_dec_ref(v_m_2404_);
return v_res_2405_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toList___redArg___lam__0(lean_object* v_a_2406_, lean_object* v_b_2407_, lean_object* v_d_2408_){
_start:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2409_, 0, v_a_2406_);
lean_ctor_set(v___x_2409_, 1, v_b_2407_);
v___x_2410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2409_);
lean_ctor_set(v___x_2410_, 1, v_d_2408_);
return v___x_2410_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toList___redArg___lam__1(lean_object* v___x_2411_, lean_object* v___f_2412_, lean_object* v_l_2413_, lean_object* v_acc_2414_){
_start:
{
lean_object* v___x_2415_; 
v___x_2415_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_2411_, v___f_2412_, v_acc_2414_, v_l_2413_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toList___redArg(lean_object* v_m_2420_){
_start:
{
lean_object* v___x_2421_; lean_object* v_buckets_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; uint8_t v___x_2426_; 
v___x_2421_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_2422_ = lean_ctor_get(v_m_2420_, 1);
lean_inc_ref(v_buckets_2422_);
lean_dec_ref(v_m_2420_);
v___x_2423_ = lean_box(0);
v___x_2424_ = lean_array_get_size(v_buckets_2422_);
v___x_2425_ = lean_unsigned_to_nat(0u);
v___x_2426_ = lean_nat_dec_lt(v___x_2425_, v___x_2424_);
if (v___x_2426_ == 0)
{
lean_dec_ref(v_buckets_2422_);
return v___x_2423_;
}
else
{
lean_object* v___f_2427_; size_t v___x_2428_; size_t v___x_2429_; lean_object* v___x_2430_; 
v___f_2427_ = ((lean_object*)(l_Std_DHashMap_Raw_toList___redArg___closed__1));
v___x_2428_ = lean_usize_of_nat(v___x_2424_);
v___x_2429_ = ((size_t)0ULL);
v___x_2430_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2421_, v___f_2427_, v_buckets_2422_, v___x_2428_, v___x_2429_, v___x_2423_);
return v___x_2430_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toList(lean_object* v_00_u03b1_2431_, lean_object* v_00_u03b2_2432_, lean_object* v_m_2433_){
_start:
{
lean_object* v___x_2434_; lean_object* v_buckets_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; uint8_t v___x_2439_; 
v___x_2434_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_2435_ = lean_ctor_get(v_m_2433_, 1);
lean_inc_ref(v_buckets_2435_);
lean_dec_ref(v_m_2433_);
v___x_2436_ = lean_box(0);
v___x_2437_ = lean_array_get_size(v_buckets_2435_);
v___x_2438_ = lean_unsigned_to_nat(0u);
v___x_2439_ = lean_nat_dec_lt(v___x_2438_, v___x_2437_);
if (v___x_2439_ == 0)
{
lean_dec_ref(v_buckets_2435_);
return v___x_2436_;
}
else
{
lean_object* v___f_2440_; size_t v___x_2441_; size_t v___x_2442_; lean_object* v___x_2443_; 
v___f_2440_ = ((lean_object*)(l_Std_DHashMap_Raw_toList___redArg___closed__1));
v___x_2441_ = lean_usize_of_nat(v___x_2437_);
v___x_2442_ = ((size_t)0ULL);
v___x_2443_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2434_, v___f_2440_, v_buckets_2435_, v___x_2441_, v___x_2442_, v___x_2436_);
return v___x_2443_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toList___redArg___lam__0(lean_object* v_a_2444_, lean_object* v_b_2445_, lean_object* v_d_2446_){
_start:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2447_, 0, v_a_2444_);
lean_ctor_set(v___x_2447_, 1, v_b_2445_);
v___x_2448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2447_);
lean_ctor_set(v___x_2448_, 1, v_d_2446_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toList___redArg___lam__1(lean_object* v___x_2449_, lean_object* v___f_2450_, lean_object* v_l_2451_, lean_object* v_acc_2452_){
_start:
{
lean_object* v___x_2453_; 
v___x_2453_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_2449_, v___f_2450_, v_acc_2452_, v_l_2451_);
return v___x_2453_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toList___redArg(lean_object* v_m_2458_){
_start:
{
lean_object* v___x_2459_; lean_object* v_buckets_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; uint8_t v___x_2464_; 
v___x_2459_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_2460_ = lean_ctor_get(v_m_2458_, 1);
lean_inc_ref(v_buckets_2460_);
lean_dec_ref(v_m_2458_);
v___x_2461_ = lean_box(0);
v___x_2462_ = lean_array_get_size(v_buckets_2460_);
v___x_2463_ = lean_unsigned_to_nat(0u);
v___x_2464_ = lean_nat_dec_lt(v___x_2463_, v___x_2462_);
if (v___x_2464_ == 0)
{
lean_dec_ref(v_buckets_2460_);
return v___x_2461_;
}
else
{
lean_object* v___f_2465_; size_t v___x_2466_; size_t v___x_2467_; lean_object* v___x_2468_; 
v___f_2465_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_toList___redArg___closed__1));
v___x_2466_ = lean_usize_of_nat(v___x_2462_);
v___x_2467_ = ((size_t)0ULL);
v___x_2468_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2459_, v___f_2465_, v_buckets_2460_, v___x_2466_, v___x_2467_, v___x_2461_);
return v___x_2468_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toList(lean_object* v_00_u03b1_2469_, lean_object* v_00_u03b2_2470_, lean_object* v_m_2471_){
_start:
{
lean_object* v___x_2472_; lean_object* v_buckets_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; uint8_t v___x_2477_; 
v___x_2472_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_2473_ = lean_ctor_get(v_m_2471_, 1);
lean_inc_ref(v_buckets_2473_);
lean_dec_ref(v_m_2471_);
v___x_2474_ = lean_box(0);
v___x_2475_ = lean_array_get_size(v_buckets_2473_);
v___x_2476_ = lean_unsigned_to_nat(0u);
v___x_2477_ = lean_nat_dec_lt(v___x_2476_, v___x_2475_);
if (v___x_2477_ == 0)
{
lean_dec_ref(v_buckets_2473_);
return v___x_2474_;
}
else
{
lean_object* v___f_2478_; size_t v___x_2479_; size_t v___x_2480_; lean_object* v___x_2481_; 
v___f_2478_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_toList___redArg___closed__1));
v___x_2479_ = lean_usize_of_nat(v___x_2475_);
v___x_2480_ = ((size_t)0ULL);
v___x_2481_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2472_, v___f_2478_, v_buckets_2473_, v___x_2479_, v___x_2480_, v___x_2474_);
return v___x_2481_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instRepr___redArg___lam__2(lean_object* v___x_2485_, lean_object* v___f_2486_, lean_object* v_m_2487_, lean_object* v_prec_2488_){
_start:
{
lean_object* v___x_2489_; lean_object* v_buckets_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2510_; 
v___x_2489_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_2490_ = lean_ctor_get(v_m_2487_, 1);
v_isSharedCheck_2510_ = !lean_is_exclusive(v_m_2487_);
if (v_isSharedCheck_2510_ == 0)
{
lean_object* v_unused_2511_; 
v_unused_2511_ = lean_ctor_get(v_m_2487_, 0);
lean_dec(v_unused_2511_);
v___x_2492_ = v_m_2487_;
v_isShared_2493_ = v_isSharedCheck_2510_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_buckets_2490_);
lean_dec(v_m_2487_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2510_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2494_; lean_object* v___y_2496_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; uint8_t v___x_2505_; 
v___x_2494_ = ((lean_object*)(l_Std_DHashMap_Raw_instRepr___redArg___lam__2___closed__1));
v___x_2502_ = lean_box(0);
v___x_2503_ = lean_array_get_size(v_buckets_2490_);
v___x_2504_ = lean_unsigned_to_nat(0u);
v___x_2505_ = lean_nat_dec_lt(v___x_2504_, v___x_2503_);
if (v___x_2505_ == 0)
{
lean_dec_ref(v_buckets_2490_);
lean_dec_ref(v___f_2486_);
v___y_2496_ = v___x_2502_;
goto v___jp_2495_;
}
else
{
lean_object* v___f_2506_; size_t v___x_2507_; size_t v___x_2508_; lean_object* v___x_2509_; 
v___f_2506_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_toList___redArg___lam__1), 4, 2);
lean_closure_set(v___f_2506_, 0, v___x_2489_);
lean_closure_set(v___f_2506_, 1, v___f_2486_);
v___x_2507_ = lean_usize_of_nat(v___x_2503_);
v___x_2508_ = ((size_t)0ULL);
v___x_2509_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2489_, v___f_2506_, v_buckets_2490_, v___x_2507_, v___x_2508_, v___x_2502_);
v___y_2496_ = v___x_2509_;
goto v___jp_2495_;
}
v___jp_2495_:
{
lean_object* v___x_2497_; lean_object* v___x_2499_; 
v___x_2497_ = l_List_repr___redArg(v___x_2485_, v___y_2496_);
if (v_isShared_2493_ == 0)
{
lean_ctor_set_tag(v___x_2492_, 5);
lean_ctor_set(v___x_2492_, 1, v___x_2497_);
lean_ctor_set(v___x_2492_, 0, v___x_2494_);
v___x_2499_ = v___x_2492_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v___x_2494_);
lean_ctor_set(v_reuseFailAlloc_2501_, 1, v___x_2497_);
v___x_2499_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
lean_object* v___x_2500_; 
v___x_2500_ = l_Repr_addAppParen(v___x_2499_, v_prec_2488_);
return v___x_2500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instRepr___redArg___lam__2___boxed(lean_object* v___x_2512_, lean_object* v___f_2513_, lean_object* v_m_2514_, lean_object* v_prec_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l_Std_DHashMap_Raw_instRepr___redArg___lam__2(v___x_2512_, v___f_2513_, v_m_2514_, v_prec_2515_);
lean_dec(v_prec_2515_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instRepr___redArg(lean_object* v_inst_2517_, lean_object* v_inst_2518_){
_start:
{
lean_object* v___f_2519_; lean_object* v___x_2520_; lean_object* v___f_2521_; 
v___f_2519_ = ((lean_object*)(l_Std_DHashMap_Raw_toList___redArg___closed__0));
v___x_2520_ = lean_alloc_closure((void*)(l_Sigma_repr___boxed), 6, 4);
lean_closure_set(v___x_2520_, 0, lean_box(0));
lean_closure_set(v___x_2520_, 1, lean_box(0));
lean_closure_set(v___x_2520_, 2, v_inst_2517_);
lean_closure_set(v___x_2520_, 3, v_inst_2518_);
v___f_2521_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instRepr___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2521_, 0, v___x_2520_);
lean_closure_set(v___f_2521_, 1, v___f_2519_);
return v___f_2521_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instRepr(lean_object* v_00_u03b1_2522_, lean_object* v_00_u03b2_2523_, lean_object* v_inst_2524_, lean_object* v_inst_2525_){
_start:
{
lean_object* v___x_2526_; 
v___x_2526_ = l_Std_DHashMap_Raw_instRepr___redArg(v_inst_2524_, v_inst_2525_);
return v___x_2526_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keys___redArg___lam__0(lean_object* v_a_2527_, lean_object* v_b_2528_, lean_object* v_d_2529_){
_start:
{
lean_object* v___x_2530_; 
v___x_2530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2530_, 0, v_a_2527_);
lean_ctor_set(v___x_2530_, 1, v_d_2529_);
return v___x_2530_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keys___redArg___lam__0___boxed(lean_object* v_a_2531_, lean_object* v_b_2532_, lean_object* v_d_2533_){
_start:
{
lean_object* v_res_2534_; 
v_res_2534_ = l_Std_DHashMap_Raw_keys___redArg___lam__0(v_a_2531_, v_b_2532_, v_d_2533_);
lean_dec(v_b_2532_);
return v_res_2534_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keys___redArg(lean_object* v_m_2539_){
_start:
{
lean_object* v___x_2540_; lean_object* v_buckets_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; uint8_t v___x_2545_; 
v___x_2540_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_2541_ = lean_ctor_get(v_m_2539_, 1);
lean_inc_ref(v_buckets_2541_);
lean_dec_ref(v_m_2539_);
v___x_2542_ = lean_box(0);
v___x_2543_ = lean_array_get_size(v_buckets_2541_);
v___x_2544_ = lean_unsigned_to_nat(0u);
v___x_2545_ = lean_nat_dec_lt(v___x_2544_, v___x_2543_);
if (v___x_2545_ == 0)
{
lean_dec_ref(v_buckets_2541_);
return v___x_2542_;
}
else
{
lean_object* v___f_2546_; size_t v___x_2547_; size_t v___x_2548_; lean_object* v___x_2549_; 
v___f_2546_ = ((lean_object*)(l_Std_DHashMap_Raw_keys___redArg___closed__1));
v___x_2547_ = lean_usize_of_nat(v___x_2543_);
v___x_2548_ = ((size_t)0ULL);
v___x_2549_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2540_, v___f_2546_, v_buckets_2541_, v___x_2547_, v___x_2548_, v___x_2542_);
return v___x_2549_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keys(lean_object* v_00_u03b1_2550_, lean_object* v_00_u03b2_2551_, lean_object* v_m_2552_){
_start:
{
lean_object* v___x_2553_; lean_object* v_buckets_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; uint8_t v___x_2558_; 
v___x_2553_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v_buckets_2554_ = lean_ctor_get(v_m_2552_, 1);
lean_inc_ref(v_buckets_2554_);
lean_dec_ref(v_m_2552_);
v___x_2555_ = lean_box(0);
v___x_2556_ = lean_array_get_size(v_buckets_2554_);
v___x_2557_ = lean_unsigned_to_nat(0u);
v___x_2558_ = lean_nat_dec_lt(v___x_2557_, v___x_2556_);
if (v___x_2558_ == 0)
{
lean_dec_ref(v_buckets_2554_);
return v___x_2555_;
}
else
{
lean_object* v___f_2559_; size_t v___x_2560_; size_t v___x_2561_; lean_object* v___x_2562_; 
v___f_2559_ = ((lean_object*)(l_Std_DHashMap_Raw_keys___redArg___closed__1));
v___x_2560_ = lean_usize_of_nat(v___x_2556_);
v___x_2561_ = ((size_t)0ULL);
v___x_2562_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2553_, v___f_2559_, v_buckets_2554_, v___x_2560_, v___x_2561_, v___x_2555_);
return v___x_2562_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_ofList___redArg(lean_object* v_inst_2567_, lean_object* v_inst_2568_, lean_object* v_l_2569_){
_start:
{
lean_object* v___x_2570_; uint8_t v___x_2571_; 
v___x_2570_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
v___x_2571_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2571_ == 0)
{
lean_dec(v_l_2569_);
lean_dec_ref(v_inst_2568_);
lean_dec_ref(v_inst_2567_);
return v___x_2570_;
}
else
{
lean_object* v___f_2572_; lean_object* v___x_2573_; 
v___f_2572_ = ((lean_object*)(l_Std_DHashMap_Raw_ofList___redArg___closed__1));
v___x_2573_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_2572_, v_inst_2567_, v_inst_2568_, v___x_2570_, v_l_2569_);
return v___x_2573_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_ofList(lean_object* v_00_u03b1_2574_, lean_object* v_00_u03b2_2575_, lean_object* v_inst_2576_, lean_object* v_inst_2577_, lean_object* v_l_2578_){
_start:
{
lean_object* v___x_2579_; uint8_t v___x_2580_; 
v___x_2579_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
v___x_2580_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2580_ == 0)
{
lean_dec(v_l_2578_);
lean_dec_ref(v_inst_2577_);
lean_dec_ref(v_inst_2576_);
return v___x_2579_;
}
else
{
lean_object* v___f_2581_; lean_object* v___x_2582_; 
v___f_2581_ = ((lean_object*)(l_Std_DHashMap_Raw_ofList___redArg___closed__1));
v___x_2582_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_2581_, v_inst_2576_, v_inst_2577_, v___x_2579_, v_l_2578_);
return v___x_2582_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_ofArray___redArg(lean_object* v_inst_2583_, lean_object* v_inst_2584_, lean_object* v_l_2585_){
_start:
{
lean_object* v___x_2586_; uint8_t v___x_2587_; 
v___x_2586_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
v___x_2587_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2587_ == 0)
{
lean_dec_ref(v_l_2585_);
lean_dec_ref(v_inst_2584_);
lean_dec_ref(v_inst_2583_);
return v___x_2586_;
}
else
{
lean_object* v___f_2588_; lean_object* v___x_2589_; 
v___f_2588_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1));
v___x_2589_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_2588_, v_inst_2583_, v_inst_2584_, v___x_2586_, v_l_2585_);
return v___x_2589_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_ofArray(lean_object* v_00_u03b1_2590_, lean_object* v_00_u03b2_2591_, lean_object* v_inst_2592_, lean_object* v_inst_2593_, lean_object* v_l_2594_){
_start:
{
lean_object* v___x_2595_; uint8_t v___x_2596_; 
v___x_2595_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
v___x_2596_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2596_ == 0)
{
lean_dec_ref(v_l_2594_);
lean_dec_ref(v_inst_2593_);
lean_dec_ref(v_inst_2592_);
return v___x_2595_;
}
else
{
lean_object* v___f_2597_; lean_object* v___x_2598_; 
v___f_2597_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1));
v___x_2598_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_2597_, v_inst_2592_, v_inst_2593_, v___x_2595_, v_l_2594_);
return v___x_2598_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_ofList___redArg(lean_object* v_inst_2599_, lean_object* v_inst_2600_, lean_object* v_l_2601_){
_start:
{
lean_object* v___x_2602_; uint8_t v___x_2603_; 
v___x_2602_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
v___x_2603_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2603_ == 0)
{
lean_dec(v_l_2601_);
lean_dec_ref(v_inst_2600_);
lean_dec_ref(v_inst_2599_);
return v___x_2602_;
}
else
{
lean_object* v___f_2604_; lean_object* v___x_2605_; 
v___f_2604_ = ((lean_object*)(l_Std_DHashMap_Raw_ofList___redArg___closed__1));
v___x_2605_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_2604_, v_inst_2599_, v_inst_2600_, v___x_2602_, v_l_2601_);
return v___x_2605_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_ofList(lean_object* v_00_u03b1_2606_, lean_object* v_00_u03b2_2607_, lean_object* v_inst_2608_, lean_object* v_inst_2609_, lean_object* v_l_2610_){
_start:
{
lean_object* v___x_2611_; uint8_t v___x_2612_; 
v___x_2611_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
v___x_2612_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2612_ == 0)
{
lean_dec(v_l_2610_);
lean_dec_ref(v_inst_2609_);
lean_dec_ref(v_inst_2608_);
return v___x_2611_;
}
else
{
lean_object* v___f_2613_; lean_object* v___x_2614_; 
v___f_2613_ = ((lean_object*)(l_Std_DHashMap_Raw_ofList___redArg___closed__1));
v___x_2614_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_2613_, v_inst_2608_, v_inst_2609_, v___x_2611_, v_l_2610_);
return v___x_2614_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_ofArray___redArg(lean_object* v_inst_2615_, lean_object* v_inst_2616_, lean_object* v_l_2617_){
_start:
{
lean_object* v___x_2618_; uint8_t v___x_2619_; 
v___x_2618_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
v___x_2619_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2619_ == 0)
{
lean_dec_ref(v_l_2617_);
lean_dec_ref(v_inst_2616_);
lean_dec_ref(v_inst_2615_);
return v___x_2618_;
}
else
{
lean_object* v___f_2620_; lean_object* v___x_2621_; 
v___f_2620_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1));
v___x_2621_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_2620_, v_inst_2615_, v_inst_2616_, v___x_2618_, v_l_2617_);
return v___x_2621_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_ofArray(lean_object* v_00_u03b1_2622_, lean_object* v_00_u03b2_2623_, lean_object* v_inst_2624_, lean_object* v_inst_2625_, lean_object* v_l_2626_){
_start:
{
lean_object* v___x_2627_; uint8_t v___x_2628_; 
v___x_2627_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
v___x_2628_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2628_ == 0)
{
lean_dec_ref(v_l_2626_);
lean_dec_ref(v_inst_2625_);
lean_dec_ref(v_inst_2624_);
return v___x_2627_;
}
else
{
lean_object* v___f_2629_; lean_object* v___x_2630_; 
v___f_2629_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1));
v___x_2630_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_2629_, v_inst_2624_, v_inst_2625_, v___x_2627_, v_l_2626_);
return v___x_2630_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_unitOfList___redArg(lean_object* v_inst_2631_, lean_object* v_inst_2632_, lean_object* v_l_2633_){
_start:
{
lean_object* v___x_2634_; uint8_t v___x_2635_; 
v___x_2634_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
v___x_2635_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2635_ == 0)
{
lean_dec(v_l_2633_);
lean_dec_ref(v_inst_2632_);
lean_dec_ref(v_inst_2631_);
return v___x_2634_;
}
else
{
lean_object* v___f_2636_; lean_object* v___x_2637_; 
v___f_2636_ = ((lean_object*)(l_Std_DHashMap_Raw_ofList___redArg___closed__1));
v___x_2637_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2636_, v_inst_2631_, v_inst_2632_, v___x_2634_, v_l_2633_);
return v___x_2637_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_unitOfList(lean_object* v_00_u03b1_2638_, lean_object* v_inst_2639_, lean_object* v_inst_2640_, lean_object* v_l_2641_){
_start:
{
lean_object* v___x_2642_; uint8_t v___x_2643_; 
v___x_2642_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___redArg___closed__1);
v___x_2643_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2643_ == 0)
{
lean_dec(v_l_2641_);
lean_dec_ref(v_inst_2640_);
lean_dec_ref(v_inst_2639_);
return v___x_2642_;
}
else
{
lean_object* v___f_2644_; lean_object* v___x_2645_; 
v___f_2644_ = ((lean_object*)(l_Std_DHashMap_Raw_ofList___redArg___closed__1));
v___x_2645_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2644_, v_inst_2639_, v_inst_2640_, v___x_2642_, v_l_2641_);
return v___x_2645_;
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
