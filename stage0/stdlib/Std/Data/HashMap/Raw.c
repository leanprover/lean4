// Lean compiler output
// Module: Std.Data.HashMap.Raw
// Imports: public import Std.Data.DHashMap.Raw
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
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_mark_linear(lean_object*);
lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instForInOfForIn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Raw_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(lean_object*, lean_object*);
lean_object* l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_Internal_numBuckets___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_map___redArg(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Raw_Const_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instReprTupleOfRepr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Prod_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_emptyWithCapacity___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_emptyWithCapacity___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_emptyWithCapacity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_emptyWithCapacity___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__0;
static lean_once_cell_t l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instEmptyCollection___redArg();
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instEmptyCollection___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_HashMap_Raw_instEmptyCollection___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashMap_Raw_instEmptyCollection___closed__0;
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instEmptyCollection(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInhabited___redArg();
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInhabited___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_HashMap_Raw_instInhabited___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashMap_Raw_instInhabited___closed__0;
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInhabited(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_markLinear___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_markLinear(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_HashMap_Raw_term___x7em___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Std_HashMap_Raw_term___x7em___00__closed__0 = (const lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__0_value;
static const lean_string_object l_Std_HashMap_Raw_term___x7em___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "HashMap"};
static const lean_object* l_Std_HashMap_Raw_term___x7em___00__closed__1 = (const lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__1_value;
static const lean_string_object l_Std_HashMap_Raw_term___x7em___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Raw"};
static const lean_object* l_Std_HashMap_Raw_term___x7em___00__closed__2 = (const lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__2_value;
static const lean_string_object l_Std_HashMap_Raw_term___x7em___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_~m_"};
static const lean_object* l_Std_HashMap_Raw_term___x7em___00__closed__3 = (const lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__3_value;
static const lean_ctor_object l_Std_HashMap_Raw_term___x7em___00__closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_HashMap_Raw_term___x7em___00__closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__4_value_aux_0),((lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(34, 156, 61, 172, 252, 129, 143, 98)}};
static const lean_ctor_object l_Std_HashMap_Raw_term___x7em___00__closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__4_value_aux_1),((lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(49, 114, 108, 172, 163, 107, 109, 115)}};
static const lean_ctor_object l_Std_HashMap_Raw_term___x7em___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__4_value_aux_2),((lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__3_value),LEAN_SCALAR_PTR_LITERAL(59, 178, 34, 125, 85, 115, 99, 157)}};
static const lean_object* l_Std_HashMap_Raw_term___x7em___00__closed__4 = (const lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__4_value;
static const lean_string_object l_Std_HashMap_Raw_term___x7em___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Std_HashMap_Raw_term___x7em___00__closed__5 = (const lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__5_value;
static const lean_ctor_object l_Std_HashMap_Raw_term___x7em___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__5_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Std_HashMap_Raw_term___x7em___00__closed__6 = (const lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__6_value;
static const lean_string_object l_Std_HashMap_Raw_term___x7em___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " ~m "};
static const lean_object* l_Std_HashMap_Raw_term___x7em___00__closed__7 = (const lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__7_value;
static const lean_ctor_object l_Std_HashMap_Raw_term___x7em___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__7_value)}};
static const lean_object* l_Std_HashMap_Raw_term___x7em___00__closed__8 = (const lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__8_value;
static const lean_string_object l_Std_HashMap_Raw_term___x7em___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Std_HashMap_Raw_term___x7em___00__closed__9 = (const lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__9_value;
static const lean_ctor_object l_Std_HashMap_Raw_term___x7em___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__9_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Std_HashMap_Raw_term___x7em___00__closed__10 = (const lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__10_value;
static const lean_ctor_object l_Std_HashMap_Raw_term___x7em___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__10_value),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l_Std_HashMap_Raw_term___x7em___00__closed__11 = (const lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__11_value;
static const lean_ctor_object l_Std_HashMap_Raw_term___x7em___00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__6_value),((lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__8_value),((lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__11_value)}};
static const lean_object* l_Std_HashMap_Raw_term___x7em___00__closed__12 = (const lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__12_value;
static const lean_ctor_object l_Std_HashMap_Raw_term___x7em___00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__4_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__12_value)}};
static const lean_object* l_Std_HashMap_Raw_term___x7em___00__closed__13 = (const lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__13_value;
LEAN_EXPORT const lean_object* l_Std_HashMap_Raw_term___x7em__ = (const lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__13_value;
static const lean_string_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__0 = (const lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__0_value;
static const lean_string_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__1 = (const lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__1_value;
static const lean_string_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__2 = (const lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__2_value;
static const lean_string_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__3 = (const lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__3_value;
static const lean_ctor_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4_value_aux_0),((lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4_value_aux_1),((lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4_value_aux_2),((lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4 = (const lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4_value;
static const lean_string_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Equiv"};
static const lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__5 = (const lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__5_value;
static lean_once_cell_t l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__6;
static const lean_ctor_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(0, 253, 123, 237, 128, 91, 245, 83)}};
static const lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__7 = (const lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__7_value;
static const lean_ctor_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8_value_aux_0),((lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(34, 156, 61, 172, 252, 129, 143, 98)}};
static const lean_ctor_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8_value_aux_1),((lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(49, 114, 108, 172, 163, 107, 109, 115)}};
static const lean_ctor_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8_value_aux_2),((lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(82, 235, 84, 249, 222, 26, 229, 203)}};
static const lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8 = (const lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8_value;
static const lean_ctor_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__9 = (const lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__9_value;
static const lean_ctor_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8_value)}};
static const lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__10 = (const lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__10_value;
static const lean_ctor_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__11 = (const lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__11_value;
static const lean_ctor_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__9_value),((lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__11_value)}};
static const lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__12 = (const lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__12_value;
static const lean_string_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__13 = (const lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__13_value;
static const lean_ctor_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__14 = (const lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__14_value;
LEAN_EXPORT lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___closed__0 = (const lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___closed__0_value;
static const lean_ctor_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___closed__1 = (const lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0;
static lean_once_cell_t l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertIfNew(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_containsThenInsert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_containsThenInsert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_containsThenInsertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_containsThenInsertIfNew(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getThenInsertIfNew_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getThenInsertIfNew_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_contains___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instMembershipOfBEqOfHashable___redArg();
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instMembershipOfBEqOfHashable___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instMembershipOfBEqOfHashable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instMembershipOfBEqOfHashable___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instDecidableMem___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_instDecidableMem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instDecidableMem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKeyD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKeyD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKeyD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_size___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_size(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_size___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_isEmpty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_isEmpty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashMap_Raw_keys___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_Raw_keys___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__0_value;
static const lean_closure_object l_Std_HashMap_Raw_keys___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_Raw_keys___redArg___closed__1 = (const lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__1_value;
static const lean_closure_object l_Std_HashMap_Raw_keys___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_Raw_keys___redArg___closed__2 = (const lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__2_value;
static const lean_closure_object l_Std_HashMap_Raw_keys___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_Raw_keys___redArg___closed__3 = (const lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__3_value;
static const lean_closure_object l_Std_HashMap_Raw_keys___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_Raw_keys___redArg___closed__4 = (const lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__4_value;
static const lean_closure_object l_Std_HashMap_Raw_keys___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_Raw_keys___redArg___closed__5 = (const lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__5_value;
static const lean_closure_object l_Std_HashMap_Raw_keys___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_Raw_keys___redArg___closed__6 = (const lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__6_value;
static const lean_ctor_object l_Std_HashMap_Raw_keys___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__0_value),((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__1_value)}};
static const lean_object* l_Std_HashMap_Raw_keys___redArg___closed__7 = (const lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__7_value;
static const lean_ctor_object l_Std_HashMap_Raw_keys___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__7_value),((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__2_value),((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__3_value),((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__4_value),((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__5_value)}};
static const lean_object* l_Std_HashMap_Raw_keys___redArg___closed__8 = (const lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__8_value;
static const lean_ctor_object l_Std_HashMap_Raw_keys___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__8_value),((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__6_value)}};
static const lean_object* l_Std_HashMap_Raw_keys___redArg___closed__9 = (const lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__9_value;
static const lean_closure_object l_Std_HashMap_Raw_keys___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_Raw_keys___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_Raw_keys___redArg___closed__10 = (const lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__10_value;
static const lean_closure_object l_Std_HashMap_Raw_keys___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_Raw_keys___redArg___lam__1, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__9_value),((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__10_value)} };
static const lean_object* l_Std_HashMap_Raw_keys___redArg___closed__11 = (const lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__11_value;
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashMap_Raw_ofList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__9_value)} };
static const lean_object* l_Std_HashMap_Raw_ofList___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_Raw_ofList___redArg___closed__0_value;
static const lean_closure_object l_Std_HashMap_Raw_ofList___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instForInOfForIn_x27___redArg___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_ofList___redArg___closed__0_value)} };
static const lean_object* l_Std_HashMap_Raw_ofList___redArg___closed__1 = (const lean_object*)&l_Std_HashMap_Raw_ofList___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_ofList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_ofList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_unitOfList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_unitOfList(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashMap_Raw_ofArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__9_value)} };
static const lean_object* l_Std_HashMap_Raw_ofArray___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_Raw_ofArray___redArg___closed__0_value;
static const lean_closure_object l_Std_HashMap_Raw_ofArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instForInOfForIn_x27___redArg___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_ofArray___redArg___closed__0_value)} };
static const lean_object* l_Std_HashMap_Raw_ofArray___redArg___closed__1 = (const lean_object*)&l_Std_HashMap_Raw_ofArray___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_ofArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_ofArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_alter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_modify(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toList___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toList___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashMap_Raw_toList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_Raw_toList___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_Raw_toList___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_Raw_toList___redArg___closed__0_value;
static const lean_closure_object l_Std_HashMap_Raw_toList___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_Raw_toList___redArg___lam__1, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__9_value),((lean_object*)&l_Std_HashMap_Raw_toList___redArg___closed__0_value)} };
static const lean_object* l_Std_HashMap_Raw_toList___redArg___closed__1 = (const lean_object*)&l_Std_HashMap_Raw_toList___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_foldM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_fold___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_fold___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_fold___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forIn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_HashMap_Raw_all___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_HashMap_Raw_all___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_Raw_all___redArg___closed__0_value;
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_all___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_all(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_any___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_any___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_any___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_any(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_union___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_union___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashMap_Raw_union___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__9_value)} };
static const lean_object* l_Std_HashMap_Raw_union___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_Raw_union___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_union___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_union(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_inter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_inter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_diff___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_diff___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_diff___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_diff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instUnionOfBEqOfHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instUnionOfBEqOfHashable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInterOfBEqOfHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInterOfBEqOfHashable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSDiffOfBEqOfHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSDiffOfBEqOfHashable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_beq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_beq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instBEqOfHashable___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instBEqOfHashable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filterMap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filterMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toArray___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashMap_Raw_toArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_Raw_toArray___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_Raw_toArray___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_Raw_toArray___redArg___closed__0_value;
static const lean_closure_object l_Std_HashMap_Raw_toArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_Raw_toArray___redArg___lam__1, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__9_value),((lean_object*)&l_Std_HashMap_Raw_toArray___redArg___closed__0_value)} };
static const lean_object* l_Std_HashMap_Raw_toArray___redArg___closed__1 = (const lean_object*)&l_Std_HashMap_Raw_toArray___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashMap_Raw_keysArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_Raw_keysArray___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_Raw_keysArray___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_Raw_keysArray___redArg___closed__0_value;
static const lean_closure_object l_Std_HashMap_Raw_keysArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_Raw_keysArray___redArg___lam__1, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__9_value),((lean_object*)&l_Std_HashMap_Raw_keysArray___redArg___closed__0_value)} };
static const lean_object* l_Std_HashMap_Raw_keysArray___redArg___closed__1 = (const lean_object*)&l_Std_HashMap_Raw_keysArray___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashMap_Raw_values___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_Raw_values___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_Raw_values___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_Raw_values___redArg___closed__0_value;
static const lean_closure_object l_Std_HashMap_Raw_values___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_Raw_keys___redArg___lam__1, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__9_value),((lean_object*)&l_Std_HashMap_Raw_values___redArg___closed__0_value)} };
static const lean_object* l_Std_HashMap_Raw_values___redArg___closed__1 = (const lean_object*)&l_Std_HashMap_Raw_values___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesArray___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashMap_Raw_valuesArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_Raw_valuesArray___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_Raw_valuesArray___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_Raw_valuesArray___redArg___closed__0_value;
static const lean_closure_object l_Std_HashMap_Raw_valuesArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_Raw_keysArray___redArg___lam__1, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__9_value),((lean_object*)&l_Std_HashMap_Raw_valuesArray___redArg___closed__0_value)} };
static const lean_object* l_Std_HashMap_Raw_valuesArray___redArg___closed__1 = (const lean_object*)&l_Std_HashMap_Raw_valuesArray___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertManyIfNewUnit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertManyIfNewUnit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_unitOfArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_unitOfArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_Internal_numBuckets___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_Internal_numBuckets___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_Internal_numBuckets(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_Internal_numBuckets___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_HashMap_Raw_instRepr___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Std.HashMap.Raw.ofList "};
static const lean_object* l_Std_HashMap_Raw_instRepr___redArg___lam__2___closed__0 = (const lean_object*)&l_Std_HashMap_Raw_instRepr___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_Std_HashMap_Raw_instRepr___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_instRepr___redArg___lam__2___closed__0_value)}};
static const lean_object* l_Std_HashMap_Raw_instRepr___redArg___lam__2___closed__1 = (const lean_object*)&l_Std_HashMap_Raw_instRepr___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_emptyWithCapacity___redArg(lean_object* v_capacity_1_){
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
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_emptyWithCapacity___redArg___boxed(lean_object* v_capacity_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Std_HashMap_Raw_emptyWithCapacity___redArg(v_capacity_11_);
lean_dec(v_capacity_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_emptyWithCapacity(lean_object* v_00_u03b1_13_, lean_object* v_00_u03b2_14_, lean_object* v_capacity_15_){
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
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_emptyWithCapacity___boxed(lean_object* v_00_u03b1_25_, lean_object* v_00_u03b2_26_, lean_object* v_capacity_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Std_HashMap_Raw_emptyWithCapacity(v_00_u03b1_25_, v_00_u03b2_26_, v_capacity_27_);
lean_dec(v_capacity_27_);
return v_res_28_;
}
}
static lean_object* _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__0(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = lean_box(0);
v___x_30_ = lean_unsigned_to_nat(16u);
v___x_31_ = lean_mk_array(v___x_30_, v___x_29_);
return v___x_31_;
}
}
static lean_object* _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1(void){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_32_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__0, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__0_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__0);
v___x_33_ = lean_unsigned_to_nat(0u);
v___x_34_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_34_, 0, v___x_33_);
lean_ctor_set(v___x_34_, 1, v___x_32_);
return v___x_34_;
}
}
lean_object* l_Std_HashMap_Raw_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_36_;
}
}
LEAN_EXPORT void l_Std_HashMap_Raw_instEmptyCollection___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_37_;
v_res_37_ = l_Std_HashMap_Raw_instEmptyCollection___redArg();
stack->m_obj
 = v_res_37_;
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instEmptyCollection___redArg___boxed(lean_object* v___dummy_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Std_HashMap_Raw_instEmptyCollection___redArg();
return v_res_39_;
}
}
static lean_object* _init_l_Std_HashMap_Raw_instEmptyCollection___closed__0(void){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Std_HashMap_Raw_instEmptyCollection___redArg();
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instEmptyCollection(lean_object* v_00_u03b1_41_, lean_object* v_00_u03b2_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__0, &l_Std_HashMap_Raw_instEmptyCollection___closed__0_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__0);
return v___x_43_;
}
}
lean_object* l_Std_HashMap_Raw_instInhabited___redArg(){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_45_;
}
}
LEAN_EXPORT void l_Std_HashMap_Raw_instInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_46_;
v_res_46_ = l_Std_HashMap_Raw_instInhabited___redArg();
stack->m_obj
 = v_res_46_;
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInhabited___redArg___boxed(lean_object* v___dummy_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Std_HashMap_Raw_instInhabited___redArg();
return v_res_48_;
}
}
static lean_object* _init_l_Std_HashMap_Raw_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Std_HashMap_Raw_instInhabited___redArg();
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInhabited(lean_object* v_00_u03b1_50_, lean_object* v_00_u03b2_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = lean_obj_once(&l_Std_HashMap_Raw_instInhabited___closed__0, &l_Std_HashMap_Raw_instInhabited___closed__0_once, _init_l_Std_HashMap_Raw_instInhabited___closed__0);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_markLinear___redArg(lean_object* v_m_53_){
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
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_markLinear(lean_object* v_00_u03b1_64_, lean_object* v_00_u03b2_65_, lean_object* v_m_66_){
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
static lean_object* _init_l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__6(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = ((lean_object*)(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__5));
v___x_118_ = l_String_toRawSubstring_x27(v___x_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1(lean_object* v_x_140_, lean_object* v_a_141_, lean_object* v_a_142_){
_start:
{
lean_object* v___x_143_; uint8_t v___x_144_; 
v___x_143_ = ((lean_object*)(l_Std_HashMap_Raw_term___x7em___00__closed__4));
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
v___x_156_ = ((lean_object*)(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4));
v___x_157_ = lean_obj_once(&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__6, &l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__6_once, _init_l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__6);
v___x_158_ = ((lean_object*)(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__7));
lean_inc(v_currMacroScope_148_);
lean_inc(v_quotContext_147_);
v___x_159_ = l_Lean_addMacroScope(v_quotContext_147_, v___x_158_, v_currMacroScope_148_);
v___x_160_ = ((lean_object*)(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__12));
lean_inc_n(v___x_155_, 2);
v___x_161_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_161_, 0, v___x_155_);
lean_ctor_set(v___x_161_, 1, v___x_157_);
lean_ctor_set(v___x_161_, 2, v___x_159_);
lean_ctor_set(v___x_161_, 3, v___x_160_);
v___x_162_ = ((lean_object*)(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__14));
v___x_163_ = l_Lean_Syntax_node2(v___x_155_, v___x_162_, v___x_151_, v___x_153_);
v___x_164_ = l_Lean_Syntax_node2(v___x_155_, v___x_156_, v___x_161_, v___x_163_);
v___x_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
lean_ctor_set(v___x_165_, 1, v_a_142_);
return v___x_165_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___boxed(lean_object* v_x_166_, lean_object* v_a_167_, lean_object* v_a_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1(v_x_166_, v_a_167_, v_a_168_);
lean_dec_ref(v_a_167_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1(lean_object* v_x_173_, lean_object* v_a_174_, lean_object* v_a_175_){
_start:
{
lean_object* v___x_176_; uint8_t v___x_177_; 
v___x_176_ = ((lean_object*)(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4));
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
v___x_182_ = ((lean_object*)(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___closed__1));
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
v___x_197_ = ((lean_object*)(l_Std_HashMap_Raw_term___x7em___00__closed__4));
v___x_198_ = ((lean_object*)(l_Std_HashMap_Raw_term___x7em___00__closed__7));
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
LEAN_EXPORT lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___boxed(lean_object* v_x_202_, lean_object* v_a_203_, lean_object* v_a_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1(v_x_202_, v_a_203_, v_a_204_);
lean_dec(v_a_203_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insert___redArg(lean_object* v_beq_206_, lean_object* v_inst_207_, lean_object* v_m_208_, lean_object* v_a_209_, lean_object* v_b_210_){
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
lean_dec_ref(v_beq_206_);
return v_m_208_;
}
else
{
lean_object* v___x_215_; 
v___x_215_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_beq_206_, v_inst_207_, v_m_208_, v_a_209_, v_b_210_);
return v___x_215_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insert(lean_object* v_00_u03b1_216_, lean_object* v_00_u03b2_217_, lean_object* v_beq_218_, lean_object* v_inst_219_, lean_object* v_m_220_, lean_object* v_a_221_, lean_object* v_b_222_){
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
lean_dec_ref(v_beq_218_);
return v_m_220_;
}
else
{
lean_object* v___x_227_; 
v___x_227_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_beq_218_, v_inst_219_, v_m_220_, v_a_221_, v_b_222_);
return v___x_227_;
}
}
}
static lean_object* _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__0, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__0_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__0);
v___x_229_ = lean_array_get_size(v___x_228_);
return v___x_229_;
}
}
static uint8_t _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_230_ = lean_obj_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0);
v___x_231_ = lean_unsigned_to_nat(0u);
v___x_232_ = lean_nat_dec_lt(v___x_231_, v___x_230_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0(lean_object* v_inst_233_, lean_object* v_inst_234_, lean_object* v_x_235_){
_start:
{
lean_object* v_fst_236_; lean_object* v_snd_237_; lean_object* v___x_238_; uint8_t v___x_239_; 
v_fst_236_ = lean_ctor_get(v_x_235_, 0);
lean_inc(v_fst_236_);
v_snd_237_ = lean_ctor_get(v_x_235_, 1);
lean_inc(v_snd_237_);
lean_dec_ref(v_x_235_);
v___x_238_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1);
v___x_239_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
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
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg(lean_object* v_inst_241_, lean_object* v_inst_242_){
_start:
{
lean_object* v___f_243_; 
v___f_243_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_243_, 0, v_inst_241_);
lean_closure_set(v___f_243_, 1, v_inst_242_);
return v___f_243_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable(lean_object* v_00_u03b1_244_, lean_object* v_00_u03b2_245_, lean_object* v_inst_246_, lean_object* v_inst_247_){
_start:
{
lean_object* v___f_248_; 
v___f_248_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_248_, 0, v_inst_246_);
lean_closure_set(v___f_248_, 1, v_inst_247_);
return v___f_248_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable___redArg___lam__0(lean_object* v_inst_249_, lean_object* v_inst_250_, lean_object* v_x_251_, lean_object* v_s_252_){
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
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable___redArg(lean_object* v_inst_260_, lean_object* v_inst_261_){
_start:
{
lean_object* v___f_262_; 
v___f_262_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_262_, 0, v_inst_260_);
lean_closure_set(v___f_262_, 1, v_inst_261_);
return v___f_262_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable(lean_object* v_00_u03b1_263_, lean_object* v_00_u03b2_264_, lean_object* v_inst_265_, lean_object* v_inst_266_){
_start:
{
lean_object* v___f_267_; 
v___f_267_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_267_, 0, v_inst_265_);
lean_closure_set(v___f_267_, 1, v_inst_266_);
return v___f_267_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertIfNew___redArg(lean_object* v_inst_268_, lean_object* v_inst_269_, lean_object* v_m_270_, lean_object* v_a_271_, lean_object* v_b_272_){
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
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertIfNew(lean_object* v_00_u03b1_278_, lean_object* v_00_u03b2_279_, lean_object* v_inst_280_, lean_object* v_inst_281_, lean_object* v_m_282_, lean_object* v_a_283_, lean_object* v_b_284_){
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
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_containsThenInsert___redArg(lean_object* v_inst_290_, lean_object* v_inst_291_, lean_object* v_m_292_, lean_object* v_a_293_, lean_object* v_b_294_){
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
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_containsThenInsert(lean_object* v_00_u03b1_354_, lean_object* v_00_u03b2_355_, lean_object* v_inst_356_, lean_object* v_inst_357_, lean_object* v_m_358_, lean_object* v_a_359_, lean_object* v_b_360_){
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
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_containsThenInsertIfNew___redArg(lean_object* v_inst_420_, lean_object* v_inst_421_, lean_object* v_m_422_, lean_object* v_a_423_, lean_object* v_b_424_){
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
v___x_430_ = lean_box(v___x_429_);
v___x_431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
lean_ctor_set(v___x_431_, 1, v_m_422_);
return v___x_431_;
}
else
{
lean_object* v___x_432_; uint64_t v___x_433_; uint64_t v___x_434_; uint64_t v___x_435_; uint64_t v___x_436_; uint64_t v_fold_437_; uint64_t v___x_438_; uint64_t v___x_439_; uint64_t v___x_440_; size_t v___x_441_; size_t v___x_442_; size_t v___x_443_; size_t v___x_444_; size_t v___x_445_; lean_object* v_bkt_446_; uint8_t v___x_447_; 
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
v___x_447_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_420_, v_a_423_, v_bkt_446_);
if (v___x_447_ == 0)
{
lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_472_; 
lean_inc_ref(v_buckets_426_);
lean_inc(v_size_425_);
v_isSharedCheck_472_ = !lean_is_exclusive(v_m_422_);
if (v_isSharedCheck_472_ == 0)
{
lean_object* v_unused_473_; lean_object* v_unused_474_; 
v_unused_473_ = lean_ctor_get(v_m_422_, 1);
lean_dec(v_unused_473_);
v_unused_474_ = lean_ctor_get(v_m_422_, 0);
lean_dec(v_unused_474_);
v___x_449_ = v_m_422_;
v_isShared_450_ = v_isSharedCheck_472_;
goto v_resetjp_448_;
}
else
{
lean_dec(v_m_422_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_472_;
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
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_size_x27_452_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v_val_461_);
v___x_463_ = v_reuseFailAlloc_466_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = lean_box(v___x_447_);
v___x_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
lean_ctor_set(v___x_465_, 1, v___x_463_);
return v___x_465_;
}
}
else
{
lean_object* v___x_468_; 
lean_dec_ref(v_inst_421_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 1, v_buckets_x27_454_);
lean_ctor_set(v___x_449_, 0, v_size_x27_452_);
v___x_468_ = v___x_449_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_size_x27_452_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v_buckets_x27_454_);
v___x_468_ = v_reuseFailAlloc_471_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_469_ = lean_box(v___x_447_);
v___x_470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
lean_ctor_set(v___x_470_, 1, v___x_468_);
return v___x_470_;
}
}
}
}
else
{
lean_object* v___x_475_; lean_object* v___x_476_; 
lean_dec(v_b_424_);
lean_dec(v_a_423_);
lean_dec_ref(v_inst_421_);
v___x_475_ = lean_box(v___x_447_);
v___x_476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
lean_ctor_set(v___x_476_, 1, v_m_422_);
return v___x_476_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_containsThenInsertIfNew(lean_object* v_00_u03b1_477_, lean_object* v_00_u03b2_478_, lean_object* v_inst_479_, lean_object* v_inst_480_, lean_object* v_m_481_, lean_object* v_a_482_, lean_object* v_b_483_){
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
lean_dec_ref(v_inst_480_);
lean_dec_ref(v_inst_479_);
v___x_489_ = lean_box(v___x_488_);
v___x_490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
lean_ctor_set(v___x_490_, 1, v_m_481_);
return v___x_490_;
}
else
{
lean_object* v___x_491_; uint64_t v___x_492_; uint64_t v___x_493_; uint64_t v___x_494_; uint64_t v___x_495_; uint64_t v_fold_496_; uint64_t v___x_497_; uint64_t v___x_498_; uint64_t v___x_499_; size_t v___x_500_; size_t v___x_501_; size_t v___x_502_; size_t v___x_503_; size_t v___x_504_; lean_object* v_bkt_505_; uint8_t v___x_506_; 
lean_inc_ref(v_inst_480_);
lean_inc_n(v_a_482_, 2);
v___x_491_ = lean_apply_1(v_inst_480_, v_a_482_);
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
v___x_506_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_479_, v_a_482_, v_bkt_505_);
if (v___x_506_ == 0)
{
lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_531_; 
lean_inc_ref(v_buckets_485_);
lean_inc(v_size_484_);
v_isSharedCheck_531_ = !lean_is_exclusive(v_m_481_);
if (v_isSharedCheck_531_ == 0)
{
lean_object* v_unused_532_; lean_object* v_unused_533_; 
v_unused_532_ = lean_ctor_get(v_m_481_, 1);
lean_dec(v_unused_532_);
v_unused_533_ = lean_ctor_get(v_m_481_, 0);
lean_dec(v_unused_533_);
v___x_508_ = v_m_481_;
v_isShared_509_ = v_isSharedCheck_531_;
goto v_resetjp_507_;
}
else
{
lean_dec(v_m_481_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_531_;
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
v_val_520_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_480_, v_buckets_x27_513_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 1, v_val_520_);
lean_ctor_set(v___x_508_, 0, v_size_x27_511_);
v___x_522_ = v___x_508_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_size_x27_511_);
lean_ctor_set(v_reuseFailAlloc_525_, 1, v_val_520_);
v___x_522_ = v_reuseFailAlloc_525_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = lean_box(v___x_506_);
v___x_524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_524_, 0, v___x_523_);
lean_ctor_set(v___x_524_, 1, v___x_522_);
return v___x_524_;
}
}
else
{
lean_object* v___x_527_; 
lean_dec_ref(v_inst_480_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 1, v_buckets_x27_513_);
lean_ctor_set(v___x_508_, 0, v_size_x27_511_);
v___x_527_ = v___x_508_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_size_x27_511_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_buckets_x27_513_);
v___x_527_ = v_reuseFailAlloc_530_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = lean_box(v___x_506_);
v___x_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
lean_ctor_set(v___x_529_, 1, v___x_527_);
return v___x_529_;
}
}
}
}
else
{
lean_object* v___x_534_; lean_object* v___x_535_; 
lean_dec(v_b_483_);
lean_dec(v_a_482_);
lean_dec_ref(v_inst_480_);
v___x_534_ = lean_box(v___x_506_);
v___x_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
lean_ctor_set(v___x_535_, 1, v_m_481_);
return v___x_535_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getThenInsertIfNew_x3f___redArg(lean_object* v_inst_536_, lean_object* v_inst_537_, lean_object* v_m_538_, lean_object* v_a_539_, lean_object* v_b_540_){
_start:
{
lean_object* v_size_541_; lean_object* v_buckets_542_; lean_object* v___x_543_; lean_object* v___x_544_; uint8_t v___x_545_; 
v_size_541_ = lean_ctor_get(v_m_538_, 0);
v_buckets_542_ = lean_ctor_get(v_m_538_, 1);
v___x_543_ = lean_unsigned_to_nat(0u);
v___x_544_ = lean_array_get_size(v_buckets_542_);
v___x_545_ = lean_nat_dec_lt(v___x_543_, v___x_544_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; lean_object* v___x_547_; 
lean_dec(v_b_540_);
lean_dec(v_a_539_);
lean_dec_ref(v_inst_537_);
lean_dec_ref(v_inst_536_);
v___x_546_ = lean_box(0);
v___x_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
lean_ctor_set(v___x_547_, 1, v_m_538_);
return v___x_547_;
}
else
{
lean_object* v___x_548_; uint64_t v___x_549_; uint64_t v___x_550_; uint64_t v___x_551_; uint64_t v___x_552_; uint64_t v_fold_553_; uint64_t v___x_554_; uint64_t v___x_555_; uint64_t v___x_556_; size_t v___x_557_; size_t v___x_558_; size_t v___x_559_; size_t v___x_560_; size_t v___x_561_; lean_object* v_bkt_562_; lean_object* v___x_563_; 
lean_inc_ref(v_inst_537_);
lean_inc_n(v_a_539_, 2);
v___x_548_ = lean_apply_1(v_inst_537_, v_a_539_);
v___x_549_ = 32ULL;
v___x_550_ = lean_unbox_uint64(v___x_548_);
v___x_551_ = lean_uint64_shift_right(v___x_550_, v___x_549_);
v___x_552_ = lean_unbox_uint64(v___x_548_);
lean_dec_ref(v___x_548_);
v_fold_553_ = lean_uint64_xor(v___x_552_, v___x_551_);
v___x_554_ = 16ULL;
v___x_555_ = lean_uint64_shift_right(v_fold_553_, v___x_554_);
v___x_556_ = lean_uint64_xor(v_fold_553_, v___x_555_);
v___x_557_ = lean_uint64_to_usize(v___x_556_);
v___x_558_ = lean_usize_of_nat(v___x_544_);
v___x_559_ = ((size_t)1ULL);
v___x_560_ = lean_usize_sub(v___x_558_, v___x_559_);
v___x_561_ = lean_usize_land(v___x_557_, v___x_560_);
v_bkt_562_ = lean_array_uget_borrowed(v_buckets_542_, v___x_561_);
lean_inc(v_bkt_562_);
v___x_563_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_inst_536_, v_a_539_, v_bkt_562_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_586_; 
lean_inc_ref(v_buckets_542_);
lean_inc(v_size_541_);
v_isSharedCheck_586_ = !lean_is_exclusive(v_m_538_);
if (v_isSharedCheck_586_ == 0)
{
lean_object* v_unused_587_; lean_object* v_unused_588_; 
v_unused_587_ = lean_ctor_get(v_m_538_, 1);
lean_dec(v_unused_587_);
v_unused_588_ = lean_ctor_get(v_m_538_, 0);
lean_dec(v_unused_588_);
v___x_565_ = v_m_538_;
v_isShared_566_ = v_isSharedCheck_586_;
goto v_resetjp_564_;
}
else
{
lean_dec(v_m_538_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_586_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_567_; lean_object* v_size_x27_568_; lean_object* v___x_569_; lean_object* v_buckets_x27_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; uint8_t v___x_576_; 
v___x_567_ = lean_unsigned_to_nat(1u);
v_size_x27_568_ = lean_nat_add(v_size_541_, v___x_567_);
lean_dec(v_size_541_);
lean_inc(v_bkt_562_);
v___x_569_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_569_, 0, v_a_539_);
lean_ctor_set(v___x_569_, 1, v_b_540_);
lean_ctor_set(v___x_569_, 2, v_bkt_562_);
v_buckets_x27_570_ = lean_array_uset(v_buckets_542_, v___x_561_, v___x_569_);
v___x_571_ = lean_unsigned_to_nat(4u);
v___x_572_ = lean_nat_mul(v_size_x27_568_, v___x_571_);
v___x_573_ = lean_unsigned_to_nat(3u);
v___x_574_ = lean_nat_div(v___x_572_, v___x_573_);
lean_dec(v___x_572_);
v___x_575_ = lean_array_get_size(v_buckets_x27_570_);
v___x_576_ = lean_nat_dec_le(v___x_574_, v___x_575_);
lean_dec(v___x_574_);
if (v___x_576_ == 0)
{
lean_object* v_val_577_; lean_object* v___x_579_; 
v_val_577_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_537_, v_buckets_x27_570_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 1, v_val_577_);
lean_ctor_set(v___x_565_, 0, v_size_x27_568_);
v___x_579_ = v___x_565_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_size_x27_568_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v_val_577_);
v___x_579_ = v_reuseFailAlloc_581_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
lean_object* v___x_580_; 
v___x_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_580_, 0, v___x_563_);
lean_ctor_set(v___x_580_, 1, v___x_579_);
return v___x_580_;
}
}
else
{
lean_object* v___x_583_; 
lean_dec_ref(v_inst_537_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 1, v_buckets_x27_570_);
lean_ctor_set(v___x_565_, 0, v_size_x27_568_);
v___x_583_ = v___x_565_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_size_x27_568_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v_buckets_x27_570_);
v___x_583_ = v_reuseFailAlloc_585_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
lean_object* v___x_584_; 
v___x_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_563_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
return v___x_584_;
}
}
}
}
else
{
lean_object* v___x_589_; 
lean_dec(v_b_540_);
lean_dec(v_a_539_);
lean_dec_ref(v_inst_537_);
v___x_589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_589_, 0, v___x_563_);
lean_ctor_set(v___x_589_, 1, v_m_538_);
return v___x_589_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_590_, lean_object* v_00_u03b2_591_, lean_object* v_inst_592_, lean_object* v_inst_593_, lean_object* v_m_594_, lean_object* v_a_595_, lean_object* v_b_596_){
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
v___x_602_ = lean_box(0);
v___x_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
lean_ctor_set(v___x_603_, 1, v_m_594_);
return v___x_603_;
}
else
{
lean_object* v___x_604_; uint64_t v___x_605_; uint64_t v___x_606_; uint64_t v___x_607_; uint64_t v___x_608_; uint64_t v_fold_609_; uint64_t v___x_610_; uint64_t v___x_611_; uint64_t v___x_612_; size_t v___x_613_; size_t v___x_614_; size_t v___x_615_; size_t v___x_616_; size_t v___x_617_; lean_object* v_bkt_618_; lean_object* v___x_619_; 
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
v___x_619_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_inst_592_, v_a_595_, v_bkt_618_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_642_; 
lean_inc_ref(v_buckets_598_);
lean_inc(v_size_597_);
v_isSharedCheck_642_ = !lean_is_exclusive(v_m_594_);
if (v_isSharedCheck_642_ == 0)
{
lean_object* v_unused_643_; lean_object* v_unused_644_; 
v_unused_643_ = lean_ctor_get(v_m_594_, 1);
lean_dec(v_unused_643_);
v_unused_644_ = lean_ctor_get(v_m_594_, 0);
lean_dec(v_unused_644_);
v___x_621_ = v_m_594_;
v_isShared_622_ = v_isSharedCheck_642_;
goto v_resetjp_620_;
}
else
{
lean_dec(v_m_594_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_642_;
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
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_size_x27_624_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_val_633_);
v___x_635_ = v_reuseFailAlloc_637_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
lean_object* v___x_636_; 
v___x_636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_619_);
lean_ctor_set(v___x_636_, 1, v___x_635_);
return v___x_636_;
}
}
else
{
lean_object* v___x_639_; 
lean_dec_ref(v_inst_593_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 1, v_buckets_x27_626_);
lean_ctor_set(v___x_621_, 0, v_size_x27_624_);
v___x_639_ = v___x_621_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_size_x27_624_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v_buckets_x27_626_);
v___x_639_ = v_reuseFailAlloc_641_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
lean_object* v___x_640_; 
v___x_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_619_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
return v___x_640_;
}
}
}
}
else
{
lean_object* v___x_645_; 
lean_dec(v_b_596_);
lean_dec(v_a_595_);
lean_dec_ref(v_inst_593_);
v___x_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_645_, 0, v___x_619_);
lean_ctor_set(v___x_645_, 1, v_m_594_);
return v___x_645_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x3f___redArg(lean_object* v_beq_646_, lean_object* v_inst_647_, lean_object* v_m_648_, lean_object* v_a_649_){
_start:
{
lean_object* v_buckets_650_; lean_object* v___x_651_; lean_object* v___x_652_; uint8_t v___x_653_; 
v_buckets_650_ = lean_ctor_get(v_m_648_, 1);
v___x_651_ = lean_unsigned_to_nat(0u);
v___x_652_ = lean_array_get_size(v_buckets_650_);
v___x_653_ = lean_nat_dec_lt(v___x_651_, v___x_652_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; 
lean_dec(v_a_649_);
lean_dec_ref(v_inst_647_);
lean_dec_ref(v_beq_646_);
v___x_654_ = lean_box(0);
return v___x_654_;
}
else
{
lean_object* v___x_655_; 
v___x_655_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_beq_646_, v_inst_647_, v_m_648_, v_a_649_);
return v___x_655_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x3f___redArg___boxed(lean_object* v_beq_656_, lean_object* v_inst_657_, lean_object* v_m_658_, lean_object* v_a_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Std_HashMap_Raw_get_x3f___redArg(v_beq_656_, v_inst_657_, v_m_658_, v_a_659_);
lean_dec_ref(v_m_658_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x3f(lean_object* v_00_u03b1_661_, lean_object* v_00_u03b2_662_, lean_object* v_beq_663_, lean_object* v_inst_664_, lean_object* v_m_665_, lean_object* v_a_666_){
_start:
{
lean_object* v_buckets_667_; lean_object* v___x_668_; lean_object* v___x_669_; uint8_t v___x_670_; 
v_buckets_667_ = lean_ctor_get(v_m_665_, 1);
v___x_668_ = lean_unsigned_to_nat(0u);
v___x_669_ = lean_array_get_size(v_buckets_667_);
v___x_670_ = lean_nat_dec_lt(v___x_668_, v___x_669_);
if (v___x_670_ == 0)
{
lean_object* v___x_671_; 
lean_dec(v_a_666_);
lean_dec_ref(v_inst_664_);
lean_dec_ref(v_beq_663_);
v___x_671_ = lean_box(0);
return v___x_671_;
}
else
{
lean_object* v___x_672_; 
v___x_672_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_beq_663_, v_inst_664_, v_m_665_, v_a_666_);
return v___x_672_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x3f___boxed(lean_object* v_00_u03b1_673_, lean_object* v_00_u03b2_674_, lean_object* v_beq_675_, lean_object* v_inst_676_, lean_object* v_m_677_, lean_object* v_a_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Std_HashMap_Raw_get_x3f(v_00_u03b1_673_, v_00_u03b2_674_, v_beq_675_, v_inst_676_, v_m_677_, v_a_678_);
lean_dec_ref(v_m_677_);
return v_res_679_;
}
}
uint8_t l_Std_HashMap_Raw_contains___redArg(lean_object* v_inst_680_, lean_object* v_inst_681_, lean_object* v_m_682_, lean_object* v_a_683_){
_start:
{
lean_object* v_buckets_684_; lean_object* v___x_685_; lean_object* v___x_686_; uint8_t v___x_687_; 
v_buckets_684_ = lean_ctor_get(v_m_682_, 1);
v___x_685_ = lean_unsigned_to_nat(0u);
v___x_686_ = lean_array_get_size(v_buckets_684_);
v___x_687_ = lean_nat_dec_lt(v___x_685_, v___x_686_);
if (v___x_687_ == 0)
{
lean_dec(v_a_683_);
lean_dec_ref(v_inst_681_);
lean_dec_ref(v_inst_680_);
return v___x_687_;
}
else
{
uint8_t v___x_688_; 
v___x_688_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_680_, v_inst_681_, v_m_682_, v_a_683_);
return v___x_688_;
}
}
}
LEAN_EXPORT void l_Std_HashMap_Raw_contains___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_680_ = stack[0].m_obj;
lean_object* v_inst_681_ = stack[1].m_obj;
lean_object* v_m_682_ = stack[2].m_obj;
lean_object* v_a_683_ = stack[3].m_obj;
uint8_t v_res_689_;
v_res_689_ = l_Std_HashMap_Raw_contains___redArg(v_inst_680_, v_inst_681_, v_m_682_, v_a_683_);
stack->m_num = v_res_689_;
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_contains___redArg___boxed(lean_object* v_inst_690_, lean_object* v_inst_691_, lean_object* v_m_692_, lean_object* v_a_693_){
_start:
{
uint8_t v_res_694_; lean_object* v_r_695_; 
v_res_694_ = l_Std_HashMap_Raw_contains___redArg(v_inst_690_, v_inst_691_, v_m_692_, v_a_693_);
lean_dec_ref(v_m_692_);
v_r_695_ = lean_box(v_res_694_);
return v_r_695_;
}
}
uint8_t l_Std_HashMap_Raw_contains(lean_object* v_00_u03b1_696_, lean_object* v_00_u03b2_697_, lean_object* v_inst_698_, lean_object* v_inst_699_, lean_object* v_m_700_, lean_object* v_a_701_){
_start:
{
lean_object* v_buckets_702_; lean_object* v___x_703_; lean_object* v___x_704_; uint8_t v___x_705_; 
v_buckets_702_ = lean_ctor_get(v_m_700_, 1);
v___x_703_ = lean_unsigned_to_nat(0u);
v___x_704_ = lean_array_get_size(v_buckets_702_);
v___x_705_ = lean_nat_dec_lt(v___x_703_, v___x_704_);
if (v___x_705_ == 0)
{
lean_dec(v_a_701_);
lean_dec_ref(v_inst_699_);
lean_dec_ref(v_inst_698_);
return v___x_705_;
}
else
{
uint8_t v___x_706_; 
v___x_706_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_698_, v_inst_699_, v_m_700_, v_a_701_);
return v___x_706_;
}
}
}
LEAN_EXPORT void l_Std_HashMap_Raw_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_698_ = stack[2].m_obj;
lean_object* v_inst_699_ = stack[3].m_obj;
lean_object* v_m_700_ = stack[4].m_obj;
lean_object* v_a_701_ = stack[5].m_obj;
uint8_t v_res_707_;
v_res_707_ = l_Std_HashMap_Raw_contains(lean_box(0), lean_box(0), v_inst_698_, v_inst_699_, v_m_700_, v_a_701_);
stack->m_num = v_res_707_;
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_contains___boxed(lean_object* v_00_u03b1_708_, lean_object* v_00_u03b2_709_, lean_object* v_inst_710_, lean_object* v_inst_711_, lean_object* v_m_712_, lean_object* v_a_713_){
_start:
{
uint8_t v_res_714_; lean_object* v_r_715_; 
v_res_714_ = l_Std_HashMap_Raw_contains(v_00_u03b1_708_, v_00_u03b2_709_, v_inst_710_, v_inst_711_, v_m_712_, v_a_713_);
lean_dec_ref(v_m_712_);
v_r_715_ = lean_box(v_res_714_);
return v_r_715_;
}
}
lean_object* l_Std_HashMap_Raw_instMembershipOfBEqOfHashable___redArg(){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = lean_box(0);
return v___x_717_;
}
}
LEAN_EXPORT void l_Std_HashMap_Raw_instMembershipOfBEqOfHashable___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_718_;
v_res_718_ = l_Std_HashMap_Raw_instMembershipOfBEqOfHashable___redArg();
stack->m_obj
 = v_res_718_;
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instMembershipOfBEqOfHashable___redArg___boxed(lean_object* v___dummy_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Std_HashMap_Raw_instMembershipOfBEqOfHashable___redArg();
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instMembershipOfBEqOfHashable(lean_object* v_00_u03b1_721_, lean_object* v_00_u03b2_722_, lean_object* v_inst_723_, lean_object* v_inst_724_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = lean_box(0);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instMembershipOfBEqOfHashable___boxed(lean_object* v_00_u03b1_726_, lean_object* v_00_u03b2_727_, lean_object* v_inst_728_, lean_object* v_inst_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Std_HashMap_Raw_instMembershipOfBEqOfHashable(v_00_u03b1_726_, v_00_u03b2_727_, v_inst_728_, v_inst_729_);
lean_dec_ref(v_inst_729_);
lean_dec_ref(v_inst_728_);
return v_res_730_;
}
}
uint8_t l_Std_HashMap_Raw_instDecidableMem___redArg(lean_object* v_inst_731_, lean_object* v_inst_732_, lean_object* v_m_733_, lean_object* v_a_734_){
_start:
{
uint8_t v___x_735_; 
v___x_735_ = l_Std_DHashMap_Raw_instDecidableMem___redArg(v_inst_731_, v_inst_732_, v_m_733_, v_a_734_);
return v___x_735_;
}
}
LEAN_EXPORT void l_Std_HashMap_Raw_instDecidableMem___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_731_ = stack[0].m_obj;
lean_object* v_inst_732_ = stack[1].m_obj;
lean_object* v_m_733_ = stack[2].m_obj;
lean_object* v_a_734_ = stack[3].m_obj;
uint8_t v_res_736_;
v_res_736_ = l_Std_HashMap_Raw_instDecidableMem___redArg(v_inst_731_, v_inst_732_, v_m_733_, v_a_734_);
stack->m_num = v_res_736_;
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instDecidableMem___redArg___boxed(lean_object* v_inst_737_, lean_object* v_inst_738_, lean_object* v_m_739_, lean_object* v_a_740_){
_start:
{
uint8_t v_res_741_; lean_object* v_r_742_; 
v_res_741_ = l_Std_HashMap_Raw_instDecidableMem___redArg(v_inst_737_, v_inst_738_, v_m_739_, v_a_740_);
lean_dec_ref(v_m_739_);
v_r_742_ = lean_box(v_res_741_);
return v_r_742_;
}
}
uint8_t l_Std_HashMap_Raw_instDecidableMem(lean_object* v_00_u03b1_743_, lean_object* v_00_u03b2_744_, lean_object* v_inst_745_, lean_object* v_inst_746_, lean_object* v_m_747_, lean_object* v_a_748_){
_start:
{
uint8_t v___x_749_; 
v___x_749_ = l_Std_DHashMap_Raw_instDecidableMem___redArg(v_inst_745_, v_inst_746_, v_m_747_, v_a_748_);
return v___x_749_;
}
}
LEAN_EXPORT void l_Std_HashMap_Raw_instDecidableMem_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_745_ = stack[2].m_obj;
lean_object* v_inst_746_ = stack[3].m_obj;
lean_object* v_m_747_ = stack[4].m_obj;
lean_object* v_a_748_ = stack[5].m_obj;
uint8_t v_res_750_;
v_res_750_ = l_Std_HashMap_Raw_instDecidableMem(lean_box(0), lean_box(0), v_inst_745_, v_inst_746_, v_m_747_, v_a_748_);
stack->m_num = v_res_750_;
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instDecidableMem___boxed(lean_object* v_00_u03b1_751_, lean_object* v_00_u03b2_752_, lean_object* v_inst_753_, lean_object* v_inst_754_, lean_object* v_m_755_, lean_object* v_a_756_){
_start:
{
uint8_t v_res_757_; lean_object* v_r_758_; 
v_res_757_ = l_Std_HashMap_Raw_instDecidableMem(v_00_u03b1_751_, v_00_u03b2_752_, v_inst_753_, v_inst_754_, v_m_755_, v_a_756_);
lean_dec_ref(v_m_755_);
v_r_758_ = lean_box(v_res_757_);
return v_r_758_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get___redArg(lean_object* v_inst_759_, lean_object* v_inst_760_, lean_object* v_m_761_, lean_object* v_a_762_){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_759_, v_inst_760_, v_m_761_, v_a_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get___redArg___boxed(lean_object* v_inst_764_, lean_object* v_inst_765_, lean_object* v_m_766_, lean_object* v_a_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Std_HashMap_Raw_get___redArg(v_inst_764_, v_inst_765_, v_m_766_, v_a_767_);
lean_dec_ref(v_m_766_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get(lean_object* v_00_u03b1_769_, lean_object* v_00_u03b2_770_, lean_object* v_inst_771_, lean_object* v_inst_772_, lean_object* v_m_773_, lean_object* v_a_774_, lean_object* v_h_775_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_771_, v_inst_772_, v_m_773_, v_a_774_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get___boxed(lean_object* v_00_u03b1_777_, lean_object* v_00_u03b2_778_, lean_object* v_inst_779_, lean_object* v_inst_780_, lean_object* v_m_781_, lean_object* v_a_782_, lean_object* v_h_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Std_HashMap_Raw_get(v_00_u03b1_777_, v_00_u03b2_778_, v_inst_779_, v_inst_780_, v_m_781_, v_a_782_, v_h_783_);
lean_dec_ref(v_m_781_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getD___redArg(lean_object* v_inst_785_, lean_object* v_inst_786_, lean_object* v_m_787_, lean_object* v_a_788_, lean_object* v_fallback_789_){
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
lean_inc(v_fallback_789_);
return v_fallback_789_;
}
else
{
lean_object* v___x_794_; 
v___x_794_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_inst_785_, v_inst_786_, v_m_787_, v_a_788_, v_fallback_789_);
return v___x_794_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getD___redArg___boxed(lean_object* v_inst_795_, lean_object* v_inst_796_, lean_object* v_m_797_, lean_object* v_a_798_, lean_object* v_fallback_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Std_HashMap_Raw_getD___redArg(v_inst_795_, v_inst_796_, v_m_797_, v_a_798_, v_fallback_799_);
lean_dec(v_fallback_799_);
lean_dec_ref(v_m_797_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getD(lean_object* v_00_u03b1_801_, lean_object* v_00_u03b2_802_, lean_object* v_inst_803_, lean_object* v_inst_804_, lean_object* v_m_805_, lean_object* v_a_806_, lean_object* v_fallback_807_){
_start:
{
lean_object* v_buckets_808_; lean_object* v___x_809_; lean_object* v___x_810_; uint8_t v___x_811_; 
v_buckets_808_ = lean_ctor_get(v_m_805_, 1);
v___x_809_ = lean_unsigned_to_nat(0u);
v___x_810_ = lean_array_get_size(v_buckets_808_);
v___x_811_ = lean_nat_dec_lt(v___x_809_, v___x_810_);
if (v___x_811_ == 0)
{
lean_dec(v_a_806_);
lean_dec_ref(v_inst_804_);
lean_dec_ref(v_inst_803_);
lean_inc(v_fallback_807_);
return v_fallback_807_;
}
else
{
lean_object* v___x_812_; 
v___x_812_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_inst_803_, v_inst_804_, v_m_805_, v_a_806_, v_fallback_807_);
return v___x_812_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getD___boxed(lean_object* v_00_u03b1_813_, lean_object* v_00_u03b2_814_, lean_object* v_inst_815_, lean_object* v_inst_816_, lean_object* v_m_817_, lean_object* v_a_818_, lean_object* v_fallback_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Std_HashMap_Raw_getD(v_00_u03b1_813_, v_00_u03b2_814_, v_inst_815_, v_inst_816_, v_m_817_, v_a_818_, v_fallback_819_);
lean_dec(v_fallback_819_);
lean_dec_ref(v_m_817_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x21___redArg(lean_object* v_inst_821_, lean_object* v_inst_822_, lean_object* v_inst_823_, lean_object* v_m_824_, lean_object* v_a_825_){
_start:
{
lean_object* v_buckets_826_; lean_object* v___x_827_; lean_object* v___x_828_; uint8_t v___x_829_; 
v_buckets_826_ = lean_ctor_get(v_m_824_, 1);
v___x_827_ = lean_unsigned_to_nat(0u);
v___x_828_ = lean_array_get_size(v_buckets_826_);
v___x_829_ = lean_nat_dec_lt(v___x_827_, v___x_828_);
if (v___x_829_ == 0)
{
lean_dec(v_a_825_);
lean_dec_ref(v_inst_822_);
lean_dec_ref(v_inst_821_);
lean_inc(v_inst_823_);
return v_inst_823_;
}
else
{
lean_object* v___x_830_; 
v___x_830_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_821_, v_inst_822_, v_inst_823_, v_m_824_, v_a_825_);
return v___x_830_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x21___redArg___boxed(lean_object* v_inst_831_, lean_object* v_inst_832_, lean_object* v_inst_833_, lean_object* v_m_834_, lean_object* v_a_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Std_HashMap_Raw_get_x21___redArg(v_inst_831_, v_inst_832_, v_inst_833_, v_m_834_, v_a_835_);
lean_dec_ref(v_m_834_);
lean_dec(v_inst_833_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x21(lean_object* v_00_u03b1_837_, lean_object* v_00_u03b2_838_, lean_object* v_inst_839_, lean_object* v_inst_840_, lean_object* v_inst_841_, lean_object* v_m_842_, lean_object* v_a_843_){
_start:
{
lean_object* v_buckets_844_; lean_object* v___x_845_; lean_object* v___x_846_; uint8_t v___x_847_; 
v_buckets_844_ = lean_ctor_get(v_m_842_, 1);
v___x_845_ = lean_unsigned_to_nat(0u);
v___x_846_ = lean_array_get_size(v_buckets_844_);
v___x_847_ = lean_nat_dec_lt(v___x_845_, v___x_846_);
if (v___x_847_ == 0)
{
lean_dec(v_a_843_);
lean_dec_ref(v_inst_840_);
lean_dec_ref(v_inst_839_);
lean_inc(v_inst_841_);
return v_inst_841_;
}
else
{
lean_object* v___x_848_; 
v___x_848_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_839_, v_inst_840_, v_inst_841_, v_m_842_, v_a_843_);
return v___x_848_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x21___boxed(lean_object* v_00_u03b1_849_, lean_object* v_00_u03b2_850_, lean_object* v_inst_851_, lean_object* v_inst_852_, lean_object* v_inst_853_, lean_object* v_m_854_, lean_object* v_a_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Std_HashMap_Raw_get_x21(v_00_u03b1_849_, v_00_u03b2_850_, v_inst_851_, v_inst_852_, v_inst_853_, v_m_854_, v_a_855_);
lean_dec_ref(v_m_854_);
lean_dec(v_inst_853_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__0(lean_object* v_inst_857_, lean_object* v_inst_858_, lean_object* v_m_859_, lean_object* v_a_860_, lean_object* v_h_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_857_, v_inst_858_, v_m_859_, v_a_860_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__0___boxed(lean_object* v_inst_863_, lean_object* v_inst_864_, lean_object* v_m_865_, lean_object* v_a_866_, lean_object* v_h_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__0(v_inst_863_, v_inst_864_, v_m_865_, v_a_866_, v_h_867_);
lean_dec_ref(v_m_865_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__1(lean_object* v_inst_869_, lean_object* v_inst_870_, lean_object* v_m_871_, lean_object* v_a_872_){
_start:
{
lean_object* v_buckets_873_; lean_object* v___x_874_; lean_object* v___x_875_; uint8_t v___x_876_; 
v_buckets_873_ = lean_ctor_get(v_m_871_, 1);
v___x_874_ = lean_unsigned_to_nat(0u);
v___x_875_ = lean_array_get_size(v_buckets_873_);
v___x_876_ = lean_nat_dec_lt(v___x_874_, v___x_875_);
if (v___x_876_ == 0)
{
lean_object* v___x_877_; 
lean_dec(v_a_872_);
lean_dec_ref(v_inst_870_);
lean_dec_ref(v_inst_869_);
v___x_877_ = lean_box(0);
return v___x_877_;
}
else
{
lean_object* v___x_878_; 
v___x_878_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_869_, v_inst_870_, v_m_871_, v_a_872_);
return v___x_878_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__1___boxed(lean_object* v_inst_879_, lean_object* v_inst_880_, lean_object* v_m_881_, lean_object* v_a_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__1(v_inst_879_, v_inst_880_, v_m_881_, v_a_882_);
lean_dec_ref(v_m_881_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__2(lean_object* v_inst_884_, lean_object* v_inst_885_, lean_object* v_inst_886_, lean_object* v_m_887_, lean_object* v_a_888_){
_start:
{
lean_object* v_buckets_889_; lean_object* v___x_890_; lean_object* v___x_891_; uint8_t v___x_892_; 
v_buckets_889_ = lean_ctor_get(v_m_887_, 1);
v___x_890_ = lean_unsigned_to_nat(0u);
v___x_891_ = lean_array_get_size(v_buckets_889_);
v___x_892_ = lean_nat_dec_lt(v___x_890_, v___x_891_);
if (v___x_892_ == 0)
{
lean_dec(v_a_888_);
lean_dec_ref(v_inst_885_);
lean_dec_ref(v_inst_884_);
lean_inc(v_inst_886_);
return v_inst_886_;
}
else
{
lean_object* v___x_893_; 
v___x_893_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_884_, v_inst_885_, v_inst_886_, v_m_887_, v_a_888_);
return v___x_893_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__2___boxed(lean_object* v_inst_894_, lean_object* v_inst_895_, lean_object* v_inst_896_, lean_object* v_m_897_, lean_object* v_a_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__2(v_inst_894_, v_inst_895_, v_inst_896_, v_m_897_, v_a_898_);
lean_dec_ref(v_m_897_);
lean_dec(v_inst_896_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg(lean_object* v_inst_900_, lean_object* v_inst_901_){
_start:
{
lean_object* v___f_902_; lean_object* v___f_903_; lean_object* v___f_904_; lean_object* v___x_905_; 
lean_inc_ref_n(v_inst_901_, 2);
lean_inc_ref_n(v_inst_900_, 2);
v___f_902_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_902_, 0, v_inst_900_);
lean_closure_set(v___f_902_, 1, v_inst_901_);
v___f_903_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_903_, 0, v_inst_900_);
lean_closure_set(v___f_903_, 1, v_inst_901_);
v___f_904_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__2___boxed), 5, 2);
lean_closure_set(v___f_904_, 0, v_inst_900_);
lean_closure_set(v___f_904_, 1, v_inst_901_);
v___x_905_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_905_, 0, v___f_902_);
lean_ctor_set(v___x_905_, 1, v___f_903_);
lean_ctor_set(v___x_905_, 2, v___f_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem(lean_object* v_00_u03b1_906_, lean_object* v_00_u03b2_907_, lean_object* v_inst_908_, lean_object* v_inst_909_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = l_Std_HashMap_Raw_instGetElem_x3fMem___redArg(v_inst_908_, v_inst_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x3f___redArg(lean_object* v_inst_911_, lean_object* v_inst_912_, lean_object* v_m_913_, lean_object* v_a_914_){
_start:
{
lean_object* v_buckets_915_; lean_object* v___x_916_; lean_object* v___x_917_; uint8_t v___x_918_; 
v_buckets_915_ = lean_ctor_get(v_m_913_, 1);
v___x_916_ = lean_unsigned_to_nat(0u);
v___x_917_ = lean_array_get_size(v_buckets_915_);
v___x_918_ = lean_nat_dec_lt(v___x_916_, v___x_917_);
if (v___x_918_ == 0)
{
lean_object* v___x_919_; 
lean_dec(v_a_914_);
lean_dec_ref(v_inst_912_);
lean_dec_ref(v_inst_911_);
v___x_919_ = lean_box(0);
return v___x_919_;
}
else
{
lean_object* v___x_920_; 
v___x_920_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_911_, v_inst_912_, v_m_913_, v_a_914_);
return v___x_920_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x3f___redArg___boxed(lean_object* v_inst_921_, lean_object* v_inst_922_, lean_object* v_m_923_, lean_object* v_a_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Std_HashMap_Raw_getKey_x3f___redArg(v_inst_921_, v_inst_922_, v_m_923_, v_a_924_);
lean_dec_ref(v_m_923_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x3f(lean_object* v_00_u03b1_926_, lean_object* v_00_u03b2_927_, lean_object* v_inst_928_, lean_object* v_inst_929_, lean_object* v_m_930_, lean_object* v_a_931_){
_start:
{
lean_object* v_buckets_932_; lean_object* v___x_933_; lean_object* v___x_934_; uint8_t v___x_935_; 
v_buckets_932_ = lean_ctor_get(v_m_930_, 1);
v___x_933_ = lean_unsigned_to_nat(0u);
v___x_934_ = lean_array_get_size(v_buckets_932_);
v___x_935_ = lean_nat_dec_lt(v___x_933_, v___x_934_);
if (v___x_935_ == 0)
{
lean_object* v___x_936_; 
lean_dec(v_a_931_);
lean_dec_ref(v_inst_929_);
lean_dec_ref(v_inst_928_);
v___x_936_ = lean_box(0);
return v___x_936_;
}
else
{
lean_object* v___x_937_; 
v___x_937_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_928_, v_inst_929_, v_m_930_, v_a_931_);
return v___x_937_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x3f___boxed(lean_object* v_00_u03b1_938_, lean_object* v_00_u03b2_939_, lean_object* v_inst_940_, lean_object* v_inst_941_, lean_object* v_m_942_, lean_object* v_a_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Std_HashMap_Raw_getKey_x3f(v_00_u03b1_938_, v_00_u03b2_939_, v_inst_940_, v_inst_941_, v_m_942_, v_a_943_);
lean_dec_ref(v_m_942_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey___redArg(lean_object* v_inst_945_, lean_object* v_inst_946_, lean_object* v_m_947_, lean_object* v_a_948_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_945_, v_inst_946_, v_m_947_, v_a_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey___redArg___boxed(lean_object* v_inst_950_, lean_object* v_inst_951_, lean_object* v_m_952_, lean_object* v_a_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Std_HashMap_Raw_getKey___redArg(v_inst_950_, v_inst_951_, v_m_952_, v_a_953_);
lean_dec_ref(v_m_952_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey(lean_object* v_00_u03b1_955_, lean_object* v_00_u03b2_956_, lean_object* v_inst_957_, lean_object* v_inst_958_, lean_object* v_m_959_, lean_object* v_a_960_, lean_object* v_h_961_){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_957_, v_inst_958_, v_m_959_, v_a_960_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey___boxed(lean_object* v_00_u03b1_963_, lean_object* v_00_u03b2_964_, lean_object* v_inst_965_, lean_object* v_inst_966_, lean_object* v_m_967_, lean_object* v_a_968_, lean_object* v_h_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Std_HashMap_Raw_getKey(v_00_u03b1_963_, v_00_u03b2_964_, v_inst_965_, v_inst_966_, v_m_967_, v_a_968_, v_h_969_);
lean_dec_ref(v_m_967_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKeyD___redArg(lean_object* v_inst_971_, lean_object* v_inst_972_, lean_object* v_m_973_, lean_object* v_a_974_, lean_object* v_fallback_975_){
_start:
{
lean_object* v_buckets_976_; lean_object* v___x_977_; lean_object* v___x_978_; uint8_t v___x_979_; 
v_buckets_976_ = lean_ctor_get(v_m_973_, 1);
v___x_977_ = lean_unsigned_to_nat(0u);
v___x_978_ = lean_array_get_size(v_buckets_976_);
v___x_979_ = lean_nat_dec_lt(v___x_977_, v___x_978_);
if (v___x_979_ == 0)
{
lean_dec(v_a_974_);
lean_dec_ref(v_inst_972_);
lean_dec_ref(v_inst_971_);
lean_inc(v_fallback_975_);
return v_fallback_975_;
}
else
{
lean_object* v___x_980_; 
v___x_980_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_971_, v_inst_972_, v_m_973_, v_a_974_, v_fallback_975_);
return v___x_980_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKeyD___redArg___boxed(lean_object* v_inst_981_, lean_object* v_inst_982_, lean_object* v_m_983_, lean_object* v_a_984_, lean_object* v_fallback_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Std_HashMap_Raw_getKeyD___redArg(v_inst_981_, v_inst_982_, v_m_983_, v_a_984_, v_fallback_985_);
lean_dec(v_fallback_985_);
lean_dec_ref(v_m_983_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKeyD(lean_object* v_00_u03b1_987_, lean_object* v_00_u03b2_988_, lean_object* v_inst_989_, lean_object* v_inst_990_, lean_object* v_m_991_, lean_object* v_a_992_, lean_object* v_fallback_993_){
_start:
{
lean_object* v_buckets_994_; lean_object* v___x_995_; lean_object* v___x_996_; uint8_t v___x_997_; 
v_buckets_994_ = lean_ctor_get(v_m_991_, 1);
v___x_995_ = lean_unsigned_to_nat(0u);
v___x_996_ = lean_array_get_size(v_buckets_994_);
v___x_997_ = lean_nat_dec_lt(v___x_995_, v___x_996_);
if (v___x_997_ == 0)
{
lean_dec(v_a_992_);
lean_dec_ref(v_inst_990_);
lean_dec_ref(v_inst_989_);
lean_inc(v_fallback_993_);
return v_fallback_993_;
}
else
{
lean_object* v___x_998_; 
v___x_998_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_989_, v_inst_990_, v_m_991_, v_a_992_, v_fallback_993_);
return v___x_998_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKeyD___boxed(lean_object* v_00_u03b1_999_, lean_object* v_00_u03b2_1000_, lean_object* v_inst_1001_, lean_object* v_inst_1002_, lean_object* v_m_1003_, lean_object* v_a_1004_, lean_object* v_fallback_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_Std_HashMap_Raw_getKeyD(v_00_u03b1_999_, v_00_u03b2_1000_, v_inst_1001_, v_inst_1002_, v_m_1003_, v_a_1004_, v_fallback_1005_);
lean_dec(v_fallback_1005_);
lean_dec_ref(v_m_1003_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x21___redArg(lean_object* v_inst_1007_, lean_object* v_inst_1008_, lean_object* v_inst_1009_, lean_object* v_m_1010_, lean_object* v_a_1011_){
_start:
{
lean_object* v_buckets_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; uint8_t v___x_1015_; 
v_buckets_1012_ = lean_ctor_get(v_m_1010_, 1);
v___x_1013_ = lean_unsigned_to_nat(0u);
v___x_1014_ = lean_array_get_size(v_buckets_1012_);
v___x_1015_ = lean_nat_dec_lt(v___x_1013_, v___x_1014_);
if (v___x_1015_ == 0)
{
lean_dec(v_a_1011_);
lean_dec_ref(v_inst_1008_);
lean_dec_ref(v_inst_1007_);
lean_inc(v_inst_1009_);
return v_inst_1009_;
}
else
{
lean_object* v___x_1016_; 
v___x_1016_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_1007_, v_inst_1008_, v_inst_1009_, v_m_1010_, v_a_1011_);
return v___x_1016_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x21___redArg___boxed(lean_object* v_inst_1017_, lean_object* v_inst_1018_, lean_object* v_inst_1019_, lean_object* v_m_1020_, lean_object* v_a_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Std_HashMap_Raw_getKey_x21___redArg(v_inst_1017_, v_inst_1018_, v_inst_1019_, v_m_1020_, v_a_1021_);
lean_dec_ref(v_m_1020_);
lean_dec(v_inst_1019_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x21(lean_object* v_00_u03b1_1023_, lean_object* v_00_u03b2_1024_, lean_object* v_inst_1025_, lean_object* v_inst_1026_, lean_object* v_inst_1027_, lean_object* v_m_1028_, lean_object* v_a_1029_){
_start:
{
lean_object* v_buckets_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; uint8_t v___x_1033_; 
v_buckets_1030_ = lean_ctor_get(v_m_1028_, 1);
v___x_1031_ = lean_unsigned_to_nat(0u);
v___x_1032_ = lean_array_get_size(v_buckets_1030_);
v___x_1033_ = lean_nat_dec_lt(v___x_1031_, v___x_1032_);
if (v___x_1033_ == 0)
{
lean_dec(v_a_1029_);
lean_dec_ref(v_inst_1026_);
lean_dec_ref(v_inst_1025_);
lean_inc(v_inst_1027_);
return v_inst_1027_;
}
else
{
lean_object* v___x_1034_; 
v___x_1034_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_1025_, v_inst_1026_, v_inst_1027_, v_m_1028_, v_a_1029_);
return v___x_1034_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x21___boxed(lean_object* v_00_u03b1_1035_, lean_object* v_00_u03b2_1036_, lean_object* v_inst_1037_, lean_object* v_inst_1038_, lean_object* v_inst_1039_, lean_object* v_m_1040_, lean_object* v_a_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l_Std_HashMap_Raw_getKey_x21(v_00_u03b1_1035_, v_00_u03b2_1036_, v_inst_1037_, v_inst_1038_, v_inst_1039_, v_m_1040_, v_a_1041_);
lean_dec_ref(v_m_1040_);
lean_dec(v_inst_1039_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_erase___redArg(lean_object* v_inst_1043_, lean_object* v_inst_1044_, lean_object* v_m_1045_, lean_object* v_a_1046_){
_start:
{
lean_object* v_buckets_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; uint8_t v___x_1050_; 
v_buckets_1047_ = lean_ctor_get(v_m_1045_, 1);
v___x_1048_ = lean_unsigned_to_nat(0u);
v___x_1049_ = lean_array_get_size(v_buckets_1047_);
v___x_1050_ = lean_nat_dec_lt(v___x_1048_, v___x_1049_);
if (v___x_1050_ == 0)
{
lean_dec(v_a_1046_);
lean_dec_ref(v_inst_1044_);
lean_dec_ref(v_inst_1043_);
return v_m_1045_;
}
else
{
lean_object* v___x_1051_; 
v___x_1051_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_1043_, v_inst_1044_, v_m_1045_, v_a_1046_);
return v___x_1051_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_erase(lean_object* v_00_u03b1_1052_, lean_object* v_00_u03b2_1053_, lean_object* v_inst_1054_, lean_object* v_inst_1055_, lean_object* v_m_1056_, lean_object* v_a_1057_){
_start:
{
lean_object* v_buckets_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; uint8_t v___x_1061_; 
v_buckets_1058_ = lean_ctor_get(v_m_1056_, 1);
v___x_1059_ = lean_unsigned_to_nat(0u);
v___x_1060_ = lean_array_get_size(v_buckets_1058_);
v___x_1061_ = lean_nat_dec_lt(v___x_1059_, v___x_1060_);
if (v___x_1061_ == 0)
{
lean_dec(v_a_1057_);
lean_dec_ref(v_inst_1055_);
lean_dec_ref(v_inst_1054_);
return v_m_1056_;
}
else
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_1054_, v_inst_1055_, v_m_1056_, v_a_1057_);
return v___x_1062_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_size___redArg(lean_object* v_m_1063_){
_start:
{
lean_object* v_size_1064_; 
v_size_1064_ = lean_ctor_get(v_m_1063_, 0);
lean_inc(v_size_1064_);
return v_size_1064_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_size___redArg___boxed(lean_object* v_m_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_Std_HashMap_Raw_size___redArg(v_m_1065_);
lean_dec_ref(v_m_1065_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_size(lean_object* v_00_u03b1_1067_, lean_object* v_00_u03b2_1068_, lean_object* v_m_1069_){
_start:
{
lean_object* v_size_1070_; 
v_size_1070_ = lean_ctor_get(v_m_1069_, 0);
lean_inc(v_size_1070_);
return v_size_1070_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_size___boxed(lean_object* v_00_u03b1_1071_, lean_object* v_00_u03b2_1072_, lean_object* v_m_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Std_HashMap_Raw_size(v_00_u03b1_1071_, v_00_u03b2_1072_, v_m_1073_);
lean_dec_ref(v_m_1073_);
return v_res_1074_;
}
}
uint8_t l_Std_HashMap_Raw_isEmpty___redArg(lean_object* v_m_1075_){
_start:
{
lean_object* v_size_1076_; lean_object* v___x_1077_; uint8_t v___x_1078_; 
v_size_1076_ = lean_ctor_get(v_m_1075_, 0);
v___x_1077_ = lean_unsigned_to_nat(0u);
v___x_1078_ = lean_nat_dec_eq(v_size_1076_, v___x_1077_);
return v___x_1078_;
}
}
LEAN_EXPORT void l_Std_HashMap_Raw_isEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1075_ = stack[0].m_obj;
uint8_t v_res_1079_;
v_res_1079_ = l_Std_HashMap_Raw_isEmpty___redArg(v_m_1075_);
stack->m_num = v_res_1079_;
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_isEmpty___redArg___boxed(lean_object* v_m_1080_){
_start:
{
uint8_t v_res_1081_; lean_object* v_r_1082_; 
v_res_1081_ = l_Std_HashMap_Raw_isEmpty___redArg(v_m_1080_);
lean_dec_ref(v_m_1080_);
v_r_1082_ = lean_box(v_res_1081_);
return v_r_1082_;
}
}
uint8_t l_Std_HashMap_Raw_isEmpty(lean_object* v_00_u03b1_1083_, lean_object* v_00_u03b2_1084_, lean_object* v_m_1085_){
_start:
{
lean_object* v_size_1086_; lean_object* v___x_1087_; uint8_t v___x_1088_; 
v_size_1086_ = lean_ctor_get(v_m_1085_, 0);
v___x_1087_ = lean_unsigned_to_nat(0u);
v___x_1088_ = lean_nat_dec_eq(v_size_1086_, v___x_1087_);
return v___x_1088_;
}
}
LEAN_EXPORT void l_Std_HashMap_Raw_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1085_ = stack[2].m_obj;
uint8_t v_res_1089_;
v_res_1089_ = l_Std_HashMap_Raw_isEmpty(lean_box(0), lean_box(0), v_m_1085_);
stack->m_num = v_res_1089_;
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_isEmpty___boxed(lean_object* v_00_u03b1_1090_, lean_object* v_00_u03b2_1091_, lean_object* v_m_1092_){
_start:
{
uint8_t v_res_1093_; lean_object* v_r_1094_; 
v_res_1093_ = l_Std_HashMap_Raw_isEmpty(v_00_u03b1_1090_, v_00_u03b2_1091_, v_m_1092_);
lean_dec_ref(v_m_1092_);
v_r_1094_ = lean_box(v_res_1093_);
return v_r_1094_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys___redArg___lam__0(lean_object* v_a_1095_, lean_object* v_b_1096_, lean_object* v_d_1097_){
_start:
{
lean_object* v___x_1098_; 
v___x_1098_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1098_, 0, v_a_1095_);
lean_ctor_set(v___x_1098_, 1, v_d_1097_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys___redArg___lam__0___boxed(lean_object* v_a_1099_, lean_object* v_b_1100_, lean_object* v_d_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Std_HashMap_Raw_keys___redArg___lam__0(v_a_1099_, v_b_1100_, v_d_1101_);
lean_dec(v_b_1100_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys___redArg___lam__1(lean_object* v___x_1103_, lean_object* v___f_1104_, lean_object* v_l_1105_, lean_object* v_acc_1106_){
_start:
{
lean_object* v___x_1107_; 
v___x_1107_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_1103_, v___f_1104_, v_acc_1106_, v_l_1105_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys___redArg(lean_object* v_m_1131_){
_start:
{
lean_object* v___x_1132_; lean_object* v_buckets_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; uint8_t v___x_1137_; 
v___x_1132_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1133_ = lean_ctor_get(v_m_1131_, 1);
lean_inc_ref(v_buckets_1133_);
lean_dec_ref(v_m_1131_);
v___x_1134_ = lean_box(0);
v___x_1135_ = lean_array_get_size(v_buckets_1133_);
v___x_1136_ = lean_unsigned_to_nat(0u);
v___x_1137_ = lean_nat_dec_lt(v___x_1136_, v___x_1135_);
if (v___x_1137_ == 0)
{
lean_dec_ref(v_buckets_1133_);
return v___x_1134_;
}
else
{
lean_object* v___f_1138_; size_t v___x_1139_; size_t v___x_1140_; lean_object* v___x_1141_; 
v___f_1138_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__11));
v___x_1139_ = lean_usize_of_nat(v___x_1135_);
v___x_1140_ = ((size_t)0ULL);
v___x_1141_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1132_, v___f_1138_, v_buckets_1133_, v___x_1139_, v___x_1140_, v___x_1134_);
return v___x_1141_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys(lean_object* v_00_u03b1_1142_, lean_object* v_00_u03b2_1143_, lean_object* v_m_1144_){
_start:
{
lean_object* v___x_1145_; lean_object* v_buckets_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; uint8_t v___x_1150_; 
v___x_1145_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1146_ = lean_ctor_get(v_m_1144_, 1);
lean_inc_ref(v_buckets_1146_);
lean_dec_ref(v_m_1144_);
v___x_1147_ = lean_box(0);
v___x_1148_ = lean_array_get_size(v_buckets_1146_);
v___x_1149_ = lean_unsigned_to_nat(0u);
v___x_1150_ = lean_nat_dec_lt(v___x_1149_, v___x_1148_);
if (v___x_1150_ == 0)
{
lean_dec_ref(v_buckets_1146_);
return v___x_1147_;
}
else
{
lean_object* v___f_1151_; size_t v___x_1152_; size_t v___x_1153_; lean_object* v___x_1154_; 
v___f_1151_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__11));
v___x_1152_ = lean_usize_of_nat(v___x_1148_);
v___x_1153_ = ((size_t)0ULL);
v___x_1154_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1145_, v___f_1151_, v_buckets_1146_, v___x_1152_, v___x_1153_, v___x_1147_);
return v___x_1154_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_ofList___redArg(lean_object* v_inst_1159_, lean_object* v_inst_1160_, lean_object* v_l_1161_){
_start:
{
lean_object* v___x_1162_; uint8_t v___x_1163_; 
v___x_1162_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1);
v___x_1163_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1163_ == 0)
{
lean_dec(v_l_1161_);
lean_dec_ref(v_inst_1160_);
lean_dec_ref(v_inst_1159_);
return v___x_1162_;
}
else
{
lean_object* v___f_1164_; lean_object* v___x_1165_; 
v___f_1164_ = ((lean_object*)(l_Std_HashMap_Raw_ofList___redArg___closed__1));
v___x_1165_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1164_, v_inst_1159_, v_inst_1160_, v___x_1162_, v_l_1161_);
return v___x_1165_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_ofList(lean_object* v_00_u03b1_1166_, lean_object* v_00_u03b2_1167_, lean_object* v_inst_1168_, lean_object* v_inst_1169_, lean_object* v_l_1170_){
_start:
{
lean_object* v___x_1171_; uint8_t v___x_1172_; 
v___x_1171_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1);
v___x_1172_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1172_ == 0)
{
lean_dec(v_l_1170_);
lean_dec_ref(v_inst_1169_);
lean_dec_ref(v_inst_1168_);
return v___x_1171_;
}
else
{
lean_object* v___f_1173_; lean_object* v___x_1174_; 
v___f_1173_ = ((lean_object*)(l_Std_HashMap_Raw_ofList___redArg___closed__1));
v___x_1174_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1173_, v_inst_1168_, v_inst_1169_, v___x_1171_, v_l_1170_);
return v___x_1174_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_unitOfList___redArg(lean_object* v_inst_1175_, lean_object* v_inst_1176_, lean_object* v_l_1177_){
_start:
{
lean_object* v___x_1178_; uint8_t v___x_1179_; 
v___x_1178_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1);
v___x_1179_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1179_ == 0)
{
lean_dec(v_l_1177_);
lean_dec_ref(v_inst_1176_);
lean_dec_ref(v_inst_1175_);
return v___x_1178_;
}
else
{
lean_object* v___f_1180_; lean_object* v___x_1181_; 
v___f_1180_ = ((lean_object*)(l_Std_HashMap_Raw_ofList___redArg___closed__1));
v___x_1181_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1180_, v_inst_1175_, v_inst_1176_, v___x_1178_, v_l_1177_);
return v___x_1181_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_unitOfList(lean_object* v_00_u03b1_1182_, lean_object* v_inst_1183_, lean_object* v_inst_1184_, lean_object* v_l_1185_){
_start:
{
lean_object* v___x_1186_; uint8_t v___x_1187_; 
v___x_1186_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1);
v___x_1187_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1187_ == 0)
{
lean_dec(v_l_1185_);
lean_dec_ref(v_inst_1184_);
lean_dec_ref(v_inst_1183_);
return v___x_1186_;
}
else
{
lean_object* v___f_1188_; lean_object* v___x_1189_; 
v___f_1188_ = ((lean_object*)(l_Std_HashMap_Raw_ofList___redArg___closed__1));
v___x_1189_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1188_, v_inst_1183_, v_inst_1184_, v___x_1186_, v_l_1185_);
return v___x_1189_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_ofArray___redArg(lean_object* v_inst_1194_, lean_object* v_inst_1195_, lean_object* v_a_1196_){
_start:
{
lean_object* v___x_1197_; uint8_t v___x_1198_; 
v___x_1197_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1);
v___x_1198_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1198_ == 0)
{
lean_dec_ref(v_a_1196_);
lean_dec_ref(v_inst_1195_);
lean_dec_ref(v_inst_1194_);
return v___x_1197_;
}
else
{
lean_object* v___f_1199_; lean_object* v___x_1200_; 
v___f_1199_ = ((lean_object*)(l_Std_HashMap_Raw_ofArray___redArg___closed__1));
v___x_1200_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1199_, v_inst_1194_, v_inst_1195_, v___x_1197_, v_a_1196_);
return v___x_1200_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_ofArray(lean_object* v_00_u03b1_1201_, lean_object* v_00_u03b2_1202_, lean_object* v_inst_1203_, lean_object* v_inst_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v___x_1206_; uint8_t v___x_1207_; 
v___x_1206_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1);
v___x_1207_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1207_ == 0)
{
lean_dec_ref(v_a_1205_);
lean_dec_ref(v_inst_1204_);
lean_dec_ref(v_inst_1203_);
return v___x_1206_;
}
else
{
lean_object* v___f_1208_; lean_object* v___x_1209_; 
v___f_1208_ = ((lean_object*)(l_Std_HashMap_Raw_ofArray___redArg___closed__1));
v___x_1209_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1208_, v_inst_1203_, v_inst_1204_, v___x_1206_, v_a_1205_);
return v___x_1209_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_alter___redArg(lean_object* v_inst_1210_, lean_object* v_inst_1211_, lean_object* v_m_1212_, lean_object* v_a_1213_, lean_object* v_f_1214_){
_start:
{
lean_object* v_buckets_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; uint8_t v___x_1218_; 
v_buckets_1215_ = lean_ctor_get(v_m_1212_, 1);
v___x_1216_ = lean_unsigned_to_nat(0u);
v___x_1217_ = lean_array_get_size(v_buckets_1215_);
v___x_1218_ = lean_nat_dec_lt(v___x_1216_, v___x_1217_);
if (v___x_1218_ == 0)
{
lean_object* v___x_1219_; 
lean_dec_ref(v_f_1214_);
lean_dec(v_a_1213_);
lean_dec_ref(v_m_1212_);
lean_dec_ref(v_inst_1211_);
lean_dec_ref(v_inst_1210_);
v___x_1219_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1219_;
}
else
{
lean_object* v___x_1220_; 
v___x_1220_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_1210_, v_inst_1211_, v_m_1212_, v_a_1213_, v_f_1214_);
return v___x_1220_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_alter(lean_object* v_00_u03b1_1221_, lean_object* v_00_u03b2_1222_, lean_object* v_inst_1223_, lean_object* v_inst_1224_, lean_object* v_inst_1225_, lean_object* v_m_1226_, lean_object* v_a_1227_, lean_object* v_f_1228_){
_start:
{
lean_object* v_buckets_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; 
v_buckets_1229_ = lean_ctor_get(v_m_1226_, 1);
v___x_1230_ = lean_unsigned_to_nat(0u);
v___x_1231_ = lean_array_get_size(v_buckets_1229_);
v___x_1232_ = lean_nat_dec_lt(v___x_1230_, v___x_1231_);
if (v___x_1232_ == 0)
{
lean_object* v___x_1233_; 
lean_dec_ref(v_f_1228_);
lean_dec(v_a_1227_);
lean_dec_ref(v_m_1226_);
lean_dec_ref(v_inst_1225_);
lean_dec_ref(v_inst_1223_);
v___x_1233_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1233_;
}
else
{
lean_object* v___x_1234_; 
v___x_1234_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_1223_, v_inst_1225_, v_m_1226_, v_a_1227_, v_f_1228_);
return v___x_1234_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_modify___redArg(lean_object* v_inst_1235_, lean_object* v_inst_1236_, lean_object* v_m_1237_, lean_object* v_a_1238_, lean_object* v_f_1239_){
_start:
{
lean_object* v_buckets_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; uint8_t v___x_1243_; 
v_buckets_1240_ = lean_ctor_get(v_m_1237_, 1);
v___x_1241_ = lean_unsigned_to_nat(0u);
v___x_1242_ = lean_array_get_size(v_buckets_1240_);
v___x_1243_ = lean_nat_dec_lt(v___x_1241_, v___x_1242_);
if (v___x_1243_ == 0)
{
lean_object* v___x_1244_; 
lean_dec(v_f_1239_);
lean_dec(v_a_1238_);
lean_dec_ref(v_m_1237_);
lean_dec_ref(v_inst_1236_);
lean_dec_ref(v_inst_1235_);
v___x_1244_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1244_;
}
else
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_inst_1235_, v_inst_1236_, v_m_1237_, v_a_1238_, v_f_1239_);
return v___x_1245_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_modify(lean_object* v_00_u03b1_1246_, lean_object* v_00_u03b2_1247_, lean_object* v_inst_1248_, lean_object* v_inst_1249_, lean_object* v_inst_1250_, lean_object* v_m_1251_, lean_object* v_a_1252_, lean_object* v_f_1253_){
_start:
{
lean_object* v_buckets_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; uint8_t v___x_1257_; 
v_buckets_1254_ = lean_ctor_get(v_m_1251_, 1);
v___x_1255_ = lean_unsigned_to_nat(0u);
v___x_1256_ = lean_array_get_size(v_buckets_1254_);
v___x_1257_ = lean_nat_dec_lt(v___x_1255_, v___x_1256_);
if (v___x_1257_ == 0)
{
lean_object* v___x_1258_; 
lean_dec(v_f_1253_);
lean_dec(v_a_1252_);
lean_dec_ref(v_m_1251_);
lean_dec_ref(v_inst_1250_);
lean_dec_ref(v_inst_1248_);
v___x_1258_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1258_;
}
else
{
lean_object* v___x_1259_; 
v___x_1259_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_inst_1248_, v_inst_1250_, v_m_1251_, v_a_1252_, v_f_1253_);
return v___x_1259_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toList___redArg___lam__0(lean_object* v_a_1260_, lean_object* v_b_1261_, lean_object* v_d_1262_){
_start:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1263_, 0, v_a_1260_);
lean_ctor_set(v___x_1263_, 1, v_b_1261_);
v___x_1264_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1263_);
lean_ctor_set(v___x_1264_, 1, v_d_1262_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toList___redArg___lam__1(lean_object* v___x_1265_, lean_object* v___f_1266_, lean_object* v_l_1267_, lean_object* v_acc_1268_){
_start:
{
lean_object* v___x_1269_; 
v___x_1269_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_1265_, v___f_1266_, v_acc_1268_, v_l_1267_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toList___redArg(lean_object* v_m_1274_){
_start:
{
lean_object* v___x_1275_; lean_object* v_buckets_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; uint8_t v___x_1280_; 
v___x_1275_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1276_ = lean_ctor_get(v_m_1274_, 1);
lean_inc_ref(v_buckets_1276_);
lean_dec_ref(v_m_1274_);
v___x_1277_ = lean_box(0);
v___x_1278_ = lean_array_get_size(v_buckets_1276_);
v___x_1279_ = lean_unsigned_to_nat(0u);
v___x_1280_ = lean_nat_dec_lt(v___x_1279_, v___x_1278_);
if (v___x_1280_ == 0)
{
lean_dec_ref(v_buckets_1276_);
return v___x_1277_;
}
else
{
lean_object* v___f_1281_; size_t v___x_1282_; size_t v___x_1283_; lean_object* v___x_1284_; 
v___f_1281_ = ((lean_object*)(l_Std_HashMap_Raw_toList___redArg___closed__1));
v___x_1282_ = lean_usize_of_nat(v___x_1278_);
v___x_1283_ = ((size_t)0ULL);
v___x_1284_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1275_, v___f_1281_, v_buckets_1276_, v___x_1282_, v___x_1283_, v___x_1277_);
return v___x_1284_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toList(lean_object* v_00_u03b1_1285_, lean_object* v_00_u03b2_1286_, lean_object* v_m_1287_){
_start:
{
lean_object* v___x_1288_; lean_object* v_buckets_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; uint8_t v___x_1293_; 
v___x_1288_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1289_ = lean_ctor_get(v_m_1287_, 1);
lean_inc_ref(v_buckets_1289_);
lean_dec_ref(v_m_1287_);
v___x_1290_ = lean_box(0);
v___x_1291_ = lean_array_get_size(v_buckets_1289_);
v___x_1292_ = lean_unsigned_to_nat(0u);
v___x_1293_ = lean_nat_dec_lt(v___x_1292_, v___x_1291_);
if (v___x_1293_ == 0)
{
lean_dec_ref(v_buckets_1289_);
return v___x_1290_;
}
else
{
lean_object* v___f_1294_; size_t v___x_1295_; size_t v___x_1296_; lean_object* v___x_1297_; 
v___f_1294_ = ((lean_object*)(l_Std_HashMap_Raw_toList___redArg___closed__1));
v___x_1295_ = lean_usize_of_nat(v___x_1291_);
v___x_1296_ = ((size_t)0ULL);
v___x_1297_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1288_, v___f_1294_, v_buckets_1289_, v___x_1295_, v___x_1296_, v___x_1290_);
return v___x_1297_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_foldM___redArg___lam__0(lean_object* v_inst_1298_, lean_object* v_f_1299_, lean_object* v_acc_1300_, lean_object* v_l_1301_){
_start:
{
lean_object* v___x_1302_; 
v___x_1302_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_1298_, v_f_1299_, v_acc_1300_, v_l_1301_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_foldM___redArg(lean_object* v_inst_1303_, lean_object* v_f_1304_, lean_object* v_init_1305_, lean_object* v_b_1306_){
_start:
{
lean_object* v_toApplicative_1307_; lean_object* v_buckets_1308_; lean_object* v_toPure_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; uint8_t v___x_1312_; 
v_toApplicative_1307_ = lean_ctor_get(v_inst_1303_, 0);
v_buckets_1308_ = lean_ctor_get(v_b_1306_, 1);
lean_inc_ref(v_buckets_1308_);
lean_dec_ref(v_b_1306_);
v_toPure_1309_ = lean_ctor_get(v_toApplicative_1307_, 1);
v___x_1310_ = lean_unsigned_to_nat(0u);
v___x_1311_ = lean_array_get_size(v_buckets_1308_);
v___x_1312_ = lean_nat_dec_lt(v___x_1310_, v___x_1311_);
if (v___x_1312_ == 0)
{
lean_object* v___x_1313_; 
lean_inc(v_toPure_1309_);
lean_dec_ref(v_buckets_1308_);
lean_dec(v_f_1304_);
lean_dec_ref(v_inst_1303_);
v___x_1313_ = lean_apply_2(v_toPure_1309_, lean_box(0), v_init_1305_);
return v___x_1313_;
}
else
{
lean_object* v___f_1314_; size_t v___x_1315_; size_t v___x_1316_; lean_object* v___x_1317_; 
lean_inc_ref(v_inst_1303_);
v___f_1314_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_foldM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1314_, 0, v_inst_1303_);
lean_closure_set(v___f_1314_, 1, v_f_1304_);
v___x_1315_ = ((size_t)0ULL);
v___x_1316_ = lean_usize_of_nat(v___x_1311_);
v___x_1317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1303_, v___f_1314_, v_buckets_1308_, v___x_1315_, v___x_1316_, v_init_1305_);
return v___x_1317_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_foldM(lean_object* v_00_u03b1_1318_, lean_object* v_00_u03b2_1319_, lean_object* v_m_1320_, lean_object* v_inst_1321_, lean_object* v_00_u03b3_1322_, lean_object* v_f_1323_, lean_object* v_init_1324_, lean_object* v_b_1325_){
_start:
{
lean_object* v_toApplicative_1326_; lean_object* v_buckets_1327_; lean_object* v_toPure_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; uint8_t v___x_1331_; 
v_toApplicative_1326_ = lean_ctor_get(v_inst_1321_, 0);
v_buckets_1327_ = lean_ctor_get(v_b_1325_, 1);
lean_inc_ref(v_buckets_1327_);
lean_dec_ref(v_b_1325_);
v_toPure_1328_ = lean_ctor_get(v_toApplicative_1326_, 1);
v___x_1329_ = lean_unsigned_to_nat(0u);
v___x_1330_ = lean_array_get_size(v_buckets_1327_);
v___x_1331_ = lean_nat_dec_lt(v___x_1329_, v___x_1330_);
if (v___x_1331_ == 0)
{
lean_object* v___x_1332_; 
lean_inc(v_toPure_1328_);
lean_dec_ref(v_buckets_1327_);
lean_dec(v_f_1323_);
lean_dec_ref(v_inst_1321_);
v___x_1332_ = lean_apply_2(v_toPure_1328_, lean_box(0), v_init_1324_);
return v___x_1332_;
}
else
{
lean_object* v___f_1333_; size_t v___x_1334_; size_t v___x_1335_; lean_object* v___x_1336_; 
lean_inc_ref(v_inst_1321_);
v___f_1333_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_foldM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1333_, 0, v_inst_1321_);
lean_closure_set(v___f_1333_, 1, v_f_1323_);
v___x_1334_ = ((size_t)0ULL);
v___x_1335_ = lean_usize_of_nat(v___x_1330_);
v___x_1336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1321_, v___f_1333_, v_buckets_1327_, v___x_1334_, v___x_1335_, v_init_1324_);
return v___x_1336_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_fold___redArg___lam__0(lean_object* v_f_1337_, lean_object* v_x1_1338_, lean_object* v_x2_1339_, lean_object* v_x3_1340_){
_start:
{
lean_object* v___x_1341_; 
v___x_1341_ = lean_apply_3(v_f_1337_, v_x1_1338_, v_x2_1339_, v_x3_1340_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_fold___redArg___lam__1(lean_object* v___x_1342_, lean_object* v___f_1343_, lean_object* v_acc_1344_, lean_object* v_l_1345_){
_start:
{
lean_object* v___x_1346_; 
v___x_1346_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1342_, v___f_1343_, v_acc_1344_, v_l_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_fold___redArg(lean_object* v_f_1347_, lean_object* v_init_1348_, lean_object* v_b_1349_){
_start:
{
lean_object* v___x_1350_; lean_object* v_buckets_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; uint8_t v___x_1354_; 
v___x_1350_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1351_ = lean_ctor_get(v_b_1349_, 1);
lean_inc_ref(v_buckets_1351_);
lean_dec_ref(v_b_1349_);
v___x_1352_ = lean_unsigned_to_nat(0u);
v___x_1353_ = lean_array_get_size(v_buckets_1351_);
v___x_1354_ = lean_nat_dec_lt(v___x_1352_, v___x_1353_);
if (v___x_1354_ == 0)
{
lean_dec_ref(v_buckets_1351_);
lean_dec(v_f_1347_);
return v_init_1348_;
}
else
{
lean_object* v___f_1355_; lean_object* v___f_1356_; size_t v___x_1357_; size_t v___x_1358_; lean_object* v___x_1359_; 
v___f_1355_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1355_, 0, v_f_1347_);
v___f_1356_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1356_, 0, v___x_1350_);
lean_closure_set(v___f_1356_, 1, v___f_1355_);
v___x_1357_ = ((size_t)0ULL);
v___x_1358_ = lean_usize_of_nat(v___x_1353_);
v___x_1359_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1350_, v___f_1356_, v_buckets_1351_, v___x_1357_, v___x_1358_, v_init_1348_);
return v___x_1359_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_fold(lean_object* v_00_u03b1_1360_, lean_object* v_00_u03b2_1361_, lean_object* v_00_u03b3_1362_, lean_object* v_f_1363_, lean_object* v_init_1364_, lean_object* v_b_1365_){
_start:
{
lean_object* v___x_1366_; lean_object* v_buckets_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; uint8_t v___x_1370_; 
v___x_1366_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1367_ = lean_ctor_get(v_b_1365_, 1);
lean_inc_ref(v_buckets_1367_);
lean_dec_ref(v_b_1365_);
v___x_1368_ = lean_unsigned_to_nat(0u);
v___x_1369_ = lean_array_get_size(v_buckets_1367_);
v___x_1370_ = lean_nat_dec_lt(v___x_1368_, v___x_1369_);
if (v___x_1370_ == 0)
{
lean_dec_ref(v_buckets_1367_);
lean_dec(v_f_1363_);
return v_init_1364_;
}
else
{
lean_object* v___f_1371_; lean_object* v___f_1372_; size_t v___x_1373_; size_t v___x_1374_; lean_object* v___x_1375_; 
v___f_1371_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1371_, 0, v_f_1363_);
v___f_1372_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1372_, 0, v___x_1366_);
lean_closure_set(v___f_1372_, 1, v___f_1371_);
v___x_1373_ = ((size_t)0ULL);
v___x_1374_ = lean_usize_of_nat(v___x_1369_);
v___x_1375_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1366_, v___f_1372_, v_buckets_1367_, v___x_1373_, v___x_1374_, v_init_1364_);
return v___x_1375_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forM___redArg___lam__0(lean_object* v_f_1376_, lean_object* v_x_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v___x_1380_; 
v___x_1380_ = lean_apply_2(v_f_1376_, v___y_1378_, v___y_1379_);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forM___redArg___lam__1(lean_object* v_inst_1381_, lean_object* v___f_1382_, lean_object* v_x_1383_, lean_object* v___y_1384_){
_start:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1385_ = lean_box(0);
v___x_1386_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_1381_, v___f_1382_, v___x_1385_, v___y_1384_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forM___redArg(lean_object* v_inst_1387_, lean_object* v_f_1388_, lean_object* v_b_1389_){
_start:
{
lean_object* v_toApplicative_1390_; lean_object* v_buckets_1391_; lean_object* v_toPure_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; uint8_t v___x_1396_; 
v_toApplicative_1390_ = lean_ctor_get(v_inst_1387_, 0);
v_buckets_1391_ = lean_ctor_get(v_b_1389_, 1);
lean_inc_ref(v_buckets_1391_);
lean_dec_ref(v_b_1389_);
v_toPure_1392_ = lean_ctor_get(v_toApplicative_1390_, 1);
v___x_1393_ = lean_unsigned_to_nat(0u);
v___x_1394_ = lean_array_get_size(v_buckets_1391_);
v___x_1395_ = lean_box(0);
v___x_1396_ = lean_nat_dec_lt(v___x_1393_, v___x_1394_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; 
lean_inc(v_toPure_1392_);
lean_dec_ref(v_buckets_1391_);
lean_dec(v_f_1388_);
lean_dec_ref(v_inst_1387_);
v___x_1397_ = lean_apply_2(v_toPure_1392_, lean_box(0), v___x_1395_);
return v___x_1397_;
}
else
{
lean_object* v___f_1398_; lean_object* v___f_1399_; size_t v___x_1400_; size_t v___x_1401_; lean_object* v___x_1402_; 
v___f_1398_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1398_, 0, v_f_1388_);
lean_inc_ref(v_inst_1387_);
v___f_1399_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1399_, 0, v_inst_1387_);
lean_closure_set(v___f_1399_, 1, v___f_1398_);
v___x_1400_ = ((size_t)0ULL);
v___x_1401_ = lean_usize_of_nat(v___x_1394_);
v___x_1402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1387_, v___f_1399_, v_buckets_1391_, v___x_1400_, v___x_1401_, v___x_1395_);
return v___x_1402_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forM(lean_object* v_00_u03b1_1403_, lean_object* v_00_u03b2_1404_, lean_object* v_m_1405_, lean_object* v_inst_1406_, lean_object* v_f_1407_, lean_object* v_b_1408_){
_start:
{
lean_object* v_toApplicative_1409_; lean_object* v_buckets_1410_; lean_object* v_toPure_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; uint8_t v___x_1415_; 
v_toApplicative_1409_ = lean_ctor_get(v_inst_1406_, 0);
v_buckets_1410_ = lean_ctor_get(v_b_1408_, 1);
lean_inc_ref(v_buckets_1410_);
lean_dec_ref(v_b_1408_);
v_toPure_1411_ = lean_ctor_get(v_toApplicative_1409_, 1);
v___x_1412_ = lean_unsigned_to_nat(0u);
v___x_1413_ = lean_array_get_size(v_buckets_1410_);
v___x_1414_ = lean_box(0);
v___x_1415_ = lean_nat_dec_lt(v___x_1412_, v___x_1413_);
if (v___x_1415_ == 0)
{
lean_object* v___x_1416_; 
lean_inc(v_toPure_1411_);
lean_dec_ref(v_buckets_1410_);
lean_dec(v_f_1407_);
lean_dec_ref(v_inst_1406_);
v___x_1416_ = lean_apply_2(v_toPure_1411_, lean_box(0), v___x_1414_);
return v___x_1416_;
}
else
{
lean_object* v___f_1417_; lean_object* v___f_1418_; size_t v___x_1419_; size_t v___x_1420_; lean_object* v___x_1421_; 
v___f_1417_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1417_, 0, v_f_1407_);
lean_inc_ref(v_inst_1406_);
v___f_1418_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1418_, 0, v_inst_1406_);
lean_closure_set(v___f_1418_, 1, v___f_1417_);
v___x_1419_ = ((size_t)0ULL);
v___x_1420_ = lean_usize_of_nat(v___x_1413_);
v___x_1421_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1406_, v___f_1418_, v_buckets_1410_, v___x_1419_, v___x_1420_, v___x_1414_);
return v___x_1421_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forIn___redArg___lam__0(lean_object* v_inst_1422_, lean_object* v_f_1423_, lean_object* v_a_1424_, lean_object* v_x_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v___x_1427_; 
v___x_1427_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_1422_, v_f_1423_, v_a_1424_, v___y_1426_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forIn___redArg(lean_object* v_inst_1428_, lean_object* v_f_1429_, lean_object* v_init_1430_, lean_object* v_b_1431_){
_start:
{
lean_object* v_buckets_1432_; lean_object* v___f_1433_; size_t v_sz_1434_; size_t v___x_1435_; lean_object* v___x_1436_; 
v_buckets_1432_ = lean_ctor_get(v_b_1431_, 1);
lean_inc_ref(v_buckets_1432_);
lean_dec_ref(v_b_1431_);
lean_inc_ref(v_inst_1428_);
v___f_1433_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forIn___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1433_, 0, v_inst_1428_);
lean_closure_set(v___f_1433_, 1, v_f_1429_);
v_sz_1434_ = lean_array_size(v_buckets_1432_);
v___x_1435_ = ((size_t)0ULL);
v___x_1436_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1428_, v_buckets_1432_, v___f_1433_, v_sz_1434_, v___x_1435_, v_init_1430_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forIn(lean_object* v_00_u03b1_1437_, lean_object* v_00_u03b2_1438_, lean_object* v_m_1439_, lean_object* v_inst_1440_, lean_object* v_00_u03b3_1441_, lean_object* v_f_1442_, lean_object* v_init_1443_, lean_object* v_b_1444_){
_start:
{
lean_object* v_buckets_1445_; lean_object* v___f_1446_; size_t v_sz_1447_; size_t v___x_1448_; lean_object* v___x_1449_; 
v_buckets_1445_ = lean_ctor_get(v_b_1444_, 1);
lean_inc_ref(v_buckets_1445_);
lean_dec_ref(v_b_1444_);
lean_inc_ref(v_inst_1440_);
v___f_1446_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forIn___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1446_, 0, v_inst_1440_);
lean_closure_set(v___f_1446_, 1, v_f_1442_);
v_sz_1447_ = lean_array_size(v_buckets_1445_);
v___x_1448_ = ((size_t)0ULL);
v___x_1449_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1440_, v_buckets_1445_, v___f_1446_, v_sz_1447_, v___x_1448_, v_init_1443_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__0(lean_object* v_f_1450_, lean_object* v_x_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1454_, 0, v___y_1452_);
lean_ctor_set(v___x_1454_, 1, v___y_1453_);
v___x_1455_ = lean_apply_1(v_f_1450_, v___x_1454_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__2(lean_object* v_inst_1456_, lean_object* v_m_1457_, lean_object* v_f_1458_){
_start:
{
lean_object* v_toApplicative_1459_; lean_object* v_buckets_1460_; lean_object* v_toPure_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; uint8_t v___x_1465_; 
v_toApplicative_1459_ = lean_ctor_get(v_inst_1456_, 0);
v_buckets_1460_ = lean_ctor_get(v_m_1457_, 1);
lean_inc_ref(v_buckets_1460_);
lean_dec_ref(v_m_1457_);
v_toPure_1461_ = lean_ctor_get(v_toApplicative_1459_, 1);
v___x_1462_ = lean_unsigned_to_nat(0u);
v___x_1463_ = lean_array_get_size(v_buckets_1460_);
v___x_1464_ = lean_box(0);
v___x_1465_ = lean_nat_dec_lt(v___x_1462_, v___x_1463_);
if (v___x_1465_ == 0)
{
lean_object* v___x_1466_; 
lean_inc(v_toPure_1461_);
lean_dec_ref(v_buckets_1460_);
lean_dec(v_f_1458_);
lean_dec_ref(v_inst_1456_);
v___x_1466_ = lean_apply_2(v_toPure_1461_, lean_box(0), v___x_1464_);
return v___x_1466_;
}
else
{
lean_object* v___f_1467_; lean_object* v___f_1468_; size_t v___x_1469_; size_t v___x_1470_; lean_object* v___x_1471_; 
v___f_1467_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1467_, 0, v_f_1458_);
lean_inc_ref(v_inst_1456_);
v___f_1468_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1468_, 0, v_inst_1456_);
lean_closure_set(v___f_1468_, 1, v___f_1467_);
v___x_1469_ = ((size_t)0ULL);
v___x_1470_ = lean_usize_of_nat(v___x_1463_);
v___x_1471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1456_, v___f_1468_, v_buckets_1460_, v___x_1469_, v___x_1470_, v___x_1464_);
return v___x_1471_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad___redArg(lean_object* v_inst_1472_){
_start:
{
lean_object* v___f_1473_; 
v___f_1473_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_1473_, 0, v_inst_1472_);
return v___f_1473_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad(lean_object* v_00_u03b1_1474_, lean_object* v_00_u03b2_1475_, lean_object* v_m_1476_, lean_object* v_inst_1477_){
_start:
{
lean_object* v___f_1478_; 
v___f_1478_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_1478_, 0, v_inst_1477_);
return v___f_1478_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__0(lean_object* v_f_1479_, lean_object* v_a_1480_, lean_object* v_b_1481_, lean_object* v_acc_1482_){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1483_, 0, v_a_1480_);
lean_ctor_set(v___x_1483_, 1, v_b_1481_);
v___x_1484_ = lean_apply_2(v_f_1479_, v___x_1483_, v_acc_1482_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__1(lean_object* v_inst_1485_, lean_object* v___f_1486_, lean_object* v_a_1487_, lean_object* v_x_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v___x_1490_; 
v___x_1490_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_1485_, v___f_1486_, v_a_1487_, v___y_1489_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__2(lean_object* v_inst_1491_, lean_object* v_00_u03b2_1492_, lean_object* v_m_1493_, lean_object* v_init_1494_, lean_object* v_f_1495_){
_start:
{
lean_object* v_buckets_1496_; lean_object* v___f_1497_; lean_object* v___f_1498_; size_t v_sz_1499_; size_t v___x_1500_; lean_object* v___x_1501_; 
v_buckets_1496_ = lean_ctor_get(v_m_1493_, 1);
lean_inc_ref(v_buckets_1496_);
lean_dec_ref(v_m_1493_);
v___f_1497_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1497_, 0, v_f_1495_);
lean_inc_ref(v_inst_1491_);
v___f_1498_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1498_, 0, v_inst_1491_);
lean_closure_set(v___f_1498_, 1, v___f_1497_);
v_sz_1499_ = lean_array_size(v_buckets_1496_);
v___x_1500_ = ((size_t)0ULL);
v___x_1501_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1491_, v_buckets_1496_, v___f_1498_, v_sz_1499_, v___x_1500_, v_init_1494_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad___redArg(lean_object* v_inst_1502_){
_start:
{
lean_object* v___f_1503_; 
v___f_1503_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1503_, 0, v_inst_1502_);
return v___f_1503_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad(lean_object* v_00_u03b1_1504_, lean_object* v_00_u03b2_1505_, lean_object* v_m_1506_, lean_object* v_inst_1507_){
_start:
{
lean_object* v___f_1508_; 
v___f_1508_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1508_, 0, v_inst_1507_);
return v___f_1508_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___redArg___lam__0(lean_object* v_p_1509_, lean_object* v___x_1510_, lean_object* v___x_1511_, lean_object* v_a_1512_, lean_object* v_b_1513_, lean_object* v_acc_1514_){
_start:
{
lean_object* v___x_1515_; uint8_t v___x_1516_; 
v___x_1515_ = lean_apply_2(v_p_1509_, v_a_1512_, v_b_1513_);
v___x_1516_ = lean_unbox(v___x_1515_);
if (v___x_1516_ == 0)
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
lean_dec_ref(v___x_1511_);
v___x_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1515_);
v___x_1518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1517_);
lean_ctor_set(v___x_1518_, 1, v___x_1510_);
v___x_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1518_);
return v___x_1519_;
}
else
{
lean_object* v___x_1520_; 
v___x_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1511_);
return v___x_1520_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___redArg___lam__0___boxed(lean_object* v_p_1521_, lean_object* v___x_1522_, lean_object* v___x_1523_, lean_object* v_a_1524_, lean_object* v_b_1525_, lean_object* v_acc_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l_Std_HashMap_Raw_all___redArg___lam__0(v_p_1521_, v___x_1522_, v___x_1523_, v_a_1524_, v_b_1525_, v_acc_1526_);
lean_dec_ref(v_acc_1526_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___redArg___lam__1(lean_object* v___x_1528_, lean_object* v___f_1529_, lean_object* v_a_1530_, lean_object* v_x_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1528_, v___f_1529_, v_a_1530_, v___y_1532_);
return v___x_1533_;
}
}
uint8_t l_Std_HashMap_Raw_all___redArg(lean_object* v_m_1537_, lean_object* v_p_1538_){
_start:
{
lean_object* v___x_1539_; lean_object* v_buckets_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___f_1543_; lean_object* v___f_1544_; size_t v_sz_1545_; size_t v___x_1546_; lean_object* v___x_1547_; lean_object* v_fst_1548_; 
v___x_1539_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1540_ = lean_ctor_get(v_m_1537_, 1);
lean_inc_ref(v_buckets_1540_);
lean_dec_ref(v_m_1537_);
v___x_1541_ = lean_box(0);
v___x_1542_ = ((lean_object*)(l_Std_HashMap_Raw_all___redArg___closed__0));
v___f_1543_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1543_, 0, v_p_1538_);
lean_closure_set(v___f_1543_, 1, v___x_1541_);
lean_closure_set(v___f_1543_, 2, v___x_1542_);
v___f_1544_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1544_, 0, v___x_1539_);
lean_closure_set(v___f_1544_, 1, v___f_1543_);
v_sz_1545_ = lean_array_size(v_buckets_1540_);
v___x_1546_ = ((size_t)0ULL);
v___x_1547_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1539_, v_buckets_1540_, v___f_1544_, v_sz_1545_, v___x_1546_, v___x_1542_);
v_fst_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_fst_1548_);
lean_dec(v___x_1547_);
if (lean_obj_tag(v_fst_1548_) == 0)
{
uint8_t v___x_1549_; 
v___x_1549_ = 1;
return v___x_1549_;
}
else
{
lean_object* v_val_1550_; uint8_t v___x_1551_; 
v_val_1550_ = lean_ctor_get(v_fst_1548_, 0);
lean_inc(v_val_1550_);
lean_dec_ref_known(v_fst_1548_, 1);
v___x_1551_ = lean_unbox(v_val_1550_);
lean_dec(v_val_1550_);
return v___x_1551_;
}
}
}
LEAN_EXPORT void l_Std_HashMap_Raw_all___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1537_ = stack[0].m_obj;
lean_object* v_p_1538_ = stack[1].m_obj;
uint8_t v_res_1552_;
v_res_1552_ = l_Std_HashMap_Raw_all___redArg(v_m_1537_, v_p_1538_);
stack->m_num = v_res_1552_;
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___redArg___boxed(lean_object* v_m_1553_, lean_object* v_p_1554_){
_start:
{
uint8_t v_res_1555_; lean_object* v_r_1556_; 
v_res_1555_ = l_Std_HashMap_Raw_all___redArg(v_m_1553_, v_p_1554_);
v_r_1556_ = lean_box(v_res_1555_);
return v_r_1556_;
}
}
uint8_t l_Std_HashMap_Raw_all(lean_object* v_00_u03b1_1557_, lean_object* v_00_u03b2_1558_, lean_object* v_m_1559_, lean_object* v_p_1560_){
_start:
{
lean_object* v___x_1561_; lean_object* v_buckets_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___f_1565_; lean_object* v___f_1566_; size_t v_sz_1567_; size_t v___x_1568_; lean_object* v___x_1569_; lean_object* v_fst_1570_; 
v___x_1561_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1562_ = lean_ctor_get(v_m_1559_, 1);
lean_inc_ref(v_buckets_1562_);
lean_dec_ref(v_m_1559_);
v___x_1563_ = lean_box(0);
v___x_1564_ = ((lean_object*)(l_Std_HashMap_Raw_all___redArg___closed__0));
v___f_1565_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1565_, 0, v_p_1560_);
lean_closure_set(v___f_1565_, 1, v___x_1563_);
lean_closure_set(v___f_1565_, 2, v___x_1564_);
v___f_1566_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1566_, 0, v___x_1561_);
lean_closure_set(v___f_1566_, 1, v___f_1565_);
v_sz_1567_ = lean_array_size(v_buckets_1562_);
v___x_1568_ = ((size_t)0ULL);
v___x_1569_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1561_, v_buckets_1562_, v___f_1566_, v_sz_1567_, v___x_1568_, v___x_1564_);
v_fst_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_fst_1570_);
lean_dec(v___x_1569_);
if (lean_obj_tag(v_fst_1570_) == 0)
{
uint8_t v___x_1571_; 
v___x_1571_ = 1;
return v___x_1571_;
}
else
{
lean_object* v_val_1572_; uint8_t v___x_1573_; 
v_val_1572_ = lean_ctor_get(v_fst_1570_, 0);
lean_inc(v_val_1572_);
lean_dec_ref_known(v_fst_1570_, 1);
v___x_1573_ = lean_unbox(v_val_1572_);
lean_dec(v_val_1572_);
return v___x_1573_;
}
}
}
LEAN_EXPORT void l_Std_HashMap_Raw_all_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1559_ = stack[2].m_obj;
lean_object* v_p_1560_ = stack[3].m_obj;
uint8_t v_res_1574_;
v_res_1574_ = l_Std_HashMap_Raw_all(lean_box(0), lean_box(0), v_m_1559_, v_p_1560_);
stack->m_num = v_res_1574_;
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___boxed(lean_object* v_00_u03b1_1575_, lean_object* v_00_u03b2_1576_, lean_object* v_m_1577_, lean_object* v_p_1578_){
_start:
{
uint8_t v_res_1579_; lean_object* v_r_1580_; 
v_res_1579_ = l_Std_HashMap_Raw_all(v_00_u03b1_1575_, v_00_u03b2_1576_, v_m_1577_, v_p_1578_);
v_r_1580_ = lean_box(v_res_1579_);
return v_r_1580_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_any___redArg___lam__0(lean_object* v_p_1581_, lean_object* v___x_1582_, lean_object* v___x_1583_, lean_object* v_a_1584_, lean_object* v_b_1585_, lean_object* v_acc_1586_){
_start:
{
lean_object* v___x_1587_; uint8_t v___x_1588_; 
v___x_1587_ = lean_apply_2(v_p_1581_, v_a_1584_, v_b_1585_);
v___x_1588_ = lean_unbox(v___x_1587_);
if (v___x_1588_ == 0)
{
lean_object* v___x_1589_; 
v___x_1589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1582_);
return v___x_1589_;
}
else
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
lean_dec_ref(v___x_1582_);
v___x_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1587_);
v___x_1591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1590_);
lean_ctor_set(v___x_1591_, 1, v___x_1583_);
v___x_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1591_);
return v___x_1592_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_any___redArg___lam__0___boxed(lean_object* v_p_1593_, lean_object* v___x_1594_, lean_object* v___x_1595_, lean_object* v_a_1596_, lean_object* v_b_1597_, lean_object* v_acc_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l_Std_HashMap_Raw_any___redArg___lam__0(v_p_1593_, v___x_1594_, v___x_1595_, v_a_1596_, v_b_1597_, v_acc_1598_);
lean_dec_ref(v_acc_1598_);
return v_res_1599_;
}
}
uint8_t l_Std_HashMap_Raw_any___redArg(lean_object* v_m_1600_, lean_object* v_p_1601_){
_start:
{
lean_object* v___x_1602_; lean_object* v_buckets_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___f_1606_; lean_object* v___f_1607_; size_t v_sz_1608_; size_t v___x_1609_; lean_object* v___x_1610_; lean_object* v_fst_1611_; 
v___x_1602_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1603_ = lean_ctor_get(v_m_1600_, 1);
lean_inc_ref(v_buckets_1603_);
lean_dec_ref(v_m_1600_);
v___x_1604_ = lean_box(0);
v___x_1605_ = ((lean_object*)(l_Std_HashMap_Raw_all___redArg___closed__0));
v___f_1606_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1606_, 0, v_p_1601_);
lean_closure_set(v___f_1606_, 1, v___x_1605_);
lean_closure_set(v___f_1606_, 2, v___x_1604_);
v___f_1607_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1607_, 0, v___x_1602_);
lean_closure_set(v___f_1607_, 1, v___f_1606_);
v_sz_1608_ = lean_array_size(v_buckets_1603_);
v___x_1609_ = ((size_t)0ULL);
v___x_1610_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1602_, v_buckets_1603_, v___f_1607_, v_sz_1608_, v___x_1609_, v___x_1605_);
v_fst_1611_ = lean_ctor_get(v___x_1610_, 0);
lean_inc(v_fst_1611_);
lean_dec(v___x_1610_);
if (lean_obj_tag(v_fst_1611_) == 0)
{
uint8_t v___x_1612_; 
v___x_1612_ = 0;
return v___x_1612_;
}
else
{
lean_object* v_val_1613_; uint8_t v___x_1614_; 
v_val_1613_ = lean_ctor_get(v_fst_1611_, 0);
lean_inc(v_val_1613_);
lean_dec_ref_known(v_fst_1611_, 1);
v___x_1614_ = lean_unbox(v_val_1613_);
lean_dec(v_val_1613_);
return v___x_1614_;
}
}
}
LEAN_EXPORT void l_Std_HashMap_Raw_any___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1600_ = stack[0].m_obj;
lean_object* v_p_1601_ = stack[1].m_obj;
uint8_t v_res_1615_;
v_res_1615_ = l_Std_HashMap_Raw_any___redArg(v_m_1600_, v_p_1601_);
stack->m_num = v_res_1615_;
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_any___redArg___boxed(lean_object* v_m_1616_, lean_object* v_p_1617_){
_start:
{
uint8_t v_res_1618_; lean_object* v_r_1619_; 
v_res_1618_ = l_Std_HashMap_Raw_any___redArg(v_m_1616_, v_p_1617_);
v_r_1619_ = lean_box(v_res_1618_);
return v_r_1619_;
}
}
uint8_t l_Std_HashMap_Raw_any(lean_object* v_00_u03b1_1620_, lean_object* v_00_u03b2_1621_, lean_object* v_m_1622_, lean_object* v_p_1623_){
_start:
{
lean_object* v___x_1624_; lean_object* v_buckets_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___f_1628_; lean_object* v___f_1629_; size_t v_sz_1630_; size_t v___x_1631_; lean_object* v___x_1632_; lean_object* v_fst_1633_; 
v___x_1624_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1625_ = lean_ctor_get(v_m_1622_, 1);
lean_inc_ref(v_buckets_1625_);
lean_dec_ref(v_m_1622_);
v___x_1626_ = lean_box(0);
v___x_1627_ = ((lean_object*)(l_Std_HashMap_Raw_all___redArg___closed__0));
v___f_1628_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1628_, 0, v_p_1623_);
lean_closure_set(v___f_1628_, 1, v___x_1627_);
lean_closure_set(v___f_1628_, 2, v___x_1626_);
v___f_1629_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1629_, 0, v___x_1624_);
lean_closure_set(v___f_1629_, 1, v___f_1628_);
v_sz_1630_ = lean_array_size(v_buckets_1625_);
v___x_1631_ = ((size_t)0ULL);
v___x_1632_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1624_, v_buckets_1625_, v___f_1629_, v_sz_1630_, v___x_1631_, v___x_1627_);
v_fst_1633_ = lean_ctor_get(v___x_1632_, 0);
lean_inc(v_fst_1633_);
lean_dec(v___x_1632_);
if (lean_obj_tag(v_fst_1633_) == 0)
{
uint8_t v___x_1634_; 
v___x_1634_ = 0;
return v___x_1634_;
}
else
{
lean_object* v_val_1635_; uint8_t v___x_1636_; 
v_val_1635_ = lean_ctor_get(v_fst_1633_, 0);
lean_inc(v_val_1635_);
lean_dec_ref_known(v_fst_1633_, 1);
v___x_1636_ = lean_unbox(v_val_1635_);
lean_dec(v_val_1635_);
return v___x_1636_;
}
}
}
LEAN_EXPORT void l_Std_HashMap_Raw_any_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1622_ = stack[2].m_obj;
lean_object* v_p_1623_ = stack[3].m_obj;
uint8_t v_res_1637_;
v_res_1637_ = l_Std_HashMap_Raw_any(lean_box(0), lean_box(0), v_m_1622_, v_p_1623_);
stack->m_num = v_res_1637_;
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_any___boxed(lean_object* v_00_u03b1_1638_, lean_object* v_00_u03b2_1639_, lean_object* v_m_1640_, lean_object* v_p_1641_){
_start:
{
uint8_t v_res_1642_; lean_object* v_r_1643_; 
v_res_1642_ = l_Std_HashMap_Raw_any(v_00_u03b1_1638_, v_00_u03b2_1639_, v_m_1640_, v_p_1641_);
v_r_1643_ = lean_box(v_res_1642_);
return v_r_1643_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_union___redArg___lam__0(lean_object* v_inst_1644_, lean_object* v_inst_1645_, lean_object* v_a_1646_, lean_object* v_b_1647_, lean_object* v_acc_1648_){
_start:
{
lean_object* v_r_1649_; lean_object* v___x_1650_; 
v_r_1649_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_1644_, v_inst_1645_, v_acc_1648_, v_a_1646_, v_b_1647_);
v___x_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1650_, 0, v_r_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_union___redArg___lam__1(lean_object* v___x_1651_, lean_object* v___f_1652_, lean_object* v_a_1653_, lean_object* v_x_1654_, lean_object* v___y_1655_){
_start:
{
lean_object* v___x_1656_; 
v___x_1656_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1651_, v___f_1652_, v_a_1653_, v___y_1655_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_union___redArg(lean_object* v_inst_1659_, lean_object* v_inst_1660_, lean_object* v_m_u2081_1661_, lean_object* v_m_u2082_1662_){
_start:
{
lean_object* v_size_1663_; lean_object* v_buckets_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; uint8_t v___x_1667_; 
v_size_1663_ = lean_ctor_get(v_m_u2081_1661_, 0);
v_buckets_1664_ = lean_ctor_get(v_m_u2081_1661_, 1);
v___x_1665_ = lean_unsigned_to_nat(0u);
v___x_1666_ = lean_array_get_size(v_buckets_1664_);
v___x_1667_ = lean_nat_dec_lt(v___x_1665_, v___x_1666_);
if (v___x_1667_ == 0)
{
lean_dec_ref(v_m_u2081_1661_);
lean_dec_ref(v_inst_1660_);
lean_dec_ref(v_inst_1659_);
return v_m_u2082_1662_;
}
else
{
lean_object* v_size_1668_; lean_object* v_buckets_1669_; lean_object* v___x_1670_; uint8_t v___x_1671_; 
v_size_1668_ = lean_ctor_get(v_m_u2082_1662_, 0);
v_buckets_1669_ = lean_ctor_get(v_m_u2082_1662_, 1);
v___x_1670_ = lean_array_get_size(v_buckets_1669_);
v___x_1671_ = lean_nat_dec_lt(v___x_1665_, v___x_1670_);
if (v___x_1671_ == 0)
{
lean_dec_ref(v_m_u2082_1662_);
lean_dec_ref(v_inst_1660_);
lean_dec_ref(v_inst_1659_);
return v_m_u2081_1661_;
}
else
{
lean_object* v___x_1672_; uint8_t v___x_1673_; 
v___x_1672_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_1673_ = lean_nat_dec_le(v_size_1663_, v_size_1668_);
if (v___x_1673_ == 0)
{
lean_object* v___f_1674_; lean_object* v___x_1675_; 
v___f_1674_ = ((lean_object*)(l_Std_HashMap_Raw_union___redArg___closed__0));
v___x_1675_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1674_, v_inst_1659_, v_inst_1660_, v_m_u2081_1661_, v_m_u2082_1662_);
return v___x_1675_;
}
else
{
lean_object* v___f_1676_; lean_object* v___f_1677_; size_t v_sz_1678_; size_t v___x_1679_; lean_object* v___x_1680_; 
lean_inc_ref(v_buckets_1664_);
lean_dec_ref(v_m_u2081_1661_);
v___f_1676_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1676_, 0, v_inst_1659_);
lean_closure_set(v___f_1676_, 1, v_inst_1660_);
v___f_1677_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1677_, 0, v___x_1672_);
lean_closure_set(v___f_1677_, 1, v___f_1676_);
v_sz_1678_ = lean_array_size(v_buckets_1664_);
v___x_1679_ = ((size_t)0ULL);
v___x_1680_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1672_, v_buckets_1664_, v___f_1677_, v_sz_1678_, v___x_1679_, v_m_u2082_1662_);
return v___x_1680_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_union(lean_object* v_00_u03b1_1681_, lean_object* v_00_u03b2_1682_, lean_object* v_inst_1683_, lean_object* v_inst_1684_, lean_object* v_m_u2081_1685_, lean_object* v_m_u2082_1686_){
_start:
{
lean_object* v_size_1687_; lean_object* v_buckets_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; uint8_t v___x_1691_; 
v_size_1687_ = lean_ctor_get(v_m_u2081_1685_, 0);
v_buckets_1688_ = lean_ctor_get(v_m_u2081_1685_, 1);
v___x_1689_ = lean_unsigned_to_nat(0u);
v___x_1690_ = lean_array_get_size(v_buckets_1688_);
v___x_1691_ = lean_nat_dec_lt(v___x_1689_, v___x_1690_);
if (v___x_1691_ == 0)
{
lean_dec_ref(v_m_u2081_1685_);
lean_dec_ref(v_inst_1684_);
lean_dec_ref(v_inst_1683_);
return v_m_u2082_1686_;
}
else
{
lean_object* v_size_1692_; lean_object* v_buckets_1693_; lean_object* v___x_1694_; uint8_t v___x_1695_; 
v_size_1692_ = lean_ctor_get(v_m_u2082_1686_, 0);
v_buckets_1693_ = lean_ctor_get(v_m_u2082_1686_, 1);
v___x_1694_ = lean_array_get_size(v_buckets_1693_);
v___x_1695_ = lean_nat_dec_lt(v___x_1689_, v___x_1694_);
if (v___x_1695_ == 0)
{
lean_dec_ref(v_m_u2082_1686_);
lean_dec_ref(v_inst_1684_);
lean_dec_ref(v_inst_1683_);
return v_m_u2081_1685_;
}
else
{
lean_object* v___x_1696_; uint8_t v___x_1697_; 
v___x_1696_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_1697_ = lean_nat_dec_le(v_size_1687_, v_size_1692_);
if (v___x_1697_ == 0)
{
lean_object* v___f_1698_; lean_object* v___x_1699_; 
v___f_1698_ = ((lean_object*)(l_Std_HashMap_Raw_union___redArg___closed__0));
v___x_1699_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1698_, v_inst_1683_, v_inst_1684_, v_m_u2081_1685_, v_m_u2082_1686_);
return v___x_1699_;
}
else
{
lean_object* v___f_1700_; lean_object* v___f_1701_; size_t v_sz_1702_; size_t v___x_1703_; lean_object* v___x_1704_; 
lean_inc_ref(v_buckets_1688_);
lean_dec_ref(v_m_u2081_1685_);
v___f_1700_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1700_, 0, v_inst_1683_);
lean_closure_set(v___f_1700_, 1, v_inst_1684_);
v___f_1701_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1701_, 0, v___x_1696_);
lean_closure_set(v___f_1701_, 1, v___f_1700_);
v_sz_1702_ = lean_array_size(v_buckets_1688_);
v___x_1703_ = ((size_t)0ULL);
v___x_1704_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1696_, v_buckets_1688_, v___f_1701_, v_sz_1702_, v___x_1703_, v_m_u2082_1686_);
return v___x_1704_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_inter___redArg(lean_object* v_inst_1705_, lean_object* v_inst_1706_, lean_object* v_m_u2081_1707_, lean_object* v_m_u2082_1708_){
_start:
{
lean_object* v_buckets_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; uint8_t v___x_1712_; 
v_buckets_1709_ = lean_ctor_get(v_m_u2081_1707_, 1);
v___x_1710_ = lean_unsigned_to_nat(0u);
v___x_1711_ = lean_array_get_size(v_buckets_1709_);
v___x_1712_ = lean_nat_dec_lt(v___x_1710_, v___x_1711_);
if (v___x_1712_ == 0)
{
lean_dec_ref(v_m_u2081_1707_);
lean_dec_ref(v_inst_1706_);
lean_dec_ref(v_inst_1705_);
return v_m_u2082_1708_;
}
else
{
lean_object* v_buckets_1713_; lean_object* v___x_1714_; uint8_t v___x_1715_; 
v_buckets_1713_ = lean_ctor_get(v_m_u2082_1708_, 1);
v___x_1714_ = lean_array_get_size(v_buckets_1713_);
v___x_1715_ = lean_nat_dec_lt(v___x_1710_, v___x_1714_);
if (v___x_1715_ == 0)
{
lean_dec_ref(v_m_u2082_1708_);
lean_dec_ref(v_inst_1706_);
lean_dec_ref(v_inst_1705_);
return v_m_u2081_1707_;
}
else
{
lean_object* v___x_1716_; 
v___x_1716_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1705_, v_inst_1706_, v_m_u2081_1707_, v_m_u2082_1708_);
return v___x_1716_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_inter(lean_object* v_00_u03b1_1717_, lean_object* v_00_u03b2_1718_, lean_object* v_inst_1719_, lean_object* v_inst_1720_, lean_object* v_m_u2081_1721_, lean_object* v_m_u2082_1722_){
_start:
{
lean_object* v_buckets_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; uint8_t v___x_1726_; 
v_buckets_1723_ = lean_ctor_get(v_m_u2081_1721_, 1);
v___x_1724_ = lean_unsigned_to_nat(0u);
v___x_1725_ = lean_array_get_size(v_buckets_1723_);
v___x_1726_ = lean_nat_dec_lt(v___x_1724_, v___x_1725_);
if (v___x_1726_ == 0)
{
lean_dec_ref(v_m_u2081_1721_);
lean_dec_ref(v_inst_1720_);
lean_dec_ref(v_inst_1719_);
return v_m_u2082_1722_;
}
else
{
lean_object* v_buckets_1727_; lean_object* v___x_1728_; uint8_t v___x_1729_; 
v_buckets_1727_ = lean_ctor_get(v_m_u2082_1722_, 1);
v___x_1728_ = lean_array_get_size(v_buckets_1727_);
v___x_1729_ = lean_nat_dec_lt(v___x_1724_, v___x_1728_);
if (v___x_1729_ == 0)
{
lean_dec_ref(v_m_u2082_1722_);
lean_dec_ref(v_inst_1720_);
lean_dec_ref(v_inst_1719_);
return v_m_u2081_1721_;
}
else
{
lean_object* v___x_1730_; 
v___x_1730_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1719_, v_inst_1720_, v_m_u2081_1721_, v_m_u2082_1722_);
return v___x_1730_;
}
}
}
}
uint8_t l_Std_HashMap_Raw_diff___redArg___lam__0(lean_object* v_inst_1731_, lean_object* v_inst_1732_, lean_object* v_m_u2082_1733_, uint8_t v___x_1734_, lean_object* v_k_1735_, lean_object* v_x_1736_){
_start:
{
uint8_t v___x_1737_; 
v___x_1737_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1731_, v_inst_1732_, v_m_u2082_1733_, v_k_1735_);
if (v___x_1737_ == 0)
{
return v___x_1734_;
}
else
{
uint8_t v___x_1738_; 
v___x_1738_ = 0;
return v___x_1738_;
}
}
}
LEAN_EXPORT void l_Std_HashMap_Raw_diff___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1731_ = stack[0].m_obj;
lean_object* v_inst_1732_ = stack[1].m_obj;
lean_object* v_m_u2082_1733_ = stack[2].m_obj;
uint8_t v___x_1734_ = stack[3].m_num;
lean_object* v_k_1735_ = stack[4].m_obj;
lean_object* v_x_1736_ = stack[5].m_obj;
uint8_t v_res_1739_;
v_res_1739_ = l_Std_HashMap_Raw_diff___redArg___lam__0(v_inst_1731_, v_inst_1732_, v_m_u2082_1733_, v___x_1734_, v_k_1735_, v_x_1736_);
stack->m_num = v_res_1739_;
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_diff___redArg___lam__0___boxed(lean_object* v_inst_1740_, lean_object* v_inst_1741_, lean_object* v_m_u2082_1742_, lean_object* v___x_1743_, lean_object* v_k_1744_, lean_object* v_x_1745_){
_start:
{
uint8_t v___x_94__boxed_1746_; uint8_t v_res_1747_; lean_object* v_r_1748_; 
v___x_94__boxed_1746_ = lean_unbox(v___x_1743_);
v_res_1747_ = l_Std_HashMap_Raw_diff___redArg___lam__0(v_inst_1740_, v_inst_1741_, v_m_u2082_1742_, v___x_94__boxed_1746_, v_k_1744_, v_x_1745_);
lean_dec(v_x_1745_);
lean_dec_ref(v_m_u2082_1742_);
v_r_1748_ = lean_box(v_res_1747_);
return v_r_1748_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_diff___redArg(lean_object* v_inst_1749_, lean_object* v_inst_1750_, lean_object* v_m_u2081_1751_, lean_object* v_m_u2082_1752_){
_start:
{
lean_object* v_size_1753_; lean_object* v_buckets_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; uint8_t v___x_1757_; 
v_size_1753_ = lean_ctor_get(v_m_u2081_1751_, 0);
v_buckets_1754_ = lean_ctor_get(v_m_u2081_1751_, 1);
v___x_1755_ = lean_unsigned_to_nat(0u);
v___x_1756_ = lean_array_get_size(v_buckets_1754_);
v___x_1757_ = lean_nat_dec_lt(v___x_1755_, v___x_1756_);
if (v___x_1757_ == 0)
{
lean_dec_ref(v_m_u2081_1751_);
lean_dec_ref(v_inst_1750_);
lean_dec_ref(v_inst_1749_);
return v_m_u2082_1752_;
}
else
{
lean_object* v_size_1758_; lean_object* v_buckets_1759_; lean_object* v___x_1760_; uint8_t v___x_1761_; 
v_size_1758_ = lean_ctor_get(v_m_u2082_1752_, 0);
v_buckets_1759_ = lean_ctor_get(v_m_u2082_1752_, 1);
v___x_1760_ = lean_array_get_size(v_buckets_1759_);
v___x_1761_ = lean_nat_dec_lt(v___x_1755_, v___x_1760_);
if (v___x_1761_ == 0)
{
lean_dec_ref(v_m_u2082_1752_);
lean_dec_ref(v_inst_1750_);
lean_dec_ref(v_inst_1749_);
return v_m_u2081_1751_;
}
else
{
uint8_t v___x_1762_; 
v___x_1762_ = lean_nat_dec_le(v_size_1753_, v_size_1758_);
if (v___x_1762_ == 0)
{
lean_object* v___f_1763_; lean_object* v___x_1764_; 
v___f_1763_ = ((lean_object*)(l_Std_HashMap_Raw_union___redArg___closed__0));
v___x_1764_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1763_, v_inst_1749_, v_inst_1750_, v_m_u2081_1751_, v_m_u2082_1752_);
return v___x_1764_;
}
else
{
lean_object* v___x_1765_; lean_object* v___f_1766_; lean_object* v___x_1767_; 
v___x_1765_ = lean_box(v___x_1762_);
v___f_1766_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1766_, 0, v_inst_1749_);
lean_closure_set(v___f_1766_, 1, v_inst_1750_);
lean_closure_set(v___f_1766_, 2, v_m_u2082_1752_);
lean_closure_set(v___f_1766_, 3, v___x_1765_);
v___x_1767_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1766_, v_m_u2081_1751_);
return v___x_1767_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_diff(lean_object* v_00_u03b1_1768_, lean_object* v_00_u03b2_1769_, lean_object* v_inst_1770_, lean_object* v_inst_1771_, lean_object* v_m_u2081_1772_, lean_object* v_m_u2082_1773_){
_start:
{
lean_object* v_size_1774_; lean_object* v_buckets_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; uint8_t v___x_1778_; 
v_size_1774_ = lean_ctor_get(v_m_u2081_1772_, 0);
v_buckets_1775_ = lean_ctor_get(v_m_u2081_1772_, 1);
v___x_1776_ = lean_unsigned_to_nat(0u);
v___x_1777_ = lean_array_get_size(v_buckets_1775_);
v___x_1778_ = lean_nat_dec_lt(v___x_1776_, v___x_1777_);
if (v___x_1778_ == 0)
{
lean_dec_ref(v_m_u2081_1772_);
lean_dec_ref(v_inst_1771_);
lean_dec_ref(v_inst_1770_);
return v_m_u2082_1773_;
}
else
{
lean_object* v_size_1779_; lean_object* v_buckets_1780_; lean_object* v___x_1781_; uint8_t v___x_1782_; 
v_size_1779_ = lean_ctor_get(v_m_u2082_1773_, 0);
v_buckets_1780_ = lean_ctor_get(v_m_u2082_1773_, 1);
v___x_1781_ = lean_array_get_size(v_buckets_1780_);
v___x_1782_ = lean_nat_dec_lt(v___x_1776_, v___x_1781_);
if (v___x_1782_ == 0)
{
lean_dec_ref(v_m_u2082_1773_);
lean_dec_ref(v_inst_1771_);
lean_dec_ref(v_inst_1770_);
return v_m_u2081_1772_;
}
else
{
uint8_t v___x_1783_; 
v___x_1783_ = lean_nat_dec_le(v_size_1774_, v_size_1779_);
if (v___x_1783_ == 0)
{
lean_object* v___f_1784_; lean_object* v___x_1785_; 
v___f_1784_ = ((lean_object*)(l_Std_HashMap_Raw_union___redArg___closed__0));
v___x_1785_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1784_, v_inst_1770_, v_inst_1771_, v_m_u2081_1772_, v_m_u2082_1773_);
return v___x_1785_;
}
else
{
lean_object* v___x_1786_; lean_object* v___f_1787_; lean_object* v___x_1788_; 
v___x_1786_ = lean_box(v___x_1783_);
v___f_1787_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1787_, 0, v_inst_1770_);
lean_closure_set(v___f_1787_, 1, v_inst_1771_);
lean_closure_set(v___f_1787_, 2, v_m_u2082_1773_);
lean_closure_set(v___f_1787_, 3, v___x_1786_);
v___x_1788_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1787_, v_m_u2081_1772_);
return v___x_1788_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instUnionOfBEqOfHashable___redArg(lean_object* v_inst_1789_, lean_object* v_inst_1790_){
_start:
{
lean_object* v___x_1791_; 
v___x_1791_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union), 6, 4);
lean_closure_set(v___x_1791_, 0, lean_box(0));
lean_closure_set(v___x_1791_, 1, lean_box(0));
lean_closure_set(v___x_1791_, 2, v_inst_1789_);
lean_closure_set(v___x_1791_, 3, v_inst_1790_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instUnionOfBEqOfHashable(lean_object* v_00_u03b1_1792_, lean_object* v_00_u03b2_1793_, lean_object* v_inst_1794_, lean_object* v_inst_1795_){
_start:
{
lean_object* v___x_1796_; 
v___x_1796_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union), 6, 4);
lean_closure_set(v___x_1796_, 0, lean_box(0));
lean_closure_set(v___x_1796_, 1, lean_box(0));
lean_closure_set(v___x_1796_, 2, v_inst_1794_);
lean_closure_set(v___x_1796_, 3, v_inst_1795_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInterOfBEqOfHashable___redArg(lean_object* v_inst_1797_, lean_object* v_inst_1798_){
_start:
{
lean_object* v___x_1799_; 
v___x_1799_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_inter), 6, 4);
lean_closure_set(v___x_1799_, 0, lean_box(0));
lean_closure_set(v___x_1799_, 1, lean_box(0));
lean_closure_set(v___x_1799_, 2, v_inst_1797_);
lean_closure_set(v___x_1799_, 3, v_inst_1798_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInterOfBEqOfHashable(lean_object* v_00_u03b1_1800_, lean_object* v_00_u03b2_1801_, lean_object* v_inst_1802_, lean_object* v_inst_1803_){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_inter), 6, 4);
lean_closure_set(v___x_1804_, 0, lean_box(0));
lean_closure_set(v___x_1804_, 1, lean_box(0));
lean_closure_set(v___x_1804_, 2, v_inst_1802_);
lean_closure_set(v___x_1804_, 3, v_inst_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSDiffOfBEqOfHashable___redArg(lean_object* v_inst_1805_, lean_object* v_inst_1806_){
_start:
{
lean_object* v___x_1807_; 
v___x_1807_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_diff), 6, 4);
lean_closure_set(v___x_1807_, 0, lean_box(0));
lean_closure_set(v___x_1807_, 1, lean_box(0));
lean_closure_set(v___x_1807_, 2, v_inst_1805_);
lean_closure_set(v___x_1807_, 3, v_inst_1806_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSDiffOfBEqOfHashable(lean_object* v_00_u03b1_1808_, lean_object* v_00_u03b2_1809_, lean_object* v_inst_1810_, lean_object* v_inst_1811_){
_start:
{
lean_object* v___x_1812_; 
v___x_1812_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_diff), 6, 4);
lean_closure_set(v___x_1812_, 0, lean_box(0));
lean_closure_set(v___x_1812_, 1, lean_box(0));
lean_closure_set(v___x_1812_, 2, v_inst_1810_);
lean_closure_set(v___x_1812_, 3, v_inst_1811_);
return v___x_1812_;
}
}
uint8_t l_Std_HashMap_Raw_beq___redArg(lean_object* v_inst_1813_, lean_object* v_inst_1814_, lean_object* v_inst_1815_, lean_object* v_m_u2081_1816_, lean_object* v_m_u2082_1817_){
_start:
{
uint8_t v___x_1818_; 
v___x_1818_ = l_Std_DHashMap_Raw_Const_beq___redArg(v_inst_1813_, v_inst_1814_, v_inst_1815_, v_m_u2081_1816_, v_m_u2082_1817_);
return v___x_1818_;
}
}
LEAN_EXPORT void l_Std_HashMap_Raw_beq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1813_ = stack[0].m_obj;
lean_object* v_inst_1814_ = stack[1].m_obj;
lean_object* v_inst_1815_ = stack[2].m_obj;
lean_object* v_m_u2081_1816_ = stack[3].m_obj;
lean_object* v_m_u2082_1817_ = stack[4].m_obj;
uint8_t v_res_1819_;
v_res_1819_ = l_Std_HashMap_Raw_beq___redArg(v_inst_1813_, v_inst_1814_, v_inst_1815_, v_m_u2081_1816_, v_m_u2082_1817_);
stack->m_num = v_res_1819_;
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_beq___redArg___boxed(lean_object* v_inst_1820_, lean_object* v_inst_1821_, lean_object* v_inst_1822_, lean_object* v_m_u2081_1823_, lean_object* v_m_u2082_1824_){
_start:
{
uint8_t v_res_1825_; lean_object* v_r_1826_; 
v_res_1825_ = l_Std_HashMap_Raw_beq___redArg(v_inst_1820_, v_inst_1821_, v_inst_1822_, v_m_u2081_1823_, v_m_u2082_1824_);
v_r_1826_ = lean_box(v_res_1825_);
return v_r_1826_;
}
}
uint8_t l_Std_HashMap_Raw_beq(lean_object* v_00_u03b1_1827_, lean_object* v_00_u03b2_1828_, lean_object* v_inst_1829_, lean_object* v_inst_1830_, lean_object* v_inst_1831_, lean_object* v_m_u2081_1832_, lean_object* v_m_u2082_1833_){
_start:
{
uint8_t v___x_1834_; 
v___x_1834_ = l_Std_DHashMap_Raw_Const_beq___redArg(v_inst_1829_, v_inst_1830_, v_inst_1831_, v_m_u2081_1832_, v_m_u2082_1833_);
return v___x_1834_;
}
}
LEAN_EXPORT void l_Std_HashMap_Raw_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1829_ = stack[2].m_obj;
lean_object* v_inst_1830_ = stack[3].m_obj;
lean_object* v_inst_1831_ = stack[4].m_obj;
lean_object* v_m_u2081_1832_ = stack[5].m_obj;
lean_object* v_m_u2082_1833_ = stack[6].m_obj;
uint8_t v_res_1835_;
v_res_1835_ = l_Std_HashMap_Raw_beq(lean_box(0), lean_box(0), v_inst_1829_, v_inst_1830_, v_inst_1831_, v_m_u2081_1832_, v_m_u2082_1833_);
stack->m_num = v_res_1835_;
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_beq___boxed(lean_object* v_00_u03b1_1836_, lean_object* v_00_u03b2_1837_, lean_object* v_inst_1838_, lean_object* v_inst_1839_, lean_object* v_inst_1840_, lean_object* v_m_u2081_1841_, lean_object* v_m_u2082_1842_){
_start:
{
uint8_t v_res_1843_; lean_object* v_r_1844_; 
v_res_1843_ = l_Std_HashMap_Raw_beq(v_00_u03b1_1836_, v_00_u03b2_1837_, v_inst_1838_, v_inst_1839_, v_inst_1840_, v_m_u2081_1841_, v_m_u2082_1842_);
v_r_1844_ = lean_box(v_res_1843_);
return v_r_1844_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instBEqOfHashable___redArg(lean_object* v_inst_1845_, lean_object* v_inst_1846_, lean_object* v_inst_1847_){
_start:
{
lean_object* v___x_1848_; 
v___x_1848_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_beq___boxed), 7, 5);
lean_closure_set(v___x_1848_, 0, lean_box(0));
lean_closure_set(v___x_1848_, 1, lean_box(0));
lean_closure_set(v___x_1848_, 2, v_inst_1845_);
lean_closure_set(v___x_1848_, 3, v_inst_1846_);
lean_closure_set(v___x_1848_, 4, v_inst_1847_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instBEqOfHashable(lean_object* v_00_u03b1_1849_, lean_object* v_00_u03b2_1850_, lean_object* v_inst_1851_, lean_object* v_inst_1852_, lean_object* v_inst_1853_){
_start:
{
lean_object* v___x_1854_; 
v___x_1854_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_beq___boxed), 7, 5);
lean_closure_set(v___x_1854_, 0, lean_box(0));
lean_closure_set(v___x_1854_, 1, lean_box(0));
lean_closure_set(v___x_1854_, 2, v_inst_1851_);
lean_closure_set(v___x_1854_, 3, v_inst_1852_);
lean_closure_set(v___x_1854_, 4, v_inst_1853_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filterMap___redArg(lean_object* v_f_1855_, lean_object* v_m_1856_){
_start:
{
lean_object* v_buckets_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; uint8_t v___x_1860_; 
v_buckets_1857_ = lean_ctor_get(v_m_1856_, 1);
v___x_1858_ = lean_unsigned_to_nat(0u);
v___x_1859_ = lean_array_get_size(v_buckets_1857_);
v___x_1860_ = lean_nat_dec_lt(v___x_1858_, v___x_1859_);
if (v___x_1860_ == 0)
{
lean_object* v___x_1861_; 
lean_dec_ref(v_m_1856_);
lean_dec_ref(v_f_1855_);
v___x_1861_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1861_;
}
else
{
lean_object* v___x_1862_; 
v___x_1862_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_1855_, v_m_1856_);
return v___x_1862_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filterMap(lean_object* v_00_u03b1_1863_, lean_object* v_00_u03b2_1864_, lean_object* v_00_u03b3_1865_, lean_object* v_f_1866_, lean_object* v_m_1867_){
_start:
{
lean_object* v_buckets_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; uint8_t v___x_1871_; 
v_buckets_1868_ = lean_ctor_get(v_m_1867_, 1);
v___x_1869_ = lean_unsigned_to_nat(0u);
v___x_1870_ = lean_array_get_size(v_buckets_1868_);
v___x_1871_ = lean_nat_dec_lt(v___x_1869_, v___x_1870_);
if (v___x_1871_ == 0)
{
lean_object* v___x_1872_; 
lean_dec_ref(v_m_1867_);
lean_dec_ref(v_f_1866_);
v___x_1872_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1872_;
}
else
{
lean_object* v___x_1873_; 
v___x_1873_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_1866_, v_m_1867_);
return v___x_1873_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_map___redArg(lean_object* v_f_1874_, lean_object* v_m_1875_){
_start:
{
lean_object* v_buckets_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; uint8_t v___x_1879_; 
v_buckets_1876_ = lean_ctor_get(v_m_1875_, 1);
v___x_1877_ = lean_unsigned_to_nat(0u);
v___x_1878_ = lean_array_get_size(v_buckets_1876_);
v___x_1879_ = lean_nat_dec_lt(v___x_1877_, v___x_1878_);
if (v___x_1879_ == 0)
{
lean_object* v___x_1880_; 
lean_dec_ref(v_m_1875_);
lean_dec(v_f_1874_);
v___x_1880_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1880_;
}
else
{
lean_object* v___x_1881_; 
v___x_1881_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_1874_, v_m_1875_);
return v___x_1881_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_map(lean_object* v_00_u03b1_1882_, lean_object* v_00_u03b2_1883_, lean_object* v_00_u03b3_1884_, lean_object* v_f_1885_, lean_object* v_m_1886_){
_start:
{
lean_object* v_buckets_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; uint8_t v___x_1890_; 
v_buckets_1887_ = lean_ctor_get(v_m_1886_, 1);
v___x_1888_ = lean_unsigned_to_nat(0u);
v___x_1889_ = lean_array_get_size(v_buckets_1887_);
v___x_1890_ = lean_nat_dec_lt(v___x_1888_, v___x_1889_);
if (v___x_1890_ == 0)
{
lean_object* v___x_1891_; 
lean_dec_ref(v_m_1886_);
lean_dec(v_f_1885_);
v___x_1891_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1891_;
}
else
{
lean_object* v___x_1892_; 
v___x_1892_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_1885_, v_m_1886_);
return v___x_1892_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filter___redArg(lean_object* v_f_1893_, lean_object* v_m_1894_){
_start:
{
lean_object* v_buckets_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; uint8_t v___x_1898_; 
v_buckets_1895_ = lean_ctor_get(v_m_1894_, 1);
v___x_1896_ = lean_unsigned_to_nat(0u);
v___x_1897_ = lean_array_get_size(v_buckets_1895_);
v___x_1898_ = lean_nat_dec_lt(v___x_1896_, v___x_1897_);
if (v___x_1898_ == 0)
{
lean_object* v___x_1899_; 
lean_dec_ref(v_m_1894_);
lean_dec_ref(v_f_1893_);
v___x_1899_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1899_;
}
else
{
lean_object* v___x_1900_; 
v___x_1900_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1893_, v_m_1894_);
return v___x_1900_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filter(lean_object* v_00_u03b1_1901_, lean_object* v_00_u03b2_1902_, lean_object* v_f_1903_, lean_object* v_m_1904_){
_start:
{
lean_object* v_buckets_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; uint8_t v___x_1908_; 
v_buckets_1905_ = lean_ctor_get(v_m_1904_, 1);
v___x_1906_ = lean_unsigned_to_nat(0u);
v___x_1907_ = lean_array_get_size(v_buckets_1905_);
v___x_1908_ = lean_nat_dec_lt(v___x_1906_, v___x_1907_);
if (v___x_1908_ == 0)
{
lean_object* v___x_1909_; 
lean_dec_ref(v_m_1904_);
lean_dec_ref(v_f_1903_);
v___x_1909_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1909_;
}
else
{
lean_object* v___x_1910_; 
v___x_1910_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1903_, v_m_1904_);
return v___x_1910_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toArray___redArg___lam__0(lean_object* v_x1_1911_, lean_object* v_x2_1912_, lean_object* v_x3_1913_){
_start:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1914_, 0, v_x2_1912_);
lean_ctor_set(v___x_1914_, 1, v_x3_1913_);
v___x_1915_ = lean_array_push(v_x1_1911_, v___x_1914_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toArray___redArg___lam__1(lean_object* v___x_1916_, lean_object* v___f_1917_, lean_object* v_acc_1918_, lean_object* v_l_1919_){
_start:
{
lean_object* v___x_1920_; 
v___x_1920_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1916_, v___f_1917_, v_acc_1918_, v_l_1919_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toArray___redArg(lean_object* v_m_1925_){
_start:
{
lean_object* v_size_1926_; lean_object* v_buckets_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; uint8_t v___x_1932_; 
v_size_1926_ = lean_ctor_get(v_m_1925_, 0);
lean_inc(v_size_1926_);
v_buckets_1927_ = lean_ctor_get(v_m_1925_, 1);
lean_inc_ref(v_buckets_1927_);
lean_dec_ref(v_m_1925_);
v___x_1928_ = lean_mk_empty_array_with_capacity(v_size_1926_);
lean_dec(v_size_1926_);
v___x_1929_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_1930_ = lean_unsigned_to_nat(0u);
v___x_1931_ = lean_array_get_size(v_buckets_1927_);
v___x_1932_ = lean_nat_dec_lt(v___x_1930_, v___x_1931_);
if (v___x_1932_ == 0)
{
lean_dec_ref(v_buckets_1927_);
return v___x_1928_;
}
else
{
lean_object* v___f_1933_; size_t v___x_1934_; size_t v___x_1935_; lean_object* v___x_1936_; 
v___f_1933_ = ((lean_object*)(l_Std_HashMap_Raw_toArray___redArg___closed__1));
v___x_1934_ = ((size_t)0ULL);
v___x_1935_ = lean_usize_of_nat(v___x_1931_);
v___x_1936_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1929_, v___f_1933_, v_buckets_1927_, v___x_1934_, v___x_1935_, v___x_1928_);
return v___x_1936_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toArray(lean_object* v_00_u03b1_1937_, lean_object* v_00_u03b2_1938_, lean_object* v_m_1939_){
_start:
{
lean_object* v_size_1940_; lean_object* v_buckets_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; uint8_t v___x_1946_; 
v_size_1940_ = lean_ctor_get(v_m_1939_, 0);
lean_inc(v_size_1940_);
v_buckets_1941_ = lean_ctor_get(v_m_1939_, 1);
lean_inc_ref(v_buckets_1941_);
lean_dec_ref(v_m_1939_);
v___x_1942_ = lean_mk_empty_array_with_capacity(v_size_1940_);
lean_dec(v_size_1940_);
v___x_1943_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_1944_ = lean_unsigned_to_nat(0u);
v___x_1945_ = lean_array_get_size(v_buckets_1941_);
v___x_1946_ = lean_nat_dec_lt(v___x_1944_, v___x_1945_);
if (v___x_1946_ == 0)
{
lean_dec_ref(v_buckets_1941_);
return v___x_1942_;
}
else
{
lean_object* v___f_1947_; size_t v___x_1948_; size_t v___x_1949_; lean_object* v___x_1950_; 
v___f_1947_ = ((lean_object*)(l_Std_HashMap_Raw_toArray___redArg___closed__1));
v___x_1948_ = ((size_t)0ULL);
v___x_1949_ = lean_usize_of_nat(v___x_1945_);
v___x_1950_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1943_, v___f_1947_, v_buckets_1941_, v___x_1948_, v___x_1949_, v___x_1942_);
return v___x_1950_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray___redArg___lam__0(lean_object* v_x1_1951_, lean_object* v_x2_1952_, lean_object* v_x3_1953_){
_start:
{
lean_object* v___x_1954_; 
v___x_1954_ = lean_array_push(v_x1_1951_, v_x2_1952_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray___redArg___lam__0___boxed(lean_object* v_x1_1955_, lean_object* v_x2_1956_, lean_object* v_x3_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l_Std_HashMap_Raw_keysArray___redArg___lam__0(v_x1_1955_, v_x2_1956_, v_x3_1957_);
lean_dec(v_x3_1957_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray___redArg___lam__1(lean_object* v___x_1959_, lean_object* v___f_1960_, lean_object* v_acc_1961_, lean_object* v_l_1962_){
_start:
{
lean_object* v___x_1963_; 
v___x_1963_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1959_, v___f_1960_, v_acc_1961_, v_l_1962_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray___redArg(lean_object* v_m_1968_){
_start:
{
lean_object* v_size_1969_; lean_object* v_buckets_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; uint8_t v___x_1975_; 
v_size_1969_ = lean_ctor_get(v_m_1968_, 0);
lean_inc(v_size_1969_);
v_buckets_1970_ = lean_ctor_get(v_m_1968_, 1);
lean_inc_ref(v_buckets_1970_);
lean_dec_ref(v_m_1968_);
v___x_1971_ = lean_mk_empty_array_with_capacity(v_size_1969_);
lean_dec(v_size_1969_);
v___x_1972_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_1973_ = lean_unsigned_to_nat(0u);
v___x_1974_ = lean_array_get_size(v_buckets_1970_);
v___x_1975_ = lean_nat_dec_lt(v___x_1973_, v___x_1974_);
if (v___x_1975_ == 0)
{
lean_dec_ref(v_buckets_1970_);
return v___x_1971_;
}
else
{
lean_object* v___f_1976_; size_t v___x_1977_; size_t v___x_1978_; lean_object* v___x_1979_; 
v___f_1976_ = ((lean_object*)(l_Std_HashMap_Raw_keysArray___redArg___closed__1));
v___x_1977_ = ((size_t)0ULL);
v___x_1978_ = lean_usize_of_nat(v___x_1974_);
v___x_1979_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1972_, v___f_1976_, v_buckets_1970_, v___x_1977_, v___x_1978_, v___x_1971_);
return v___x_1979_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray(lean_object* v_00_u03b1_1980_, lean_object* v_00_u03b2_1981_, lean_object* v_m_1982_){
_start:
{
lean_object* v_size_1983_; lean_object* v_buckets_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; uint8_t v___x_1989_; 
v_size_1983_ = lean_ctor_get(v_m_1982_, 0);
lean_inc(v_size_1983_);
v_buckets_1984_ = lean_ctor_get(v_m_1982_, 1);
lean_inc_ref(v_buckets_1984_);
lean_dec_ref(v_m_1982_);
v___x_1985_ = lean_mk_empty_array_with_capacity(v_size_1983_);
lean_dec(v_size_1983_);
v___x_1986_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_1987_ = lean_unsigned_to_nat(0u);
v___x_1988_ = lean_array_get_size(v_buckets_1984_);
v___x_1989_ = lean_nat_dec_lt(v___x_1987_, v___x_1988_);
if (v___x_1989_ == 0)
{
lean_dec_ref(v_buckets_1984_);
return v___x_1985_;
}
else
{
lean_object* v___f_1990_; size_t v___x_1991_; size_t v___x_1992_; lean_object* v___x_1993_; 
v___f_1990_ = ((lean_object*)(l_Std_HashMap_Raw_keysArray___redArg___closed__1));
v___x_1991_ = ((size_t)0ULL);
v___x_1992_ = lean_usize_of_nat(v___x_1988_);
v___x_1993_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1986_, v___f_1990_, v_buckets_1984_, v___x_1991_, v___x_1992_, v___x_1985_);
return v___x_1993_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values___redArg___lam__0(lean_object* v_a_1994_, lean_object* v_b_1995_, lean_object* v_d_1996_){
_start:
{
lean_object* v___x_1997_; 
v___x_1997_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1997_, 0, v_b_1995_);
lean_ctor_set(v___x_1997_, 1, v_d_1996_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values___redArg___lam__0___boxed(lean_object* v_a_1998_, lean_object* v_b_1999_, lean_object* v_d_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l_Std_HashMap_Raw_values___redArg___lam__0(v_a_1998_, v_b_1999_, v_d_2000_);
lean_dec(v_a_1998_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values___redArg(lean_object* v_m_2006_){
_start:
{
lean_object* v___x_2007_; lean_object* v_buckets_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; uint8_t v___x_2012_; 
v___x_2007_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_2008_ = lean_ctor_get(v_m_2006_, 1);
lean_inc_ref(v_buckets_2008_);
lean_dec_ref(v_m_2006_);
v___x_2009_ = lean_box(0);
v___x_2010_ = lean_array_get_size(v_buckets_2008_);
v___x_2011_ = lean_unsigned_to_nat(0u);
v___x_2012_ = lean_nat_dec_lt(v___x_2011_, v___x_2010_);
if (v___x_2012_ == 0)
{
lean_dec_ref(v_buckets_2008_);
return v___x_2009_;
}
else
{
lean_object* v___f_2013_; size_t v___x_2014_; size_t v___x_2015_; lean_object* v___x_2016_; 
v___f_2013_ = ((lean_object*)(l_Std_HashMap_Raw_values___redArg___closed__1));
v___x_2014_ = lean_usize_of_nat(v___x_2010_);
v___x_2015_ = ((size_t)0ULL);
v___x_2016_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2007_, v___f_2013_, v_buckets_2008_, v___x_2014_, v___x_2015_, v___x_2009_);
return v___x_2016_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values(lean_object* v_00_u03b1_2017_, lean_object* v_00_u03b2_2018_, lean_object* v_m_2019_){
_start:
{
lean_object* v___x_2020_; lean_object* v_buckets_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; uint8_t v___x_2025_; 
v___x_2020_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_2021_ = lean_ctor_get(v_m_2019_, 1);
lean_inc_ref(v_buckets_2021_);
lean_dec_ref(v_m_2019_);
v___x_2022_ = lean_box(0);
v___x_2023_ = lean_array_get_size(v_buckets_2021_);
v___x_2024_ = lean_unsigned_to_nat(0u);
v___x_2025_ = lean_nat_dec_lt(v___x_2024_, v___x_2023_);
if (v___x_2025_ == 0)
{
lean_dec_ref(v_buckets_2021_);
return v___x_2022_;
}
else
{
lean_object* v___f_2026_; size_t v___x_2027_; size_t v___x_2028_; lean_object* v___x_2029_; 
v___f_2026_ = ((lean_object*)(l_Std_HashMap_Raw_values___redArg___closed__1));
v___x_2027_ = lean_usize_of_nat(v___x_2023_);
v___x_2028_ = ((size_t)0ULL);
v___x_2029_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2020_, v___f_2026_, v_buckets_2021_, v___x_2027_, v___x_2028_, v___x_2022_);
return v___x_2029_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesArray___redArg___lam__0(lean_object* v_x1_2030_, lean_object* v_x2_2031_, lean_object* v_x3_2032_){
_start:
{
lean_object* v___x_2033_; 
v___x_2033_ = lean_array_push(v_x1_2030_, v_x3_2032_);
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesArray___redArg___lam__0___boxed(lean_object* v_x1_2034_, lean_object* v_x2_2035_, lean_object* v_x3_2036_){
_start:
{
lean_object* v_res_2037_; 
v_res_2037_ = l_Std_HashMap_Raw_valuesArray___redArg___lam__0(v_x1_2034_, v_x2_2035_, v_x3_2036_);
lean_dec(v_x2_2035_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesArray___redArg(lean_object* v_m_2042_){
_start:
{
lean_object* v_size_2043_; lean_object* v_buckets_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; uint8_t v___x_2049_; 
v_size_2043_ = lean_ctor_get(v_m_2042_, 0);
lean_inc(v_size_2043_);
v_buckets_2044_ = lean_ctor_get(v_m_2042_, 1);
lean_inc_ref(v_buckets_2044_);
lean_dec_ref(v_m_2042_);
v___x_2045_ = lean_mk_empty_array_with_capacity(v_size_2043_);
lean_dec(v_size_2043_);
v___x_2046_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_2047_ = lean_unsigned_to_nat(0u);
v___x_2048_ = lean_array_get_size(v_buckets_2044_);
v___x_2049_ = lean_nat_dec_lt(v___x_2047_, v___x_2048_);
if (v___x_2049_ == 0)
{
lean_dec_ref(v_buckets_2044_);
return v___x_2045_;
}
else
{
lean_object* v___f_2050_; size_t v___x_2051_; size_t v___x_2052_; lean_object* v___x_2053_; 
v___f_2050_ = ((lean_object*)(l_Std_HashMap_Raw_valuesArray___redArg___closed__1));
v___x_2051_ = ((size_t)0ULL);
v___x_2052_ = lean_usize_of_nat(v___x_2048_);
v___x_2053_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2046_, v___f_2050_, v_buckets_2044_, v___x_2051_, v___x_2052_, v___x_2045_);
return v___x_2053_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesArray(lean_object* v_00_u03b1_2054_, lean_object* v_00_u03b2_2055_, lean_object* v_m_2056_){
_start:
{
lean_object* v_size_2057_; lean_object* v_buckets_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; uint8_t v___x_2063_; 
v_size_2057_ = lean_ctor_get(v_m_2056_, 0);
lean_inc(v_size_2057_);
v_buckets_2058_ = lean_ctor_get(v_m_2056_, 1);
lean_inc_ref(v_buckets_2058_);
lean_dec_ref(v_m_2056_);
v___x_2059_ = lean_mk_empty_array_with_capacity(v_size_2057_);
lean_dec(v_size_2057_);
v___x_2060_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_2061_ = lean_unsigned_to_nat(0u);
v___x_2062_ = lean_array_get_size(v_buckets_2058_);
v___x_2063_ = lean_nat_dec_lt(v___x_2061_, v___x_2062_);
if (v___x_2063_ == 0)
{
lean_dec_ref(v_buckets_2058_);
return v___x_2059_;
}
else
{
lean_object* v___f_2064_; size_t v___x_2065_; size_t v___x_2066_; lean_object* v___x_2067_; 
v___f_2064_ = ((lean_object*)(l_Std_HashMap_Raw_valuesArray___redArg___closed__1));
v___x_2065_ = ((size_t)0ULL);
v___x_2066_ = lean_usize_of_nat(v___x_2062_);
v___x_2067_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2060_, v___f_2064_, v_buckets_2058_, v___x_2065_, v___x_2066_, v___x_2059_);
return v___x_2067_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertMany___redArg(lean_object* v_inst_2068_, lean_object* v_inst_2069_, lean_object* v_inst_2070_, lean_object* v_m_2071_, lean_object* v_l_2072_){
_start:
{
lean_object* v_buckets_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; uint8_t v___x_2076_; 
v_buckets_2073_ = lean_ctor_get(v_m_2071_, 1);
v___x_2074_ = lean_unsigned_to_nat(0u);
v___x_2075_ = lean_array_get_size(v_buckets_2073_);
v___x_2076_ = lean_nat_dec_lt(v___x_2074_, v___x_2075_);
if (v___x_2076_ == 0)
{
lean_dec(v_l_2072_);
lean_dec(v_inst_2070_);
lean_dec_ref(v_inst_2069_);
lean_dec_ref(v_inst_2068_);
return v_m_2071_;
}
else
{
lean_object* v___x_2077_; 
v___x_2077_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v_inst_2070_, v_inst_2068_, v_inst_2069_, v_m_2071_, v_l_2072_);
return v___x_2077_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertMany(lean_object* v_00_u03b1_2078_, lean_object* v_00_u03b2_2079_, lean_object* v_inst_2080_, lean_object* v_inst_2081_, lean_object* v_00_u03c1_2082_, lean_object* v_inst_2083_, lean_object* v_m_2084_, lean_object* v_l_2085_){
_start:
{
lean_object* v_buckets_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; uint8_t v___x_2089_; 
v_buckets_2086_ = lean_ctor_get(v_m_2084_, 1);
v___x_2087_ = lean_unsigned_to_nat(0u);
v___x_2088_ = lean_array_get_size(v_buckets_2086_);
v___x_2089_ = lean_nat_dec_lt(v___x_2087_, v___x_2088_);
if (v___x_2089_ == 0)
{
lean_dec(v_l_2085_);
lean_dec(v_inst_2083_);
lean_dec_ref(v_inst_2081_);
lean_dec_ref(v_inst_2080_);
return v_m_2084_;
}
else
{
lean_object* v___x_2090_; 
v___x_2090_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v_inst_2083_, v_inst_2080_, v_inst_2081_, v_m_2084_, v_l_2085_);
return v___x_2090_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertManyIfNewUnit___redArg(lean_object* v_inst_2091_, lean_object* v_inst_2092_, lean_object* v_inst_2093_, lean_object* v_m_2094_, lean_object* v_l_2095_){
_start:
{
lean_object* v_buckets_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; uint8_t v___x_2099_; 
v_buckets_2096_ = lean_ctor_get(v_m_2094_, 1);
v___x_2097_ = lean_unsigned_to_nat(0u);
v___x_2098_ = lean_array_get_size(v_buckets_2096_);
v___x_2099_ = lean_nat_dec_lt(v___x_2097_, v___x_2098_);
if (v___x_2099_ == 0)
{
lean_dec(v_l_2095_);
lean_dec(v_inst_2093_);
lean_dec_ref(v_inst_2092_);
lean_dec_ref(v_inst_2091_);
return v_m_2094_;
}
else
{
lean_object* v___x_2100_; 
v___x_2100_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_2093_, v_inst_2091_, v_inst_2092_, v_m_2094_, v_l_2095_);
return v___x_2100_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertManyIfNewUnit(lean_object* v_00_u03b1_2101_, lean_object* v_inst_2102_, lean_object* v_inst_2103_, lean_object* v_00_u03c1_2104_, lean_object* v_inst_2105_, lean_object* v_m_2106_, lean_object* v_l_2107_){
_start:
{
lean_object* v_buckets_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; uint8_t v___x_2111_; 
v_buckets_2108_ = lean_ctor_get(v_m_2106_, 1);
v___x_2109_ = lean_unsigned_to_nat(0u);
v___x_2110_ = lean_array_get_size(v_buckets_2108_);
v___x_2111_ = lean_nat_dec_lt(v___x_2109_, v___x_2110_);
if (v___x_2111_ == 0)
{
lean_dec(v_l_2107_);
lean_dec(v_inst_2105_);
lean_dec_ref(v_inst_2103_);
lean_dec_ref(v_inst_2102_);
return v_m_2106_;
}
else
{
lean_object* v___x_2112_; 
v___x_2112_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_2105_, v_inst_2102_, v_inst_2103_, v_m_2106_, v_l_2107_);
return v___x_2112_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_unitOfArray___redArg(lean_object* v_inst_2113_, lean_object* v_inst_2114_, lean_object* v_l_2115_){
_start:
{
lean_object* v___x_2116_; uint8_t v___x_2117_; 
v___x_2116_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1);
v___x_2117_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2117_ == 0)
{
lean_dec_ref(v_l_2115_);
lean_dec_ref(v_inst_2114_);
lean_dec_ref(v_inst_2113_);
return v___x_2116_;
}
else
{
lean_object* v___f_2118_; lean_object* v___x_2119_; 
v___f_2118_ = ((lean_object*)(l_Std_HashMap_Raw_ofArray___redArg___closed__1));
v___x_2119_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2118_, v_inst_2113_, v_inst_2114_, v___x_2116_, v_l_2115_);
return v___x_2119_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_unitOfArray(lean_object* v_00_u03b1_2120_, lean_object* v_inst_2121_, lean_object* v_inst_2122_, lean_object* v_l_2123_){
_start:
{
lean_object* v___x_2124_; uint8_t v___x_2125_; 
v___x_2124_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1);
v___x_2125_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2125_ == 0)
{
lean_dec_ref(v_l_2123_);
lean_dec_ref(v_inst_2122_);
lean_dec_ref(v_inst_2121_);
return v___x_2124_;
}
else
{
lean_object* v___f_2126_; lean_object* v___x_2127_; 
v___f_2126_ = ((lean_object*)(l_Std_HashMap_Raw_ofArray___redArg___closed__1));
v___x_2127_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2126_, v_inst_2121_, v_inst_2122_, v___x_2124_, v_l_2123_);
return v___x_2127_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_Internal_numBuckets___redArg(lean_object* v_m_2128_){
_start:
{
lean_object* v___x_2129_; 
v___x_2129_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2128_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_Internal_numBuckets___redArg___boxed(lean_object* v_m_2130_){
_start:
{
lean_object* v_res_2131_; 
v_res_2131_ = l_Std_HashMap_Raw_Internal_numBuckets___redArg(v_m_2130_);
lean_dec_ref(v_m_2130_);
return v_res_2131_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_Internal_numBuckets(lean_object* v_00_u03b1_2132_, lean_object* v_00_u03b2_2133_, lean_object* v_m_2134_){
_start:
{
lean_object* v___x_2135_; 
v___x_2135_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2134_);
return v___x_2135_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_Internal_numBuckets___boxed(lean_object* v_00_u03b1_2136_, lean_object* v_00_u03b2_2137_, lean_object* v_m_2138_){
_start:
{
lean_object* v_res_2139_; 
v_res_2139_ = l_Std_HashMap_Raw_Internal_numBuckets(v_00_u03b1_2136_, v_00_u03b2_2137_, v_m_2138_);
lean_dec_ref(v_m_2138_);
return v_res_2139_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr___redArg___lam__2(lean_object* v___x_2143_, lean_object* v___f_2144_, lean_object* v_m_2145_, lean_object* v_prec_2146_){
_start:
{
lean_object* v___x_2147_; lean_object* v_buckets_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2168_; 
v___x_2147_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_2148_ = lean_ctor_get(v_m_2145_, 1);
v_isSharedCheck_2168_ = !lean_is_exclusive(v_m_2145_);
if (v_isSharedCheck_2168_ == 0)
{
lean_object* v_unused_2169_; 
v_unused_2169_ = lean_ctor_get(v_m_2145_, 0);
lean_dec(v_unused_2169_);
v___x_2150_ = v_m_2145_;
v_isShared_2151_ = v_isSharedCheck_2168_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_buckets_2148_);
lean_dec(v_m_2145_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2168_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2152_; lean_object* v___y_2154_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; uint8_t v___x_2163_; 
v___x_2152_ = ((lean_object*)(l_Std_HashMap_Raw_instRepr___redArg___lam__2___closed__1));
v___x_2160_ = lean_box(0);
v___x_2161_ = lean_array_get_size(v_buckets_2148_);
v___x_2162_ = lean_unsigned_to_nat(0u);
v___x_2163_ = lean_nat_dec_lt(v___x_2162_, v___x_2161_);
if (v___x_2163_ == 0)
{
lean_dec_ref(v_buckets_2148_);
lean_dec_ref(v___f_2144_);
v___y_2154_ = v___x_2160_;
goto v___jp_2153_;
}
else
{
lean_object* v___f_2164_; size_t v___x_2165_; size_t v___x_2166_; lean_object* v___x_2167_; 
v___f_2164_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_toList___redArg___lam__1), 4, 2);
lean_closure_set(v___f_2164_, 0, v___x_2147_);
lean_closure_set(v___f_2164_, 1, v___f_2144_);
v___x_2165_ = lean_usize_of_nat(v___x_2161_);
v___x_2166_ = ((size_t)0ULL);
v___x_2167_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2147_, v___f_2164_, v_buckets_2148_, v___x_2165_, v___x_2166_, v___x_2160_);
v___y_2154_ = v___x_2167_;
goto v___jp_2153_;
}
v___jp_2153_:
{
lean_object* v___x_2155_; lean_object* v___x_2157_; 
v___x_2155_ = l_List_repr___redArg(v___x_2143_, v___y_2154_);
if (v_isShared_2151_ == 0)
{
lean_ctor_set_tag(v___x_2150_, 5);
lean_ctor_set(v___x_2150_, 1, v___x_2155_);
lean_ctor_set(v___x_2150_, 0, v___x_2152_);
v___x_2157_ = v___x_2150_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v___x_2152_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v___x_2155_);
v___x_2157_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
lean_object* v___x_2158_; 
v___x_2158_ = l_Repr_addAppParen(v___x_2157_, v_prec_2146_);
return v___x_2158_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr___redArg___lam__2___boxed(lean_object* v___x_2170_, lean_object* v___f_2171_, lean_object* v_m_2172_, lean_object* v_prec_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l_Std_HashMap_Raw_instRepr___redArg___lam__2(v___x_2170_, v___f_2171_, v_m_2172_, v_prec_2173_);
lean_dec(v_prec_2173_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr___redArg(lean_object* v_inst_2175_, lean_object* v_inst_2176_){
_start:
{
lean_object* v___f_2177_; lean_object* v___f_2178_; lean_object* v___x_2179_; lean_object* v___f_2180_; 
v___f_2177_ = ((lean_object*)(l_Std_HashMap_Raw_toList___redArg___closed__0));
v___f_2178_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2178_, 0, v_inst_2176_);
v___x_2179_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_2179_, 0, lean_box(0));
lean_closure_set(v___x_2179_, 1, lean_box(0));
lean_closure_set(v___x_2179_, 2, v_inst_2175_);
lean_closure_set(v___x_2179_, 3, v___f_2178_);
v___f_2180_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instRepr___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2180_, 0, v___x_2179_);
lean_closure_set(v___f_2180_, 1, v___f_2177_);
return v___f_2180_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr(lean_object* v_00_u03b1_2181_, lean_object* v_00_u03b2_2182_, lean_object* v_inst_2183_, lean_object* v_inst_2184_){
_start:
{
lean_object* v___x_2185_; 
v___x_2185_ = l_Std_HashMap_Raw_instRepr___redArg(v_inst_2183_, v_inst_2184_);
return v___x_2185_;
}
}
lean_object* runtime_initialize_Std_Data_DHashMap_Raw(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_HashMap_Raw(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Data_DHashMap_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_HashMap_Raw(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_DHashMap_Raw(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_HashMap_Raw(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_DHashMap_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashMap_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_HashMap_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_HashMap_Raw(builtin);
}
#ifdef __cplusplus
}
#endif
