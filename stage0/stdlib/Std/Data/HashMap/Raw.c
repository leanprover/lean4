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
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instEmptyCollection___redArg___boxed(lean_object* v___dummy_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Std_HashMap_Raw_instEmptyCollection___redArg();
return v_res_38_;
}
}
static lean_object* _init_l_Std_HashMap_Raw_instEmptyCollection___closed__0(void){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Std_HashMap_Raw_instEmptyCollection___redArg();
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instEmptyCollection(lean_object* v_00_u03b1_40_, lean_object* v_00_u03b2_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__0, &l_Std_HashMap_Raw_instEmptyCollection___closed__0_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__0);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInhabited___redArg(){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInhabited___redArg___boxed(lean_object* v___dummy_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Std_HashMap_Raw_instInhabited___redArg();
return v_res_46_;
}
}
static lean_object* _init_l_Std_HashMap_Raw_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Std_HashMap_Raw_instInhabited___redArg();
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInhabited(lean_object* v_00_u03b1_48_, lean_object* v_00_u03b2_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = lean_obj_once(&l_Std_HashMap_Raw_instInhabited___closed__0, &l_Std_HashMap_Raw_instInhabited___closed__0_once, _init_l_Std_HashMap_Raw_instInhabited___closed__0);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_markLinear___redArg(lean_object* v_m_51_){
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
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_markLinear(lean_object* v_00_u03b1_62_, lean_object* v_00_u03b2_63_, lean_object* v_m_64_){
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
static lean_object* _init_l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__6(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = ((lean_object*)(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__5));
v___x_116_ = l_String_toRawSubstring_x27(v___x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1(lean_object* v_x_138_, lean_object* v_a_139_, lean_object* v_a_140_){
_start:
{
lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_141_ = ((lean_object*)(l_Std_HashMap_Raw_term___x7em___00__closed__4));
lean_inc(v_x_138_);
v___x_142_ = l_Lean_Syntax_isOfKind(v_x_138_, v___x_141_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; lean_object* v___x_144_; 
lean_dec(v_x_138_);
v___x_143_ = lean_box(1);
v___x_144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
lean_ctor_set(v___x_144_, 1, v_a_140_);
return v___x_144_;
}
else
{
lean_object* v_quotContext_145_; lean_object* v_currMacroScope_146_; lean_object* v_ref_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; uint8_t v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v_quotContext_145_ = lean_ctor_get(v_a_139_, 1);
v_currMacroScope_146_ = lean_ctor_get(v_a_139_, 2);
v_ref_147_ = lean_ctor_get(v_a_139_, 5);
v___x_148_ = lean_unsigned_to_nat(0u);
v___x_149_ = l_Lean_Syntax_getArg(v_x_138_, v___x_148_);
v___x_150_ = lean_unsigned_to_nat(2u);
v___x_151_ = l_Lean_Syntax_getArg(v_x_138_, v___x_150_);
lean_dec(v_x_138_);
v___x_152_ = 0;
v___x_153_ = l_Lean_SourceInfo_fromRef(v_ref_147_, v___x_152_);
v___x_154_ = ((lean_object*)(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4));
v___x_155_ = lean_obj_once(&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__6, &l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__6_once, _init_l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__6);
v___x_156_ = ((lean_object*)(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__7));
lean_inc(v_currMacroScope_146_);
lean_inc(v_quotContext_145_);
v___x_157_ = l_Lean_addMacroScope(v_quotContext_145_, v___x_156_, v_currMacroScope_146_);
v___x_158_ = ((lean_object*)(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__12));
lean_inc_n(v___x_153_, 2);
v___x_159_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_159_, 0, v___x_153_);
lean_ctor_set(v___x_159_, 1, v___x_155_);
lean_ctor_set(v___x_159_, 2, v___x_157_);
lean_ctor_set(v___x_159_, 3, v___x_158_);
v___x_160_ = ((lean_object*)(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__14));
v___x_161_ = l_Lean_Syntax_node2(v___x_153_, v___x_160_, v___x_149_, v___x_151_);
v___x_162_ = l_Lean_Syntax_node2(v___x_153_, v___x_154_, v___x_159_, v___x_161_);
v___x_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
lean_ctor_set(v___x_163_, 1, v_a_140_);
return v___x_163_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___boxed(lean_object* v_x_164_, lean_object* v_a_165_, lean_object* v_a_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1(v_x_164_, v_a_165_, v_a_166_);
lean_dec_ref(v_a_165_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1(lean_object* v_x_171_, lean_object* v_a_172_, lean_object* v_a_173_){
_start:
{
lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_174_ = ((lean_object*)(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4));
lean_inc(v_x_171_);
v___x_175_ = l_Lean_Syntax_isOfKind(v_x_171_, v___x_174_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; lean_object* v___x_177_; 
lean_dec(v_x_171_);
v___x_176_ = lean_box(0);
v___x_177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
lean_ctor_set(v___x_177_, 1, v_a_173_);
return v___x_177_;
}
else
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; uint8_t v___x_181_; 
v___x_178_ = lean_unsigned_to_nat(0u);
v___x_179_ = l_Lean_Syntax_getArg(v_x_171_, v___x_178_);
v___x_180_ = ((lean_object*)(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___closed__1));
lean_inc(v___x_179_);
v___x_181_ = l_Lean_Syntax_isOfKind(v___x_179_, v___x_180_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; lean_object* v___x_183_; 
lean_dec(v___x_179_);
lean_dec(v_x_171_);
v___x_182_ = lean_box(0);
v___x_183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
lean_ctor_set(v___x_183_, 1, v_a_173_);
return v___x_183_;
}
else
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_184_ = lean_unsigned_to_nat(1u);
v___x_185_ = l_Lean_Syntax_getArg(v_x_171_, v___x_184_);
lean_dec(v_x_171_);
v___x_186_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_185_);
v___x_187_ = l_Lean_Syntax_matchesNull(v___x_185_, v___x_186_);
if (v___x_187_ == 0)
{
lean_object* v___x_188_; lean_object* v___x_189_; 
lean_dec(v___x_185_);
lean_dec(v___x_179_);
v___x_188_ = lean_box(0);
v___x_189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
lean_ctor_set(v___x_189_, 1, v_a_173_);
return v___x_189_;
}
else
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v_ref_192_; uint8_t v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_190_ = l_Lean_Syntax_getArg(v___x_185_, v___x_178_);
v___x_191_ = l_Lean_Syntax_getArg(v___x_185_, v___x_184_);
lean_dec(v___x_185_);
v_ref_192_ = l_Lean_replaceRef(v___x_179_, v_a_172_);
lean_dec(v___x_179_);
v___x_193_ = 0;
v___x_194_ = l_Lean_SourceInfo_fromRef(v_ref_192_, v___x_193_);
lean_dec(v_ref_192_);
v___x_195_ = ((lean_object*)(l_Std_HashMap_Raw_term___x7em___00__closed__4));
v___x_196_ = ((lean_object*)(l_Std_HashMap_Raw_term___x7em___00__closed__7));
lean_inc(v___x_194_);
v___x_197_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_197_, 0, v___x_194_);
lean_ctor_set(v___x_197_, 1, v___x_196_);
v___x_198_ = l_Lean_Syntax_node3(v___x_194_, v___x_195_, v___x_190_, v___x_197_, v___x_191_);
v___x_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
lean_ctor_set(v___x_199_, 1, v_a_173_);
return v___x_199_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___boxed(lean_object* v_x_200_, lean_object* v_a_201_, lean_object* v_a_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1(v_x_200_, v_a_201_, v_a_202_);
lean_dec(v_a_201_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insert___redArg(lean_object* v_beq_204_, lean_object* v_inst_205_, lean_object* v_m_206_, lean_object* v_a_207_, lean_object* v_b_208_){
_start:
{
lean_object* v_buckets_209_; lean_object* v___x_210_; lean_object* v___x_211_; uint8_t v___x_212_; 
v_buckets_209_ = lean_ctor_get(v_m_206_, 1);
v___x_210_ = lean_unsigned_to_nat(0u);
v___x_211_ = lean_array_get_size(v_buckets_209_);
v___x_212_ = lean_nat_dec_lt(v___x_210_, v___x_211_);
if (v___x_212_ == 0)
{
lean_dec(v_b_208_);
lean_dec(v_a_207_);
lean_dec_ref(v_inst_205_);
lean_dec_ref(v_beq_204_);
return v_m_206_;
}
else
{
lean_object* v___x_213_; 
v___x_213_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_beq_204_, v_inst_205_, v_m_206_, v_a_207_, v_b_208_);
return v___x_213_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insert(lean_object* v_00_u03b1_214_, lean_object* v_00_u03b2_215_, lean_object* v_beq_216_, lean_object* v_inst_217_, lean_object* v_m_218_, lean_object* v_a_219_, lean_object* v_b_220_){
_start:
{
lean_object* v_buckets_221_; lean_object* v___x_222_; lean_object* v___x_223_; uint8_t v___x_224_; 
v_buckets_221_ = lean_ctor_get(v_m_218_, 1);
v___x_222_ = lean_unsigned_to_nat(0u);
v___x_223_ = lean_array_get_size(v_buckets_221_);
v___x_224_ = lean_nat_dec_lt(v___x_222_, v___x_223_);
if (v___x_224_ == 0)
{
lean_dec(v_b_220_);
lean_dec(v_a_219_);
lean_dec_ref(v_inst_217_);
lean_dec_ref(v_beq_216_);
return v_m_218_;
}
else
{
lean_object* v___x_225_; 
v___x_225_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_beq_216_, v_inst_217_, v_m_218_, v_a_219_, v_b_220_);
return v___x_225_;
}
}
}
static lean_object* _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__0, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__0_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__0);
v___x_227_ = lean_array_get_size(v___x_226_);
return v___x_227_;
}
}
static uint8_t _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; uint8_t v___x_230_; 
v___x_228_ = lean_obj_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0);
v___x_229_ = lean_unsigned_to_nat(0u);
v___x_230_ = lean_nat_dec_lt(v___x_229_, v___x_228_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0(lean_object* v_inst_231_, lean_object* v_inst_232_, lean_object* v_x_233_){
_start:
{
lean_object* v_fst_234_; lean_object* v_snd_235_; lean_object* v___x_236_; uint8_t v___x_237_; 
v_fst_234_ = lean_ctor_get(v_x_233_, 0);
lean_inc(v_fst_234_);
v_snd_235_ = lean_ctor_get(v_x_233_, 1);
lean_inc(v_snd_235_);
lean_dec_ref(v_x_233_);
v___x_236_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1);
v___x_237_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_237_ == 0)
{
lean_dec(v_snd_235_);
lean_dec(v_fst_234_);
lean_dec_ref(v_inst_232_);
lean_dec_ref(v_inst_231_);
return v___x_236_;
}
else
{
lean_object* v___x_238_; 
v___x_238_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_231_, v_inst_232_, v___x_236_, v_fst_234_, v_snd_235_);
return v___x_238_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg(lean_object* v_inst_239_, lean_object* v_inst_240_){
_start:
{
lean_object* v___f_241_; 
v___f_241_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_241_, 0, v_inst_239_);
lean_closure_set(v___f_241_, 1, v_inst_240_);
return v___f_241_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable(lean_object* v_00_u03b1_242_, lean_object* v_00_u03b2_243_, lean_object* v_inst_244_, lean_object* v_inst_245_){
_start:
{
lean_object* v___f_246_; 
v___f_246_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_246_, 0, v_inst_244_);
lean_closure_set(v___f_246_, 1, v_inst_245_);
return v___f_246_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable___redArg___lam__0(lean_object* v_inst_247_, lean_object* v_inst_248_, lean_object* v_x_249_, lean_object* v_s_250_){
_start:
{
lean_object* v_fst_251_; lean_object* v_snd_252_; lean_object* v_buckets_253_; lean_object* v___x_254_; lean_object* v___x_255_; uint8_t v___x_256_; 
v_fst_251_ = lean_ctor_get(v_x_249_, 0);
lean_inc(v_fst_251_);
v_snd_252_ = lean_ctor_get(v_x_249_, 1);
lean_inc(v_snd_252_);
lean_dec_ref(v_x_249_);
v_buckets_253_ = lean_ctor_get(v_s_250_, 1);
v___x_254_ = lean_unsigned_to_nat(0u);
v___x_255_ = lean_array_get_size(v_buckets_253_);
v___x_256_ = lean_nat_dec_lt(v___x_254_, v___x_255_);
if (v___x_256_ == 0)
{
lean_dec(v_snd_252_);
lean_dec(v_fst_251_);
lean_dec_ref(v_inst_248_);
lean_dec_ref(v_inst_247_);
return v_s_250_;
}
else
{
lean_object* v___x_257_; 
v___x_257_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_247_, v_inst_248_, v_s_250_, v_fst_251_, v_snd_252_);
return v___x_257_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable___redArg(lean_object* v_inst_258_, lean_object* v_inst_259_){
_start:
{
lean_object* v___f_260_; 
v___f_260_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_260_, 0, v_inst_258_);
lean_closure_set(v___f_260_, 1, v_inst_259_);
return v___f_260_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable(lean_object* v_00_u03b1_261_, lean_object* v_00_u03b2_262_, lean_object* v_inst_263_, lean_object* v_inst_264_){
_start:
{
lean_object* v___f_265_; 
v___f_265_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_265_, 0, v_inst_263_);
lean_closure_set(v___f_265_, 1, v_inst_264_);
return v___f_265_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertIfNew___redArg(lean_object* v_inst_266_, lean_object* v_inst_267_, lean_object* v_m_268_, lean_object* v_a_269_, lean_object* v_b_270_){
_start:
{
lean_object* v_buckets_271_; lean_object* v___x_272_; lean_object* v___x_273_; uint8_t v___x_274_; 
v_buckets_271_ = lean_ctor_get(v_m_268_, 1);
v___x_272_ = lean_unsigned_to_nat(0u);
v___x_273_ = lean_array_get_size(v_buckets_271_);
v___x_274_ = lean_nat_dec_lt(v___x_272_, v___x_273_);
if (v___x_274_ == 0)
{
lean_dec(v_b_270_);
lean_dec(v_a_269_);
lean_dec_ref(v_inst_267_);
lean_dec_ref(v_inst_266_);
return v_m_268_;
}
else
{
lean_object* v___x_275_; 
v___x_275_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_266_, v_inst_267_, v_m_268_, v_a_269_, v_b_270_);
return v___x_275_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertIfNew(lean_object* v_00_u03b1_276_, lean_object* v_00_u03b2_277_, lean_object* v_inst_278_, lean_object* v_inst_279_, lean_object* v_m_280_, lean_object* v_a_281_, lean_object* v_b_282_){
_start:
{
lean_object* v_buckets_283_; lean_object* v___x_284_; lean_object* v___x_285_; uint8_t v___x_286_; 
v_buckets_283_ = lean_ctor_get(v_m_280_, 1);
v___x_284_ = lean_unsigned_to_nat(0u);
v___x_285_ = lean_array_get_size(v_buckets_283_);
v___x_286_ = lean_nat_dec_lt(v___x_284_, v___x_285_);
if (v___x_286_ == 0)
{
lean_dec(v_b_282_);
lean_dec(v_a_281_);
lean_dec_ref(v_inst_279_);
lean_dec_ref(v_inst_278_);
return v_m_280_;
}
else
{
lean_object* v___x_287_; 
v___x_287_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_278_, v_inst_279_, v_m_280_, v_a_281_, v_b_282_);
return v___x_287_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_containsThenInsert___redArg(lean_object* v_inst_288_, lean_object* v_inst_289_, lean_object* v_m_290_, lean_object* v_a_291_, lean_object* v_b_292_){
_start:
{
lean_object* v_size_293_; lean_object* v_buckets_294_; lean_object* v___x_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v_size_293_ = lean_ctor_get(v_m_290_, 0);
v_buckets_294_ = lean_ctor_get(v_m_290_, 1);
v___x_295_ = lean_unsigned_to_nat(0u);
v___x_296_ = lean_array_get_size(v_buckets_294_);
v___x_297_ = lean_nat_dec_lt(v___x_295_, v___x_296_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; lean_object* v___x_299_; 
lean_dec(v_b_292_);
lean_dec(v_a_291_);
lean_dec_ref(v_inst_289_);
lean_dec_ref(v_inst_288_);
v___x_298_ = lean_box(v___x_297_);
v___x_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
lean_ctor_set(v___x_299_, 1, v_m_290_);
return v___x_299_;
}
else
{
lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_349_; 
lean_inc_ref(v_buckets_294_);
lean_inc(v_size_293_);
v_isSharedCheck_349_ = !lean_is_exclusive(v_m_290_);
if (v_isSharedCheck_349_ == 0)
{
lean_object* v_unused_350_; lean_object* v_unused_351_; 
v_unused_350_ = lean_ctor_get(v_m_290_, 1);
lean_dec(v_unused_350_);
v_unused_351_ = lean_ctor_get(v_m_290_, 0);
lean_dec(v_unused_351_);
v___x_301_ = v_m_290_;
v_isShared_302_ = v_isSharedCheck_349_;
goto v_resetjp_300_;
}
else
{
lean_dec(v_m_290_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_349_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_303_; uint64_t v___x_304_; uint64_t v___x_305_; uint64_t v___x_306_; uint64_t v___x_307_; uint64_t v_fold_308_; uint64_t v___x_309_; uint64_t v___x_310_; uint64_t v___x_311_; size_t v___x_312_; size_t v___x_313_; size_t v___x_314_; size_t v___x_315_; size_t v___x_316_; lean_object* v_bkt_317_; uint8_t v___x_318_; 
lean_inc_ref(v_inst_289_);
lean_inc_n(v_a_291_, 2);
v___x_303_ = lean_apply_1(v_inst_289_, v_a_291_);
v___x_304_ = 32ULL;
v___x_305_ = lean_unbox_uint64(v___x_303_);
v___x_306_ = lean_uint64_shift_right(v___x_305_, v___x_304_);
v___x_307_ = lean_unbox_uint64(v___x_303_);
lean_dec_ref(v___x_303_);
v_fold_308_ = lean_uint64_xor(v___x_307_, v___x_306_);
v___x_309_ = 16ULL;
v___x_310_ = lean_uint64_shift_right(v_fold_308_, v___x_309_);
v___x_311_ = lean_uint64_xor(v_fold_308_, v___x_310_);
v___x_312_ = lean_uint64_to_usize(v___x_311_);
v___x_313_ = lean_usize_of_nat(v___x_296_);
v___x_314_ = ((size_t)1ULL);
v___x_315_ = lean_usize_sub(v___x_313_, v___x_314_);
v___x_316_ = lean_usize_land(v___x_312_, v___x_315_);
v_bkt_317_ = lean_array_uget_borrowed(v_buckets_294_, v___x_316_);
lean_inc(v_bkt_317_);
lean_inc_ref(v_inst_288_);
v___x_318_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_288_, v_a_291_, v_bkt_317_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; lean_object* v_size_x27_320_; lean_object* v___x_321_; lean_object* v_buckets_x27_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; uint8_t v___x_328_; 
lean_dec_ref(v_inst_288_);
v___x_319_ = lean_unsigned_to_nat(1u);
v_size_x27_320_ = lean_nat_add(v_size_293_, v___x_319_);
lean_dec(v_size_293_);
lean_inc(v_bkt_317_);
v___x_321_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_321_, 0, v_a_291_);
lean_ctor_set(v___x_321_, 1, v_b_292_);
lean_ctor_set(v___x_321_, 2, v_bkt_317_);
v_buckets_x27_322_ = lean_array_uset(v_buckets_294_, v___x_316_, v___x_321_);
v___x_323_ = lean_unsigned_to_nat(4u);
v___x_324_ = lean_nat_mul(v_size_x27_320_, v___x_323_);
v___x_325_ = lean_unsigned_to_nat(3u);
v___x_326_ = lean_nat_div(v___x_324_, v___x_325_);
lean_dec(v___x_324_);
v___x_327_ = lean_array_get_size(v_buckets_x27_322_);
v___x_328_ = lean_nat_dec_le(v___x_326_, v___x_327_);
lean_dec(v___x_326_);
if (v___x_328_ == 0)
{
lean_object* v_val_329_; lean_object* v___x_331_; 
v_val_329_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_289_, v_buckets_x27_322_);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 1, v_val_329_);
lean_ctor_set(v___x_301_, 0, v_size_x27_320_);
v___x_331_ = v___x_301_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_size_x27_320_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_val_329_);
v___x_331_ = v_reuseFailAlloc_334_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = lean_box(v___x_318_);
v___x_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v___x_331_);
return v___x_333_;
}
}
else
{
lean_object* v___x_336_; 
lean_dec_ref(v_inst_289_);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 1, v_buckets_x27_322_);
lean_ctor_set(v___x_301_, 0, v_size_x27_320_);
v___x_336_ = v___x_301_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_size_x27_320_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v_buckets_x27_322_);
v___x_336_ = v_reuseFailAlloc_339_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_box(v___x_318_);
v___x_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
lean_ctor_set(v___x_338_, 1, v___x_336_);
return v___x_338_;
}
}
}
else
{
lean_object* v___x_340_; lean_object* v_buckets_x27_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_345_; 
lean_inc(v_bkt_317_);
lean_dec_ref(v_inst_289_);
v___x_340_ = lean_box(0);
v_buckets_x27_341_ = lean_array_uset(v_buckets_294_, v___x_316_, v___x_340_);
v___x_342_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_inst_288_, v_a_291_, v_b_292_, v_bkt_317_);
v___x_343_ = lean_array_uset(v_buckets_x27_341_, v___x_316_, v___x_342_);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 1, v___x_343_);
v___x_345_ = v___x_301_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_size_293_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v___x_343_);
v___x_345_ = v_reuseFailAlloc_348_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = lean_box(v___x_318_);
v___x_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
lean_ctor_set(v___x_347_, 1, v___x_345_);
return v___x_347_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_containsThenInsert(lean_object* v_00_u03b1_352_, lean_object* v_00_u03b2_353_, lean_object* v_inst_354_, lean_object* v_inst_355_, lean_object* v_m_356_, lean_object* v_a_357_, lean_object* v_b_358_){
_start:
{
lean_object* v_size_359_; lean_object* v_buckets_360_; lean_object* v___x_361_; lean_object* v___x_362_; uint8_t v___x_363_; 
v_size_359_ = lean_ctor_get(v_m_356_, 0);
v_buckets_360_ = lean_ctor_get(v_m_356_, 1);
v___x_361_ = lean_unsigned_to_nat(0u);
v___x_362_ = lean_array_get_size(v_buckets_360_);
v___x_363_ = lean_nat_dec_lt(v___x_361_, v___x_362_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; lean_object* v___x_365_; 
lean_dec(v_b_358_);
lean_dec(v_a_357_);
lean_dec_ref(v_inst_355_);
lean_dec_ref(v_inst_354_);
v___x_364_ = lean_box(v___x_363_);
v___x_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
lean_ctor_set(v___x_365_, 1, v_m_356_);
return v___x_365_;
}
else
{
lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_415_; 
lean_inc_ref(v_buckets_360_);
lean_inc(v_size_359_);
v_isSharedCheck_415_ = !lean_is_exclusive(v_m_356_);
if (v_isSharedCheck_415_ == 0)
{
lean_object* v_unused_416_; lean_object* v_unused_417_; 
v_unused_416_ = lean_ctor_get(v_m_356_, 1);
lean_dec(v_unused_416_);
v_unused_417_ = lean_ctor_get(v_m_356_, 0);
lean_dec(v_unused_417_);
v___x_367_ = v_m_356_;
v_isShared_368_ = v_isSharedCheck_415_;
goto v_resetjp_366_;
}
else
{
lean_dec(v_m_356_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_415_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_369_; uint64_t v___x_370_; uint64_t v___x_371_; uint64_t v___x_372_; uint64_t v___x_373_; uint64_t v_fold_374_; uint64_t v___x_375_; uint64_t v___x_376_; uint64_t v___x_377_; size_t v___x_378_; size_t v___x_379_; size_t v___x_380_; size_t v___x_381_; size_t v___x_382_; lean_object* v_bkt_383_; uint8_t v___x_384_; 
lean_inc_ref(v_inst_355_);
lean_inc_n(v_a_357_, 2);
v___x_369_ = lean_apply_1(v_inst_355_, v_a_357_);
v___x_370_ = 32ULL;
v___x_371_ = lean_unbox_uint64(v___x_369_);
v___x_372_ = lean_uint64_shift_right(v___x_371_, v___x_370_);
v___x_373_ = lean_unbox_uint64(v___x_369_);
lean_dec_ref(v___x_369_);
v_fold_374_ = lean_uint64_xor(v___x_373_, v___x_372_);
v___x_375_ = 16ULL;
v___x_376_ = lean_uint64_shift_right(v_fold_374_, v___x_375_);
v___x_377_ = lean_uint64_xor(v_fold_374_, v___x_376_);
v___x_378_ = lean_uint64_to_usize(v___x_377_);
v___x_379_ = lean_usize_of_nat(v___x_362_);
v___x_380_ = ((size_t)1ULL);
v___x_381_ = lean_usize_sub(v___x_379_, v___x_380_);
v___x_382_ = lean_usize_land(v___x_378_, v___x_381_);
v_bkt_383_ = lean_array_uget_borrowed(v_buckets_360_, v___x_382_);
lean_inc(v_bkt_383_);
lean_inc_ref(v_inst_354_);
v___x_384_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_354_, v_a_357_, v_bkt_383_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; lean_object* v_size_x27_386_; lean_object* v___x_387_; lean_object* v_buckets_x27_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; uint8_t v___x_394_; 
lean_dec_ref(v_inst_354_);
v___x_385_ = lean_unsigned_to_nat(1u);
v_size_x27_386_ = lean_nat_add(v_size_359_, v___x_385_);
lean_dec(v_size_359_);
lean_inc(v_bkt_383_);
v___x_387_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_387_, 0, v_a_357_);
lean_ctor_set(v___x_387_, 1, v_b_358_);
lean_ctor_set(v___x_387_, 2, v_bkt_383_);
v_buckets_x27_388_ = lean_array_uset(v_buckets_360_, v___x_382_, v___x_387_);
v___x_389_ = lean_unsigned_to_nat(4u);
v___x_390_ = lean_nat_mul(v_size_x27_386_, v___x_389_);
v___x_391_ = lean_unsigned_to_nat(3u);
v___x_392_ = lean_nat_div(v___x_390_, v___x_391_);
lean_dec(v___x_390_);
v___x_393_ = lean_array_get_size(v_buckets_x27_388_);
v___x_394_ = lean_nat_dec_le(v___x_392_, v___x_393_);
lean_dec(v___x_392_);
if (v___x_394_ == 0)
{
lean_object* v_val_395_; lean_object* v___x_397_; 
v_val_395_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_355_, v_buckets_x27_388_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 1, v_val_395_);
lean_ctor_set(v___x_367_, 0, v_size_x27_386_);
v___x_397_ = v___x_367_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_size_x27_386_);
lean_ctor_set(v_reuseFailAlloc_400_, 1, v_val_395_);
v___x_397_ = v_reuseFailAlloc_400_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = lean_box(v___x_384_);
v___x_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
lean_ctor_set(v___x_399_, 1, v___x_397_);
return v___x_399_;
}
}
else
{
lean_object* v___x_402_; 
lean_dec_ref(v_inst_355_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 1, v_buckets_x27_388_);
lean_ctor_set(v___x_367_, 0, v_size_x27_386_);
v___x_402_ = v___x_367_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_size_x27_386_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_buckets_x27_388_);
v___x_402_ = v_reuseFailAlloc_405_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = lean_box(v___x_384_);
v___x_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
lean_ctor_set(v___x_404_, 1, v___x_402_);
return v___x_404_;
}
}
}
else
{
lean_object* v___x_406_; lean_object* v_buckets_x27_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_411_; 
lean_inc(v_bkt_383_);
lean_dec_ref(v_inst_355_);
v___x_406_ = lean_box(0);
v_buckets_x27_407_ = lean_array_uset(v_buckets_360_, v___x_382_, v___x_406_);
v___x_408_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_inst_354_, v_a_357_, v_b_358_, v_bkt_383_);
v___x_409_ = lean_array_uset(v_buckets_x27_407_, v___x_382_, v___x_408_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 1, v___x_409_);
v___x_411_ = v___x_367_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_size_359_);
lean_ctor_set(v_reuseFailAlloc_414_, 1, v___x_409_);
v___x_411_ = v_reuseFailAlloc_414_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = lean_box(v___x_384_);
v___x_413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
lean_ctor_set(v___x_413_, 1, v___x_411_);
return v___x_413_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_containsThenInsertIfNew___redArg(lean_object* v_inst_418_, lean_object* v_inst_419_, lean_object* v_m_420_, lean_object* v_a_421_, lean_object* v_b_422_){
_start:
{
lean_object* v_size_423_; lean_object* v_buckets_424_; lean_object* v___x_425_; lean_object* v___x_426_; uint8_t v___x_427_; 
v_size_423_ = lean_ctor_get(v_m_420_, 0);
v_buckets_424_ = lean_ctor_get(v_m_420_, 1);
v___x_425_ = lean_unsigned_to_nat(0u);
v___x_426_ = lean_array_get_size(v_buckets_424_);
v___x_427_ = lean_nat_dec_lt(v___x_425_, v___x_426_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; lean_object* v___x_429_; 
lean_dec(v_b_422_);
lean_dec(v_a_421_);
lean_dec_ref(v_inst_419_);
lean_dec_ref(v_inst_418_);
v___x_428_ = lean_box(v___x_427_);
v___x_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
lean_ctor_set(v___x_429_, 1, v_m_420_);
return v___x_429_;
}
else
{
lean_object* v___x_430_; uint64_t v___x_431_; uint64_t v___x_432_; uint64_t v___x_433_; uint64_t v___x_434_; uint64_t v_fold_435_; uint64_t v___x_436_; uint64_t v___x_437_; uint64_t v___x_438_; size_t v___x_439_; size_t v___x_440_; size_t v___x_441_; size_t v___x_442_; size_t v___x_443_; lean_object* v_bkt_444_; uint8_t v___x_445_; 
lean_inc_ref(v_inst_419_);
lean_inc_n(v_a_421_, 2);
v___x_430_ = lean_apply_1(v_inst_419_, v_a_421_);
v___x_431_ = 32ULL;
v___x_432_ = lean_unbox_uint64(v___x_430_);
v___x_433_ = lean_uint64_shift_right(v___x_432_, v___x_431_);
v___x_434_ = lean_unbox_uint64(v___x_430_);
lean_dec_ref(v___x_430_);
v_fold_435_ = lean_uint64_xor(v___x_434_, v___x_433_);
v___x_436_ = 16ULL;
v___x_437_ = lean_uint64_shift_right(v_fold_435_, v___x_436_);
v___x_438_ = lean_uint64_xor(v_fold_435_, v___x_437_);
v___x_439_ = lean_uint64_to_usize(v___x_438_);
v___x_440_ = lean_usize_of_nat(v___x_426_);
v___x_441_ = ((size_t)1ULL);
v___x_442_ = lean_usize_sub(v___x_440_, v___x_441_);
v___x_443_ = lean_usize_land(v___x_439_, v___x_442_);
v_bkt_444_ = lean_array_uget_borrowed(v_buckets_424_, v___x_443_);
lean_inc(v_bkt_444_);
v___x_445_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_418_, v_a_421_, v_bkt_444_);
if (v___x_445_ == 0)
{
lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_470_; 
lean_inc_ref(v_buckets_424_);
lean_inc(v_size_423_);
v_isSharedCheck_470_ = !lean_is_exclusive(v_m_420_);
if (v_isSharedCheck_470_ == 0)
{
lean_object* v_unused_471_; lean_object* v_unused_472_; 
v_unused_471_ = lean_ctor_get(v_m_420_, 1);
lean_dec(v_unused_471_);
v_unused_472_ = lean_ctor_get(v_m_420_, 0);
lean_dec(v_unused_472_);
v___x_447_ = v_m_420_;
v_isShared_448_ = v_isSharedCheck_470_;
goto v_resetjp_446_;
}
else
{
lean_dec(v_m_420_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_470_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_449_; lean_object* v_size_x27_450_; lean_object* v___x_451_; lean_object* v_buckets_x27_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_449_ = lean_unsigned_to_nat(1u);
v_size_x27_450_ = lean_nat_add(v_size_423_, v___x_449_);
lean_dec(v_size_423_);
lean_inc(v_bkt_444_);
v___x_451_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_451_, 0, v_a_421_);
lean_ctor_set(v___x_451_, 1, v_b_422_);
lean_ctor_set(v___x_451_, 2, v_bkt_444_);
v_buckets_x27_452_ = lean_array_uset(v_buckets_424_, v___x_443_, v___x_451_);
v___x_453_ = lean_unsigned_to_nat(4u);
v___x_454_ = lean_nat_mul(v_size_x27_450_, v___x_453_);
v___x_455_ = lean_unsigned_to_nat(3u);
v___x_456_ = lean_nat_div(v___x_454_, v___x_455_);
lean_dec(v___x_454_);
v___x_457_ = lean_array_get_size(v_buckets_x27_452_);
v___x_458_ = lean_nat_dec_le(v___x_456_, v___x_457_);
lean_dec(v___x_456_);
if (v___x_458_ == 0)
{
lean_object* v_val_459_; lean_object* v___x_461_; 
v_val_459_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_419_, v_buckets_x27_452_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 1, v_val_459_);
lean_ctor_set(v___x_447_, 0, v_size_x27_450_);
v___x_461_ = v___x_447_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_size_x27_450_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v_val_459_);
v___x_461_ = v_reuseFailAlloc_464_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = lean_box(v___x_445_);
v___x_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
lean_ctor_set(v___x_463_, 1, v___x_461_);
return v___x_463_;
}
}
else
{
lean_object* v___x_466_; 
lean_dec_ref(v_inst_419_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 1, v_buckets_x27_452_);
lean_ctor_set(v___x_447_, 0, v_size_x27_450_);
v___x_466_ = v___x_447_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_size_x27_450_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v_buckets_x27_452_);
v___x_466_ = v_reuseFailAlloc_469_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = lean_box(v___x_445_);
v___x_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
lean_ctor_set(v___x_468_, 1, v___x_466_);
return v___x_468_;
}
}
}
}
else
{
lean_object* v___x_473_; lean_object* v___x_474_; 
lean_dec(v_b_422_);
lean_dec(v_a_421_);
lean_dec_ref(v_inst_419_);
v___x_473_ = lean_box(v___x_445_);
v___x_474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
lean_ctor_set(v___x_474_, 1, v_m_420_);
return v___x_474_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_containsThenInsertIfNew(lean_object* v_00_u03b1_475_, lean_object* v_00_u03b2_476_, lean_object* v_inst_477_, lean_object* v_inst_478_, lean_object* v_m_479_, lean_object* v_a_480_, lean_object* v_b_481_){
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
lean_dec_ref(v_inst_478_);
lean_dec_ref(v_inst_477_);
v___x_487_ = lean_box(v___x_486_);
v___x_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
lean_ctor_set(v___x_488_, 1, v_m_479_);
return v___x_488_;
}
else
{
lean_object* v___x_489_; uint64_t v___x_490_; uint64_t v___x_491_; uint64_t v___x_492_; uint64_t v___x_493_; uint64_t v_fold_494_; uint64_t v___x_495_; uint64_t v___x_496_; uint64_t v___x_497_; size_t v___x_498_; size_t v___x_499_; size_t v___x_500_; size_t v___x_501_; size_t v___x_502_; lean_object* v_bkt_503_; uint8_t v___x_504_; 
lean_inc_ref(v_inst_478_);
lean_inc_n(v_a_480_, 2);
v___x_489_ = lean_apply_1(v_inst_478_, v_a_480_);
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
v___x_504_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_477_, v_a_480_, v_bkt_503_);
if (v___x_504_ == 0)
{
lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_529_; 
lean_inc_ref(v_buckets_483_);
lean_inc(v_size_482_);
v_isSharedCheck_529_ = !lean_is_exclusive(v_m_479_);
if (v_isSharedCheck_529_ == 0)
{
lean_object* v_unused_530_; lean_object* v_unused_531_; 
v_unused_530_ = lean_ctor_get(v_m_479_, 1);
lean_dec(v_unused_530_);
v_unused_531_ = lean_ctor_get(v_m_479_, 0);
lean_dec(v_unused_531_);
v___x_506_ = v_m_479_;
v_isShared_507_ = v_isSharedCheck_529_;
goto v_resetjp_505_;
}
else
{
lean_dec(v_m_479_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_529_;
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
v_val_518_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_478_, v_buckets_x27_511_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 1, v_val_518_);
lean_ctor_set(v___x_506_, 0, v_size_x27_509_);
v___x_520_ = v___x_506_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_size_x27_509_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v_val_518_);
v___x_520_ = v_reuseFailAlloc_523_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = lean_box(v___x_504_);
v___x_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
lean_ctor_set(v___x_522_, 1, v___x_520_);
return v___x_522_;
}
}
else
{
lean_object* v___x_525_; 
lean_dec_ref(v_inst_478_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 1, v_buckets_x27_511_);
lean_ctor_set(v___x_506_, 0, v_size_x27_509_);
v___x_525_ = v___x_506_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_size_x27_509_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v_buckets_x27_511_);
v___x_525_ = v_reuseFailAlloc_528_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_box(v___x_504_);
v___x_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
lean_ctor_set(v___x_527_, 1, v___x_525_);
return v___x_527_;
}
}
}
}
else
{
lean_object* v___x_532_; lean_object* v___x_533_; 
lean_dec(v_b_481_);
lean_dec(v_a_480_);
lean_dec_ref(v_inst_478_);
v___x_532_ = lean_box(v___x_504_);
v___x_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
lean_ctor_set(v___x_533_, 1, v_m_479_);
return v___x_533_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getThenInsertIfNew_x3f___redArg(lean_object* v_inst_534_, lean_object* v_inst_535_, lean_object* v_m_536_, lean_object* v_a_537_, lean_object* v_b_538_){
_start:
{
lean_object* v_size_539_; lean_object* v_buckets_540_; lean_object* v___x_541_; lean_object* v___x_542_; uint8_t v___x_543_; 
v_size_539_ = lean_ctor_get(v_m_536_, 0);
v_buckets_540_ = lean_ctor_get(v_m_536_, 1);
v___x_541_ = lean_unsigned_to_nat(0u);
v___x_542_ = lean_array_get_size(v_buckets_540_);
v___x_543_ = lean_nat_dec_lt(v___x_541_, v___x_542_);
if (v___x_543_ == 0)
{
lean_object* v___x_544_; lean_object* v___x_545_; 
lean_dec(v_b_538_);
lean_dec(v_a_537_);
lean_dec_ref(v_inst_535_);
lean_dec_ref(v_inst_534_);
v___x_544_ = lean_box(0);
v___x_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
lean_ctor_set(v___x_545_, 1, v_m_536_);
return v___x_545_;
}
else
{
lean_object* v___x_546_; uint64_t v___x_547_; uint64_t v___x_548_; uint64_t v___x_549_; uint64_t v___x_550_; uint64_t v_fold_551_; uint64_t v___x_552_; uint64_t v___x_553_; uint64_t v___x_554_; size_t v___x_555_; size_t v___x_556_; size_t v___x_557_; size_t v___x_558_; size_t v___x_559_; lean_object* v_bkt_560_; lean_object* v___x_561_; 
lean_inc_ref(v_inst_535_);
lean_inc_n(v_a_537_, 2);
v___x_546_ = lean_apply_1(v_inst_535_, v_a_537_);
v___x_547_ = 32ULL;
v___x_548_ = lean_unbox_uint64(v___x_546_);
v___x_549_ = lean_uint64_shift_right(v___x_548_, v___x_547_);
v___x_550_ = lean_unbox_uint64(v___x_546_);
lean_dec_ref(v___x_546_);
v_fold_551_ = lean_uint64_xor(v___x_550_, v___x_549_);
v___x_552_ = 16ULL;
v___x_553_ = lean_uint64_shift_right(v_fold_551_, v___x_552_);
v___x_554_ = lean_uint64_xor(v_fold_551_, v___x_553_);
v___x_555_ = lean_uint64_to_usize(v___x_554_);
v___x_556_ = lean_usize_of_nat(v___x_542_);
v___x_557_ = ((size_t)1ULL);
v___x_558_ = lean_usize_sub(v___x_556_, v___x_557_);
v___x_559_ = lean_usize_land(v___x_555_, v___x_558_);
v_bkt_560_ = lean_array_uget_borrowed(v_buckets_540_, v___x_559_);
lean_inc(v_bkt_560_);
v___x_561_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_inst_534_, v_a_537_, v_bkt_560_);
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_584_; 
lean_inc_ref(v_buckets_540_);
lean_inc(v_size_539_);
v_isSharedCheck_584_ = !lean_is_exclusive(v_m_536_);
if (v_isSharedCheck_584_ == 0)
{
lean_object* v_unused_585_; lean_object* v_unused_586_; 
v_unused_585_ = lean_ctor_get(v_m_536_, 1);
lean_dec(v_unused_585_);
v_unused_586_ = lean_ctor_get(v_m_536_, 0);
lean_dec(v_unused_586_);
v___x_563_ = v_m_536_;
v_isShared_564_ = v_isSharedCheck_584_;
goto v_resetjp_562_;
}
else
{
lean_dec(v_m_536_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_584_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_565_; lean_object* v_size_x27_566_; lean_object* v___x_567_; lean_object* v_buckets_x27_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; uint8_t v___x_574_; 
v___x_565_ = lean_unsigned_to_nat(1u);
v_size_x27_566_ = lean_nat_add(v_size_539_, v___x_565_);
lean_dec(v_size_539_);
lean_inc(v_bkt_560_);
v___x_567_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_567_, 0, v_a_537_);
lean_ctor_set(v___x_567_, 1, v_b_538_);
lean_ctor_set(v___x_567_, 2, v_bkt_560_);
v_buckets_x27_568_ = lean_array_uset(v_buckets_540_, v___x_559_, v___x_567_);
v___x_569_ = lean_unsigned_to_nat(4u);
v___x_570_ = lean_nat_mul(v_size_x27_566_, v___x_569_);
v___x_571_ = lean_unsigned_to_nat(3u);
v___x_572_ = lean_nat_div(v___x_570_, v___x_571_);
lean_dec(v___x_570_);
v___x_573_ = lean_array_get_size(v_buckets_x27_568_);
v___x_574_ = lean_nat_dec_le(v___x_572_, v___x_573_);
lean_dec(v___x_572_);
if (v___x_574_ == 0)
{
lean_object* v_val_575_; lean_object* v___x_577_; 
v_val_575_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_535_, v_buckets_x27_568_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 1, v_val_575_);
lean_ctor_set(v___x_563_, 0, v_size_x27_566_);
v___x_577_ = v___x_563_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_size_x27_566_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v_val_575_);
v___x_577_ = v_reuseFailAlloc_579_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
lean_object* v___x_578_; 
v___x_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_561_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
return v___x_578_;
}
}
else
{
lean_object* v___x_581_; 
lean_dec_ref(v_inst_535_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 1, v_buckets_x27_568_);
lean_ctor_set(v___x_563_, 0, v_size_x27_566_);
v___x_581_ = v___x_563_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_size_x27_566_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v_buckets_x27_568_);
v___x_581_ = v_reuseFailAlloc_583_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
lean_object* v___x_582_; 
v___x_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_561_);
lean_ctor_set(v___x_582_, 1, v___x_581_);
return v___x_582_;
}
}
}
}
else
{
lean_object* v___x_587_; 
lean_dec(v_b_538_);
lean_dec(v_a_537_);
lean_dec_ref(v_inst_535_);
v___x_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_561_);
lean_ctor_set(v___x_587_, 1, v_m_536_);
return v___x_587_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_588_, lean_object* v_00_u03b2_589_, lean_object* v_inst_590_, lean_object* v_inst_591_, lean_object* v_m_592_, lean_object* v_a_593_, lean_object* v_b_594_){
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
v___x_600_ = lean_box(0);
v___x_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
lean_ctor_set(v___x_601_, 1, v_m_592_);
return v___x_601_;
}
else
{
lean_object* v___x_602_; uint64_t v___x_603_; uint64_t v___x_604_; uint64_t v___x_605_; uint64_t v___x_606_; uint64_t v_fold_607_; uint64_t v___x_608_; uint64_t v___x_609_; uint64_t v___x_610_; size_t v___x_611_; size_t v___x_612_; size_t v___x_613_; size_t v___x_614_; size_t v___x_615_; lean_object* v_bkt_616_; lean_object* v___x_617_; 
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
v___x_617_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_inst_590_, v_a_593_, v_bkt_616_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_640_; 
lean_inc_ref(v_buckets_596_);
lean_inc(v_size_595_);
v_isSharedCheck_640_ = !lean_is_exclusive(v_m_592_);
if (v_isSharedCheck_640_ == 0)
{
lean_object* v_unused_641_; lean_object* v_unused_642_; 
v_unused_641_ = lean_ctor_get(v_m_592_, 1);
lean_dec(v_unused_641_);
v_unused_642_ = lean_ctor_get(v_m_592_, 0);
lean_dec(v_unused_642_);
v___x_619_ = v_m_592_;
v_isShared_620_ = v_isSharedCheck_640_;
goto v_resetjp_618_;
}
else
{
lean_dec(v_m_592_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_640_;
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
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_size_x27_622_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v_val_631_);
v___x_633_ = v_reuseFailAlloc_635_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
lean_object* v___x_634_; 
v___x_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_617_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
return v___x_634_;
}
}
else
{
lean_object* v___x_637_; 
lean_dec_ref(v_inst_591_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 1, v_buckets_x27_624_);
lean_ctor_set(v___x_619_, 0, v_size_x27_622_);
v___x_637_ = v___x_619_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_size_x27_622_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v_buckets_x27_624_);
v___x_637_ = v_reuseFailAlloc_639_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
lean_object* v___x_638_; 
v___x_638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_617_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
return v___x_638_;
}
}
}
}
else
{
lean_object* v___x_643_; 
lean_dec(v_b_594_);
lean_dec(v_a_593_);
lean_dec_ref(v_inst_591_);
v___x_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_617_);
lean_ctor_set(v___x_643_, 1, v_m_592_);
return v___x_643_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x3f___redArg(lean_object* v_beq_644_, lean_object* v_inst_645_, lean_object* v_m_646_, lean_object* v_a_647_){
_start:
{
lean_object* v_buckets_648_; lean_object* v___x_649_; lean_object* v___x_650_; uint8_t v___x_651_; 
v_buckets_648_ = lean_ctor_get(v_m_646_, 1);
v___x_649_ = lean_unsigned_to_nat(0u);
v___x_650_ = lean_array_get_size(v_buckets_648_);
v___x_651_ = lean_nat_dec_lt(v___x_649_, v___x_650_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; 
lean_dec(v_a_647_);
lean_dec_ref(v_inst_645_);
lean_dec_ref(v_beq_644_);
v___x_652_ = lean_box(0);
return v___x_652_;
}
else
{
lean_object* v___x_653_; 
v___x_653_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_beq_644_, v_inst_645_, v_m_646_, v_a_647_);
return v___x_653_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x3f___redArg___boxed(lean_object* v_beq_654_, lean_object* v_inst_655_, lean_object* v_m_656_, lean_object* v_a_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Std_HashMap_Raw_get_x3f___redArg(v_beq_654_, v_inst_655_, v_m_656_, v_a_657_);
lean_dec_ref(v_m_656_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x3f(lean_object* v_00_u03b1_659_, lean_object* v_00_u03b2_660_, lean_object* v_beq_661_, lean_object* v_inst_662_, lean_object* v_m_663_, lean_object* v_a_664_){
_start:
{
lean_object* v_buckets_665_; lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
v_buckets_665_ = lean_ctor_get(v_m_663_, 1);
v___x_666_ = lean_unsigned_to_nat(0u);
v___x_667_ = lean_array_get_size(v_buckets_665_);
v___x_668_ = lean_nat_dec_lt(v___x_666_, v___x_667_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; 
lean_dec(v_a_664_);
lean_dec_ref(v_inst_662_);
lean_dec_ref(v_beq_661_);
v___x_669_ = lean_box(0);
return v___x_669_;
}
else
{
lean_object* v___x_670_; 
v___x_670_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_beq_661_, v_inst_662_, v_m_663_, v_a_664_);
return v___x_670_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x3f___boxed(lean_object* v_00_u03b1_671_, lean_object* v_00_u03b2_672_, lean_object* v_beq_673_, lean_object* v_inst_674_, lean_object* v_m_675_, lean_object* v_a_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Std_HashMap_Raw_get_x3f(v_00_u03b1_671_, v_00_u03b2_672_, v_beq_673_, v_inst_674_, v_m_675_, v_a_676_);
lean_dec_ref(v_m_675_);
return v_res_677_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_contains___redArg(lean_object* v_inst_678_, lean_object* v_inst_679_, lean_object* v_m_680_, lean_object* v_a_681_){
_start:
{
lean_object* v_buckets_682_; lean_object* v___x_683_; lean_object* v___x_684_; uint8_t v___x_685_; 
v_buckets_682_ = lean_ctor_get(v_m_680_, 1);
v___x_683_ = lean_unsigned_to_nat(0u);
v___x_684_ = lean_array_get_size(v_buckets_682_);
v___x_685_ = lean_nat_dec_lt(v___x_683_, v___x_684_);
if (v___x_685_ == 0)
{
lean_dec(v_a_681_);
lean_dec_ref(v_inst_679_);
lean_dec_ref(v_inst_678_);
return v___x_685_;
}
else
{
uint8_t v___x_686_; 
v___x_686_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_678_, v_inst_679_, v_m_680_, v_a_681_);
return v___x_686_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_contains___redArg___boxed(lean_object* v_inst_687_, lean_object* v_inst_688_, lean_object* v_m_689_, lean_object* v_a_690_){
_start:
{
uint8_t v_res_691_; lean_object* v_r_692_; 
v_res_691_ = l_Std_HashMap_Raw_contains___redArg(v_inst_687_, v_inst_688_, v_m_689_, v_a_690_);
lean_dec_ref(v_m_689_);
v_r_692_ = lean_box(v_res_691_);
return v_r_692_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_contains(lean_object* v_00_u03b1_693_, lean_object* v_00_u03b2_694_, lean_object* v_inst_695_, lean_object* v_inst_696_, lean_object* v_m_697_, lean_object* v_a_698_){
_start:
{
lean_object* v_buckets_699_; lean_object* v___x_700_; lean_object* v___x_701_; uint8_t v___x_702_; 
v_buckets_699_ = lean_ctor_get(v_m_697_, 1);
v___x_700_ = lean_unsigned_to_nat(0u);
v___x_701_ = lean_array_get_size(v_buckets_699_);
v___x_702_ = lean_nat_dec_lt(v___x_700_, v___x_701_);
if (v___x_702_ == 0)
{
lean_dec(v_a_698_);
lean_dec_ref(v_inst_696_);
lean_dec_ref(v_inst_695_);
return v___x_702_;
}
else
{
uint8_t v___x_703_; 
v___x_703_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_695_, v_inst_696_, v_m_697_, v_a_698_);
return v___x_703_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_contains___boxed(lean_object* v_00_u03b1_704_, lean_object* v_00_u03b2_705_, lean_object* v_inst_706_, lean_object* v_inst_707_, lean_object* v_m_708_, lean_object* v_a_709_){
_start:
{
uint8_t v_res_710_; lean_object* v_r_711_; 
v_res_710_ = l_Std_HashMap_Raw_contains(v_00_u03b1_704_, v_00_u03b2_705_, v_inst_706_, v_inst_707_, v_m_708_, v_a_709_);
lean_dec_ref(v_m_708_);
v_r_711_ = lean_box(v_res_710_);
return v_r_711_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instMembershipOfBEqOfHashable___redArg(){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = lean_box(0);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instMembershipOfBEqOfHashable___redArg___boxed(lean_object* v___dummy_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Std_HashMap_Raw_instMembershipOfBEqOfHashable___redArg();
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instMembershipOfBEqOfHashable(lean_object* v_00_u03b1_716_, lean_object* v_00_u03b2_717_, lean_object* v_inst_718_, lean_object* v_inst_719_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = lean_box(0);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instMembershipOfBEqOfHashable___boxed(lean_object* v_00_u03b1_721_, lean_object* v_00_u03b2_722_, lean_object* v_inst_723_, lean_object* v_inst_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Std_HashMap_Raw_instMembershipOfBEqOfHashable(v_00_u03b1_721_, v_00_u03b2_722_, v_inst_723_, v_inst_724_);
lean_dec_ref(v_inst_724_);
lean_dec_ref(v_inst_723_);
return v_res_725_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_instDecidableMem___redArg(lean_object* v_inst_726_, lean_object* v_inst_727_, lean_object* v_m_728_, lean_object* v_a_729_){
_start:
{
uint8_t v___x_730_; 
v___x_730_ = l_Std_DHashMap_Raw_instDecidableMem___redArg(v_inst_726_, v_inst_727_, v_m_728_, v_a_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instDecidableMem___redArg___boxed(lean_object* v_inst_731_, lean_object* v_inst_732_, lean_object* v_m_733_, lean_object* v_a_734_){
_start:
{
uint8_t v_res_735_; lean_object* v_r_736_; 
v_res_735_ = l_Std_HashMap_Raw_instDecidableMem___redArg(v_inst_731_, v_inst_732_, v_m_733_, v_a_734_);
lean_dec_ref(v_m_733_);
v_r_736_ = lean_box(v_res_735_);
return v_r_736_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_instDecidableMem(lean_object* v_00_u03b1_737_, lean_object* v_00_u03b2_738_, lean_object* v_inst_739_, lean_object* v_inst_740_, lean_object* v_m_741_, lean_object* v_a_742_){
_start:
{
uint8_t v___x_743_; 
v___x_743_ = l_Std_DHashMap_Raw_instDecidableMem___redArg(v_inst_739_, v_inst_740_, v_m_741_, v_a_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instDecidableMem___boxed(lean_object* v_00_u03b1_744_, lean_object* v_00_u03b2_745_, lean_object* v_inst_746_, lean_object* v_inst_747_, lean_object* v_m_748_, lean_object* v_a_749_){
_start:
{
uint8_t v_res_750_; lean_object* v_r_751_; 
v_res_750_ = l_Std_HashMap_Raw_instDecidableMem(v_00_u03b1_744_, v_00_u03b2_745_, v_inst_746_, v_inst_747_, v_m_748_, v_a_749_);
lean_dec_ref(v_m_748_);
v_r_751_ = lean_box(v_res_750_);
return v_r_751_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get___redArg(lean_object* v_inst_752_, lean_object* v_inst_753_, lean_object* v_m_754_, lean_object* v_a_755_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_752_, v_inst_753_, v_m_754_, v_a_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get___redArg___boxed(lean_object* v_inst_757_, lean_object* v_inst_758_, lean_object* v_m_759_, lean_object* v_a_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_Std_HashMap_Raw_get___redArg(v_inst_757_, v_inst_758_, v_m_759_, v_a_760_);
lean_dec_ref(v_m_759_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get(lean_object* v_00_u03b1_762_, lean_object* v_00_u03b2_763_, lean_object* v_inst_764_, lean_object* v_inst_765_, lean_object* v_m_766_, lean_object* v_a_767_, lean_object* v_h_768_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_764_, v_inst_765_, v_m_766_, v_a_767_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get___boxed(lean_object* v_00_u03b1_770_, lean_object* v_00_u03b2_771_, lean_object* v_inst_772_, lean_object* v_inst_773_, lean_object* v_m_774_, lean_object* v_a_775_, lean_object* v_h_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Std_HashMap_Raw_get(v_00_u03b1_770_, v_00_u03b2_771_, v_inst_772_, v_inst_773_, v_m_774_, v_a_775_, v_h_776_);
lean_dec_ref(v_m_774_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getD___redArg(lean_object* v_inst_778_, lean_object* v_inst_779_, lean_object* v_m_780_, lean_object* v_a_781_, lean_object* v_fallback_782_){
_start:
{
lean_object* v_buckets_783_; lean_object* v___x_784_; lean_object* v___x_785_; uint8_t v___x_786_; 
v_buckets_783_ = lean_ctor_get(v_m_780_, 1);
v___x_784_ = lean_unsigned_to_nat(0u);
v___x_785_ = lean_array_get_size(v_buckets_783_);
v___x_786_ = lean_nat_dec_lt(v___x_784_, v___x_785_);
if (v___x_786_ == 0)
{
lean_dec(v_a_781_);
lean_dec_ref(v_inst_779_);
lean_dec_ref(v_inst_778_);
lean_inc(v_fallback_782_);
return v_fallback_782_;
}
else
{
lean_object* v___x_787_; 
v___x_787_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_inst_778_, v_inst_779_, v_m_780_, v_a_781_, v_fallback_782_);
return v___x_787_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getD___redArg___boxed(lean_object* v_inst_788_, lean_object* v_inst_789_, lean_object* v_m_790_, lean_object* v_a_791_, lean_object* v_fallback_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Std_HashMap_Raw_getD___redArg(v_inst_788_, v_inst_789_, v_m_790_, v_a_791_, v_fallback_792_);
lean_dec(v_fallback_792_);
lean_dec_ref(v_m_790_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getD(lean_object* v_00_u03b1_794_, lean_object* v_00_u03b2_795_, lean_object* v_inst_796_, lean_object* v_inst_797_, lean_object* v_m_798_, lean_object* v_a_799_, lean_object* v_fallback_800_){
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
v___x_805_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_inst_796_, v_inst_797_, v_m_798_, v_a_799_, v_fallback_800_);
return v___x_805_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getD___boxed(lean_object* v_00_u03b1_806_, lean_object* v_00_u03b2_807_, lean_object* v_inst_808_, lean_object* v_inst_809_, lean_object* v_m_810_, lean_object* v_a_811_, lean_object* v_fallback_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Std_HashMap_Raw_getD(v_00_u03b1_806_, v_00_u03b2_807_, v_inst_808_, v_inst_809_, v_m_810_, v_a_811_, v_fallback_812_);
lean_dec(v_fallback_812_);
lean_dec_ref(v_m_810_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x21___redArg(lean_object* v_inst_814_, lean_object* v_inst_815_, lean_object* v_inst_816_, lean_object* v_m_817_, lean_object* v_a_818_){
_start:
{
lean_object* v_buckets_819_; lean_object* v___x_820_; lean_object* v___x_821_; uint8_t v___x_822_; 
v_buckets_819_ = lean_ctor_get(v_m_817_, 1);
v___x_820_ = lean_unsigned_to_nat(0u);
v___x_821_ = lean_array_get_size(v_buckets_819_);
v___x_822_ = lean_nat_dec_lt(v___x_820_, v___x_821_);
if (v___x_822_ == 0)
{
lean_dec(v_a_818_);
lean_dec_ref(v_inst_815_);
lean_dec_ref(v_inst_814_);
lean_inc(v_inst_816_);
return v_inst_816_;
}
else
{
lean_object* v___x_823_; 
v___x_823_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_814_, v_inst_815_, v_inst_816_, v_m_817_, v_a_818_);
return v___x_823_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x21___redArg___boxed(lean_object* v_inst_824_, lean_object* v_inst_825_, lean_object* v_inst_826_, lean_object* v_m_827_, lean_object* v_a_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Std_HashMap_Raw_get_x21___redArg(v_inst_824_, v_inst_825_, v_inst_826_, v_m_827_, v_a_828_);
lean_dec_ref(v_m_827_);
lean_dec(v_inst_826_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x21(lean_object* v_00_u03b1_830_, lean_object* v_00_u03b2_831_, lean_object* v_inst_832_, lean_object* v_inst_833_, lean_object* v_inst_834_, lean_object* v_m_835_, lean_object* v_a_836_){
_start:
{
lean_object* v_buckets_837_; lean_object* v___x_838_; lean_object* v___x_839_; uint8_t v___x_840_; 
v_buckets_837_ = lean_ctor_get(v_m_835_, 1);
v___x_838_ = lean_unsigned_to_nat(0u);
v___x_839_ = lean_array_get_size(v_buckets_837_);
v___x_840_ = lean_nat_dec_lt(v___x_838_, v___x_839_);
if (v___x_840_ == 0)
{
lean_dec(v_a_836_);
lean_dec_ref(v_inst_833_);
lean_dec_ref(v_inst_832_);
lean_inc(v_inst_834_);
return v_inst_834_;
}
else
{
lean_object* v___x_841_; 
v___x_841_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_832_, v_inst_833_, v_inst_834_, v_m_835_, v_a_836_);
return v___x_841_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x21___boxed(lean_object* v_00_u03b1_842_, lean_object* v_00_u03b2_843_, lean_object* v_inst_844_, lean_object* v_inst_845_, lean_object* v_inst_846_, lean_object* v_m_847_, lean_object* v_a_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Std_HashMap_Raw_get_x21(v_00_u03b1_842_, v_00_u03b2_843_, v_inst_844_, v_inst_845_, v_inst_846_, v_m_847_, v_a_848_);
lean_dec_ref(v_m_847_);
lean_dec(v_inst_846_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__0(lean_object* v_inst_850_, lean_object* v_inst_851_, lean_object* v_m_852_, lean_object* v_a_853_, lean_object* v_h_854_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_850_, v_inst_851_, v_m_852_, v_a_853_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__0___boxed(lean_object* v_inst_856_, lean_object* v_inst_857_, lean_object* v_m_858_, lean_object* v_a_859_, lean_object* v_h_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__0(v_inst_856_, v_inst_857_, v_m_858_, v_a_859_, v_h_860_);
lean_dec_ref(v_m_858_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__1(lean_object* v_inst_862_, lean_object* v_inst_863_, lean_object* v_m_864_, lean_object* v_a_865_){
_start:
{
lean_object* v_buckets_866_; lean_object* v___x_867_; lean_object* v___x_868_; uint8_t v___x_869_; 
v_buckets_866_ = lean_ctor_get(v_m_864_, 1);
v___x_867_ = lean_unsigned_to_nat(0u);
v___x_868_ = lean_array_get_size(v_buckets_866_);
v___x_869_ = lean_nat_dec_lt(v___x_867_, v___x_868_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; 
lean_dec(v_a_865_);
lean_dec_ref(v_inst_863_);
lean_dec_ref(v_inst_862_);
v___x_870_ = lean_box(0);
return v___x_870_;
}
else
{
lean_object* v___x_871_; 
v___x_871_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_862_, v_inst_863_, v_m_864_, v_a_865_);
return v___x_871_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__1___boxed(lean_object* v_inst_872_, lean_object* v_inst_873_, lean_object* v_m_874_, lean_object* v_a_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__1(v_inst_872_, v_inst_873_, v_m_874_, v_a_875_);
lean_dec_ref(v_m_874_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__2(lean_object* v_inst_877_, lean_object* v_inst_878_, lean_object* v_inst_879_, lean_object* v_m_880_, lean_object* v_a_881_){
_start:
{
lean_object* v_buckets_882_; lean_object* v___x_883_; lean_object* v___x_884_; uint8_t v___x_885_; 
v_buckets_882_ = lean_ctor_get(v_m_880_, 1);
v___x_883_ = lean_unsigned_to_nat(0u);
v___x_884_ = lean_array_get_size(v_buckets_882_);
v___x_885_ = lean_nat_dec_lt(v___x_883_, v___x_884_);
if (v___x_885_ == 0)
{
lean_dec(v_a_881_);
lean_dec_ref(v_inst_878_);
lean_dec_ref(v_inst_877_);
lean_inc(v_inst_879_);
return v_inst_879_;
}
else
{
lean_object* v___x_886_; 
v___x_886_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_877_, v_inst_878_, v_inst_879_, v_m_880_, v_a_881_);
return v___x_886_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__2___boxed(lean_object* v_inst_887_, lean_object* v_inst_888_, lean_object* v_inst_889_, lean_object* v_m_890_, lean_object* v_a_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__2(v_inst_887_, v_inst_888_, v_inst_889_, v_m_890_, v_a_891_);
lean_dec_ref(v_m_890_);
lean_dec(v_inst_889_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg(lean_object* v_inst_893_, lean_object* v_inst_894_){
_start:
{
lean_object* v___f_895_; lean_object* v___f_896_; lean_object* v___f_897_; lean_object* v___x_898_; 
lean_inc_ref_n(v_inst_894_, 2);
lean_inc_ref_n(v_inst_893_, 2);
v___f_895_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_895_, 0, v_inst_893_);
lean_closure_set(v___f_895_, 1, v_inst_894_);
v___f_896_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_896_, 0, v_inst_893_);
lean_closure_set(v___f_896_, 1, v_inst_894_);
v___f_897_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__2___boxed), 5, 2);
lean_closure_set(v___f_897_, 0, v_inst_893_);
lean_closure_set(v___f_897_, 1, v_inst_894_);
v___x_898_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_898_, 0, v___f_895_);
lean_ctor_set(v___x_898_, 1, v___f_896_);
lean_ctor_set(v___x_898_, 2, v___f_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem(lean_object* v_00_u03b1_899_, lean_object* v_00_u03b2_900_, lean_object* v_inst_901_, lean_object* v_inst_902_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l_Std_HashMap_Raw_instGetElem_x3fMem___redArg(v_inst_901_, v_inst_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x3f___redArg(lean_object* v_inst_904_, lean_object* v_inst_905_, lean_object* v_m_906_, lean_object* v_a_907_){
_start:
{
lean_object* v_buckets_908_; lean_object* v___x_909_; lean_object* v___x_910_; uint8_t v___x_911_; 
v_buckets_908_ = lean_ctor_get(v_m_906_, 1);
v___x_909_ = lean_unsigned_to_nat(0u);
v___x_910_ = lean_array_get_size(v_buckets_908_);
v___x_911_ = lean_nat_dec_lt(v___x_909_, v___x_910_);
if (v___x_911_ == 0)
{
lean_object* v___x_912_; 
lean_dec(v_a_907_);
lean_dec_ref(v_inst_905_);
lean_dec_ref(v_inst_904_);
v___x_912_ = lean_box(0);
return v___x_912_;
}
else
{
lean_object* v___x_913_; 
v___x_913_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_904_, v_inst_905_, v_m_906_, v_a_907_);
return v___x_913_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x3f___redArg___boxed(lean_object* v_inst_914_, lean_object* v_inst_915_, lean_object* v_m_916_, lean_object* v_a_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_Std_HashMap_Raw_getKey_x3f___redArg(v_inst_914_, v_inst_915_, v_m_916_, v_a_917_);
lean_dec_ref(v_m_916_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x3f(lean_object* v_00_u03b1_919_, lean_object* v_00_u03b2_920_, lean_object* v_inst_921_, lean_object* v_inst_922_, lean_object* v_m_923_, lean_object* v_a_924_){
_start:
{
lean_object* v_buckets_925_; lean_object* v___x_926_; lean_object* v___x_927_; uint8_t v___x_928_; 
v_buckets_925_ = lean_ctor_get(v_m_923_, 1);
v___x_926_ = lean_unsigned_to_nat(0u);
v___x_927_ = lean_array_get_size(v_buckets_925_);
v___x_928_ = lean_nat_dec_lt(v___x_926_, v___x_927_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; 
lean_dec(v_a_924_);
lean_dec_ref(v_inst_922_);
lean_dec_ref(v_inst_921_);
v___x_929_ = lean_box(0);
return v___x_929_;
}
else
{
lean_object* v___x_930_; 
v___x_930_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_921_, v_inst_922_, v_m_923_, v_a_924_);
return v___x_930_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x3f___boxed(lean_object* v_00_u03b1_931_, lean_object* v_00_u03b2_932_, lean_object* v_inst_933_, lean_object* v_inst_934_, lean_object* v_m_935_, lean_object* v_a_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Std_HashMap_Raw_getKey_x3f(v_00_u03b1_931_, v_00_u03b2_932_, v_inst_933_, v_inst_934_, v_m_935_, v_a_936_);
lean_dec_ref(v_m_935_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey___redArg(lean_object* v_inst_938_, lean_object* v_inst_939_, lean_object* v_m_940_, lean_object* v_a_941_){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_938_, v_inst_939_, v_m_940_, v_a_941_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey___redArg___boxed(lean_object* v_inst_943_, lean_object* v_inst_944_, lean_object* v_m_945_, lean_object* v_a_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Std_HashMap_Raw_getKey___redArg(v_inst_943_, v_inst_944_, v_m_945_, v_a_946_);
lean_dec_ref(v_m_945_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey(lean_object* v_00_u03b1_948_, lean_object* v_00_u03b2_949_, lean_object* v_inst_950_, lean_object* v_inst_951_, lean_object* v_m_952_, lean_object* v_a_953_, lean_object* v_h_954_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_950_, v_inst_951_, v_m_952_, v_a_953_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey___boxed(lean_object* v_00_u03b1_956_, lean_object* v_00_u03b2_957_, lean_object* v_inst_958_, lean_object* v_inst_959_, lean_object* v_m_960_, lean_object* v_a_961_, lean_object* v_h_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Std_HashMap_Raw_getKey(v_00_u03b1_956_, v_00_u03b2_957_, v_inst_958_, v_inst_959_, v_m_960_, v_a_961_, v_h_962_);
lean_dec_ref(v_m_960_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKeyD___redArg(lean_object* v_inst_964_, lean_object* v_inst_965_, lean_object* v_m_966_, lean_object* v_a_967_, lean_object* v_fallback_968_){
_start:
{
lean_object* v_buckets_969_; lean_object* v___x_970_; lean_object* v___x_971_; uint8_t v___x_972_; 
v_buckets_969_ = lean_ctor_get(v_m_966_, 1);
v___x_970_ = lean_unsigned_to_nat(0u);
v___x_971_ = lean_array_get_size(v_buckets_969_);
v___x_972_ = lean_nat_dec_lt(v___x_970_, v___x_971_);
if (v___x_972_ == 0)
{
lean_dec(v_a_967_);
lean_dec_ref(v_inst_965_);
lean_dec_ref(v_inst_964_);
lean_inc(v_fallback_968_);
return v_fallback_968_;
}
else
{
lean_object* v___x_973_; 
v___x_973_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_964_, v_inst_965_, v_m_966_, v_a_967_, v_fallback_968_);
return v___x_973_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKeyD___redArg___boxed(lean_object* v_inst_974_, lean_object* v_inst_975_, lean_object* v_m_976_, lean_object* v_a_977_, lean_object* v_fallback_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Std_HashMap_Raw_getKeyD___redArg(v_inst_974_, v_inst_975_, v_m_976_, v_a_977_, v_fallback_978_);
lean_dec(v_fallback_978_);
lean_dec_ref(v_m_976_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKeyD(lean_object* v_00_u03b1_980_, lean_object* v_00_u03b2_981_, lean_object* v_inst_982_, lean_object* v_inst_983_, lean_object* v_m_984_, lean_object* v_a_985_, lean_object* v_fallback_986_){
_start:
{
lean_object* v_buckets_987_; lean_object* v___x_988_; lean_object* v___x_989_; uint8_t v___x_990_; 
v_buckets_987_ = lean_ctor_get(v_m_984_, 1);
v___x_988_ = lean_unsigned_to_nat(0u);
v___x_989_ = lean_array_get_size(v_buckets_987_);
v___x_990_ = lean_nat_dec_lt(v___x_988_, v___x_989_);
if (v___x_990_ == 0)
{
lean_dec(v_a_985_);
lean_dec_ref(v_inst_983_);
lean_dec_ref(v_inst_982_);
lean_inc(v_fallback_986_);
return v_fallback_986_;
}
else
{
lean_object* v___x_991_; 
v___x_991_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_982_, v_inst_983_, v_m_984_, v_a_985_, v_fallback_986_);
return v___x_991_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKeyD___boxed(lean_object* v_00_u03b1_992_, lean_object* v_00_u03b2_993_, lean_object* v_inst_994_, lean_object* v_inst_995_, lean_object* v_m_996_, lean_object* v_a_997_, lean_object* v_fallback_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Std_HashMap_Raw_getKeyD(v_00_u03b1_992_, v_00_u03b2_993_, v_inst_994_, v_inst_995_, v_m_996_, v_a_997_, v_fallback_998_);
lean_dec(v_fallback_998_);
lean_dec_ref(v_m_996_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x21___redArg(lean_object* v_inst_1000_, lean_object* v_inst_1001_, lean_object* v_inst_1002_, lean_object* v_m_1003_, lean_object* v_a_1004_){
_start:
{
lean_object* v_buckets_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; uint8_t v___x_1008_; 
v_buckets_1005_ = lean_ctor_get(v_m_1003_, 1);
v___x_1006_ = lean_unsigned_to_nat(0u);
v___x_1007_ = lean_array_get_size(v_buckets_1005_);
v___x_1008_ = lean_nat_dec_lt(v___x_1006_, v___x_1007_);
if (v___x_1008_ == 0)
{
lean_dec(v_a_1004_);
lean_dec_ref(v_inst_1001_);
lean_dec_ref(v_inst_1000_);
lean_inc(v_inst_1002_);
return v_inst_1002_;
}
else
{
lean_object* v___x_1009_; 
v___x_1009_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_1000_, v_inst_1001_, v_inst_1002_, v_m_1003_, v_a_1004_);
return v___x_1009_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x21___redArg___boxed(lean_object* v_inst_1010_, lean_object* v_inst_1011_, lean_object* v_inst_1012_, lean_object* v_m_1013_, lean_object* v_a_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Std_HashMap_Raw_getKey_x21___redArg(v_inst_1010_, v_inst_1011_, v_inst_1012_, v_m_1013_, v_a_1014_);
lean_dec_ref(v_m_1013_);
lean_dec(v_inst_1012_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x21(lean_object* v_00_u03b1_1016_, lean_object* v_00_u03b2_1017_, lean_object* v_inst_1018_, lean_object* v_inst_1019_, lean_object* v_inst_1020_, lean_object* v_m_1021_, lean_object* v_a_1022_){
_start:
{
lean_object* v_buckets_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; uint8_t v___x_1026_; 
v_buckets_1023_ = lean_ctor_get(v_m_1021_, 1);
v___x_1024_ = lean_unsigned_to_nat(0u);
v___x_1025_ = lean_array_get_size(v_buckets_1023_);
v___x_1026_ = lean_nat_dec_lt(v___x_1024_, v___x_1025_);
if (v___x_1026_ == 0)
{
lean_dec(v_a_1022_);
lean_dec_ref(v_inst_1019_);
lean_dec_ref(v_inst_1018_);
lean_inc(v_inst_1020_);
return v_inst_1020_;
}
else
{
lean_object* v___x_1027_; 
v___x_1027_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_1018_, v_inst_1019_, v_inst_1020_, v_m_1021_, v_a_1022_);
return v___x_1027_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x21___boxed(lean_object* v_00_u03b1_1028_, lean_object* v_00_u03b2_1029_, lean_object* v_inst_1030_, lean_object* v_inst_1031_, lean_object* v_inst_1032_, lean_object* v_m_1033_, lean_object* v_a_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_Std_HashMap_Raw_getKey_x21(v_00_u03b1_1028_, v_00_u03b2_1029_, v_inst_1030_, v_inst_1031_, v_inst_1032_, v_m_1033_, v_a_1034_);
lean_dec_ref(v_m_1033_);
lean_dec(v_inst_1032_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_erase___redArg(lean_object* v_inst_1036_, lean_object* v_inst_1037_, lean_object* v_m_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v_buckets_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; uint8_t v___x_1043_; 
v_buckets_1040_ = lean_ctor_get(v_m_1038_, 1);
v___x_1041_ = lean_unsigned_to_nat(0u);
v___x_1042_ = lean_array_get_size(v_buckets_1040_);
v___x_1043_ = lean_nat_dec_lt(v___x_1041_, v___x_1042_);
if (v___x_1043_ == 0)
{
lean_dec(v_a_1039_);
lean_dec_ref(v_inst_1037_);
lean_dec_ref(v_inst_1036_);
return v_m_1038_;
}
else
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_1036_, v_inst_1037_, v_m_1038_, v_a_1039_);
return v___x_1044_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_erase(lean_object* v_00_u03b1_1045_, lean_object* v_00_u03b2_1046_, lean_object* v_inst_1047_, lean_object* v_inst_1048_, lean_object* v_m_1049_, lean_object* v_a_1050_){
_start:
{
lean_object* v_buckets_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; uint8_t v___x_1054_; 
v_buckets_1051_ = lean_ctor_get(v_m_1049_, 1);
v___x_1052_ = lean_unsigned_to_nat(0u);
v___x_1053_ = lean_array_get_size(v_buckets_1051_);
v___x_1054_ = lean_nat_dec_lt(v___x_1052_, v___x_1053_);
if (v___x_1054_ == 0)
{
lean_dec(v_a_1050_);
lean_dec_ref(v_inst_1048_);
lean_dec_ref(v_inst_1047_);
return v_m_1049_;
}
else
{
lean_object* v___x_1055_; 
v___x_1055_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_1047_, v_inst_1048_, v_m_1049_, v_a_1050_);
return v___x_1055_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_size___redArg(lean_object* v_m_1056_){
_start:
{
lean_object* v_size_1057_; 
v_size_1057_ = lean_ctor_get(v_m_1056_, 0);
lean_inc(v_size_1057_);
return v_size_1057_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_size___redArg___boxed(lean_object* v_m_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Std_HashMap_Raw_size___redArg(v_m_1058_);
lean_dec_ref(v_m_1058_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_size(lean_object* v_00_u03b1_1060_, lean_object* v_00_u03b2_1061_, lean_object* v_m_1062_){
_start:
{
lean_object* v_size_1063_; 
v_size_1063_ = lean_ctor_get(v_m_1062_, 0);
lean_inc(v_size_1063_);
return v_size_1063_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_size___boxed(lean_object* v_00_u03b1_1064_, lean_object* v_00_u03b2_1065_, lean_object* v_m_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Std_HashMap_Raw_size(v_00_u03b1_1064_, v_00_u03b2_1065_, v_m_1066_);
lean_dec_ref(v_m_1066_);
return v_res_1067_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_isEmpty___redArg(lean_object* v_m_1068_){
_start:
{
lean_object* v_size_1069_; lean_object* v___x_1070_; uint8_t v___x_1071_; 
v_size_1069_ = lean_ctor_get(v_m_1068_, 0);
v___x_1070_ = lean_unsigned_to_nat(0u);
v___x_1071_ = lean_nat_dec_eq(v_size_1069_, v___x_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_isEmpty___redArg___boxed(lean_object* v_m_1072_){
_start:
{
uint8_t v_res_1073_; lean_object* v_r_1074_; 
v_res_1073_ = l_Std_HashMap_Raw_isEmpty___redArg(v_m_1072_);
lean_dec_ref(v_m_1072_);
v_r_1074_ = lean_box(v_res_1073_);
return v_r_1074_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_isEmpty(lean_object* v_00_u03b1_1075_, lean_object* v_00_u03b2_1076_, lean_object* v_m_1077_){
_start:
{
lean_object* v_size_1078_; lean_object* v___x_1079_; uint8_t v___x_1080_; 
v_size_1078_ = lean_ctor_get(v_m_1077_, 0);
v___x_1079_ = lean_unsigned_to_nat(0u);
v___x_1080_ = lean_nat_dec_eq(v_size_1078_, v___x_1079_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_isEmpty___boxed(lean_object* v_00_u03b1_1081_, lean_object* v_00_u03b2_1082_, lean_object* v_m_1083_){
_start:
{
uint8_t v_res_1084_; lean_object* v_r_1085_; 
v_res_1084_ = l_Std_HashMap_Raw_isEmpty(v_00_u03b1_1081_, v_00_u03b2_1082_, v_m_1083_);
lean_dec_ref(v_m_1083_);
v_r_1085_ = lean_box(v_res_1084_);
return v_r_1085_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys___redArg___lam__0(lean_object* v_a_1086_, lean_object* v_b_1087_, lean_object* v_d_1088_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1089_, 0, v_a_1086_);
lean_ctor_set(v___x_1089_, 1, v_d_1088_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys___redArg___lam__0___boxed(lean_object* v_a_1090_, lean_object* v_b_1091_, lean_object* v_d_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l_Std_HashMap_Raw_keys___redArg___lam__0(v_a_1090_, v_b_1091_, v_d_1092_);
lean_dec(v_b_1091_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys___redArg___lam__1(lean_object* v___x_1094_, lean_object* v___f_1095_, lean_object* v_l_1096_, lean_object* v_acc_1097_){
_start:
{
lean_object* v___x_1098_; 
v___x_1098_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_1094_, v___f_1095_, v_acc_1097_, v_l_1096_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys___redArg(lean_object* v_m_1122_){
_start:
{
lean_object* v___x_1123_; lean_object* v_buckets_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; uint8_t v___x_1128_; 
v___x_1123_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1124_ = lean_ctor_get(v_m_1122_, 1);
lean_inc_ref(v_buckets_1124_);
lean_dec_ref(v_m_1122_);
v___x_1125_ = lean_box(0);
v___x_1126_ = lean_array_get_size(v_buckets_1124_);
v___x_1127_ = lean_unsigned_to_nat(0u);
v___x_1128_ = lean_nat_dec_lt(v___x_1127_, v___x_1126_);
if (v___x_1128_ == 0)
{
lean_dec_ref(v_buckets_1124_);
return v___x_1125_;
}
else
{
lean_object* v___f_1129_; size_t v___x_1130_; size_t v___x_1131_; lean_object* v___x_1132_; 
v___f_1129_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__11));
v___x_1130_ = lean_usize_of_nat(v___x_1126_);
v___x_1131_ = ((size_t)0ULL);
v___x_1132_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1123_, v___f_1129_, v_buckets_1124_, v___x_1130_, v___x_1131_, v___x_1125_);
return v___x_1132_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys(lean_object* v_00_u03b1_1133_, lean_object* v_00_u03b2_1134_, lean_object* v_m_1135_){
_start:
{
lean_object* v___x_1136_; lean_object* v_buckets_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; uint8_t v___x_1141_; 
v___x_1136_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1137_ = lean_ctor_get(v_m_1135_, 1);
lean_inc_ref(v_buckets_1137_);
lean_dec_ref(v_m_1135_);
v___x_1138_ = lean_box(0);
v___x_1139_ = lean_array_get_size(v_buckets_1137_);
v___x_1140_ = lean_unsigned_to_nat(0u);
v___x_1141_ = lean_nat_dec_lt(v___x_1140_, v___x_1139_);
if (v___x_1141_ == 0)
{
lean_dec_ref(v_buckets_1137_);
return v___x_1138_;
}
else
{
lean_object* v___f_1142_; size_t v___x_1143_; size_t v___x_1144_; lean_object* v___x_1145_; 
v___f_1142_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__11));
v___x_1143_ = lean_usize_of_nat(v___x_1139_);
v___x_1144_ = ((size_t)0ULL);
v___x_1145_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1136_, v___f_1142_, v_buckets_1137_, v___x_1143_, v___x_1144_, v___x_1138_);
return v___x_1145_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_ofList___redArg(lean_object* v_inst_1150_, lean_object* v_inst_1151_, lean_object* v_l_1152_){
_start:
{
lean_object* v___x_1153_; uint8_t v___x_1154_; 
v___x_1153_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1);
v___x_1154_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1154_ == 0)
{
lean_dec(v_l_1152_);
lean_dec_ref(v_inst_1151_);
lean_dec_ref(v_inst_1150_);
return v___x_1153_;
}
else
{
lean_object* v___f_1155_; lean_object* v___x_1156_; 
v___f_1155_ = ((lean_object*)(l_Std_HashMap_Raw_ofList___redArg___closed__1));
v___x_1156_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1155_, v_inst_1150_, v_inst_1151_, v___x_1153_, v_l_1152_);
return v___x_1156_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_ofList(lean_object* v_00_u03b1_1157_, lean_object* v_00_u03b2_1158_, lean_object* v_inst_1159_, lean_object* v_inst_1160_, lean_object* v_l_1161_){
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
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_unitOfList___redArg(lean_object* v_inst_1166_, lean_object* v_inst_1167_, lean_object* v_l_1168_){
_start:
{
lean_object* v___x_1169_; uint8_t v___x_1170_; 
v___x_1169_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1);
v___x_1170_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1170_ == 0)
{
lean_dec(v_l_1168_);
lean_dec_ref(v_inst_1167_);
lean_dec_ref(v_inst_1166_);
return v___x_1169_;
}
else
{
lean_object* v___f_1171_; lean_object* v___x_1172_; 
v___f_1171_ = ((lean_object*)(l_Std_HashMap_Raw_ofList___redArg___closed__1));
v___x_1172_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1171_, v_inst_1166_, v_inst_1167_, v___x_1169_, v_l_1168_);
return v___x_1172_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_unitOfList(lean_object* v_00_u03b1_1173_, lean_object* v_inst_1174_, lean_object* v_inst_1175_, lean_object* v_l_1176_){
_start:
{
lean_object* v___x_1177_; uint8_t v___x_1178_; 
v___x_1177_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1);
v___x_1178_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1178_ == 0)
{
lean_dec(v_l_1176_);
lean_dec_ref(v_inst_1175_);
lean_dec_ref(v_inst_1174_);
return v___x_1177_;
}
else
{
lean_object* v___f_1179_; lean_object* v___x_1180_; 
v___f_1179_ = ((lean_object*)(l_Std_HashMap_Raw_ofList___redArg___closed__1));
v___x_1180_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1179_, v_inst_1174_, v_inst_1175_, v___x_1177_, v_l_1176_);
return v___x_1180_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_ofArray___redArg(lean_object* v_inst_1185_, lean_object* v_inst_1186_, lean_object* v_a_1187_){
_start:
{
lean_object* v___x_1188_; uint8_t v___x_1189_; 
v___x_1188_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1);
v___x_1189_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1189_ == 0)
{
lean_dec_ref(v_a_1187_);
lean_dec_ref(v_inst_1186_);
lean_dec_ref(v_inst_1185_);
return v___x_1188_;
}
else
{
lean_object* v___f_1190_; lean_object* v___x_1191_; 
v___f_1190_ = ((lean_object*)(l_Std_HashMap_Raw_ofArray___redArg___closed__1));
v___x_1191_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1190_, v_inst_1185_, v_inst_1186_, v___x_1188_, v_a_1187_);
return v___x_1191_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_ofArray(lean_object* v_00_u03b1_1192_, lean_object* v_00_u03b2_1193_, lean_object* v_inst_1194_, lean_object* v_inst_1195_, lean_object* v_a_1196_){
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
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_alter___redArg(lean_object* v_inst_1201_, lean_object* v_inst_1202_, lean_object* v_m_1203_, lean_object* v_a_1204_, lean_object* v_f_1205_){
_start:
{
lean_object* v_buckets_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; uint8_t v___x_1209_; 
v_buckets_1206_ = lean_ctor_get(v_m_1203_, 1);
v___x_1207_ = lean_unsigned_to_nat(0u);
v___x_1208_ = lean_array_get_size(v_buckets_1206_);
v___x_1209_ = lean_nat_dec_lt(v___x_1207_, v___x_1208_);
if (v___x_1209_ == 0)
{
lean_object* v___x_1210_; 
lean_dec_ref(v_f_1205_);
lean_dec(v_a_1204_);
lean_dec_ref(v_m_1203_);
lean_dec_ref(v_inst_1202_);
lean_dec_ref(v_inst_1201_);
v___x_1210_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1210_;
}
else
{
lean_object* v___x_1211_; 
v___x_1211_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_1201_, v_inst_1202_, v_m_1203_, v_a_1204_, v_f_1205_);
return v___x_1211_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_alter(lean_object* v_00_u03b1_1212_, lean_object* v_00_u03b2_1213_, lean_object* v_inst_1214_, lean_object* v_inst_1215_, lean_object* v_inst_1216_, lean_object* v_m_1217_, lean_object* v_a_1218_, lean_object* v_f_1219_){
_start:
{
lean_object* v_buckets_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; uint8_t v___x_1223_; 
v_buckets_1220_ = lean_ctor_get(v_m_1217_, 1);
v___x_1221_ = lean_unsigned_to_nat(0u);
v___x_1222_ = lean_array_get_size(v_buckets_1220_);
v___x_1223_ = lean_nat_dec_lt(v___x_1221_, v___x_1222_);
if (v___x_1223_ == 0)
{
lean_object* v___x_1224_; 
lean_dec_ref(v_f_1219_);
lean_dec(v_a_1218_);
lean_dec_ref(v_m_1217_);
lean_dec_ref(v_inst_1216_);
lean_dec_ref(v_inst_1214_);
v___x_1224_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1224_;
}
else
{
lean_object* v___x_1225_; 
v___x_1225_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_1214_, v_inst_1216_, v_m_1217_, v_a_1218_, v_f_1219_);
return v___x_1225_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_modify___redArg(lean_object* v_inst_1226_, lean_object* v_inst_1227_, lean_object* v_m_1228_, lean_object* v_a_1229_, lean_object* v_f_1230_){
_start:
{
lean_object* v_buckets_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; uint8_t v___x_1234_; 
v_buckets_1231_ = lean_ctor_get(v_m_1228_, 1);
v___x_1232_ = lean_unsigned_to_nat(0u);
v___x_1233_ = lean_array_get_size(v_buckets_1231_);
v___x_1234_ = lean_nat_dec_lt(v___x_1232_, v___x_1233_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; 
lean_dec(v_f_1230_);
lean_dec(v_a_1229_);
lean_dec_ref(v_m_1228_);
lean_dec_ref(v_inst_1227_);
lean_dec_ref(v_inst_1226_);
v___x_1235_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1235_;
}
else
{
lean_object* v___x_1236_; 
v___x_1236_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_inst_1226_, v_inst_1227_, v_m_1228_, v_a_1229_, v_f_1230_);
return v___x_1236_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_modify(lean_object* v_00_u03b1_1237_, lean_object* v_00_u03b2_1238_, lean_object* v_inst_1239_, lean_object* v_inst_1240_, lean_object* v_inst_1241_, lean_object* v_m_1242_, lean_object* v_a_1243_, lean_object* v_f_1244_){
_start:
{
lean_object* v_buckets_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; uint8_t v___x_1248_; 
v_buckets_1245_ = lean_ctor_get(v_m_1242_, 1);
v___x_1246_ = lean_unsigned_to_nat(0u);
v___x_1247_ = lean_array_get_size(v_buckets_1245_);
v___x_1248_ = lean_nat_dec_lt(v___x_1246_, v___x_1247_);
if (v___x_1248_ == 0)
{
lean_object* v___x_1249_; 
lean_dec(v_f_1244_);
lean_dec(v_a_1243_);
lean_dec_ref(v_m_1242_);
lean_dec_ref(v_inst_1241_);
lean_dec_ref(v_inst_1239_);
v___x_1249_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1249_;
}
else
{
lean_object* v___x_1250_; 
v___x_1250_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_inst_1239_, v_inst_1241_, v_m_1242_, v_a_1243_, v_f_1244_);
return v___x_1250_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toList___redArg___lam__0(lean_object* v_a_1251_, lean_object* v_b_1252_, lean_object* v_d_1253_){
_start:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1254_, 0, v_a_1251_);
lean_ctor_set(v___x_1254_, 1, v_b_1252_);
v___x_1255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1254_);
lean_ctor_set(v___x_1255_, 1, v_d_1253_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toList___redArg___lam__1(lean_object* v___x_1256_, lean_object* v___f_1257_, lean_object* v_l_1258_, lean_object* v_acc_1259_){
_start:
{
lean_object* v___x_1260_; 
v___x_1260_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_1256_, v___f_1257_, v_acc_1259_, v_l_1258_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toList___redArg(lean_object* v_m_1265_){
_start:
{
lean_object* v___x_1266_; lean_object* v_buckets_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; uint8_t v___x_1271_; 
v___x_1266_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1267_ = lean_ctor_get(v_m_1265_, 1);
lean_inc_ref(v_buckets_1267_);
lean_dec_ref(v_m_1265_);
v___x_1268_ = lean_box(0);
v___x_1269_ = lean_array_get_size(v_buckets_1267_);
v___x_1270_ = lean_unsigned_to_nat(0u);
v___x_1271_ = lean_nat_dec_lt(v___x_1270_, v___x_1269_);
if (v___x_1271_ == 0)
{
lean_dec_ref(v_buckets_1267_);
return v___x_1268_;
}
else
{
lean_object* v___f_1272_; size_t v___x_1273_; size_t v___x_1274_; lean_object* v___x_1275_; 
v___f_1272_ = ((lean_object*)(l_Std_HashMap_Raw_toList___redArg___closed__1));
v___x_1273_ = lean_usize_of_nat(v___x_1269_);
v___x_1274_ = ((size_t)0ULL);
v___x_1275_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1266_, v___f_1272_, v_buckets_1267_, v___x_1273_, v___x_1274_, v___x_1268_);
return v___x_1275_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toList(lean_object* v_00_u03b1_1276_, lean_object* v_00_u03b2_1277_, lean_object* v_m_1278_){
_start:
{
lean_object* v___x_1279_; lean_object* v_buckets_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; uint8_t v___x_1284_; 
v___x_1279_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1280_ = lean_ctor_get(v_m_1278_, 1);
lean_inc_ref(v_buckets_1280_);
lean_dec_ref(v_m_1278_);
v___x_1281_ = lean_box(0);
v___x_1282_ = lean_array_get_size(v_buckets_1280_);
v___x_1283_ = lean_unsigned_to_nat(0u);
v___x_1284_ = lean_nat_dec_lt(v___x_1283_, v___x_1282_);
if (v___x_1284_ == 0)
{
lean_dec_ref(v_buckets_1280_);
return v___x_1281_;
}
else
{
lean_object* v___f_1285_; size_t v___x_1286_; size_t v___x_1287_; lean_object* v___x_1288_; 
v___f_1285_ = ((lean_object*)(l_Std_HashMap_Raw_toList___redArg___closed__1));
v___x_1286_ = lean_usize_of_nat(v___x_1282_);
v___x_1287_ = ((size_t)0ULL);
v___x_1288_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1279_, v___f_1285_, v_buckets_1280_, v___x_1286_, v___x_1287_, v___x_1281_);
return v___x_1288_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_foldM___redArg___lam__0(lean_object* v_inst_1289_, lean_object* v_f_1290_, lean_object* v_acc_1291_, lean_object* v_l_1292_){
_start:
{
lean_object* v___x_1293_; 
v___x_1293_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_1289_, v_f_1290_, v_acc_1291_, v_l_1292_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_foldM___redArg(lean_object* v_inst_1294_, lean_object* v_f_1295_, lean_object* v_init_1296_, lean_object* v_b_1297_){
_start:
{
lean_object* v_toApplicative_1298_; lean_object* v_buckets_1299_; lean_object* v_toPure_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; uint8_t v___x_1303_; 
v_toApplicative_1298_ = lean_ctor_get(v_inst_1294_, 0);
v_buckets_1299_ = lean_ctor_get(v_b_1297_, 1);
lean_inc_ref(v_buckets_1299_);
lean_dec_ref(v_b_1297_);
v_toPure_1300_ = lean_ctor_get(v_toApplicative_1298_, 1);
v___x_1301_ = lean_unsigned_to_nat(0u);
v___x_1302_ = lean_array_get_size(v_buckets_1299_);
v___x_1303_ = lean_nat_dec_lt(v___x_1301_, v___x_1302_);
if (v___x_1303_ == 0)
{
lean_object* v___x_1304_; 
lean_inc(v_toPure_1300_);
lean_dec_ref(v_buckets_1299_);
lean_dec(v_f_1295_);
lean_dec_ref(v_inst_1294_);
v___x_1304_ = lean_apply_2(v_toPure_1300_, lean_box(0), v_init_1296_);
return v___x_1304_;
}
else
{
lean_object* v___f_1305_; size_t v___x_1306_; size_t v___x_1307_; lean_object* v___x_1308_; 
lean_inc_ref(v_inst_1294_);
v___f_1305_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_foldM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1305_, 0, v_inst_1294_);
lean_closure_set(v___f_1305_, 1, v_f_1295_);
v___x_1306_ = ((size_t)0ULL);
v___x_1307_ = lean_usize_of_nat(v___x_1302_);
v___x_1308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1294_, v___f_1305_, v_buckets_1299_, v___x_1306_, v___x_1307_, v_init_1296_);
return v___x_1308_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_foldM(lean_object* v_00_u03b1_1309_, lean_object* v_00_u03b2_1310_, lean_object* v_m_1311_, lean_object* v_inst_1312_, lean_object* v_00_u03b3_1313_, lean_object* v_f_1314_, lean_object* v_init_1315_, lean_object* v_b_1316_){
_start:
{
lean_object* v_toApplicative_1317_; lean_object* v_buckets_1318_; lean_object* v_toPure_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; uint8_t v___x_1322_; 
v_toApplicative_1317_ = lean_ctor_get(v_inst_1312_, 0);
v_buckets_1318_ = lean_ctor_get(v_b_1316_, 1);
lean_inc_ref(v_buckets_1318_);
lean_dec_ref(v_b_1316_);
v_toPure_1319_ = lean_ctor_get(v_toApplicative_1317_, 1);
v___x_1320_ = lean_unsigned_to_nat(0u);
v___x_1321_ = lean_array_get_size(v_buckets_1318_);
v___x_1322_ = lean_nat_dec_lt(v___x_1320_, v___x_1321_);
if (v___x_1322_ == 0)
{
lean_object* v___x_1323_; 
lean_inc(v_toPure_1319_);
lean_dec_ref(v_buckets_1318_);
lean_dec(v_f_1314_);
lean_dec_ref(v_inst_1312_);
v___x_1323_ = lean_apply_2(v_toPure_1319_, lean_box(0), v_init_1315_);
return v___x_1323_;
}
else
{
lean_object* v___f_1324_; size_t v___x_1325_; size_t v___x_1326_; lean_object* v___x_1327_; 
lean_inc_ref(v_inst_1312_);
v___f_1324_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_foldM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1324_, 0, v_inst_1312_);
lean_closure_set(v___f_1324_, 1, v_f_1314_);
v___x_1325_ = ((size_t)0ULL);
v___x_1326_ = lean_usize_of_nat(v___x_1321_);
v___x_1327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1312_, v___f_1324_, v_buckets_1318_, v___x_1325_, v___x_1326_, v_init_1315_);
return v___x_1327_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_fold___redArg___lam__0(lean_object* v_f_1328_, lean_object* v_x1_1329_, lean_object* v_x2_1330_, lean_object* v_x3_1331_){
_start:
{
lean_object* v___x_1332_; 
v___x_1332_ = lean_apply_3(v_f_1328_, v_x1_1329_, v_x2_1330_, v_x3_1331_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_fold___redArg___lam__1(lean_object* v___x_1333_, lean_object* v___f_1334_, lean_object* v_acc_1335_, lean_object* v_l_1336_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1333_, v___f_1334_, v_acc_1335_, v_l_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_fold___redArg(lean_object* v_f_1338_, lean_object* v_init_1339_, lean_object* v_b_1340_){
_start:
{
lean_object* v___x_1341_; lean_object* v_buckets_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; uint8_t v___x_1345_; 
v___x_1341_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1342_ = lean_ctor_get(v_b_1340_, 1);
lean_inc_ref(v_buckets_1342_);
lean_dec_ref(v_b_1340_);
v___x_1343_ = lean_unsigned_to_nat(0u);
v___x_1344_ = lean_array_get_size(v_buckets_1342_);
v___x_1345_ = lean_nat_dec_lt(v___x_1343_, v___x_1344_);
if (v___x_1345_ == 0)
{
lean_dec_ref(v_buckets_1342_);
lean_dec(v_f_1338_);
return v_init_1339_;
}
else
{
lean_object* v___f_1346_; lean_object* v___f_1347_; size_t v___x_1348_; size_t v___x_1349_; lean_object* v___x_1350_; 
v___f_1346_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1346_, 0, v_f_1338_);
v___f_1347_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1347_, 0, v___x_1341_);
lean_closure_set(v___f_1347_, 1, v___f_1346_);
v___x_1348_ = ((size_t)0ULL);
v___x_1349_ = lean_usize_of_nat(v___x_1344_);
v___x_1350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1341_, v___f_1347_, v_buckets_1342_, v___x_1348_, v___x_1349_, v_init_1339_);
return v___x_1350_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_fold(lean_object* v_00_u03b1_1351_, lean_object* v_00_u03b2_1352_, lean_object* v_00_u03b3_1353_, lean_object* v_f_1354_, lean_object* v_init_1355_, lean_object* v_b_1356_){
_start:
{
lean_object* v___x_1357_; lean_object* v_buckets_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; uint8_t v___x_1361_; 
v___x_1357_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1358_ = lean_ctor_get(v_b_1356_, 1);
lean_inc_ref(v_buckets_1358_);
lean_dec_ref(v_b_1356_);
v___x_1359_ = lean_unsigned_to_nat(0u);
v___x_1360_ = lean_array_get_size(v_buckets_1358_);
v___x_1361_ = lean_nat_dec_lt(v___x_1359_, v___x_1360_);
if (v___x_1361_ == 0)
{
lean_dec_ref(v_buckets_1358_);
lean_dec(v_f_1354_);
return v_init_1355_;
}
else
{
lean_object* v___f_1362_; lean_object* v___f_1363_; size_t v___x_1364_; size_t v___x_1365_; lean_object* v___x_1366_; 
v___f_1362_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1362_, 0, v_f_1354_);
v___f_1363_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1363_, 0, v___x_1357_);
lean_closure_set(v___f_1363_, 1, v___f_1362_);
v___x_1364_ = ((size_t)0ULL);
v___x_1365_ = lean_usize_of_nat(v___x_1360_);
v___x_1366_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1357_, v___f_1363_, v_buckets_1358_, v___x_1364_, v___x_1365_, v_init_1355_);
return v___x_1366_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forM___redArg___lam__0(lean_object* v_f_1367_, lean_object* v_x_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v___x_1371_; 
v___x_1371_ = lean_apply_2(v_f_1367_, v___y_1369_, v___y_1370_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forM___redArg___lam__1(lean_object* v_inst_1372_, lean_object* v___f_1373_, lean_object* v_x_1374_, lean_object* v___y_1375_){
_start:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = lean_box(0);
v___x_1377_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_1372_, v___f_1373_, v___x_1376_, v___y_1375_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forM___redArg(lean_object* v_inst_1378_, lean_object* v_f_1379_, lean_object* v_b_1380_){
_start:
{
lean_object* v_toApplicative_1381_; lean_object* v_buckets_1382_; lean_object* v_toPure_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; uint8_t v___x_1387_; 
v_toApplicative_1381_ = lean_ctor_get(v_inst_1378_, 0);
v_buckets_1382_ = lean_ctor_get(v_b_1380_, 1);
lean_inc_ref(v_buckets_1382_);
lean_dec_ref(v_b_1380_);
v_toPure_1383_ = lean_ctor_get(v_toApplicative_1381_, 1);
v___x_1384_ = lean_unsigned_to_nat(0u);
v___x_1385_ = lean_array_get_size(v_buckets_1382_);
v___x_1386_ = lean_box(0);
v___x_1387_ = lean_nat_dec_lt(v___x_1384_, v___x_1385_);
if (v___x_1387_ == 0)
{
lean_object* v___x_1388_; 
lean_inc(v_toPure_1383_);
lean_dec_ref(v_buckets_1382_);
lean_dec(v_f_1379_);
lean_dec_ref(v_inst_1378_);
v___x_1388_ = lean_apply_2(v_toPure_1383_, lean_box(0), v___x_1386_);
return v___x_1388_;
}
else
{
lean_object* v___f_1389_; lean_object* v___f_1390_; size_t v___x_1391_; size_t v___x_1392_; lean_object* v___x_1393_; 
v___f_1389_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1389_, 0, v_f_1379_);
lean_inc_ref(v_inst_1378_);
v___f_1390_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1390_, 0, v_inst_1378_);
lean_closure_set(v___f_1390_, 1, v___f_1389_);
v___x_1391_ = ((size_t)0ULL);
v___x_1392_ = lean_usize_of_nat(v___x_1385_);
v___x_1393_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1378_, v___f_1390_, v_buckets_1382_, v___x_1391_, v___x_1392_, v___x_1386_);
return v___x_1393_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forM(lean_object* v_00_u03b1_1394_, lean_object* v_00_u03b2_1395_, lean_object* v_m_1396_, lean_object* v_inst_1397_, lean_object* v_f_1398_, lean_object* v_b_1399_){
_start:
{
lean_object* v_toApplicative_1400_; lean_object* v_buckets_1401_; lean_object* v_toPure_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; uint8_t v___x_1406_; 
v_toApplicative_1400_ = lean_ctor_get(v_inst_1397_, 0);
v_buckets_1401_ = lean_ctor_get(v_b_1399_, 1);
lean_inc_ref(v_buckets_1401_);
lean_dec_ref(v_b_1399_);
v_toPure_1402_ = lean_ctor_get(v_toApplicative_1400_, 1);
v___x_1403_ = lean_unsigned_to_nat(0u);
v___x_1404_ = lean_array_get_size(v_buckets_1401_);
v___x_1405_ = lean_box(0);
v___x_1406_ = lean_nat_dec_lt(v___x_1403_, v___x_1404_);
if (v___x_1406_ == 0)
{
lean_object* v___x_1407_; 
lean_inc(v_toPure_1402_);
lean_dec_ref(v_buckets_1401_);
lean_dec(v_f_1398_);
lean_dec_ref(v_inst_1397_);
v___x_1407_ = lean_apply_2(v_toPure_1402_, lean_box(0), v___x_1405_);
return v___x_1407_;
}
else
{
lean_object* v___f_1408_; lean_object* v___f_1409_; size_t v___x_1410_; size_t v___x_1411_; lean_object* v___x_1412_; 
v___f_1408_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1408_, 0, v_f_1398_);
lean_inc_ref(v_inst_1397_);
v___f_1409_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1409_, 0, v_inst_1397_);
lean_closure_set(v___f_1409_, 1, v___f_1408_);
v___x_1410_ = ((size_t)0ULL);
v___x_1411_ = lean_usize_of_nat(v___x_1404_);
v___x_1412_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1397_, v___f_1409_, v_buckets_1401_, v___x_1410_, v___x_1411_, v___x_1405_);
return v___x_1412_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forIn___redArg___lam__0(lean_object* v_inst_1413_, lean_object* v_f_1414_, lean_object* v_a_1415_, lean_object* v_x_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v___x_1418_; 
v___x_1418_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_1413_, v_f_1414_, v_a_1415_, v___y_1417_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forIn___redArg(lean_object* v_inst_1419_, lean_object* v_f_1420_, lean_object* v_init_1421_, lean_object* v_b_1422_){
_start:
{
lean_object* v_buckets_1423_; lean_object* v___f_1424_; size_t v_sz_1425_; size_t v___x_1426_; lean_object* v___x_1427_; 
v_buckets_1423_ = lean_ctor_get(v_b_1422_, 1);
lean_inc_ref(v_buckets_1423_);
lean_dec_ref(v_b_1422_);
lean_inc_ref(v_inst_1419_);
v___f_1424_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forIn___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1424_, 0, v_inst_1419_);
lean_closure_set(v___f_1424_, 1, v_f_1420_);
v_sz_1425_ = lean_array_size(v_buckets_1423_);
v___x_1426_ = ((size_t)0ULL);
v___x_1427_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1419_, v_buckets_1423_, v___f_1424_, v_sz_1425_, v___x_1426_, v_init_1421_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forIn(lean_object* v_00_u03b1_1428_, lean_object* v_00_u03b2_1429_, lean_object* v_m_1430_, lean_object* v_inst_1431_, lean_object* v_00_u03b3_1432_, lean_object* v_f_1433_, lean_object* v_init_1434_, lean_object* v_b_1435_){
_start:
{
lean_object* v_buckets_1436_; lean_object* v___f_1437_; size_t v_sz_1438_; size_t v___x_1439_; lean_object* v___x_1440_; 
v_buckets_1436_ = lean_ctor_get(v_b_1435_, 1);
lean_inc_ref(v_buckets_1436_);
lean_dec_ref(v_b_1435_);
lean_inc_ref(v_inst_1431_);
v___f_1437_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forIn___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1437_, 0, v_inst_1431_);
lean_closure_set(v___f_1437_, 1, v_f_1433_);
v_sz_1438_ = lean_array_size(v_buckets_1436_);
v___x_1439_ = ((size_t)0ULL);
v___x_1440_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1431_, v_buckets_1436_, v___f_1437_, v_sz_1438_, v___x_1439_, v_init_1434_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__0(lean_object* v_f_1441_, lean_object* v_x_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1445_, 0, v___y_1443_);
lean_ctor_set(v___x_1445_, 1, v___y_1444_);
v___x_1446_ = lean_apply_1(v_f_1441_, v___x_1445_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__2(lean_object* v_inst_1447_, lean_object* v_m_1448_, lean_object* v_f_1449_){
_start:
{
lean_object* v_toApplicative_1450_; lean_object* v_buckets_1451_; lean_object* v_toPure_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; uint8_t v___x_1456_; 
v_toApplicative_1450_ = lean_ctor_get(v_inst_1447_, 0);
v_buckets_1451_ = lean_ctor_get(v_m_1448_, 1);
lean_inc_ref(v_buckets_1451_);
lean_dec_ref(v_m_1448_);
v_toPure_1452_ = lean_ctor_get(v_toApplicative_1450_, 1);
v___x_1453_ = lean_unsigned_to_nat(0u);
v___x_1454_ = lean_array_get_size(v_buckets_1451_);
v___x_1455_ = lean_box(0);
v___x_1456_ = lean_nat_dec_lt(v___x_1453_, v___x_1454_);
if (v___x_1456_ == 0)
{
lean_object* v___x_1457_; 
lean_inc(v_toPure_1452_);
lean_dec_ref(v_buckets_1451_);
lean_dec(v_f_1449_);
lean_dec_ref(v_inst_1447_);
v___x_1457_ = lean_apply_2(v_toPure_1452_, lean_box(0), v___x_1455_);
return v___x_1457_;
}
else
{
lean_object* v___f_1458_; lean_object* v___f_1459_; size_t v___x_1460_; size_t v___x_1461_; lean_object* v___x_1462_; 
v___f_1458_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1458_, 0, v_f_1449_);
lean_inc_ref(v_inst_1447_);
v___f_1459_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1459_, 0, v_inst_1447_);
lean_closure_set(v___f_1459_, 1, v___f_1458_);
v___x_1460_ = ((size_t)0ULL);
v___x_1461_ = lean_usize_of_nat(v___x_1454_);
v___x_1462_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1447_, v___f_1459_, v_buckets_1451_, v___x_1460_, v___x_1461_, v___x_1455_);
return v___x_1462_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad___redArg(lean_object* v_inst_1463_){
_start:
{
lean_object* v___f_1464_; 
v___f_1464_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_1464_, 0, v_inst_1463_);
return v___f_1464_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad(lean_object* v_00_u03b1_1465_, lean_object* v_00_u03b2_1466_, lean_object* v_m_1467_, lean_object* v_inst_1468_){
_start:
{
lean_object* v___f_1469_; 
v___f_1469_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_1469_, 0, v_inst_1468_);
return v___f_1469_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__0(lean_object* v_f_1470_, lean_object* v_a_1471_, lean_object* v_b_1472_, lean_object* v_acc_1473_){
_start:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1474_, 0, v_a_1471_);
lean_ctor_set(v___x_1474_, 1, v_b_1472_);
v___x_1475_ = lean_apply_2(v_f_1470_, v___x_1474_, v_acc_1473_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__1(lean_object* v_inst_1476_, lean_object* v___f_1477_, lean_object* v_a_1478_, lean_object* v_x_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v___x_1481_; 
v___x_1481_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_1476_, v___f_1477_, v_a_1478_, v___y_1480_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__2(lean_object* v_inst_1482_, lean_object* v_00_u03b2_1483_, lean_object* v_m_1484_, lean_object* v_init_1485_, lean_object* v_f_1486_){
_start:
{
lean_object* v_buckets_1487_; lean_object* v___f_1488_; lean_object* v___f_1489_; size_t v_sz_1490_; size_t v___x_1491_; lean_object* v___x_1492_; 
v_buckets_1487_ = lean_ctor_get(v_m_1484_, 1);
lean_inc_ref(v_buckets_1487_);
lean_dec_ref(v_m_1484_);
v___f_1488_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1488_, 0, v_f_1486_);
lean_inc_ref(v_inst_1482_);
v___f_1489_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1489_, 0, v_inst_1482_);
lean_closure_set(v___f_1489_, 1, v___f_1488_);
v_sz_1490_ = lean_array_size(v_buckets_1487_);
v___x_1491_ = ((size_t)0ULL);
v___x_1492_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1482_, v_buckets_1487_, v___f_1489_, v_sz_1490_, v___x_1491_, v_init_1485_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad___redArg(lean_object* v_inst_1493_){
_start:
{
lean_object* v___f_1494_; 
v___f_1494_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1494_, 0, v_inst_1493_);
return v___f_1494_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad(lean_object* v_00_u03b1_1495_, lean_object* v_00_u03b2_1496_, lean_object* v_m_1497_, lean_object* v_inst_1498_){
_start:
{
lean_object* v___f_1499_; 
v___f_1499_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1499_, 0, v_inst_1498_);
return v___f_1499_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___redArg___lam__0(lean_object* v_p_1500_, lean_object* v___x_1501_, lean_object* v___x_1502_, lean_object* v_a_1503_, lean_object* v_b_1504_, lean_object* v_acc_1505_){
_start:
{
lean_object* v___x_1506_; uint8_t v___x_1507_; 
v___x_1506_ = lean_apply_2(v_p_1500_, v_a_1503_, v_b_1504_);
v___x_1507_ = lean_unbox(v___x_1506_);
if (v___x_1507_ == 0)
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
lean_dec_ref(v___x_1502_);
v___x_1508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1506_);
v___x_1509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
lean_ctor_set(v___x_1509_, 1, v___x_1501_);
v___x_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1509_);
return v___x_1510_;
}
else
{
lean_object* v___x_1511_; 
v___x_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1502_);
return v___x_1511_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___redArg___lam__0___boxed(lean_object* v_p_1512_, lean_object* v___x_1513_, lean_object* v___x_1514_, lean_object* v_a_1515_, lean_object* v_b_1516_, lean_object* v_acc_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_Std_HashMap_Raw_all___redArg___lam__0(v_p_1512_, v___x_1513_, v___x_1514_, v_a_1515_, v_b_1516_, v_acc_1517_);
lean_dec_ref(v_acc_1517_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___redArg___lam__1(lean_object* v___x_1519_, lean_object* v___f_1520_, lean_object* v_a_1521_, lean_object* v_x_1522_, lean_object* v___y_1523_){
_start:
{
lean_object* v___x_1524_; 
v___x_1524_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1519_, v___f_1520_, v_a_1521_, v___y_1523_);
return v___x_1524_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_all___redArg(lean_object* v_m_1528_, lean_object* v_p_1529_){
_start:
{
lean_object* v___x_1530_; lean_object* v_buckets_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___f_1534_; lean_object* v___f_1535_; size_t v_sz_1536_; size_t v___x_1537_; lean_object* v___x_1538_; lean_object* v_fst_1539_; 
v___x_1530_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1531_ = lean_ctor_get(v_m_1528_, 1);
lean_inc_ref(v_buckets_1531_);
lean_dec_ref(v_m_1528_);
v___x_1532_ = lean_box(0);
v___x_1533_ = ((lean_object*)(l_Std_HashMap_Raw_all___redArg___closed__0));
v___f_1534_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1534_, 0, v_p_1529_);
lean_closure_set(v___f_1534_, 1, v___x_1532_);
lean_closure_set(v___f_1534_, 2, v___x_1533_);
v___f_1535_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1535_, 0, v___x_1530_);
lean_closure_set(v___f_1535_, 1, v___f_1534_);
v_sz_1536_ = lean_array_size(v_buckets_1531_);
v___x_1537_ = ((size_t)0ULL);
v___x_1538_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1530_, v_buckets_1531_, v___f_1535_, v_sz_1536_, v___x_1537_, v___x_1533_);
v_fst_1539_ = lean_ctor_get(v___x_1538_, 0);
lean_inc(v_fst_1539_);
lean_dec(v___x_1538_);
if (lean_obj_tag(v_fst_1539_) == 0)
{
uint8_t v___x_1540_; 
v___x_1540_ = 1;
return v___x_1540_;
}
else
{
lean_object* v_val_1541_; uint8_t v___x_1542_; 
v_val_1541_ = lean_ctor_get(v_fst_1539_, 0);
lean_inc(v_val_1541_);
lean_dec_ref_known(v_fst_1539_, 1);
v___x_1542_ = lean_unbox(v_val_1541_);
lean_dec(v_val_1541_);
return v___x_1542_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___redArg___boxed(lean_object* v_m_1543_, lean_object* v_p_1544_){
_start:
{
uint8_t v_res_1545_; lean_object* v_r_1546_; 
v_res_1545_ = l_Std_HashMap_Raw_all___redArg(v_m_1543_, v_p_1544_);
v_r_1546_ = lean_box(v_res_1545_);
return v_r_1546_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_all(lean_object* v_00_u03b1_1547_, lean_object* v_00_u03b2_1548_, lean_object* v_m_1549_, lean_object* v_p_1550_){
_start:
{
lean_object* v___x_1551_; lean_object* v_buckets_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___f_1555_; lean_object* v___f_1556_; size_t v_sz_1557_; size_t v___x_1558_; lean_object* v___x_1559_; lean_object* v_fst_1560_; 
v___x_1551_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1552_ = lean_ctor_get(v_m_1549_, 1);
lean_inc_ref(v_buckets_1552_);
lean_dec_ref(v_m_1549_);
v___x_1553_ = lean_box(0);
v___x_1554_ = ((lean_object*)(l_Std_HashMap_Raw_all___redArg___closed__0));
v___f_1555_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1555_, 0, v_p_1550_);
lean_closure_set(v___f_1555_, 1, v___x_1553_);
lean_closure_set(v___f_1555_, 2, v___x_1554_);
v___f_1556_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1556_, 0, v___x_1551_);
lean_closure_set(v___f_1556_, 1, v___f_1555_);
v_sz_1557_ = lean_array_size(v_buckets_1552_);
v___x_1558_ = ((size_t)0ULL);
v___x_1559_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1551_, v_buckets_1552_, v___f_1556_, v_sz_1557_, v___x_1558_, v___x_1554_);
v_fst_1560_ = lean_ctor_get(v___x_1559_, 0);
lean_inc(v_fst_1560_);
lean_dec(v___x_1559_);
if (lean_obj_tag(v_fst_1560_) == 0)
{
uint8_t v___x_1561_; 
v___x_1561_ = 1;
return v___x_1561_;
}
else
{
lean_object* v_val_1562_; uint8_t v___x_1563_; 
v_val_1562_ = lean_ctor_get(v_fst_1560_, 0);
lean_inc(v_val_1562_);
lean_dec_ref_known(v_fst_1560_, 1);
v___x_1563_ = lean_unbox(v_val_1562_);
lean_dec(v_val_1562_);
return v___x_1563_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___boxed(lean_object* v_00_u03b1_1564_, lean_object* v_00_u03b2_1565_, lean_object* v_m_1566_, lean_object* v_p_1567_){
_start:
{
uint8_t v_res_1568_; lean_object* v_r_1569_; 
v_res_1568_ = l_Std_HashMap_Raw_all(v_00_u03b1_1564_, v_00_u03b2_1565_, v_m_1566_, v_p_1567_);
v_r_1569_ = lean_box(v_res_1568_);
return v_r_1569_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_any___redArg___lam__0(lean_object* v_p_1570_, lean_object* v___x_1571_, lean_object* v___x_1572_, lean_object* v_a_1573_, lean_object* v_b_1574_, lean_object* v_acc_1575_){
_start:
{
lean_object* v___x_1576_; uint8_t v___x_1577_; 
v___x_1576_ = lean_apply_2(v_p_1570_, v_a_1573_, v_b_1574_);
v___x_1577_ = lean_unbox(v___x_1576_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1578_; 
v___x_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1571_);
return v___x_1578_;
}
else
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
lean_dec_ref(v___x_1571_);
v___x_1579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1576_);
v___x_1580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1579_);
lean_ctor_set(v___x_1580_, 1, v___x_1572_);
v___x_1581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1580_);
return v___x_1581_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_any___redArg___lam__0___boxed(lean_object* v_p_1582_, lean_object* v___x_1583_, lean_object* v___x_1584_, lean_object* v_a_1585_, lean_object* v_b_1586_, lean_object* v_acc_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l_Std_HashMap_Raw_any___redArg___lam__0(v_p_1582_, v___x_1583_, v___x_1584_, v_a_1585_, v_b_1586_, v_acc_1587_);
lean_dec_ref(v_acc_1587_);
return v_res_1588_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_any___redArg(lean_object* v_m_1589_, lean_object* v_p_1590_){
_start:
{
lean_object* v___x_1591_; lean_object* v_buckets_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___f_1595_; lean_object* v___f_1596_; size_t v_sz_1597_; size_t v___x_1598_; lean_object* v___x_1599_; lean_object* v_fst_1600_; 
v___x_1591_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1592_ = lean_ctor_get(v_m_1589_, 1);
lean_inc_ref(v_buckets_1592_);
lean_dec_ref(v_m_1589_);
v___x_1593_ = lean_box(0);
v___x_1594_ = ((lean_object*)(l_Std_HashMap_Raw_all___redArg___closed__0));
v___f_1595_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1595_, 0, v_p_1590_);
lean_closure_set(v___f_1595_, 1, v___x_1594_);
lean_closure_set(v___f_1595_, 2, v___x_1593_);
v___f_1596_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1596_, 0, v___x_1591_);
lean_closure_set(v___f_1596_, 1, v___f_1595_);
v_sz_1597_ = lean_array_size(v_buckets_1592_);
v___x_1598_ = ((size_t)0ULL);
v___x_1599_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1591_, v_buckets_1592_, v___f_1596_, v_sz_1597_, v___x_1598_, v___x_1594_);
v_fst_1600_ = lean_ctor_get(v___x_1599_, 0);
lean_inc(v_fst_1600_);
lean_dec(v___x_1599_);
if (lean_obj_tag(v_fst_1600_) == 0)
{
uint8_t v___x_1601_; 
v___x_1601_ = 0;
return v___x_1601_;
}
else
{
lean_object* v_val_1602_; uint8_t v___x_1603_; 
v_val_1602_ = lean_ctor_get(v_fst_1600_, 0);
lean_inc(v_val_1602_);
lean_dec_ref_known(v_fst_1600_, 1);
v___x_1603_ = lean_unbox(v_val_1602_);
lean_dec(v_val_1602_);
return v___x_1603_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_any___redArg___boxed(lean_object* v_m_1604_, lean_object* v_p_1605_){
_start:
{
uint8_t v_res_1606_; lean_object* v_r_1607_; 
v_res_1606_ = l_Std_HashMap_Raw_any___redArg(v_m_1604_, v_p_1605_);
v_r_1607_ = lean_box(v_res_1606_);
return v_r_1607_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_any(lean_object* v_00_u03b1_1608_, lean_object* v_00_u03b2_1609_, lean_object* v_m_1610_, lean_object* v_p_1611_){
_start:
{
lean_object* v___x_1612_; lean_object* v_buckets_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___f_1616_; lean_object* v___f_1617_; size_t v_sz_1618_; size_t v___x_1619_; lean_object* v___x_1620_; lean_object* v_fst_1621_; 
v___x_1612_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1613_ = lean_ctor_get(v_m_1610_, 1);
lean_inc_ref(v_buckets_1613_);
lean_dec_ref(v_m_1610_);
v___x_1614_ = lean_box(0);
v___x_1615_ = ((lean_object*)(l_Std_HashMap_Raw_all___redArg___closed__0));
v___f_1616_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1616_, 0, v_p_1611_);
lean_closure_set(v___f_1616_, 1, v___x_1615_);
lean_closure_set(v___f_1616_, 2, v___x_1614_);
v___f_1617_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1617_, 0, v___x_1612_);
lean_closure_set(v___f_1617_, 1, v___f_1616_);
v_sz_1618_ = lean_array_size(v_buckets_1613_);
v___x_1619_ = ((size_t)0ULL);
v___x_1620_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1612_, v_buckets_1613_, v___f_1617_, v_sz_1618_, v___x_1619_, v___x_1615_);
v_fst_1621_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_fst_1621_);
lean_dec(v___x_1620_);
if (lean_obj_tag(v_fst_1621_) == 0)
{
uint8_t v___x_1622_; 
v___x_1622_ = 0;
return v___x_1622_;
}
else
{
lean_object* v_val_1623_; uint8_t v___x_1624_; 
v_val_1623_ = lean_ctor_get(v_fst_1621_, 0);
lean_inc(v_val_1623_);
lean_dec_ref_known(v_fst_1621_, 1);
v___x_1624_ = lean_unbox(v_val_1623_);
lean_dec(v_val_1623_);
return v___x_1624_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_any___boxed(lean_object* v_00_u03b1_1625_, lean_object* v_00_u03b2_1626_, lean_object* v_m_1627_, lean_object* v_p_1628_){
_start:
{
uint8_t v_res_1629_; lean_object* v_r_1630_; 
v_res_1629_ = l_Std_HashMap_Raw_any(v_00_u03b1_1625_, v_00_u03b2_1626_, v_m_1627_, v_p_1628_);
v_r_1630_ = lean_box(v_res_1629_);
return v_r_1630_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_union___redArg___lam__0(lean_object* v_inst_1631_, lean_object* v_inst_1632_, lean_object* v_a_1633_, lean_object* v_b_1634_, lean_object* v_acc_1635_){
_start:
{
lean_object* v_r_1636_; lean_object* v___x_1637_; 
v_r_1636_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_1631_, v_inst_1632_, v_acc_1635_, v_a_1633_, v_b_1634_);
v___x_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1637_, 0, v_r_1636_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_union___redArg___lam__1(lean_object* v___x_1638_, lean_object* v___f_1639_, lean_object* v_a_1640_, lean_object* v_x_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1638_, v___f_1639_, v_a_1640_, v___y_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_union___redArg(lean_object* v_inst_1646_, lean_object* v_inst_1647_, lean_object* v_m_u2081_1648_, lean_object* v_m_u2082_1649_){
_start:
{
lean_object* v_size_1650_; lean_object* v_buckets_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; uint8_t v___x_1654_; 
v_size_1650_ = lean_ctor_get(v_m_u2081_1648_, 0);
v_buckets_1651_ = lean_ctor_get(v_m_u2081_1648_, 1);
v___x_1652_ = lean_unsigned_to_nat(0u);
v___x_1653_ = lean_array_get_size(v_buckets_1651_);
v___x_1654_ = lean_nat_dec_lt(v___x_1652_, v___x_1653_);
if (v___x_1654_ == 0)
{
lean_dec_ref(v_m_u2081_1648_);
lean_dec_ref(v_inst_1647_);
lean_dec_ref(v_inst_1646_);
return v_m_u2082_1649_;
}
else
{
lean_object* v_size_1655_; lean_object* v_buckets_1656_; lean_object* v___x_1657_; uint8_t v___x_1658_; 
v_size_1655_ = lean_ctor_get(v_m_u2082_1649_, 0);
v_buckets_1656_ = lean_ctor_get(v_m_u2082_1649_, 1);
v___x_1657_ = lean_array_get_size(v_buckets_1656_);
v___x_1658_ = lean_nat_dec_lt(v___x_1652_, v___x_1657_);
if (v___x_1658_ == 0)
{
lean_dec_ref(v_m_u2082_1649_);
lean_dec_ref(v_inst_1647_);
lean_dec_ref(v_inst_1646_);
return v_m_u2081_1648_;
}
else
{
lean_object* v___x_1659_; uint8_t v___x_1660_; 
v___x_1659_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_1660_ = lean_nat_dec_le(v_size_1650_, v_size_1655_);
if (v___x_1660_ == 0)
{
lean_object* v___f_1661_; lean_object* v___x_1662_; 
v___f_1661_ = ((lean_object*)(l_Std_HashMap_Raw_union___redArg___closed__0));
v___x_1662_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1661_, v_inst_1646_, v_inst_1647_, v_m_u2081_1648_, v_m_u2082_1649_);
return v___x_1662_;
}
else
{
lean_object* v___f_1663_; lean_object* v___f_1664_; size_t v_sz_1665_; size_t v___x_1666_; lean_object* v___x_1667_; 
lean_inc_ref(v_buckets_1651_);
lean_dec_ref(v_m_u2081_1648_);
v___f_1663_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1663_, 0, v_inst_1646_);
lean_closure_set(v___f_1663_, 1, v_inst_1647_);
v___f_1664_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1664_, 0, v___x_1659_);
lean_closure_set(v___f_1664_, 1, v___f_1663_);
v_sz_1665_ = lean_array_size(v_buckets_1651_);
v___x_1666_ = ((size_t)0ULL);
v___x_1667_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1659_, v_buckets_1651_, v___f_1664_, v_sz_1665_, v___x_1666_, v_m_u2082_1649_);
return v___x_1667_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_union(lean_object* v_00_u03b1_1668_, lean_object* v_00_u03b2_1669_, lean_object* v_inst_1670_, lean_object* v_inst_1671_, lean_object* v_m_u2081_1672_, lean_object* v_m_u2082_1673_){
_start:
{
lean_object* v_size_1674_; lean_object* v_buckets_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; uint8_t v___x_1678_; 
v_size_1674_ = lean_ctor_get(v_m_u2081_1672_, 0);
v_buckets_1675_ = lean_ctor_get(v_m_u2081_1672_, 1);
v___x_1676_ = lean_unsigned_to_nat(0u);
v___x_1677_ = lean_array_get_size(v_buckets_1675_);
v___x_1678_ = lean_nat_dec_lt(v___x_1676_, v___x_1677_);
if (v___x_1678_ == 0)
{
lean_dec_ref(v_m_u2081_1672_);
lean_dec_ref(v_inst_1671_);
lean_dec_ref(v_inst_1670_);
return v_m_u2082_1673_;
}
else
{
lean_object* v_size_1679_; lean_object* v_buckets_1680_; lean_object* v___x_1681_; uint8_t v___x_1682_; 
v_size_1679_ = lean_ctor_get(v_m_u2082_1673_, 0);
v_buckets_1680_ = lean_ctor_get(v_m_u2082_1673_, 1);
v___x_1681_ = lean_array_get_size(v_buckets_1680_);
v___x_1682_ = lean_nat_dec_lt(v___x_1676_, v___x_1681_);
if (v___x_1682_ == 0)
{
lean_dec_ref(v_m_u2082_1673_);
lean_dec_ref(v_inst_1671_);
lean_dec_ref(v_inst_1670_);
return v_m_u2081_1672_;
}
else
{
lean_object* v___x_1683_; uint8_t v___x_1684_; 
v___x_1683_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_1684_ = lean_nat_dec_le(v_size_1674_, v_size_1679_);
if (v___x_1684_ == 0)
{
lean_object* v___f_1685_; lean_object* v___x_1686_; 
v___f_1685_ = ((lean_object*)(l_Std_HashMap_Raw_union___redArg___closed__0));
v___x_1686_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1685_, v_inst_1670_, v_inst_1671_, v_m_u2081_1672_, v_m_u2082_1673_);
return v___x_1686_;
}
else
{
lean_object* v___f_1687_; lean_object* v___f_1688_; size_t v_sz_1689_; size_t v___x_1690_; lean_object* v___x_1691_; 
lean_inc_ref(v_buckets_1675_);
lean_dec_ref(v_m_u2081_1672_);
v___f_1687_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1687_, 0, v_inst_1670_);
lean_closure_set(v___f_1687_, 1, v_inst_1671_);
v___f_1688_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1688_, 0, v___x_1683_);
lean_closure_set(v___f_1688_, 1, v___f_1687_);
v_sz_1689_ = lean_array_size(v_buckets_1675_);
v___x_1690_ = ((size_t)0ULL);
v___x_1691_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1683_, v_buckets_1675_, v___f_1688_, v_sz_1689_, v___x_1690_, v_m_u2082_1673_);
return v___x_1691_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_inter___redArg(lean_object* v_inst_1692_, lean_object* v_inst_1693_, lean_object* v_m_u2081_1694_, lean_object* v_m_u2082_1695_){
_start:
{
lean_object* v_buckets_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; uint8_t v___x_1699_; 
v_buckets_1696_ = lean_ctor_get(v_m_u2081_1694_, 1);
v___x_1697_ = lean_unsigned_to_nat(0u);
v___x_1698_ = lean_array_get_size(v_buckets_1696_);
v___x_1699_ = lean_nat_dec_lt(v___x_1697_, v___x_1698_);
if (v___x_1699_ == 0)
{
lean_dec_ref(v_m_u2081_1694_);
lean_dec_ref(v_inst_1693_);
lean_dec_ref(v_inst_1692_);
return v_m_u2082_1695_;
}
else
{
lean_object* v_buckets_1700_; lean_object* v___x_1701_; uint8_t v___x_1702_; 
v_buckets_1700_ = lean_ctor_get(v_m_u2082_1695_, 1);
v___x_1701_ = lean_array_get_size(v_buckets_1700_);
v___x_1702_ = lean_nat_dec_lt(v___x_1697_, v___x_1701_);
if (v___x_1702_ == 0)
{
lean_dec_ref(v_m_u2082_1695_);
lean_dec_ref(v_inst_1693_);
lean_dec_ref(v_inst_1692_);
return v_m_u2081_1694_;
}
else
{
lean_object* v___x_1703_; 
v___x_1703_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1692_, v_inst_1693_, v_m_u2081_1694_, v_m_u2082_1695_);
return v___x_1703_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_inter(lean_object* v_00_u03b1_1704_, lean_object* v_00_u03b2_1705_, lean_object* v_inst_1706_, lean_object* v_inst_1707_, lean_object* v_m_u2081_1708_, lean_object* v_m_u2082_1709_){
_start:
{
lean_object* v_buckets_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; uint8_t v___x_1713_; 
v_buckets_1710_ = lean_ctor_get(v_m_u2081_1708_, 1);
v___x_1711_ = lean_unsigned_to_nat(0u);
v___x_1712_ = lean_array_get_size(v_buckets_1710_);
v___x_1713_ = lean_nat_dec_lt(v___x_1711_, v___x_1712_);
if (v___x_1713_ == 0)
{
lean_dec_ref(v_m_u2081_1708_);
lean_dec_ref(v_inst_1707_);
lean_dec_ref(v_inst_1706_);
return v_m_u2082_1709_;
}
else
{
lean_object* v_buckets_1714_; lean_object* v___x_1715_; uint8_t v___x_1716_; 
v_buckets_1714_ = lean_ctor_get(v_m_u2082_1709_, 1);
v___x_1715_ = lean_array_get_size(v_buckets_1714_);
v___x_1716_ = lean_nat_dec_lt(v___x_1711_, v___x_1715_);
if (v___x_1716_ == 0)
{
lean_dec_ref(v_m_u2082_1709_);
lean_dec_ref(v_inst_1707_);
lean_dec_ref(v_inst_1706_);
return v_m_u2081_1708_;
}
else
{
lean_object* v___x_1717_; 
v___x_1717_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1706_, v_inst_1707_, v_m_u2081_1708_, v_m_u2082_1709_);
return v___x_1717_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_diff___redArg___lam__0(lean_object* v_inst_1718_, lean_object* v_inst_1719_, lean_object* v_m_u2082_1720_, uint8_t v___x_1721_, lean_object* v_k_1722_, lean_object* v_x_1723_){
_start:
{
uint8_t v___x_1724_; 
v___x_1724_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1718_, v_inst_1719_, v_m_u2082_1720_, v_k_1722_);
if (v___x_1724_ == 0)
{
return v___x_1721_;
}
else
{
uint8_t v___x_1725_; 
v___x_1725_ = 0;
return v___x_1725_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_diff___redArg___lam__0___boxed(lean_object* v_inst_1726_, lean_object* v_inst_1727_, lean_object* v_m_u2082_1728_, lean_object* v___x_1729_, lean_object* v_k_1730_, lean_object* v_x_1731_){
_start:
{
uint8_t v___x_94__boxed_1732_; uint8_t v_res_1733_; lean_object* v_r_1734_; 
v___x_94__boxed_1732_ = lean_unbox(v___x_1729_);
v_res_1733_ = l_Std_HashMap_Raw_diff___redArg___lam__0(v_inst_1726_, v_inst_1727_, v_m_u2082_1728_, v___x_94__boxed_1732_, v_k_1730_, v_x_1731_);
lean_dec(v_x_1731_);
lean_dec_ref(v_m_u2082_1728_);
v_r_1734_ = lean_box(v_res_1733_);
return v_r_1734_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_diff___redArg(lean_object* v_inst_1735_, lean_object* v_inst_1736_, lean_object* v_m_u2081_1737_, lean_object* v_m_u2082_1738_){
_start:
{
lean_object* v_size_1739_; lean_object* v_buckets_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; uint8_t v___x_1743_; 
v_size_1739_ = lean_ctor_get(v_m_u2081_1737_, 0);
v_buckets_1740_ = lean_ctor_get(v_m_u2081_1737_, 1);
v___x_1741_ = lean_unsigned_to_nat(0u);
v___x_1742_ = lean_array_get_size(v_buckets_1740_);
v___x_1743_ = lean_nat_dec_lt(v___x_1741_, v___x_1742_);
if (v___x_1743_ == 0)
{
lean_dec_ref(v_m_u2081_1737_);
lean_dec_ref(v_inst_1736_);
lean_dec_ref(v_inst_1735_);
return v_m_u2082_1738_;
}
else
{
lean_object* v_size_1744_; lean_object* v_buckets_1745_; lean_object* v___x_1746_; uint8_t v___x_1747_; 
v_size_1744_ = lean_ctor_get(v_m_u2082_1738_, 0);
v_buckets_1745_ = lean_ctor_get(v_m_u2082_1738_, 1);
v___x_1746_ = lean_array_get_size(v_buckets_1745_);
v___x_1747_ = lean_nat_dec_lt(v___x_1741_, v___x_1746_);
if (v___x_1747_ == 0)
{
lean_dec_ref(v_m_u2082_1738_);
lean_dec_ref(v_inst_1736_);
lean_dec_ref(v_inst_1735_);
return v_m_u2081_1737_;
}
else
{
uint8_t v___x_1748_; 
v___x_1748_ = lean_nat_dec_le(v_size_1739_, v_size_1744_);
if (v___x_1748_ == 0)
{
lean_object* v___f_1749_; lean_object* v___x_1750_; 
v___f_1749_ = ((lean_object*)(l_Std_HashMap_Raw_union___redArg___closed__0));
v___x_1750_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1749_, v_inst_1735_, v_inst_1736_, v_m_u2081_1737_, v_m_u2082_1738_);
return v___x_1750_;
}
else
{
lean_object* v___x_1751_; lean_object* v___f_1752_; lean_object* v___x_1753_; 
v___x_1751_ = lean_box(v___x_1748_);
v___f_1752_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1752_, 0, v_inst_1735_);
lean_closure_set(v___f_1752_, 1, v_inst_1736_);
lean_closure_set(v___f_1752_, 2, v_m_u2082_1738_);
lean_closure_set(v___f_1752_, 3, v___x_1751_);
v___x_1753_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1752_, v_m_u2081_1737_);
return v___x_1753_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_diff(lean_object* v_00_u03b1_1754_, lean_object* v_00_u03b2_1755_, lean_object* v_inst_1756_, lean_object* v_inst_1757_, lean_object* v_m_u2081_1758_, lean_object* v_m_u2082_1759_){
_start:
{
lean_object* v_size_1760_; lean_object* v_buckets_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; uint8_t v___x_1764_; 
v_size_1760_ = lean_ctor_get(v_m_u2081_1758_, 0);
v_buckets_1761_ = lean_ctor_get(v_m_u2081_1758_, 1);
v___x_1762_ = lean_unsigned_to_nat(0u);
v___x_1763_ = lean_array_get_size(v_buckets_1761_);
v___x_1764_ = lean_nat_dec_lt(v___x_1762_, v___x_1763_);
if (v___x_1764_ == 0)
{
lean_dec_ref(v_m_u2081_1758_);
lean_dec_ref(v_inst_1757_);
lean_dec_ref(v_inst_1756_);
return v_m_u2082_1759_;
}
else
{
lean_object* v_size_1765_; lean_object* v_buckets_1766_; lean_object* v___x_1767_; uint8_t v___x_1768_; 
v_size_1765_ = lean_ctor_get(v_m_u2082_1759_, 0);
v_buckets_1766_ = lean_ctor_get(v_m_u2082_1759_, 1);
v___x_1767_ = lean_array_get_size(v_buckets_1766_);
v___x_1768_ = lean_nat_dec_lt(v___x_1762_, v___x_1767_);
if (v___x_1768_ == 0)
{
lean_dec_ref(v_m_u2082_1759_);
lean_dec_ref(v_inst_1757_);
lean_dec_ref(v_inst_1756_);
return v_m_u2081_1758_;
}
else
{
uint8_t v___x_1769_; 
v___x_1769_ = lean_nat_dec_le(v_size_1760_, v_size_1765_);
if (v___x_1769_ == 0)
{
lean_object* v___f_1770_; lean_object* v___x_1771_; 
v___f_1770_ = ((lean_object*)(l_Std_HashMap_Raw_union___redArg___closed__0));
v___x_1771_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1770_, v_inst_1756_, v_inst_1757_, v_m_u2081_1758_, v_m_u2082_1759_);
return v___x_1771_;
}
else
{
lean_object* v___x_1772_; lean_object* v___f_1773_; lean_object* v___x_1774_; 
v___x_1772_ = lean_box(v___x_1769_);
v___f_1773_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1773_, 0, v_inst_1756_);
lean_closure_set(v___f_1773_, 1, v_inst_1757_);
lean_closure_set(v___f_1773_, 2, v_m_u2082_1759_);
lean_closure_set(v___f_1773_, 3, v___x_1772_);
v___x_1774_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1773_, v_m_u2081_1758_);
return v___x_1774_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instUnionOfBEqOfHashable___redArg(lean_object* v_inst_1775_, lean_object* v_inst_1776_){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union), 6, 4);
lean_closure_set(v___x_1777_, 0, lean_box(0));
lean_closure_set(v___x_1777_, 1, lean_box(0));
lean_closure_set(v___x_1777_, 2, v_inst_1775_);
lean_closure_set(v___x_1777_, 3, v_inst_1776_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instUnionOfBEqOfHashable(lean_object* v_00_u03b1_1778_, lean_object* v_00_u03b2_1779_, lean_object* v_inst_1780_, lean_object* v_inst_1781_){
_start:
{
lean_object* v___x_1782_; 
v___x_1782_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union), 6, 4);
lean_closure_set(v___x_1782_, 0, lean_box(0));
lean_closure_set(v___x_1782_, 1, lean_box(0));
lean_closure_set(v___x_1782_, 2, v_inst_1780_);
lean_closure_set(v___x_1782_, 3, v_inst_1781_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInterOfBEqOfHashable___redArg(lean_object* v_inst_1783_, lean_object* v_inst_1784_){
_start:
{
lean_object* v___x_1785_; 
v___x_1785_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_inter), 6, 4);
lean_closure_set(v___x_1785_, 0, lean_box(0));
lean_closure_set(v___x_1785_, 1, lean_box(0));
lean_closure_set(v___x_1785_, 2, v_inst_1783_);
lean_closure_set(v___x_1785_, 3, v_inst_1784_);
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInterOfBEqOfHashable(lean_object* v_00_u03b1_1786_, lean_object* v_00_u03b2_1787_, lean_object* v_inst_1788_, lean_object* v_inst_1789_){
_start:
{
lean_object* v___x_1790_; 
v___x_1790_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_inter), 6, 4);
lean_closure_set(v___x_1790_, 0, lean_box(0));
lean_closure_set(v___x_1790_, 1, lean_box(0));
lean_closure_set(v___x_1790_, 2, v_inst_1788_);
lean_closure_set(v___x_1790_, 3, v_inst_1789_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSDiffOfBEqOfHashable___redArg(lean_object* v_inst_1791_, lean_object* v_inst_1792_){
_start:
{
lean_object* v___x_1793_; 
v___x_1793_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_diff), 6, 4);
lean_closure_set(v___x_1793_, 0, lean_box(0));
lean_closure_set(v___x_1793_, 1, lean_box(0));
lean_closure_set(v___x_1793_, 2, v_inst_1791_);
lean_closure_set(v___x_1793_, 3, v_inst_1792_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSDiffOfBEqOfHashable(lean_object* v_00_u03b1_1794_, lean_object* v_00_u03b2_1795_, lean_object* v_inst_1796_, lean_object* v_inst_1797_){
_start:
{
lean_object* v___x_1798_; 
v___x_1798_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_diff), 6, 4);
lean_closure_set(v___x_1798_, 0, lean_box(0));
lean_closure_set(v___x_1798_, 1, lean_box(0));
lean_closure_set(v___x_1798_, 2, v_inst_1796_);
lean_closure_set(v___x_1798_, 3, v_inst_1797_);
return v___x_1798_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_beq___redArg(lean_object* v_inst_1799_, lean_object* v_inst_1800_, lean_object* v_inst_1801_, lean_object* v_m_u2081_1802_, lean_object* v_m_u2082_1803_){
_start:
{
uint8_t v___x_1804_; 
v___x_1804_ = l_Std_DHashMap_Raw_Const_beq___redArg(v_inst_1799_, v_inst_1800_, v_inst_1801_, v_m_u2081_1802_, v_m_u2082_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_beq___redArg___boxed(lean_object* v_inst_1805_, lean_object* v_inst_1806_, lean_object* v_inst_1807_, lean_object* v_m_u2081_1808_, lean_object* v_m_u2082_1809_){
_start:
{
uint8_t v_res_1810_; lean_object* v_r_1811_; 
v_res_1810_ = l_Std_HashMap_Raw_beq___redArg(v_inst_1805_, v_inst_1806_, v_inst_1807_, v_m_u2081_1808_, v_m_u2082_1809_);
v_r_1811_ = lean_box(v_res_1810_);
return v_r_1811_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_beq(lean_object* v_00_u03b1_1812_, lean_object* v_00_u03b2_1813_, lean_object* v_inst_1814_, lean_object* v_inst_1815_, lean_object* v_inst_1816_, lean_object* v_m_u2081_1817_, lean_object* v_m_u2082_1818_){
_start:
{
uint8_t v___x_1819_; 
v___x_1819_ = l_Std_DHashMap_Raw_Const_beq___redArg(v_inst_1814_, v_inst_1815_, v_inst_1816_, v_m_u2081_1817_, v_m_u2082_1818_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_beq___boxed(lean_object* v_00_u03b1_1820_, lean_object* v_00_u03b2_1821_, lean_object* v_inst_1822_, lean_object* v_inst_1823_, lean_object* v_inst_1824_, lean_object* v_m_u2081_1825_, lean_object* v_m_u2082_1826_){
_start:
{
uint8_t v_res_1827_; lean_object* v_r_1828_; 
v_res_1827_ = l_Std_HashMap_Raw_beq(v_00_u03b1_1820_, v_00_u03b2_1821_, v_inst_1822_, v_inst_1823_, v_inst_1824_, v_m_u2081_1825_, v_m_u2082_1826_);
v_r_1828_ = lean_box(v_res_1827_);
return v_r_1828_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instBEqOfHashable___redArg(lean_object* v_inst_1829_, lean_object* v_inst_1830_, lean_object* v_inst_1831_){
_start:
{
lean_object* v___x_1832_; 
v___x_1832_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_beq___boxed), 7, 5);
lean_closure_set(v___x_1832_, 0, lean_box(0));
lean_closure_set(v___x_1832_, 1, lean_box(0));
lean_closure_set(v___x_1832_, 2, v_inst_1829_);
lean_closure_set(v___x_1832_, 3, v_inst_1830_);
lean_closure_set(v___x_1832_, 4, v_inst_1831_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instBEqOfHashable(lean_object* v_00_u03b1_1833_, lean_object* v_00_u03b2_1834_, lean_object* v_inst_1835_, lean_object* v_inst_1836_, lean_object* v_inst_1837_){
_start:
{
lean_object* v___x_1838_; 
v___x_1838_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_beq___boxed), 7, 5);
lean_closure_set(v___x_1838_, 0, lean_box(0));
lean_closure_set(v___x_1838_, 1, lean_box(0));
lean_closure_set(v___x_1838_, 2, v_inst_1835_);
lean_closure_set(v___x_1838_, 3, v_inst_1836_);
lean_closure_set(v___x_1838_, 4, v_inst_1837_);
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filterMap___redArg(lean_object* v_f_1839_, lean_object* v_m_1840_){
_start:
{
lean_object* v_buckets_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; uint8_t v___x_1844_; 
v_buckets_1841_ = lean_ctor_get(v_m_1840_, 1);
v___x_1842_ = lean_unsigned_to_nat(0u);
v___x_1843_ = lean_array_get_size(v_buckets_1841_);
v___x_1844_ = lean_nat_dec_lt(v___x_1842_, v___x_1843_);
if (v___x_1844_ == 0)
{
lean_object* v___x_1845_; 
lean_dec_ref(v_m_1840_);
lean_dec_ref(v_f_1839_);
v___x_1845_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1845_;
}
else
{
lean_object* v___x_1846_; 
v___x_1846_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_1839_, v_m_1840_);
return v___x_1846_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filterMap(lean_object* v_00_u03b1_1847_, lean_object* v_00_u03b2_1848_, lean_object* v_00_u03b3_1849_, lean_object* v_f_1850_, lean_object* v_m_1851_){
_start:
{
lean_object* v_buckets_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; uint8_t v___x_1855_; 
v_buckets_1852_ = lean_ctor_get(v_m_1851_, 1);
v___x_1853_ = lean_unsigned_to_nat(0u);
v___x_1854_ = lean_array_get_size(v_buckets_1852_);
v___x_1855_ = lean_nat_dec_lt(v___x_1853_, v___x_1854_);
if (v___x_1855_ == 0)
{
lean_object* v___x_1856_; 
lean_dec_ref(v_m_1851_);
lean_dec_ref(v_f_1850_);
v___x_1856_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1856_;
}
else
{
lean_object* v___x_1857_; 
v___x_1857_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_1850_, v_m_1851_);
return v___x_1857_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_map___redArg(lean_object* v_f_1858_, lean_object* v_m_1859_){
_start:
{
lean_object* v_buckets_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; uint8_t v___x_1863_; 
v_buckets_1860_ = lean_ctor_get(v_m_1859_, 1);
v___x_1861_ = lean_unsigned_to_nat(0u);
v___x_1862_ = lean_array_get_size(v_buckets_1860_);
v___x_1863_ = lean_nat_dec_lt(v___x_1861_, v___x_1862_);
if (v___x_1863_ == 0)
{
lean_object* v___x_1864_; 
lean_dec_ref(v_m_1859_);
lean_dec(v_f_1858_);
v___x_1864_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1864_;
}
else
{
lean_object* v___x_1865_; 
v___x_1865_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_1858_, v_m_1859_);
return v___x_1865_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_map(lean_object* v_00_u03b1_1866_, lean_object* v_00_u03b2_1867_, lean_object* v_00_u03b3_1868_, lean_object* v_f_1869_, lean_object* v_m_1870_){
_start:
{
lean_object* v_buckets_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; uint8_t v___x_1874_; 
v_buckets_1871_ = lean_ctor_get(v_m_1870_, 1);
v___x_1872_ = lean_unsigned_to_nat(0u);
v___x_1873_ = lean_array_get_size(v_buckets_1871_);
v___x_1874_ = lean_nat_dec_lt(v___x_1872_, v___x_1873_);
if (v___x_1874_ == 0)
{
lean_object* v___x_1875_; 
lean_dec_ref(v_m_1870_);
lean_dec(v_f_1869_);
v___x_1875_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1875_;
}
else
{
lean_object* v___x_1876_; 
v___x_1876_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_1869_, v_m_1870_);
return v___x_1876_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filter___redArg(lean_object* v_f_1877_, lean_object* v_m_1878_){
_start:
{
lean_object* v_buckets_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; uint8_t v___x_1882_; 
v_buckets_1879_ = lean_ctor_get(v_m_1878_, 1);
v___x_1880_ = lean_unsigned_to_nat(0u);
v___x_1881_ = lean_array_get_size(v_buckets_1879_);
v___x_1882_ = lean_nat_dec_lt(v___x_1880_, v___x_1881_);
if (v___x_1882_ == 0)
{
lean_object* v___x_1883_; 
lean_dec_ref(v_m_1878_);
lean_dec_ref(v_f_1877_);
v___x_1883_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1883_;
}
else
{
lean_object* v___x_1884_; 
v___x_1884_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1877_, v_m_1878_);
return v___x_1884_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filter(lean_object* v_00_u03b1_1885_, lean_object* v_00_u03b2_1886_, lean_object* v_f_1887_, lean_object* v_m_1888_){
_start:
{
lean_object* v_buckets_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; uint8_t v___x_1892_; 
v_buckets_1889_ = lean_ctor_get(v_m_1888_, 1);
v___x_1890_ = lean_unsigned_to_nat(0u);
v___x_1891_ = lean_array_get_size(v_buckets_1889_);
v___x_1892_ = lean_nat_dec_lt(v___x_1890_, v___x_1891_);
if (v___x_1892_ == 0)
{
lean_object* v___x_1893_; 
lean_dec_ref(v_m_1888_);
lean_dec_ref(v_f_1887_);
v___x_1893_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1);
return v___x_1893_;
}
else
{
lean_object* v___x_1894_; 
v___x_1894_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1887_, v_m_1888_);
return v___x_1894_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toArray___redArg___lam__0(lean_object* v_x1_1895_, lean_object* v_x2_1896_, lean_object* v_x3_1897_){
_start:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1898_, 0, v_x2_1896_);
lean_ctor_set(v___x_1898_, 1, v_x3_1897_);
v___x_1899_ = lean_array_push(v_x1_1895_, v___x_1898_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toArray___redArg___lam__1(lean_object* v___x_1900_, lean_object* v___f_1901_, lean_object* v_acc_1902_, lean_object* v_l_1903_){
_start:
{
lean_object* v___x_1904_; 
v___x_1904_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1900_, v___f_1901_, v_acc_1902_, v_l_1903_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toArray___redArg(lean_object* v_m_1909_){
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
v___x_1913_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
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
v___f_1917_ = ((lean_object*)(l_Std_HashMap_Raw_toArray___redArg___closed__1));
v___x_1918_ = ((size_t)0ULL);
v___x_1919_ = lean_usize_of_nat(v___x_1915_);
v___x_1920_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1913_, v___f_1917_, v_buckets_1911_, v___x_1918_, v___x_1919_, v___x_1912_);
return v___x_1920_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toArray(lean_object* v_00_u03b1_1921_, lean_object* v_00_u03b2_1922_, lean_object* v_m_1923_){
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
v___x_1927_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
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
v___f_1931_ = ((lean_object*)(l_Std_HashMap_Raw_toArray___redArg___closed__1));
v___x_1932_ = ((size_t)0ULL);
v___x_1933_ = lean_usize_of_nat(v___x_1929_);
v___x_1934_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1927_, v___f_1931_, v_buckets_1925_, v___x_1932_, v___x_1933_, v___x_1926_);
return v___x_1934_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray___redArg___lam__0(lean_object* v_x1_1935_, lean_object* v_x2_1936_, lean_object* v_x3_1937_){
_start:
{
lean_object* v___x_1938_; 
v___x_1938_ = lean_array_push(v_x1_1935_, v_x2_1936_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray___redArg___lam__0___boxed(lean_object* v_x1_1939_, lean_object* v_x2_1940_, lean_object* v_x3_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l_Std_HashMap_Raw_keysArray___redArg___lam__0(v_x1_1939_, v_x2_1940_, v_x3_1941_);
lean_dec(v_x3_1941_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray___redArg___lam__1(lean_object* v___x_1943_, lean_object* v___f_1944_, lean_object* v_acc_1945_, lean_object* v_l_1946_){
_start:
{
lean_object* v___x_1947_; 
v___x_1947_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1943_, v___f_1944_, v_acc_1945_, v_l_1946_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray___redArg(lean_object* v_m_1952_){
_start:
{
lean_object* v_size_1953_; lean_object* v_buckets_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; uint8_t v___x_1959_; 
v_size_1953_ = lean_ctor_get(v_m_1952_, 0);
lean_inc(v_size_1953_);
v_buckets_1954_ = lean_ctor_get(v_m_1952_, 1);
lean_inc_ref(v_buckets_1954_);
lean_dec_ref(v_m_1952_);
v___x_1955_ = lean_mk_empty_array_with_capacity(v_size_1953_);
lean_dec(v_size_1953_);
v___x_1956_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_1957_ = lean_unsigned_to_nat(0u);
v___x_1958_ = lean_array_get_size(v_buckets_1954_);
v___x_1959_ = lean_nat_dec_lt(v___x_1957_, v___x_1958_);
if (v___x_1959_ == 0)
{
lean_dec_ref(v_buckets_1954_);
return v___x_1955_;
}
else
{
lean_object* v___f_1960_; size_t v___x_1961_; size_t v___x_1962_; lean_object* v___x_1963_; 
v___f_1960_ = ((lean_object*)(l_Std_HashMap_Raw_keysArray___redArg___closed__1));
v___x_1961_ = ((size_t)0ULL);
v___x_1962_ = lean_usize_of_nat(v___x_1958_);
v___x_1963_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1956_, v___f_1960_, v_buckets_1954_, v___x_1961_, v___x_1962_, v___x_1955_);
return v___x_1963_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray(lean_object* v_00_u03b1_1964_, lean_object* v_00_u03b2_1965_, lean_object* v_m_1966_){
_start:
{
lean_object* v_size_1967_; lean_object* v_buckets_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; uint8_t v___x_1973_; 
v_size_1967_ = lean_ctor_get(v_m_1966_, 0);
lean_inc(v_size_1967_);
v_buckets_1968_ = lean_ctor_get(v_m_1966_, 1);
lean_inc_ref(v_buckets_1968_);
lean_dec_ref(v_m_1966_);
v___x_1969_ = lean_mk_empty_array_with_capacity(v_size_1967_);
lean_dec(v_size_1967_);
v___x_1970_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_1971_ = lean_unsigned_to_nat(0u);
v___x_1972_ = lean_array_get_size(v_buckets_1968_);
v___x_1973_ = lean_nat_dec_lt(v___x_1971_, v___x_1972_);
if (v___x_1973_ == 0)
{
lean_dec_ref(v_buckets_1968_);
return v___x_1969_;
}
else
{
lean_object* v___f_1974_; size_t v___x_1975_; size_t v___x_1976_; lean_object* v___x_1977_; 
v___f_1974_ = ((lean_object*)(l_Std_HashMap_Raw_keysArray___redArg___closed__1));
v___x_1975_ = ((size_t)0ULL);
v___x_1976_ = lean_usize_of_nat(v___x_1972_);
v___x_1977_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1970_, v___f_1974_, v_buckets_1968_, v___x_1975_, v___x_1976_, v___x_1969_);
return v___x_1977_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values___redArg___lam__0(lean_object* v_a_1978_, lean_object* v_b_1979_, lean_object* v_d_1980_){
_start:
{
lean_object* v___x_1981_; 
v___x_1981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1981_, 0, v_b_1979_);
lean_ctor_set(v___x_1981_, 1, v_d_1980_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values___redArg___lam__0___boxed(lean_object* v_a_1982_, lean_object* v_b_1983_, lean_object* v_d_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l_Std_HashMap_Raw_values___redArg___lam__0(v_a_1982_, v_b_1983_, v_d_1984_);
lean_dec(v_a_1982_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values___redArg(lean_object* v_m_1990_){
_start:
{
lean_object* v___x_1991_; lean_object* v_buckets_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; uint8_t v___x_1996_; 
v___x_1991_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1992_ = lean_ctor_get(v_m_1990_, 1);
lean_inc_ref(v_buckets_1992_);
lean_dec_ref(v_m_1990_);
v___x_1993_ = lean_box(0);
v___x_1994_ = lean_array_get_size(v_buckets_1992_);
v___x_1995_ = lean_unsigned_to_nat(0u);
v___x_1996_ = lean_nat_dec_lt(v___x_1995_, v___x_1994_);
if (v___x_1996_ == 0)
{
lean_dec_ref(v_buckets_1992_);
return v___x_1993_;
}
else
{
lean_object* v___f_1997_; size_t v___x_1998_; size_t v___x_1999_; lean_object* v___x_2000_; 
v___f_1997_ = ((lean_object*)(l_Std_HashMap_Raw_values___redArg___closed__1));
v___x_1998_ = lean_usize_of_nat(v___x_1994_);
v___x_1999_ = ((size_t)0ULL);
v___x_2000_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1991_, v___f_1997_, v_buckets_1992_, v___x_1998_, v___x_1999_, v___x_1993_);
return v___x_2000_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values(lean_object* v_00_u03b1_2001_, lean_object* v_00_u03b2_2002_, lean_object* v_m_2003_){
_start:
{
lean_object* v___x_2004_; lean_object* v_buckets_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; uint8_t v___x_2009_; 
v___x_2004_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_2005_ = lean_ctor_get(v_m_2003_, 1);
lean_inc_ref(v_buckets_2005_);
lean_dec_ref(v_m_2003_);
v___x_2006_ = lean_box(0);
v___x_2007_ = lean_array_get_size(v_buckets_2005_);
v___x_2008_ = lean_unsigned_to_nat(0u);
v___x_2009_ = lean_nat_dec_lt(v___x_2008_, v___x_2007_);
if (v___x_2009_ == 0)
{
lean_dec_ref(v_buckets_2005_);
return v___x_2006_;
}
else
{
lean_object* v___f_2010_; size_t v___x_2011_; size_t v___x_2012_; lean_object* v___x_2013_; 
v___f_2010_ = ((lean_object*)(l_Std_HashMap_Raw_values___redArg___closed__1));
v___x_2011_ = lean_usize_of_nat(v___x_2007_);
v___x_2012_ = ((size_t)0ULL);
v___x_2013_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2004_, v___f_2010_, v_buckets_2005_, v___x_2011_, v___x_2012_, v___x_2006_);
return v___x_2013_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesArray___redArg___lam__0(lean_object* v_x1_2014_, lean_object* v_x2_2015_, lean_object* v_x3_2016_){
_start:
{
lean_object* v___x_2017_; 
v___x_2017_ = lean_array_push(v_x1_2014_, v_x3_2016_);
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesArray___redArg___lam__0___boxed(lean_object* v_x1_2018_, lean_object* v_x2_2019_, lean_object* v_x3_2020_){
_start:
{
lean_object* v_res_2021_; 
v_res_2021_ = l_Std_HashMap_Raw_valuesArray___redArg___lam__0(v_x1_2018_, v_x2_2019_, v_x3_2020_);
lean_dec(v_x2_2019_);
return v_res_2021_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesArray___redArg(lean_object* v_m_2026_){
_start:
{
lean_object* v_size_2027_; lean_object* v_buckets_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; uint8_t v___x_2033_; 
v_size_2027_ = lean_ctor_get(v_m_2026_, 0);
lean_inc(v_size_2027_);
v_buckets_2028_ = lean_ctor_get(v_m_2026_, 1);
lean_inc_ref(v_buckets_2028_);
lean_dec_ref(v_m_2026_);
v___x_2029_ = lean_mk_empty_array_with_capacity(v_size_2027_);
lean_dec(v_size_2027_);
v___x_2030_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_2031_ = lean_unsigned_to_nat(0u);
v___x_2032_ = lean_array_get_size(v_buckets_2028_);
v___x_2033_ = lean_nat_dec_lt(v___x_2031_, v___x_2032_);
if (v___x_2033_ == 0)
{
lean_dec_ref(v_buckets_2028_);
return v___x_2029_;
}
else
{
lean_object* v___f_2034_; size_t v___x_2035_; size_t v___x_2036_; lean_object* v___x_2037_; 
v___f_2034_ = ((lean_object*)(l_Std_HashMap_Raw_valuesArray___redArg___closed__1));
v___x_2035_ = ((size_t)0ULL);
v___x_2036_ = lean_usize_of_nat(v___x_2032_);
v___x_2037_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2030_, v___f_2034_, v_buckets_2028_, v___x_2035_, v___x_2036_, v___x_2029_);
return v___x_2037_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesArray(lean_object* v_00_u03b1_2038_, lean_object* v_00_u03b2_2039_, lean_object* v_m_2040_){
_start:
{
lean_object* v_size_2041_; lean_object* v_buckets_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; uint8_t v___x_2047_; 
v_size_2041_ = lean_ctor_get(v_m_2040_, 0);
lean_inc(v_size_2041_);
v_buckets_2042_ = lean_ctor_get(v_m_2040_, 1);
lean_inc_ref(v_buckets_2042_);
lean_dec_ref(v_m_2040_);
v___x_2043_ = lean_mk_empty_array_with_capacity(v_size_2041_);
lean_dec(v_size_2041_);
v___x_2044_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_2045_ = lean_unsigned_to_nat(0u);
v___x_2046_ = lean_array_get_size(v_buckets_2042_);
v___x_2047_ = lean_nat_dec_lt(v___x_2045_, v___x_2046_);
if (v___x_2047_ == 0)
{
lean_dec_ref(v_buckets_2042_);
return v___x_2043_;
}
else
{
lean_object* v___f_2048_; size_t v___x_2049_; size_t v___x_2050_; lean_object* v___x_2051_; 
v___f_2048_ = ((lean_object*)(l_Std_HashMap_Raw_valuesArray___redArg___closed__1));
v___x_2049_ = ((size_t)0ULL);
v___x_2050_ = lean_usize_of_nat(v___x_2046_);
v___x_2051_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2044_, v___f_2048_, v_buckets_2042_, v___x_2049_, v___x_2050_, v___x_2043_);
return v___x_2051_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertMany___redArg(lean_object* v_inst_2052_, lean_object* v_inst_2053_, lean_object* v_inst_2054_, lean_object* v_m_2055_, lean_object* v_l_2056_){
_start:
{
lean_object* v_buckets_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; uint8_t v___x_2060_; 
v_buckets_2057_ = lean_ctor_get(v_m_2055_, 1);
v___x_2058_ = lean_unsigned_to_nat(0u);
v___x_2059_ = lean_array_get_size(v_buckets_2057_);
v___x_2060_ = lean_nat_dec_lt(v___x_2058_, v___x_2059_);
if (v___x_2060_ == 0)
{
lean_dec(v_l_2056_);
lean_dec(v_inst_2054_);
lean_dec_ref(v_inst_2053_);
lean_dec_ref(v_inst_2052_);
return v_m_2055_;
}
else
{
lean_object* v___x_2061_; 
v___x_2061_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v_inst_2054_, v_inst_2052_, v_inst_2053_, v_m_2055_, v_l_2056_);
return v___x_2061_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertMany(lean_object* v_00_u03b1_2062_, lean_object* v_00_u03b2_2063_, lean_object* v_inst_2064_, lean_object* v_inst_2065_, lean_object* v_00_u03c1_2066_, lean_object* v_inst_2067_, lean_object* v_m_2068_, lean_object* v_l_2069_){
_start:
{
lean_object* v_buckets_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; uint8_t v___x_2073_; 
v_buckets_2070_ = lean_ctor_get(v_m_2068_, 1);
v___x_2071_ = lean_unsigned_to_nat(0u);
v___x_2072_ = lean_array_get_size(v_buckets_2070_);
v___x_2073_ = lean_nat_dec_lt(v___x_2071_, v___x_2072_);
if (v___x_2073_ == 0)
{
lean_dec(v_l_2069_);
lean_dec(v_inst_2067_);
lean_dec_ref(v_inst_2065_);
lean_dec_ref(v_inst_2064_);
return v_m_2068_;
}
else
{
lean_object* v___x_2074_; 
v___x_2074_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v_inst_2067_, v_inst_2064_, v_inst_2065_, v_m_2068_, v_l_2069_);
return v___x_2074_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertManyIfNewUnit___redArg(lean_object* v_inst_2075_, lean_object* v_inst_2076_, lean_object* v_inst_2077_, lean_object* v_m_2078_, lean_object* v_l_2079_){
_start:
{
lean_object* v_buckets_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; uint8_t v___x_2083_; 
v_buckets_2080_ = lean_ctor_get(v_m_2078_, 1);
v___x_2081_ = lean_unsigned_to_nat(0u);
v___x_2082_ = lean_array_get_size(v_buckets_2080_);
v___x_2083_ = lean_nat_dec_lt(v___x_2081_, v___x_2082_);
if (v___x_2083_ == 0)
{
lean_dec(v_l_2079_);
lean_dec(v_inst_2077_);
lean_dec_ref(v_inst_2076_);
lean_dec_ref(v_inst_2075_);
return v_m_2078_;
}
else
{
lean_object* v___x_2084_; 
v___x_2084_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_2077_, v_inst_2075_, v_inst_2076_, v_m_2078_, v_l_2079_);
return v___x_2084_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertManyIfNewUnit(lean_object* v_00_u03b1_2085_, lean_object* v_inst_2086_, lean_object* v_inst_2087_, lean_object* v_00_u03c1_2088_, lean_object* v_inst_2089_, lean_object* v_m_2090_, lean_object* v_l_2091_){
_start:
{
lean_object* v_buckets_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; uint8_t v___x_2095_; 
v_buckets_2092_ = lean_ctor_get(v_m_2090_, 1);
v___x_2093_ = lean_unsigned_to_nat(0u);
v___x_2094_ = lean_array_get_size(v_buckets_2092_);
v___x_2095_ = lean_nat_dec_lt(v___x_2093_, v___x_2094_);
if (v___x_2095_ == 0)
{
lean_dec(v_l_2091_);
lean_dec(v_inst_2089_);
lean_dec_ref(v_inst_2087_);
lean_dec_ref(v_inst_2086_);
return v_m_2090_;
}
else
{
lean_object* v___x_2096_; 
v___x_2096_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_2089_, v_inst_2086_, v_inst_2087_, v_m_2090_, v_l_2091_);
return v___x_2096_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_unitOfArray___redArg(lean_object* v_inst_2097_, lean_object* v_inst_2098_, lean_object* v_l_2099_){
_start:
{
lean_object* v___x_2100_; uint8_t v___x_2101_; 
v___x_2100_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1);
v___x_2101_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2101_ == 0)
{
lean_dec_ref(v_l_2099_);
lean_dec_ref(v_inst_2098_);
lean_dec_ref(v_inst_2097_);
return v___x_2100_;
}
else
{
lean_object* v___f_2102_; lean_object* v___x_2103_; 
v___f_2102_ = ((lean_object*)(l_Std_HashMap_Raw_ofArray___redArg___closed__1));
v___x_2103_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2102_, v_inst_2097_, v_inst_2098_, v___x_2100_, v_l_2099_);
return v___x_2103_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_unitOfArray(lean_object* v_00_u03b1_2104_, lean_object* v_inst_2105_, lean_object* v_inst_2106_, lean_object* v_l_2107_){
_start:
{
lean_object* v___x_2108_; uint8_t v___x_2109_; 
v___x_2108_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___redArg___closed__1);
v___x_2109_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2109_ == 0)
{
lean_dec_ref(v_l_2107_);
lean_dec_ref(v_inst_2106_);
lean_dec_ref(v_inst_2105_);
return v___x_2108_;
}
else
{
lean_object* v___f_2110_; lean_object* v___x_2111_; 
v___f_2110_ = ((lean_object*)(l_Std_HashMap_Raw_ofArray___redArg___closed__1));
v___x_2111_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2110_, v_inst_2105_, v_inst_2106_, v___x_2108_, v_l_2107_);
return v___x_2111_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_Internal_numBuckets___redArg(lean_object* v_m_2112_){
_start:
{
lean_object* v___x_2113_; 
v___x_2113_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2112_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_Internal_numBuckets___redArg___boxed(lean_object* v_m_2114_){
_start:
{
lean_object* v_res_2115_; 
v_res_2115_ = l_Std_HashMap_Raw_Internal_numBuckets___redArg(v_m_2114_);
lean_dec_ref(v_m_2114_);
return v_res_2115_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_Internal_numBuckets(lean_object* v_00_u03b1_2116_, lean_object* v_00_u03b2_2117_, lean_object* v_m_2118_){
_start:
{
lean_object* v___x_2119_; 
v___x_2119_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2118_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_Internal_numBuckets___boxed(lean_object* v_00_u03b1_2120_, lean_object* v_00_u03b2_2121_, lean_object* v_m_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l_Std_HashMap_Raw_Internal_numBuckets(v_00_u03b1_2120_, v_00_u03b2_2121_, v_m_2122_);
lean_dec_ref(v_m_2122_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr___redArg___lam__2(lean_object* v___x_2127_, lean_object* v___f_2128_, lean_object* v_m_2129_, lean_object* v_prec_2130_){
_start:
{
lean_object* v___x_2131_; lean_object* v_buckets_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2152_; 
v___x_2131_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_2132_ = lean_ctor_get(v_m_2129_, 1);
v_isSharedCheck_2152_ = !lean_is_exclusive(v_m_2129_);
if (v_isSharedCheck_2152_ == 0)
{
lean_object* v_unused_2153_; 
v_unused_2153_ = lean_ctor_get(v_m_2129_, 0);
lean_dec(v_unused_2153_);
v___x_2134_ = v_m_2129_;
v_isShared_2135_ = v_isSharedCheck_2152_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_buckets_2132_);
lean_dec(v_m_2129_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2152_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2136_; lean_object* v___y_2138_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; uint8_t v___x_2147_; 
v___x_2136_ = ((lean_object*)(l_Std_HashMap_Raw_instRepr___redArg___lam__2___closed__1));
v___x_2144_ = lean_box(0);
v___x_2145_ = lean_array_get_size(v_buckets_2132_);
v___x_2146_ = lean_unsigned_to_nat(0u);
v___x_2147_ = lean_nat_dec_lt(v___x_2146_, v___x_2145_);
if (v___x_2147_ == 0)
{
lean_dec_ref(v_buckets_2132_);
lean_dec_ref(v___f_2128_);
v___y_2138_ = v___x_2144_;
goto v___jp_2137_;
}
else
{
lean_object* v___f_2148_; size_t v___x_2149_; size_t v___x_2150_; lean_object* v___x_2151_; 
v___f_2148_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_toList___redArg___lam__1), 4, 2);
lean_closure_set(v___f_2148_, 0, v___x_2131_);
lean_closure_set(v___f_2148_, 1, v___f_2128_);
v___x_2149_ = lean_usize_of_nat(v___x_2145_);
v___x_2150_ = ((size_t)0ULL);
v___x_2151_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2131_, v___f_2148_, v_buckets_2132_, v___x_2149_, v___x_2150_, v___x_2144_);
v___y_2138_ = v___x_2151_;
goto v___jp_2137_;
}
v___jp_2137_:
{
lean_object* v___x_2139_; lean_object* v___x_2141_; 
v___x_2139_ = l_List_repr___redArg(v___x_2127_, v___y_2138_);
if (v_isShared_2135_ == 0)
{
lean_ctor_set_tag(v___x_2134_, 5);
lean_ctor_set(v___x_2134_, 1, v___x_2139_);
lean_ctor_set(v___x_2134_, 0, v___x_2136_);
v___x_2141_ = v___x_2134_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2136_);
lean_ctor_set(v_reuseFailAlloc_2143_, 1, v___x_2139_);
v___x_2141_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
lean_object* v___x_2142_; 
v___x_2142_ = l_Repr_addAppParen(v___x_2141_, v_prec_2130_);
return v___x_2142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr___redArg___lam__2___boxed(lean_object* v___x_2154_, lean_object* v___f_2155_, lean_object* v_m_2156_, lean_object* v_prec_2157_){
_start:
{
lean_object* v_res_2158_; 
v_res_2158_ = l_Std_HashMap_Raw_instRepr___redArg___lam__2(v___x_2154_, v___f_2155_, v_m_2156_, v_prec_2157_);
lean_dec(v_prec_2157_);
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr___redArg(lean_object* v_inst_2159_, lean_object* v_inst_2160_){
_start:
{
lean_object* v___f_2161_; lean_object* v___f_2162_; lean_object* v___x_2163_; lean_object* v___f_2164_; 
v___f_2161_ = ((lean_object*)(l_Std_HashMap_Raw_toList___redArg___closed__0));
v___f_2162_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2162_, 0, v_inst_2160_);
v___x_2163_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_2163_, 0, lean_box(0));
lean_closure_set(v___x_2163_, 1, lean_box(0));
lean_closure_set(v___x_2163_, 2, v_inst_2159_);
lean_closure_set(v___x_2163_, 3, v___f_2162_);
v___f_2164_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instRepr___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2164_, 0, v___x_2163_);
lean_closure_set(v___f_2164_, 1, v___f_2161_);
return v___f_2164_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr(lean_object* v_00_u03b1_2165_, lean_object* v_00_u03b2_2166_, lean_object* v_inst_2167_, lean_object* v_inst_2168_){
_start:
{
lean_object* v___x_2169_; 
v___x_2169_ = l_Std_HashMap_Raw_instRepr___redArg(v_inst_2167_, v_inst_2168_);
return v___x_2169_;
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
