// Lean compiler output
// Module: Lean.LabelAttribute
// Imports: public import Lean.DocString public meta import Init.Data.String.Extra public meta import Init.Data.ToString.Name
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
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
lean_object* l_Lean_quoteNameMk(lean_object*);
lean_object* lean_string_intercalate(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkNameLit(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_String_removeLeadingSpaces(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getDocString(lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
static lean_once_cell_t l___private_Lean_LabelAttribute_0__Lean_initFn___closed__0_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LabelAttribute_0__Lean_initFn___closed__0_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_LabelAttribute_0__Lean_initFn___closed__1_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LabelAttribute_0__Lean_initFn___closed__1_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_LabelAttribute_0__Lean_initFn___closed__2_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LabelAttribute_0__Lean_initFn___closed__2_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_LabelAttribute_0__Lean_initFn_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_LabelAttribute_0__Lean_initFn_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_labelExtensionMapRef;
static const lean_string_object l_Lean_mkLabelExt___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_mkLabelExt___auto__1___closed__0 = (const lean_object*)&l_Lean_mkLabelExt___auto__1___closed__0_value;
static const lean_string_object l_Lean_mkLabelExt___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_mkLabelExt___auto__1___closed__1 = (const lean_object*)&l_Lean_mkLabelExt___auto__1___closed__1_value;
static const lean_string_object l_Lean_mkLabelExt___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_mkLabelExt___auto__1___closed__2 = (const lean_object*)&l_Lean_mkLabelExt___auto__1___closed__2_value;
static const lean_string_object l_Lean_mkLabelExt___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_mkLabelExt___auto__1___closed__3 = (const lean_object*)&l_Lean_mkLabelExt___auto__1___closed__3_value;
static const lean_ctor_object l_Lean_mkLabelExt___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_mkLabelExt___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__4_value_aux_0),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_mkLabelExt___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__4_value_aux_1),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_mkLabelExt___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__4_value_aux_2),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_mkLabelExt___auto__1___closed__4 = (const lean_object*)&l_Lean_mkLabelExt___auto__1___closed__4_value;
static const lean_array_object l_Lean_mkLabelExt___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_mkLabelExt___auto__1___closed__5 = (const lean_object*)&l_Lean_mkLabelExt___auto__1___closed__5_value;
static const lean_string_object l_Lean_mkLabelExt___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_mkLabelExt___auto__1___closed__6 = (const lean_object*)&l_Lean_mkLabelExt___auto__1___closed__6_value;
static const lean_ctor_object l_Lean_mkLabelExt___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_mkLabelExt___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__7_value_aux_0),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_mkLabelExt___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__7_value_aux_1),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_mkLabelExt___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__7_value_aux_2),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_mkLabelExt___auto__1___closed__7 = (const lean_object*)&l_Lean_mkLabelExt___auto__1___closed__7_value;
static const lean_string_object l_Lean_mkLabelExt___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_mkLabelExt___auto__1___closed__8 = (const lean_object*)&l_Lean_mkLabelExt___auto__1___closed__8_value;
static const lean_ctor_object l_Lean_mkLabelExt___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_mkLabelExt___auto__1___closed__9 = (const lean_object*)&l_Lean_mkLabelExt___auto__1___closed__9_value;
static const lean_string_object l_Lean_mkLabelExt___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Lean_mkLabelExt___auto__1___closed__10 = (const lean_object*)&l_Lean_mkLabelExt___auto__1___closed__10_value;
static const lean_ctor_object l_Lean_mkLabelExt___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_mkLabelExt___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__11_value_aux_0),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_mkLabelExt___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__11_value_aux_1),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_mkLabelExt___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__11_value_aux_2),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Lean_mkLabelExt___auto__1___closed__11 = (const lean_object*)&l_Lean_mkLabelExt___auto__1___closed__11_value;
static lean_once_cell_t l_Lean_mkLabelExt___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkLabelExt___auto__1___closed__12;
static lean_once_cell_t l_Lean_mkLabelExt___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkLabelExt___auto__1___closed__13;
static const lean_string_object l_Lean_mkLabelExt___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_mkLabelExt___auto__1___closed__14 = (const lean_object*)&l_Lean_mkLabelExt___auto__1___closed__14_value;
static const lean_string_object l_Lean_mkLabelExt___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "declName"};
static const lean_object* l_Lean_mkLabelExt___auto__1___closed__15 = (const lean_object*)&l_Lean_mkLabelExt___auto__1___closed__15_value;
static const lean_ctor_object l_Lean_mkLabelExt___auto__1___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_mkLabelExt___auto__1___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__16_value_aux_0),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_mkLabelExt___auto__1___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__16_value_aux_1),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_mkLabelExt___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__16_value_aux_2),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(113, 211, 58, 33, 138, 196, 138, 106)}};
static const lean_object* l_Lean_mkLabelExt___auto__1___closed__16 = (const lean_object*)&l_Lean_mkLabelExt___auto__1___closed__16_value;
static const lean_string_object l_Lean_mkLabelExt___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "decl_name%"};
static const lean_object* l_Lean_mkLabelExt___auto__1___closed__17 = (const lean_object*)&l_Lean_mkLabelExt___auto__1___closed__17_value;
static lean_once_cell_t l_Lean_mkLabelExt___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkLabelExt___auto__1___closed__18;
static lean_once_cell_t l_Lean_mkLabelExt___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkLabelExt___auto__1___closed__19;
static lean_once_cell_t l_Lean_mkLabelExt___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkLabelExt___auto__1___closed__20;
static lean_once_cell_t l_Lean_mkLabelExt___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkLabelExt___auto__1___closed__21;
static lean_once_cell_t l_Lean_mkLabelExt___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkLabelExt___auto__1___closed__22;
static lean_once_cell_t l_Lean_mkLabelExt___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkLabelExt___auto__1___closed__23;
static lean_once_cell_t l_Lean_mkLabelExt___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkLabelExt___auto__1___closed__24;
static lean_once_cell_t l_Lean_mkLabelExt___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkLabelExt___auto__1___closed__25;
static lean_once_cell_t l_Lean_mkLabelExt___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkLabelExt___auto__1___closed__26;
static lean_once_cell_t l_Lean_mkLabelExt___auto__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkLabelExt___auto__1___closed__27;
static lean_once_cell_t l_Lean_mkLabelExt___auto__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkLabelExt___auto__1___closed__28;
LEAN_EXPORT lean_object* l_Lean_mkLabelExt___auto__1;
LEAN_EXPORT lean_object* l_Lean_mkLabelExt___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLabelExt___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_mkLabelExt_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_mkLabelExt_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_mkLabelExt_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_mkLabelExt_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLabelExt___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLabelExt___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLabelExt___lam__2___boxed(lean_object*);
static const lean_closure_object l_Lean_mkLabelExt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkLabelExt___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_mkLabelExt___closed__0 = (const lean_object*)&l_Lean_mkLabelExt___closed__0_value;
static const lean_closure_object l_Lean_mkLabelExt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkLabelExt___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_mkLabelExt___closed__1 = (const lean_object*)&l_Lean_mkLabelExt___closed__1_value;
static const lean_closure_object l_Lean_mkLabelExt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkLabelExt___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_mkLabelExt___closed__2 = (const lean_object*)&l_Lean_mkLabelExt___closed__2_value;
static const lean_array_object l_Lean_mkLabelExt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_mkLabelExt___closed__3 = (const lean_object*)&l_Lean_mkLabelExt___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_mkLabelExt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLabelExt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLabelAttr___auto__1;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLabelAttr___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLabelAttr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_mkLabelAttr_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_mkLabelAttr_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_mkLabelAttr_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_mkLabelAttr_spec__1_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_erase___at___00Lean_mkLabelAttr_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_erase___at___00Lean_mkLabelAttr_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLabelAttr___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLabelAttr___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLabelAttr___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLabelAttr___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkLabelAttr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkLabelAttr___closed__0;
LEAN_EXPORT lean_object* l_Lean_mkLabelAttr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLabelAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerLabelAttr___auto__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerLabelAttr_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerLabelAttr_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerLabelAttr_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerLabelAttr_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerLabelAttr_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerLabelAttr_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerLabelAttr_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerLabelAttr_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerLabelAttr_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerLabelAttr_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerLabelAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerLabelAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerLabelAttr_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerLabelAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerLabelAttr_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerLabelAttr_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerLabelAttr_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerLabelAttr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerLabelAttr_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerLabelAttr_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerLabelAttr_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerLabelAttr_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Command_registerLabelAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_root_"};
static const lean_object* l_Lean_Parser_Command_registerLabelAttr___closed__0 = (const lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__0_value;
static const lean_string_object l_Lean_Parser_Command_registerLabelAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Parser_Command_registerLabelAttr___closed__1 = (const lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__1_value;
static const lean_string_object l_Lean_Parser_Command_registerLabelAttr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "registerLabelAttr"};
static const lean_object* l_Lean_Parser_Command_registerLabelAttr___closed__2 = (const lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Command_registerLabelAttr___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Command_registerLabelAttr___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__3_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(137, 219, 247, 230, 185, 4, 38, 139)}};
static const lean_ctor_object l_Lean_Parser_Command_registerLabelAttr___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__3_value_aux_1),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(204, 77, 82, 99, 253, 53, 120, 77)}};
static const lean_ctor_object l_Lean_Parser_Command_registerLabelAttr___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__3_value_aux_2),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(21, 175, 252, 253, 79, 201, 79, 236)}};
static const lean_ctor_object l_Lean_Parser_Command_registerLabelAttr___closed__3_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__3_value_aux_3),((lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(124, 1, 33, 142, 116, 70, 52, 42)}};
static const lean_ctor_object l_Lean_Parser_Command_registerLabelAttr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__3_value_aux_4),((lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(221, 58, 2, 223, 33, 1, 81, 38)}};
static const lean_object* l_Lean_Parser_Command_registerLabelAttr___closed__3 = (const lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__3_value;
static const lean_string_object l_Lean_Parser_Command_registerLabelAttr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_Parser_Command_registerLabelAttr___closed__4 = (const lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Command_registerLabelAttr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_Parser_Command_registerLabelAttr___closed__5 = (const lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__5_value;
static const lean_string_object l_Lean_Parser_Command_registerLabelAttr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l_Lean_Parser_Command_registerLabelAttr___closed__6 = (const lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Command_registerLabelAttr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__6_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l_Lean_Parser_Command_registerLabelAttr___closed__7 = (const lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__7_value;
static const lean_string_object l_Lean_Parser_Command_registerLabelAttr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Parser_Command_registerLabelAttr___closed__8 = (const lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Command_registerLabelAttr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__8_value),LEAN_SCALAR_PTR_LITERAL(229, 56, 215, 222, 243, 187, 251, 54)}};
static const lean_object* l_Lean_Parser_Command_registerLabelAttr___closed__9 = (const lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Command_registerLabelAttr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__9_value)}};
static const lean_object* l_Lean_Parser_Command_registerLabelAttr___closed__10 = (const lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Command_registerLabelAttr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__7_value),((lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__10_value)}};
static const lean_object* l_Lean_Parser_Command_registerLabelAttr___closed__11 = (const lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__11_value;
static const lean_string_object l_Lean_Parser_Command_registerLabelAttr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "register_label_attr "};
static const lean_object* l_Lean_Parser_Command_registerLabelAttr___closed__12 = (const lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__12_value;
static const lean_ctor_object l_Lean_Parser_Command_registerLabelAttr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__12_value)}};
static const lean_object* l_Lean_Parser_Command_registerLabelAttr___closed__13 = (const lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__13_value;
static const lean_ctor_object l_Lean_Parser_Command_registerLabelAttr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__5_value),((lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__11_value),((lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__13_value)}};
static const lean_object* l_Lean_Parser_Command_registerLabelAttr___closed__14 = (const lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__14_value;
static const lean_string_object l_Lean_Parser_Command_registerLabelAttr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Parser_Command_registerLabelAttr___closed__15 = (const lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__15_value;
static const lean_ctor_object l_Lean_Parser_Command_registerLabelAttr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__15_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Parser_Command_registerLabelAttr___closed__16 = (const lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__16_value;
static const lean_ctor_object l_Lean_Parser_Command_registerLabelAttr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__16_value)}};
static const lean_object* l_Lean_Parser_Command_registerLabelAttr___closed__17 = (const lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__17_value;
static const lean_ctor_object l_Lean_Parser_Command_registerLabelAttr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__5_value),((lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__14_value),((lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__17_value)}};
static const lean_object* l_Lean_Parser_Command_registerLabelAttr___closed__18 = (const lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__18_value;
static const lean_ctor_object l_Lean_Parser_Command_registerLabelAttr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__3_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__18_value)}};
static const lean_object* l_Lean_Parser_Command_registerLabelAttr___closed__19 = (const lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__19_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Command_registerLabelAttr = (const lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__19_value;
static const lean_string_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "syntax"};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__0 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__0_value;
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__1_value_aux_0),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__1_value_aux_2),((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(39, 60, 146, 133, 142, 21, 8, 39)}};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__1 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__1_value;
static const lean_string_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__2 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__2_value;
static const lean_string_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namedName"};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__3 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__3_value;
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__4_value_aux_0),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__4_value_aux_2),((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(73, 173, 122, 11, 5, 195, 101, 245)}};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__4 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__4_value;
static const lean_string_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__5 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__5_value;
static const lean_string_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__6 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__6_value;
static const lean_string_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__7 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__7_value;
static const lean_string_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__8 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__8_value;
static const lean_string_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Syntax"};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__9 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__9_value;
static const lean_string_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "atom"};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__10 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__10_value;
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__11_value_aux_0),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__11_value_aux_1),((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__11_value_aux_2),((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(144, 22, 146, 169, 39, 242, 124, 88)}};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__11 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__11_value;
static const lean_string_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "attr"};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__12 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__12_value;
static lean_once_cell_t l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__13;
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(69, 57, 207, 35, 177, 108, 73, 87)}};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__14 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__14_value;
static const lean_string_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "initializeKeyword"};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__15 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__15_value;
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__16_value_aux_0),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__16_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__16_value_aux_2),((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(113, 140, 114, 135, 71, 133, 96, 5)}};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__16 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__16_value;
static const lean_string_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ext"};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__17 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__17_value;
static lean_once_cell_t l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__18;
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(241, 12, 90, 240, 78, 252, 149, 89)}};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__19 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__19_value;
static const lean_string_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__20 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__20_value;
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__21_value_aux_0),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__21_value_aux_1),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__21_value_aux_2),((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__21 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__21_value;
static const lean_string_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__22 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__22_value;
static const lean_string_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.LabelExtension"};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__23 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__23_value;
static lean_once_cell_t l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__24;
static const lean_string_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "LabelExtension"};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__25 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__25_value;
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__26_value_aux_0),((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(213, 88, 20, 151, 146, 163, 68, 216)}};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__26 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__26_value;
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__26_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__27 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__27_value;
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__27_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__28 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__28_value;
static const lean_string_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "←"};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__29 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__29_value;
static const lean_string_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__30 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__30_value;
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__31_value_aux_0),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__31_value_aux_1),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__31_value_aux_2),((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(93, 115, 138, 230, 225, 195, 43, 46)}};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__31 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__31_value;
static const lean_string_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doSeqItem"};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__32 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__32_value;
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__33_value_aux_0),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__33_value_aux_1),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__33_value_aux_2),((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(10, 94, 50, 120, 46, 251, 13, 13)}};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__33 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__33_value;
static const lean_string_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__34 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__34_value;
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__35_value_aux_0),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__35_value_aux_1),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__35_value_aux_2),((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(130, 168, 60, 255, 153, 218, 88, 77)}};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__35 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__35_value;
static const lean_string_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__36 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__36_value;
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__37_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__37_value_aux_0),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__37_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__37_value_aux_1),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__37_value_aux_2),((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__36_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__37 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__37_value;
static lean_once_cell_t l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__38;
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(134, 185, 60, 90, 60, 63, 227, 128)}};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__39 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__39_value;
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__40_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(15, 232, 161, 166, 106, 23, 250, 115)}};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__40 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__40_value;
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__40_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__41 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__41_value;
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__41_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__42 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__42_value;
static const lean_string_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "quotedName"};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__43 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__43_value;
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__44_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__44_value_aux_0),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__44_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__44_value_aux_1),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__44_value_aux_2),((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__43_value),LEAN_SCALAR_PTR_LITERAL(217, 120, 158, 75, 195, 162, 2, 130)}};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__44 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__44_value;
static const lean_string_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__45 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__45_value;
static const lean_string_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__46 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__46_value;
static const lean_string_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "initialize"};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__47 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__47_value;
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__48_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__48_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__48_value_aux_0),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__48_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__48_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__48_value_aux_2),((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__47_value),LEAN_SCALAR_PTR_LITERAL(55, 206, 156, 211, 241, 221, 187, 166)}};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__48 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__48_value;
static const lean_string_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__49 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__49_value;
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__50_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__50_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__50_value_aux_0),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__50_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__50_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerLabelAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__50_value_aux_2),((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__49_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__50 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__50_value;
static lean_once_cell_t l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__51;
static const lean_string_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__52 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__52_value;
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__53_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkLabelExt___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(46, 201, 23, 171, 41, 77, 220, 95)}};
static const lean_ctor_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__53_value_aux_0),((lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__52_value),LEAN_SCALAR_PTR_LITERAL(10, 9, 185, 250, 127, 107, 245, 225)}};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__53 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__53_value;
static const lean_string_object l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "labelled declarations for "};
static const lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__54 = (const lean_object*)&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__54_value;
LEAN_EXPORT lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_labelled_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_labelled_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_labelled___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "No extension named "};
static const lean_object* l_Lean_labelled___closed__0 = (const lean_object*)&l_Lean_labelled___closed__0_value;
static lean_once_cell_t l_Lean_labelled___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_labelled___closed__1;
LEAN_EXPORT lean_object* l_Lean_labelled(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_labelled___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_labelled_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_labelled_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_LabelAttribute_0__Lean_initFn___closed__0_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2_(void){
_start:
{
lean_object* v_cellCount_1_; lean_object* v___x_2_; 
v_cellCount_1_ = lean_unsigned_to_nat(16u);
v___x_2_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1_);
return v___x_2_;
}
}
static lean_object* _init_l___private_Lean_LabelAttribute_0__Lean_initFn___closed__1_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2_(void){
_start:
{
lean_object* v_cellCount_3_; lean_object* v___x_4_; 
v_cellCount_3_ = lean_unsigned_to_nat(16u);
v___x_4_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_3_);
return v___x_4_;
}
}
static lean_object* _init_l___private_Lean_LabelAttribute_0__Lean_initFn___closed__2_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_5_ = lean_obj_once(&l___private_Lean_LabelAttribute_0__Lean_initFn___closed__1_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2_, &l___private_Lean_LabelAttribute_0__Lean_initFn___closed__1_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2__once, _init_l___private_Lean_LabelAttribute_0__Lean_initFn___closed__1_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2_);
v___x_6_ = lean_obj_once(&l___private_Lean_LabelAttribute_0__Lean_initFn___closed__0_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2_, &l___private_Lean_LabelAttribute_0__Lean_initFn___closed__0_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2__once, _init_l___private_Lean_LabelAttribute_0__Lean_initFn___closed__0_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2_);
v___x_7_ = lean_unsigned_to_nat(0u);
v___x_8_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
lean_ctor_set(v___x_8_, 1, v___x_6_);
lean_ctor_set(v___x_8_, 2, v___x_5_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LabelAttribute_0__Lean_initFn_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_10_ = lean_obj_once(&l___private_Lean_LabelAttribute_0__Lean_initFn___closed__2_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2_, &l___private_Lean_LabelAttribute_0__Lean_initFn___closed__2_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2__once, _init_l___private_Lean_LabelAttribute_0__Lean_initFn___closed__2_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2_);
v___x_11_ = lean_st_mk_ref(v___x_10_);
v___x_12_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_12_, 0, v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LabelAttribute_0__Lean_initFn_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2____boxed(lean_object* v_a_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l___private_Lean_LabelAttribute_0__Lean_initFn_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2_();
return v_res_14_;
}
}
static lean_object* _init_l_Lean_mkLabelExt___auto__1___closed__12(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__10));
v___x_42_ = l_Lean_mkAtom(v___x_41_);
return v___x_42_;
}
}
static lean_object* _init_l_Lean_mkLabelExt___auto__1___closed__13(void){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_43_ = lean_obj_once(&l_Lean_mkLabelExt___auto__1___closed__12, &l_Lean_mkLabelExt___auto__1___closed__12_once, _init_l_Lean_mkLabelExt___auto__1___closed__12);
v___x_44_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__5));
v___x_45_ = lean_array_push(v___x_44_, v___x_43_);
return v___x_45_;
}
}
static lean_object* _init_l_Lean_mkLabelExt___auto__1___closed__18(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__17));
v___x_55_ = l_Lean_mkAtom(v___x_54_);
return v___x_55_;
}
}
static lean_object* _init_l_Lean_mkLabelExt___auto__1___closed__19(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_56_ = lean_obj_once(&l_Lean_mkLabelExt___auto__1___closed__18, &l_Lean_mkLabelExt___auto__1___closed__18_once, _init_l_Lean_mkLabelExt___auto__1___closed__18);
v___x_57_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__5));
v___x_58_ = lean_array_push(v___x_57_, v___x_56_);
return v___x_58_;
}
}
static lean_object* _init_l_Lean_mkLabelExt___auto__1___closed__20(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_59_ = lean_obj_once(&l_Lean_mkLabelExt___auto__1___closed__19, &l_Lean_mkLabelExt___auto__1___closed__19_once, _init_l_Lean_mkLabelExt___auto__1___closed__19);
v___x_60_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__16));
v___x_61_ = lean_box(2);
v___x_62_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v___x_60_);
lean_ctor_set(v___x_62_, 2, v___x_59_);
return v___x_62_;
}
}
static lean_object* _init_l_Lean_mkLabelExt___auto__1___closed__21(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_63_ = lean_obj_once(&l_Lean_mkLabelExt___auto__1___closed__20, &l_Lean_mkLabelExt___auto__1___closed__20_once, _init_l_Lean_mkLabelExt___auto__1___closed__20);
v___x_64_ = lean_obj_once(&l_Lean_mkLabelExt___auto__1___closed__13, &l_Lean_mkLabelExt___auto__1___closed__13_once, _init_l_Lean_mkLabelExt___auto__1___closed__13);
v___x_65_ = lean_array_push(v___x_64_, v___x_63_);
return v___x_65_;
}
}
static lean_object* _init_l_Lean_mkLabelExt___auto__1___closed__22(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_66_ = lean_obj_once(&l_Lean_mkLabelExt___auto__1___closed__21, &l_Lean_mkLabelExt___auto__1___closed__21_once, _init_l_Lean_mkLabelExt___auto__1___closed__21);
v___x_67_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__11));
v___x_68_ = lean_box(2);
v___x_69_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
lean_ctor_set(v___x_69_, 1, v___x_67_);
lean_ctor_set(v___x_69_, 2, v___x_66_);
return v___x_69_;
}
}
static lean_object* _init_l_Lean_mkLabelExt___auto__1___closed__23(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_70_ = lean_obj_once(&l_Lean_mkLabelExt___auto__1___closed__22, &l_Lean_mkLabelExt___auto__1___closed__22_once, _init_l_Lean_mkLabelExt___auto__1___closed__22);
v___x_71_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__5));
v___x_72_ = lean_array_push(v___x_71_, v___x_70_);
return v___x_72_;
}
}
static lean_object* _init_l_Lean_mkLabelExt___auto__1___closed__24(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_73_ = lean_obj_once(&l_Lean_mkLabelExt___auto__1___closed__23, &l_Lean_mkLabelExt___auto__1___closed__23_once, _init_l_Lean_mkLabelExt___auto__1___closed__23);
v___x_74_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__9));
v___x_75_ = lean_box(2);
v___x_76_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
lean_ctor_set(v___x_76_, 1, v___x_74_);
lean_ctor_set(v___x_76_, 2, v___x_73_);
return v___x_76_;
}
}
static lean_object* _init_l_Lean_mkLabelExt___auto__1___closed__25(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_77_ = lean_obj_once(&l_Lean_mkLabelExt___auto__1___closed__24, &l_Lean_mkLabelExt___auto__1___closed__24_once, _init_l_Lean_mkLabelExt___auto__1___closed__24);
v___x_78_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__5));
v___x_79_ = lean_array_push(v___x_78_, v___x_77_);
return v___x_79_;
}
}
static lean_object* _init_l_Lean_mkLabelExt___auto__1___closed__26(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_80_ = lean_obj_once(&l_Lean_mkLabelExt___auto__1___closed__25, &l_Lean_mkLabelExt___auto__1___closed__25_once, _init_l_Lean_mkLabelExt___auto__1___closed__25);
v___x_81_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__7));
v___x_82_ = lean_box(2);
v___x_83_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
lean_ctor_set(v___x_83_, 1, v___x_81_);
lean_ctor_set(v___x_83_, 2, v___x_80_);
return v___x_83_;
}
}
static lean_object* _init_l_Lean_mkLabelExt___auto__1___closed__27(void){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_84_ = lean_obj_once(&l_Lean_mkLabelExt___auto__1___closed__26, &l_Lean_mkLabelExt___auto__1___closed__26_once, _init_l_Lean_mkLabelExt___auto__1___closed__26);
v___x_85_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__5));
v___x_86_ = lean_array_push(v___x_85_, v___x_84_);
return v___x_86_;
}
}
static lean_object* _init_l_Lean_mkLabelExt___auto__1___closed__28(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_87_ = lean_obj_once(&l_Lean_mkLabelExt___auto__1___closed__27, &l_Lean_mkLabelExt___auto__1___closed__27_once, _init_l_Lean_mkLabelExt___auto__1___closed__27);
v___x_88_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__4));
v___x_89_ = lean_box(2);
v___x_90_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
lean_ctor_set(v___x_90_, 1, v___x_88_);
lean_ctor_set(v___x_90_, 2, v___x_87_);
return v___x_90_;
}
}
static lean_object* _init_l_Lean_mkLabelExt___auto__1(void){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lean_obj_once(&l_Lean_mkLabelExt___auto__1___closed__28, &l_Lean_mkLabelExt___auto__1___closed__28_once, _init_l_Lean_mkLabelExt___auto__1___closed__28);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelExt___lam__0(lean_object* v_x_92_, lean_object* v_a_93_){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_94_, 0, v_a_93_);
lean_inc_ref_n(v___x_94_, 2);
v___x_95_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
lean_ctor_set(v___x_95_, 1, v___x_94_);
lean_ctor_set(v___x_95_, 2, v___x_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelExt___lam__0___boxed(lean_object* v_x_96_, lean_object* v_a_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lean_mkLabelExt___lam__0(v_x_96_, v_a_97_);
lean_dec_ref(v_x_96_);
return v_res_98_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_mkLabelExt_spec__0_spec__0(lean_object* v_a_99_, lean_object* v_as_100_, size_t v_i_101_, size_t v_stop_102_){
_start:
{
uint8_t v___x_103_; 
v___x_103_ = lean_usize_dec_eq(v_i_101_, v_stop_102_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_104_ = lean_array_uget_borrowed(v_as_100_, v_i_101_);
v___x_105_ = lean_name_eq(v_a_99_, v___x_104_);
if (v___x_105_ == 0)
{
size_t v___x_106_; size_t v___x_107_; 
v___x_106_ = ((size_t)1ULL);
v___x_107_ = lean_usize_add(v_i_101_, v___x_106_);
v_i_101_ = v___x_107_;
goto _start;
}
else
{
return v___x_105_;
}
}
else
{
uint8_t v___x_109_; 
v___x_109_ = 0;
return v___x_109_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_mkLabelExt_spec__0_spec__0___boxed(lean_object* v_a_110_, lean_object* v_as_111_, lean_object* v_i_112_, lean_object* v_stop_113_){
_start:
{
size_t v_i_boxed_114_; size_t v_stop_boxed_115_; uint8_t v_res_116_; lean_object* v_r_117_; 
v_i_boxed_114_ = lean_unbox_usize(v_i_112_);
lean_dec(v_i_112_);
v_stop_boxed_115_ = lean_unbox_usize(v_stop_113_);
lean_dec(v_stop_113_);
v_res_116_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_mkLabelExt_spec__0_spec__0(v_a_110_, v_as_111_, v_i_boxed_114_, v_stop_boxed_115_);
lean_dec_ref(v_as_111_);
lean_dec(v_a_110_);
v_r_117_ = lean_box(v_res_116_);
return v_r_117_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_mkLabelExt_spec__0(lean_object* v_as_118_, lean_object* v_a_119_){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_120_ = lean_unsigned_to_nat(0u);
v___x_121_ = lean_array_get_size(v_as_118_);
v___x_122_ = lean_nat_dec_lt(v___x_120_, v___x_121_);
if (v___x_122_ == 0)
{
return v___x_122_;
}
else
{
if (v___x_122_ == 0)
{
return v___x_122_;
}
else
{
size_t v___x_123_; size_t v___x_124_; uint8_t v___x_125_; 
v___x_123_ = ((size_t)0ULL);
v___x_124_ = lean_usize_of_nat(v___x_121_);
v___x_125_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_mkLabelExt_spec__0_spec__0(v_a_119_, v_as_118_, v___x_123_, v___x_124_);
return v___x_125_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_mkLabelExt_spec__0___boxed(lean_object* v_as_126_, lean_object* v_a_127_){
_start:
{
uint8_t v_res_128_; lean_object* v_r_129_; 
v_res_128_ = l_Array_contains___at___00Lean_mkLabelExt_spec__0(v_as_126_, v_a_127_);
lean_dec(v_a_127_);
lean_dec_ref(v_as_126_);
v_r_129_ = lean_box(v_res_128_);
return v_r_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelExt___lam__1(lean_object* v_d_130_, lean_object* v_e_131_){
_start:
{
uint8_t v___x_132_; 
v___x_132_ = l_Array_contains___at___00Lean_mkLabelExt_spec__0(v_d_130_, v_e_131_);
if (v___x_132_ == 0)
{
lean_object* v___x_133_; 
v___x_133_ = lean_array_push(v_d_130_, v_e_131_);
return v___x_133_;
}
else
{
lean_dec(v_e_131_);
return v_d_130_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelExt___lam__2(lean_object* v___y_134_){
_start:
{
lean_inc_ref(v___y_134_);
return v___y_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelExt___lam__2___boxed(lean_object* v___y_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Lean_mkLabelExt___lam__2(v___y_135_);
lean_dec_ref(v___y_135_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelExt(lean_object* v_name_142_){
_start:
{
lean_object* v___f_144_; lean_object* v___f_145_; lean_object* v___f_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___f_144_ = ((lean_object*)(l_Lean_mkLabelExt___closed__0));
v___f_145_ = ((lean_object*)(l_Lean_mkLabelExt___closed__1));
v___f_146_ = ((lean_object*)(l_Lean_mkLabelExt___closed__2));
v___x_147_ = ((lean_object*)(l_Lean_mkLabelExt___closed__3));
v___x_148_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_148_, 0, v_name_142_);
lean_ctor_set(v___x_148_, 1, v___f_145_);
lean_ctor_set(v___x_148_, 2, v___x_147_);
lean_ctor_set(v___x_148_, 3, v___f_146_);
lean_ctor_set(v___x_148_, 4, v___f_144_);
v___x_149_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelExt___boxed(lean_object* v_name_150_, lean_object* v_a_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Lean_mkLabelExt(v_name_150_);
return v_res_152_;
}
}
static lean_object* _init_l_Lean_mkLabelAttr___auto__1(void){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = lean_obj_once(&l_Lean_mkLabelExt___auto__1___closed__28, &l_Lean_mkLabelExt___auto__1___closed__28_once, _init_l_Lean_mkLabelExt___auto__1___closed__28);
return v___x_153_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_154_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__0);
v___x_156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
return v___x_156_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__1);
v___x_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
lean_ctor_set(v___x_158_, 1, v___x_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg(lean_object* v_ext_159_, lean_object* v_b_160_, uint8_t v_kind_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
lean_object* v_currNamespace_165_; lean_object* v___x_166_; lean_object* v_env_167_; lean_object* v_nextMacroScope_168_; lean_object* v_ngen_169_; lean_object* v_auxDeclNGen_170_; lean_object* v_traceState_171_; lean_object* v_messages_172_; lean_object* v_infoState_173_; lean_object* v_snapshotTasks_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_186_; 
v_currNamespace_165_ = lean_ctor_get(v___y_162_, 6);
v___x_166_ = lean_st_ref_take(v___y_163_);
v_env_167_ = lean_ctor_get(v___x_166_, 0);
v_nextMacroScope_168_ = lean_ctor_get(v___x_166_, 1);
v_ngen_169_ = lean_ctor_get(v___x_166_, 2);
v_auxDeclNGen_170_ = lean_ctor_get(v___x_166_, 3);
v_traceState_171_ = lean_ctor_get(v___x_166_, 4);
v_messages_172_ = lean_ctor_get(v___x_166_, 6);
v_infoState_173_ = lean_ctor_get(v___x_166_, 7);
v_snapshotTasks_174_ = lean_ctor_get(v___x_166_, 8);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_186_ == 0)
{
lean_object* v_unused_187_; 
v_unused_187_ = lean_ctor_get(v___x_166_, 5);
lean_dec(v_unused_187_);
v___x_176_ = v___x_166_;
v_isShared_177_ = v_isSharedCheck_186_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_snapshotTasks_174_);
lean_inc(v_infoState_173_);
lean_inc(v_messages_172_);
lean_inc(v_traceState_171_);
lean_inc(v_auxDeclNGen_170_);
lean_inc(v_ngen_169_);
lean_inc(v_nextMacroScope_168_);
lean_inc(v_env_167_);
lean_dec(v___x_166_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_186_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_181_; 
lean_inc(v_currNamespace_165_);
v___x_178_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_167_, v_ext_159_, v_b_160_, v_kind_161_, v_currNamespace_165_);
v___x_179_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__2);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 5, v___x_179_);
lean_ctor_set(v___x_176_, 0, v___x_178_);
v___x_181_ = v___x_176_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v___x_178_);
lean_ctor_set(v_reuseFailAlloc_185_, 1, v_nextMacroScope_168_);
lean_ctor_set(v_reuseFailAlloc_185_, 2, v_ngen_169_);
lean_ctor_set(v_reuseFailAlloc_185_, 3, v_auxDeclNGen_170_);
lean_ctor_set(v_reuseFailAlloc_185_, 4, v_traceState_171_);
lean_ctor_set(v_reuseFailAlloc_185_, 5, v___x_179_);
lean_ctor_set(v_reuseFailAlloc_185_, 6, v_messages_172_);
lean_ctor_set(v_reuseFailAlloc_185_, 7, v_infoState_173_);
lean_ctor_set(v_reuseFailAlloc_185_, 8, v_snapshotTasks_174_);
v___x_181_ = v_reuseFailAlloc_185_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_182_ = lean_st_ref_put(v___y_163_, v___x_181_);
v___x_183_ = lean_box(0);
v___x_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
return v___x_184_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___boxed(lean_object* v_ext_188_, lean_object* v_b_189_, lean_object* v_kind_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
uint8_t v_kind_boxed_194_; lean_object* v_res_195_; 
v_kind_boxed_194_ = lean_unbox(v_kind_190_);
v_res_195_ = l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg(v_ext_188_, v_b_189_, v_kind_boxed_194_, v___y_191_, v___y_192_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0(lean_object* v_00_u03b1_196_, lean_object* v_00_u03b2_197_, lean_object* v_00_u03c3_198_, lean_object* v_ext_199_, lean_object* v_b_200_, uint8_t v_kind_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg(v_ext_199_, v_b_200_, v_kind_201_, v___y_202_, v___y_203_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___boxed(lean_object* v_00_u03b1_206_, lean_object* v_00_u03b2_207_, lean_object* v_00_u03c3_208_, lean_object* v_ext_209_, lean_object* v_b_210_, lean_object* v_kind_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
uint8_t v_kind_boxed_215_; lean_object* v_res_216_; 
v_kind_boxed_215_ = lean_unbox(v_kind_211_);
v_res_216_ = l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0(v_00_u03b1_206_, v_00_u03b2_207_, v_00_u03c3_208_, v_ext_209_, v_b_210_, v_kind_boxed_215_, v___y_212_, v___y_213_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelAttr___lam__0(lean_object* v_ext_217_, lean_object* v_declName_218_, lean_object* v_x_219_, uint8_t v_kind_220_, lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg(v_ext_217_, v_declName_218_, v_kind_220_, v___y_221_, v___y_222_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelAttr___lam__0___boxed(lean_object* v_ext_225_, lean_object* v_declName_226_, lean_object* v_x_227_, lean_object* v_kind_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
uint8_t v_kind_boxed_232_; lean_object* v_res_233_; 
v_kind_boxed_232_ = lean_unbox(v_kind_228_);
v_res_233_ = l_Lean_mkLabelAttr___lam__0(v_ext_225_, v_declName_226_, v_x_227_, v_kind_boxed_232_, v___y_229_, v___y_230_);
lean_dec(v___y_230_);
lean_dec_ref(v___y_229_);
lean_dec(v_x_227_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_mkLabelAttr_spec__1_spec__1_spec__2(lean_object* v_xs_234_, lean_object* v_v_235_, lean_object* v_i_236_){
_start:
{
lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_237_ = lean_array_get_size(v_xs_234_);
v___x_238_ = lean_nat_dec_lt(v_i_236_, v___x_237_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; 
lean_dec(v_i_236_);
v___x_239_ = lean_box(0);
return v___x_239_;
}
else
{
lean_object* v___x_240_; uint8_t v___x_241_; 
v___x_240_ = lean_array_fget_borrowed(v_xs_234_, v_i_236_);
v___x_241_ = lean_name_eq(v___x_240_, v_v_235_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = lean_unsigned_to_nat(1u);
v___x_243_ = lean_nat_add(v_i_236_, v___x_242_);
lean_dec(v_i_236_);
v_i_236_ = v___x_243_;
goto _start;
}
else
{
lean_object* v___x_245_; 
v___x_245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_245_, 0, v_i_236_);
return v___x_245_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_mkLabelAttr_spec__1_spec__1_spec__2___boxed(lean_object* v_xs_246_, lean_object* v_v_247_, lean_object* v_i_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_mkLabelAttr_spec__1_spec__1_spec__2(v_xs_246_, v_v_247_, v_i_248_);
lean_dec(v_v_247_);
lean_dec_ref(v_xs_246_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_mkLabelAttr_spec__1_spec__1(lean_object* v_xs_250_, lean_object* v_v_251_){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = lean_unsigned_to_nat(0u);
v___x_253_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_mkLabelAttr_spec__1_spec__1_spec__2(v_xs_250_, v_v_251_, v___x_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_mkLabelAttr_spec__1_spec__1___boxed(lean_object* v_xs_254_, lean_object* v_v_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_mkLabelAttr_spec__1_spec__1(v_xs_254_, v_v_255_);
lean_dec(v_v_255_);
lean_dec_ref(v_xs_254_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Array_erase___at___00Lean_mkLabelAttr_spec__1(lean_object* v_as_257_, lean_object* v_a_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l_Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_mkLabelAttr_spec__1_spec__1(v_as_257_, v_a_258_);
if (lean_obj_tag(v___x_259_) == 0)
{
return v_as_257_;
}
else
{
lean_object* v_val_260_; lean_object* v___x_261_; 
v_val_260_ = lean_ctor_get(v___x_259_, 0);
lean_inc(v_val_260_);
lean_dec_ref_known(v___x_259_, 1);
v___x_261_ = l_Array_eraseIdx___redArg(v_as_257_, v_val_260_);
return v___x_261_;
}
}
}
LEAN_EXPORT lean_object* l_Array_erase___at___00Lean_mkLabelAttr_spec__1___boxed(lean_object* v_as_262_, lean_object* v_a_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Array_erase___at___00Lean_mkLabelAttr_spec__1(v_as_262_, v_a_263_);
lean_dec(v_a_263_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelAttr___lam__1(lean_object* v___x_265_, lean_object* v_declName_266_, lean_object* v_x_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Array_erase___at___00Lean_mkLabelAttr_spec__1(v___x_265_, v_declName_266_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelAttr___lam__1___boxed(lean_object* v___x_269_, lean_object* v_declName_270_, lean_object* v_x_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_mkLabelAttr___lam__1(v___x_269_, v_declName_270_, v_x_271_);
lean_dec_ref(v_x_271_);
lean_dec(v_declName_270_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelAttr___lam__2(lean_object* v_ext_273_, lean_object* v___x_274_, lean_object* v_declName_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v_ext_281_; lean_object* v_toEnvExtension_282_; lean_object* v_env_283_; lean_object* v_asyncMode_284_; lean_object* v_env_285_; lean_object* v_nextMacroScope_286_; lean_object* v_ngen_287_; lean_object* v_auxDeclNGen_288_; lean_object* v_traceState_289_; lean_object* v_messages_290_; lean_object* v_infoState_291_; lean_object* v_snapshotTasks_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_306_; 
v___x_279_ = lean_st_ref_get(v___y_277_);
v___x_280_ = lean_st_ref_take(v___y_277_);
v_ext_281_ = lean_ctor_get(v_ext_273_, 1);
v_toEnvExtension_282_ = lean_ctor_get(v_ext_281_, 0);
v_env_283_ = lean_ctor_get(v___x_279_, 0);
lean_inc_ref(v_env_283_);
lean_dec(v___x_279_);
v_asyncMode_284_ = lean_ctor_get(v_toEnvExtension_282_, 2);
v_env_285_ = lean_ctor_get(v___x_280_, 0);
v_nextMacroScope_286_ = lean_ctor_get(v___x_280_, 1);
v_ngen_287_ = lean_ctor_get(v___x_280_, 2);
v_auxDeclNGen_288_ = lean_ctor_get(v___x_280_, 3);
v_traceState_289_ = lean_ctor_get(v___x_280_, 4);
v_messages_290_ = lean_ctor_get(v___x_280_, 6);
v_infoState_291_ = lean_ctor_get(v___x_280_, 7);
v_snapshotTasks_292_ = lean_ctor_get(v___x_280_, 8);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_306_ == 0)
{
lean_object* v_unused_307_; 
v_unused_307_ = lean_ctor_get(v___x_280_, 5);
lean_dec(v_unused_307_);
v___x_294_ = v___x_280_;
v_isShared_295_ = v_isSharedCheck_306_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_snapshotTasks_292_);
lean_inc(v_infoState_291_);
lean_inc(v_messages_290_);
lean_inc(v_traceState_289_);
lean_inc(v_auxDeclNGen_288_);
lean_inc(v_ngen_287_);
lean_inc(v_nextMacroScope_286_);
lean_inc(v_env_285_);
lean_dec(v___x_280_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_306_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_296_; lean_object* v___f_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_301_; 
v___x_296_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_274_, v_ext_273_, v_env_283_, v_asyncMode_284_);
v___f_297_ = lean_alloc_closure((void*)(l_Lean_mkLabelAttr___lam__1___boxed), 3, 2);
lean_closure_set(v___f_297_, 0, v___x_296_);
lean_closure_set(v___f_297_, 1, v_declName_275_);
v___x_298_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_273_, v_env_285_, v___f_297_);
v___x_299_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__2);
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 5, v___x_299_);
lean_ctor_set(v___x_294_, 0, v___x_298_);
v___x_301_ = v___x_294_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v___x_298_);
lean_ctor_set(v_reuseFailAlloc_305_, 1, v_nextMacroScope_286_);
lean_ctor_set(v_reuseFailAlloc_305_, 2, v_ngen_287_);
lean_ctor_set(v_reuseFailAlloc_305_, 3, v_auxDeclNGen_288_);
lean_ctor_set(v_reuseFailAlloc_305_, 4, v_traceState_289_);
lean_ctor_set(v_reuseFailAlloc_305_, 5, v___x_299_);
lean_ctor_set(v_reuseFailAlloc_305_, 6, v_messages_290_);
lean_ctor_set(v_reuseFailAlloc_305_, 7, v_infoState_291_);
lean_ctor_set(v_reuseFailAlloc_305_, 8, v_snapshotTasks_292_);
v___x_301_ = v_reuseFailAlloc_305_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_302_ = lean_st_ref_put(v___y_277_, v___x_301_);
v___x_303_ = lean_box(0);
v___x_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
return v___x_304_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelAttr___lam__2___boxed(lean_object* v_ext_308_, lean_object* v___x_309_, lean_object* v_declName_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Lean_mkLabelAttr___lam__2(v_ext_308_, v___x_309_, v_declName_310_, v___y_311_, v___y_312_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
lean_dec_ref(v___x_309_);
return v_res_314_;
}
}
static lean_object* _init_l_Lean_mkLabelAttr___closed__0(void){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Array_instInhabited(lean_box(0));
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelAttr(lean_object* v_attrName_316_, lean_object* v_attrDescr_317_, lean_object* v_ext_318_, lean_object* v_ref_319_){
_start:
{
lean_object* v___f_321_; lean_object* v___x_322_; lean_object* v___f_323_; uint8_t v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
lean_inc_ref(v_ext_318_);
v___f_321_ = lean_alloc_closure((void*)(l_Lean_mkLabelAttr___lam__0___boxed), 7, 1);
lean_closure_set(v___f_321_, 0, v_ext_318_);
v___x_322_ = lean_obj_once(&l_Lean_mkLabelAttr___closed__0, &l_Lean_mkLabelAttr___closed__0_once, _init_l_Lean_mkLabelAttr___closed__0);
v___f_323_ = lean_alloc_closure((void*)(l_Lean_mkLabelAttr___lam__2___boxed), 6, 2);
lean_closure_set(v___f_323_, 0, v_ext_318_);
lean_closure_set(v___f_323_, 1, v___x_322_);
v___x_324_ = 1;
v___x_325_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_325_, 0, v_ref_319_);
lean_ctor_set(v___x_325_, 1, v_attrName_316_);
lean_ctor_set(v___x_325_, 2, v_attrDescr_317_);
lean_ctor_set_uint8(v___x_325_, sizeof(void*)*3, v___x_324_);
v___x_326_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
lean_ctor_set(v___x_326_, 1, v___f_321_);
lean_ctor_set(v___x_326_, 2, v___f_323_);
v___x_327_ = l_Lean_registerBuiltinAttribute(v___x_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelAttr___boxed(lean_object* v_attrName_328_, lean_object* v_attrDescr_329_, lean_object* v_ext_330_, lean_object* v_ref_331_, lean_object* v_a_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_mkLabelAttr(v_attrName_328_, v_attrDescr_329_, v_ext_330_, v_ref_331_);
return v_res_333_;
}
}
static lean_object* _init_l_Lean_registerLabelAttr___auto__1(void){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = lean_obj_once(&l_Lean_mkLabelExt___auto__1___closed__28, &l_Lean_mkLabelExt___auto__1___closed__28_once, _init_l_Lean_mkLabelExt___auto__1___closed__28);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerLabelAttr_spec__0_spec__0___redArg(lean_object* v_m_335_, lean_object* v_query_336_, lean_object* v_x_337_, lean_object* v_x_338_, lean_object* v_x_339_){
_start:
{
lean_object* v_zero_340_; uint8_t v_isZero_341_; 
v_zero_340_ = lean_unsigned_to_nat(0u);
v_isZero_341_ = lean_nat_dec_eq(v_x_338_, v_zero_340_);
if (v_isZero_341_ == 1)
{
lean_dec(v_x_339_);
lean_dec(v_x_338_);
if (lean_obj_tag(v_x_337_) == 0)
{
lean_object* v___x_342_; 
v___x_342_ = lean_box(2);
return v___x_342_;
}
else
{
lean_object* v_val_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_350_; 
v_val_343_ = lean_ctor_get(v_x_337_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v_x_337_);
if (v_isSharedCheck_350_ == 0)
{
v___x_345_ = v_x_337_;
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_val_343_);
lean_dec(v_x_337_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_348_; 
if (v_isShared_346_ == 0)
{
v___x_348_ = v___x_345_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_val_343_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
else
{
lean_object* v_keyArray_351_; lean_object* v_valueArray_352_; lean_object* v___x_353_; uint8_t v_isSome_354_; 
v_keyArray_351_ = lean_ctor_get(v_m_335_, 1);
v_valueArray_352_ = lean_ctor_get(v_m_335_, 2);
v___x_353_ = lean_array_fget_borrowed(v_keyArray_351_, v_x_339_);
v_isSome_354_ = lean_noption_is_some(v___x_353_);
if (v_isSome_354_ == 0)
{
lean_dec(v_x_338_);
if (lean_obj_tag(v_x_337_) == 0)
{
lean_object* v___x_355_; 
v___x_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_355_, 0, v_x_339_);
return v___x_355_;
}
else
{
lean_object* v_val_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_363_; 
lean_dec(v_x_339_);
v_val_356_ = lean_ctor_get(v_x_337_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v_x_337_);
if (v_isSharedCheck_363_ == 0)
{
v___x_358_ = v_x_337_;
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_val_356_);
lean_dec(v_x_337_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_361_; 
if (v_isShared_359_ == 0)
{
v___x_361_ = v___x_358_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_val_356_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
}
else
{
lean_object* v_one_364_; lean_object* v_n_365_; lean_object* v___y_367_; 
v_one_364_ = lean_unsigned_to_nat(1u);
v_n_365_ = lean_nat_sub(v_x_338_, v_one_364_);
lean_dec(v_x_338_);
if (v_isSome_354_ == 0)
{
goto v___jp_373_;
}
else
{
lean_object* v___x_375_; uint8_t v_isSome_376_; 
v___x_375_ = lean_array_fget_borrowed(v_valueArray_352_, v_x_339_);
v_isSome_376_ = lean_noption_is_some(v___x_375_);
if (v_isSome_376_ == 0)
{
goto v___jp_373_;
}
else
{
lean_object* v_val_377_; uint8_t v___x_378_; 
lean_inc(v___x_353_);
v_val_377_ = lean_noption_get(v___x_353_);
v___x_378_ = lean_name_eq(v_val_377_, v_query_336_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; lean_object* v___x_380_; uint8_t v___x_381_; 
lean_dec(v_val_377_);
v___x_379_ = lean_array_get_size(v_keyArray_351_);
v___x_380_ = lean_nat_add(v_x_339_, v_one_364_);
lean_dec(v_x_339_);
v___x_381_ = lean_nat_dec_lt(v___x_380_, v___x_379_);
if (v___x_381_ == 0)
{
lean_dec(v___x_380_);
v_x_338_ = v_n_365_;
v_x_339_ = v_zero_340_;
goto _start;
}
else
{
v_x_338_ = v_n_365_;
v_x_339_ = v___x_380_;
goto _start;
}
}
else
{
lean_object* v_val_384_; lean_object* v___x_385_; 
lean_dec(v_n_365_);
lean_dec(v_x_337_);
lean_inc(v___x_375_);
v_val_384_ = lean_noption_get(v___x_375_);
v___x_385_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_385_, 0, v_x_339_);
lean_ctor_set(v___x_385_, 1, v_val_377_);
lean_ctor_set(v___x_385_, 2, v_val_384_);
return v___x_385_;
}
}
}
v___jp_366_:
{
lean_object* v___x_368_; lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_368_ = lean_array_get_size(v_keyArray_351_);
v___x_369_ = lean_nat_add(v_x_339_, v_one_364_);
lean_dec(v_x_339_);
v___x_370_ = lean_nat_dec_lt(v___x_369_, v___x_368_);
if (v___x_370_ == 0)
{
lean_dec(v___x_369_);
v_x_337_ = v___y_367_;
v_x_338_ = v_n_365_;
v_x_339_ = v_zero_340_;
goto _start;
}
else
{
v_x_337_ = v___y_367_;
v_x_338_ = v_n_365_;
v_x_339_ = v___x_369_;
goto _start;
}
}
v___jp_373_:
{
if (lean_obj_tag(v_x_337_) == 0)
{
lean_object* v___x_374_; 
lean_inc(v_x_339_);
v___x_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_374_, 0, v_x_339_);
v___y_367_ = v___x_374_;
goto v___jp_366_;
}
else
{
v___y_367_ = v_x_337_;
goto v___jp_366_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerLabelAttr_spec__0_spec__0___redArg___boxed(lean_object* v_m_386_, lean_object* v_query_387_, lean_object* v_x_388_, lean_object* v_x_389_, lean_object* v_x_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerLabelAttr_spec__0_spec__0___redArg(v_m_386_, v_query_387_, v_x_388_, v_x_389_, v_x_390_);
lean_dec(v_query_387_);
lean_dec_ref(v_m_386_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerLabelAttr_spec__0___redArg(lean_object* v_m_392_, lean_object* v_query_393_){
_start:
{
lean_object* v_keyArray_394_; lean_object* v___x_395_; uint64_t v___y_397_; 
v_keyArray_394_ = lean_ctor_get(v_m_392_, 1);
v___x_395_ = lean_array_get_size(v_keyArray_394_);
if (lean_obj_tag(v_query_393_) == 0)
{
uint64_t v___x_412_; 
v___x_412_ = 1723ULL;
v___y_397_ = v___x_412_;
goto v___jp_396_;
}
else
{
uint64_t v_hash_413_; 
v_hash_413_ = lean_ctor_get_uint64(v_query_393_, sizeof(void*)*2);
v___y_397_ = v_hash_413_;
goto v___jp_396_;
}
v___jp_396_:
{
uint64_t v___x_398_; uint64_t v___x_399_; uint64_t v_fold_400_; uint64_t v___x_401_; uint64_t v___x_402_; uint64_t v___x_403_; size_t v___x_404_; size_t v___x_405_; size_t v___x_406_; size_t v___x_407_; size_t v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_398_ = 32ULL;
v___x_399_ = lean_uint64_shift_right(v___y_397_, v___x_398_);
v_fold_400_ = lean_uint64_xor(v___y_397_, v___x_399_);
v___x_401_ = 16ULL;
v___x_402_ = lean_uint64_shift_right(v_fold_400_, v___x_401_);
v___x_403_ = lean_uint64_xor(v_fold_400_, v___x_402_);
v___x_404_ = lean_uint64_to_usize(v___x_403_);
v___x_405_ = lean_usize_of_nat(v___x_395_);
v___x_406_ = ((size_t)1ULL);
v___x_407_ = lean_usize_sub(v___x_405_, v___x_406_);
v___x_408_ = lean_usize_land(v___x_404_, v___x_407_);
v___x_409_ = lean_usize_to_nat(v___x_408_);
v___x_410_ = lean_box(0);
v___x_411_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerLabelAttr_spec__0_spec__0___redArg(v_m_392_, v_query_393_, v___x_410_, v___x_395_, v___x_409_);
return v___x_411_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerLabelAttr_spec__0___redArg___boxed(lean_object* v_m_414_, lean_object* v_query_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerLabelAttr_spec__0___redArg(v_m_414_, v_query_415_);
lean_dec(v_query_415_);
lean_dec_ref(v_m_414_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerLabelAttr_spec__1_spec__2_spec__3___redArg(lean_object* v_b_417_, lean_object* v_acc_418_, lean_object* v_i_419_){
_start:
{
lean_object* v___y_421_; lean_object* v_keyArray_429_; lean_object* v_valueArray_430_; lean_object* v___x_431_; uint8_t v___x_432_; 
v_keyArray_429_ = lean_ctor_get(v_b_417_, 1);
v_valueArray_430_ = lean_ctor_get(v_b_417_, 2);
v___x_431_ = lean_array_get_size(v_keyArray_429_);
v___x_432_ = lean_nat_dec_lt(v_i_419_, v___x_431_);
if (v___x_432_ == 0)
{
lean_dec(v_i_419_);
return v_acc_418_;
}
else
{
lean_object* v___x_433_; uint8_t v_isSome_434_; 
v___x_433_ = lean_array_fget_borrowed(v_keyArray_429_, v_i_419_);
v_isSome_434_ = lean_noption_is_some(v___x_433_);
if (v_isSome_434_ == 0)
{
goto v___jp_425_;
}
else
{
lean_object* v___x_435_; uint8_t v_isSome_436_; 
v___x_435_ = lean_array_fget_borrowed(v_valueArray_430_, v_i_419_);
v_isSome_436_ = lean_noption_is_some(v___x_435_);
if (v_isSome_436_ == 0)
{
goto v___jp_425_;
}
else
{
lean_object* v_val_437_; lean_object* v_val_438_; lean_object* v_i_440_; lean_object* v___x_445_; 
lean_inc(v___x_433_);
v_val_437_ = lean_noption_get(v___x_433_);
lean_inc(v___x_435_);
v_val_438_ = lean_noption_get(v___x_435_);
v___x_445_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerLabelAttr_spec__0___redArg(v_acc_418_, v_val_437_);
switch(lean_obj_tag(v___x_445_))
{
case 0:
{
lean_object* v_index_446_; lean_object* v_size_447_; lean_object* v___x_448_; 
v_index_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_index_446_);
lean_dec_ref_known(v___x_445_, 3);
v_size_447_ = lean_ctor_get(v_acc_418_, 0);
lean_inc(v_size_447_);
v___x_448_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_418_, v_size_447_, v_index_446_, v_val_437_, v_val_438_);
lean_dec(v_index_446_);
v___y_421_ = v___x_448_;
goto v___jp_420_;
}
case 1:
{
lean_object* v_index_449_; 
v_index_449_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_index_449_);
lean_dec_ref_known(v___x_445_, 1);
v_i_440_ = v_index_449_;
goto v___jp_439_;
}
default: 
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = lean_unsigned_to_nat(0u);
v___x_451_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_418_, v___x_450_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v_index_452_; 
v_index_452_ = lean_ctor_get(v___x_451_, 0);
lean_inc(v_index_452_);
lean_dec_ref_known(v___x_451_, 1);
v_i_440_ = v_index_452_;
goto v___jp_439_;
}
else
{
lean_dec(v_val_438_);
lean_dec(v_val_437_);
v___y_421_ = v_acc_418_;
goto v___jp_420_;
}
}
}
v___jp_439_:
{
lean_object* v_size_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v_size_441_ = lean_ctor_get(v_acc_418_, 0);
v___x_442_ = lean_unsigned_to_nat(1u);
v___x_443_ = lean_nat_add(v_size_441_, v___x_442_);
v___x_444_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_418_, v___x_443_, v_i_440_, v_val_437_, v_val_438_);
lean_dec(v_i_440_);
v___y_421_ = v___x_444_;
goto v___jp_420_;
}
}
}
}
v___jp_420_:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = lean_unsigned_to_nat(1u);
v___x_423_ = lean_nat_add(v_i_419_, v___x_422_);
lean_dec(v_i_419_);
v_acc_418_ = v___y_421_;
v_i_419_ = v___x_423_;
goto _start;
}
v___jp_425_:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = lean_unsigned_to_nat(1u);
v___x_427_ = lean_nat_add(v_i_419_, v___x_426_);
lean_dec(v_i_419_);
v_i_419_ = v___x_427_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerLabelAttr_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_b_453_, lean_object* v_acc_454_, lean_object* v_i_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerLabelAttr_spec__1_spec__2_spec__3___redArg(v_b_453_, v_acc_454_, v_i_455_);
lean_dec_ref(v_b_453_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerLabelAttr_spec__1_spec__2___redArg(lean_object* v_init_457_, lean_object* v_b_458_){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = lean_unsigned_to_nat(0u);
v___x_460_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerLabelAttr_spec__1_spec__2_spec__3___redArg(v_b_458_, v_init_457_, v___x_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerLabelAttr_spec__1_spec__2___redArg___boxed(lean_object* v_init_461_, lean_object* v_b_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerLabelAttr_spec__1_spec__2___redArg(v_init_461_, v_b_462_);
lean_dec_ref(v_b_462_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerLabelAttr_spec__1___redArg(lean_object* v_m_464_){
_start:
{
lean_object* v_keyArray_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v_cellCount_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v_target_472_; lean_object* v___x_473_; 
v_keyArray_465_ = lean_ctor_get(v_m_464_, 1);
v___x_466_ = lean_array_get_size(v_keyArray_465_);
v___x_467_ = lean_unsigned_to_nat(2u);
v_cellCount_468_ = lean_nat_mul(v___x_466_, v___x_467_);
v___x_469_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_468_);
v___x_470_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_468_);
v___x_471_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_468_);
v_target_472_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_472_, 0, v___x_469_);
lean_ctor_set(v_target_472_, 1, v___x_470_);
lean_ctor_set(v_target_472_, 2, v___x_471_);
v___x_473_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerLabelAttr_spec__1_spec__2___redArg(v_target_472_, v_m_464_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerLabelAttr_spec__1___redArg___boxed(lean_object* v_m_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerLabelAttr_spec__1___redArg(v_m_474_);
lean_dec_ref(v_m_474_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerLabelAttr(lean_object* v_attrName_476_, lean_object* v_attrDescr_477_, lean_object* v_ref_478_){
_start:
{
lean_object* v___x_480_; 
lean_inc(v_ref_478_);
v___x_480_ = l_Lean_mkLabelExt(v_ref_478_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v_a_481_; lean_object* v___x_482_; 
v_a_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc_n(v_a_481_, 2);
lean_dec_ref_known(v___x_480_, 1);
lean_inc(v_attrName_476_);
v___x_482_ = l_Lean_mkLabelAttr(v_attrName_476_, v_attrDescr_477_, v_a_481_, v_ref_478_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_558_; 
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_558_ == 0)
{
lean_object* v_unused_559_; 
v_unused_559_ = lean_ctor_get(v___x_482_, 0);
lean_dec(v_unused_559_);
v___x_484_ = v___x_482_;
v_isShared_485_ = v_isSharedCheck_558_;
goto v_resetjp_483_;
}
else
{
lean_dec(v___x_482_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_558_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___y_489_; lean_object* v___y_495_; lean_object* v_i_496_; lean_object* v___y_502_; lean_object* v___y_512_; lean_object* v_i_513_; lean_object* v___x_528_; 
v___x_486_ = l_Lean_labelExtensionMapRef;
v___x_487_ = lean_st_ref_take(v___x_486_);
v___x_528_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerLabelAttr_spec__0___redArg(v___x_487_, v_attrName_476_);
switch(lean_obj_tag(v___x_528_))
{
case 0:
{
lean_object* v_index_529_; lean_object* v_size_530_; lean_object* v___x_531_; 
v_index_529_ = lean_ctor_get(v___x_528_, 0);
lean_inc(v_index_529_);
lean_dec_ref_known(v___x_528_, 3);
v_size_530_ = lean_ctor_get(v___x_487_, 0);
lean_inc(v_size_530_);
lean_inc(v_a_481_);
v___x_531_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_487_, v_size_530_, v_index_529_, v_attrName_476_, v_a_481_);
lean_dec(v_index_529_);
v___y_489_ = v___x_531_;
goto v___jp_488_;
}
case 1:
{
lean_object* v_index_532_; lean_object* v_size_533_; lean_object* v_keyArray_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; uint8_t v___x_538_; 
v_index_532_ = lean_ctor_get(v___x_528_, 0);
lean_inc(v_index_532_);
lean_dec_ref_known(v___x_528_, 1);
v_size_533_ = lean_ctor_get(v___x_487_, 0);
lean_inc(v_size_533_);
v_keyArray_534_ = lean_ctor_get(v___x_487_, 1);
lean_inc_ref(v_keyArray_534_);
v___x_535_ = lean_unsigned_to_nat(1u);
v___x_536_ = lean_nat_add(v_size_533_, v___x_535_);
lean_dec(v_size_533_);
v___x_537_ = lean_array_get_size(v_keyArray_534_);
lean_dec_ref(v_keyArray_534_);
v___x_538_ = lean_nat_dec_lt(v___x_536_, v___x_537_);
if (v___x_538_ == 0)
{
lean_dec(v___x_536_);
lean_dec(v_index_532_);
goto v___jp_518_;
}
else
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; uint8_t v___x_543_; 
v___x_539_ = lean_unsigned_to_nat(4u);
v___x_540_ = lean_nat_mul(v___x_536_, v___x_539_);
v___x_541_ = lean_unsigned_to_nat(3u);
v___x_542_ = lean_nat_mul(v___x_537_, v___x_541_);
v___x_543_ = lean_nat_dec_le(v___x_540_, v___x_542_);
lean_dec(v___x_542_);
lean_dec(v___x_540_);
if (v___x_543_ == 0)
{
lean_dec(v___x_536_);
lean_dec(v_index_532_);
goto v___jp_518_;
}
else
{
lean_object* v___x_544_; 
lean_inc(v_a_481_);
v___x_544_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_487_, v___x_536_, v_index_532_, v_attrName_476_, v_a_481_);
lean_dec(v_index_532_);
v___y_489_ = v___x_544_;
goto v___jp_488_;
}
}
}
default: 
{
lean_object* v_size_545_; lean_object* v_keyArray_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; uint8_t v___x_550_; 
v_size_545_ = lean_ctor_get(v___x_487_, 0);
lean_inc(v_size_545_);
v_keyArray_546_ = lean_ctor_get(v___x_487_, 1);
lean_inc_ref(v_keyArray_546_);
v___x_547_ = lean_unsigned_to_nat(1u);
v___x_548_ = lean_nat_add(v_size_545_, v___x_547_);
lean_dec(v_size_545_);
v___x_549_ = lean_array_get_size(v_keyArray_546_);
lean_dec_ref(v_keyArray_546_);
v___x_550_ = lean_nat_dec_lt(v___x_548_, v___x_549_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; 
lean_dec(v___x_548_);
v___x_551_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerLabelAttr_spec__1___redArg(v___x_487_);
lean_dec(v___x_487_);
v___y_502_ = v___x_551_;
goto v___jp_501_;
}
else
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; uint8_t v___x_556_; 
v___x_552_ = lean_unsigned_to_nat(4u);
v___x_553_ = lean_nat_mul(v___x_548_, v___x_552_);
lean_dec(v___x_548_);
v___x_554_ = lean_unsigned_to_nat(3u);
v___x_555_ = lean_nat_mul(v___x_549_, v___x_554_);
v___x_556_ = lean_nat_dec_le(v___x_553_, v___x_555_);
lean_dec(v___x_555_);
lean_dec(v___x_553_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; 
v___x_557_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerLabelAttr_spec__1___redArg(v___x_487_);
lean_dec(v___x_487_);
v___y_502_ = v___x_557_;
goto v___jp_501_;
}
else
{
v___y_502_ = v___x_487_;
goto v___jp_501_;
}
}
}
}
v___jp_488_:
{
lean_object* v___x_490_; lean_object* v___x_492_; 
v___x_490_ = lean_st_ref_put(v___x_486_, v___y_489_);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 0, v_a_481_);
v___x_492_ = v___x_484_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_a_481_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
v___jp_494_:
{
lean_object* v_size_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v_size_497_ = lean_ctor_get(v___y_495_, 0);
v___x_498_ = lean_unsigned_to_nat(1u);
v___x_499_ = lean_nat_add(v_size_497_, v___x_498_);
lean_inc(v_a_481_);
v___x_500_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_495_, v___x_499_, v_i_496_, v_attrName_476_, v_a_481_);
lean_dec(v_i_496_);
v___y_489_ = v___x_500_;
goto v___jp_488_;
}
v___jp_501_:
{
lean_object* v___x_503_; 
v___x_503_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerLabelAttr_spec__0___redArg(v___y_502_, v_attrName_476_);
switch(lean_obj_tag(v___x_503_))
{
case 0:
{
lean_object* v_index_504_; lean_object* v_size_505_; lean_object* v___x_506_; 
v_index_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_index_504_);
lean_dec_ref_known(v___x_503_, 3);
v_size_505_ = lean_ctor_get(v___y_502_, 0);
lean_inc(v_size_505_);
lean_inc(v_a_481_);
v___x_506_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_502_, v_size_505_, v_index_504_, v_attrName_476_, v_a_481_);
lean_dec(v_index_504_);
v___y_489_ = v___x_506_;
goto v___jp_488_;
}
case 1:
{
lean_object* v_index_507_; 
v_index_507_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_index_507_);
lean_dec_ref_known(v___x_503_, 1);
v___y_495_ = v___y_502_;
v_i_496_ = v_index_507_;
goto v___jp_494_;
}
default: 
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = lean_unsigned_to_nat(0u);
v___x_509_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_502_, v___x_508_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_index_510_; 
v_index_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_index_510_);
lean_dec_ref_known(v___x_509_, 1);
v___y_495_ = v___y_502_;
v_i_496_ = v_index_510_;
goto v___jp_494_;
}
else
{
lean_dec(v_attrName_476_);
v___y_489_ = v___y_502_;
goto v___jp_488_;
}
}
}
}
v___jp_511_:
{
lean_object* v_size_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v_size_514_ = lean_ctor_get(v___y_512_, 0);
v___x_515_ = lean_unsigned_to_nat(1u);
v___x_516_ = lean_nat_add(v_size_514_, v___x_515_);
lean_inc(v_a_481_);
v___x_517_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_512_, v___x_516_, v_i_513_, v_attrName_476_, v_a_481_);
lean_dec(v_i_513_);
v___y_489_ = v___x_517_;
goto v___jp_488_;
}
v___jp_518_:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerLabelAttr_spec__1___redArg(v___x_487_);
lean_dec(v___x_487_);
v___x_520_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerLabelAttr_spec__0___redArg(v___x_519_, v_attrName_476_);
switch(lean_obj_tag(v___x_520_))
{
case 0:
{
lean_object* v_index_521_; lean_object* v_size_522_; lean_object* v___x_523_; 
v_index_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_index_521_);
lean_dec_ref_known(v___x_520_, 3);
v_size_522_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_size_522_);
lean_inc(v_a_481_);
v___x_523_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_519_, v_size_522_, v_index_521_, v_attrName_476_, v_a_481_);
lean_dec(v_index_521_);
v___y_489_ = v___x_523_;
goto v___jp_488_;
}
case 1:
{
lean_object* v_index_524_; 
v_index_524_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_index_524_);
lean_dec_ref_known(v___x_520_, 1);
v___y_512_ = v___x_519_;
v_i_513_ = v_index_524_;
goto v___jp_511_;
}
default: 
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = lean_unsigned_to_nat(0u);
v___x_526_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_519_, v___x_525_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_index_527_; 
v_index_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_index_527_);
lean_dec_ref_known(v___x_526_, 1);
v___y_512_ = v___x_519_;
v_i_513_ = v_index_527_;
goto v___jp_511_;
}
else
{
lean_dec(v_attrName_476_);
v___y_489_ = v___x_519_;
goto v___jp_488_;
}
}
}
}
}
}
else
{
lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_567_; 
lean_dec(v_a_481_);
lean_dec(v_attrName_476_);
v_a_560_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_567_ == 0)
{
v___x_562_ = v___x_482_;
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v___x_482_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_a_560_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
else
{
lean_dec(v_ref_478_);
lean_dec_ref(v_attrDescr_477_);
lean_dec(v_attrName_476_);
return v___x_480_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerLabelAttr___boxed(lean_object* v_attrName_568_, lean_object* v_attrDescr_569_, lean_object* v_ref_570_, lean_object* v_a_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_registerLabelAttr(v_attrName_568_, v_attrDescr_569_, v_ref_570_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerLabelAttr_spec__0(lean_object* v_00_u03b2_573_, lean_object* v_m_574_, lean_object* v_query_575_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerLabelAttr_spec__0___redArg(v_m_574_, v_query_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerLabelAttr_spec__0___boxed(lean_object* v_00_u03b2_577_, lean_object* v_m_578_, lean_object* v_query_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerLabelAttr_spec__0(v_00_u03b2_577_, v_m_578_, v_query_579_);
lean_dec(v_query_579_);
lean_dec_ref(v_m_578_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerLabelAttr_spec__1(lean_object* v_00_u03b2_581_, lean_object* v_m_582_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerLabelAttr_spec__1___redArg(v_m_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerLabelAttr_spec__1___boxed(lean_object* v_00_u03b2_584_, lean_object* v_m_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerLabelAttr_spec__1(v_00_u03b2_584_, v_m_585_);
lean_dec_ref(v_m_585_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerLabelAttr_spec__0_spec__0(lean_object* v_00_u03b2_587_, lean_object* v_m_588_, lean_object* v_query_589_, lean_object* v_x_590_, lean_object* v_x_591_, lean_object* v_x_592_, lean_object* v_x_593_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerLabelAttr_spec__0_spec__0___redArg(v_m_588_, v_query_589_, v_x_590_, v_x_591_, v_x_592_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerLabelAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_595_, lean_object* v_m_596_, lean_object* v_query_597_, lean_object* v_x_598_, lean_object* v_x_599_, lean_object* v_x_600_, lean_object* v_x_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerLabelAttr_spec__0_spec__0(v_00_u03b2_595_, v_m_596_, v_query_597_, v_x_598_, v_x_599_, v_x_600_, v_x_601_);
lean_dec(v_query_597_);
lean_dec_ref(v_m_596_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerLabelAttr_spec__1_spec__2(lean_object* v_00_u03b2_603_, lean_object* v_init_604_, lean_object* v_b_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerLabelAttr_spec__1_spec__2___redArg(v_init_604_, v_b_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerLabelAttr_spec__1_spec__2___boxed(lean_object* v_00_u03b2_607_, lean_object* v_init_608_, lean_object* v_b_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerLabelAttr_spec__1_spec__2(v_00_u03b2_607_, v_init_608_, v_b_609_);
lean_dec_ref(v_b_609_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerLabelAttr_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_611_, lean_object* v_b_612_, lean_object* v_acc_613_, lean_object* v_i_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerLabelAttr_spec__1_spec__2_spec__3___redArg(v_b_612_, v_acc_613_, v_i_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerLabelAttr_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_616_, lean_object* v_b_617_, lean_object* v_acc_618_, lean_object* v_i_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerLabelAttr_spec__1_spec__2_spec__3(v_00_u03b2_616_, v_b_617_, v_acc_618_, v_i_619_);
lean_dec_ref(v_b_617_);
return v_res_620_;
}
}
static lean_object* _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__13(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__12));
v___x_691_ = l_String_toRawSubstring_x27(v___x_690_);
return v___x_691_;
}
}
static lean_object* _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__18(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__17));
v___x_702_ = l_String_toRawSubstring_x27(v___x_701_);
return v___x_702_;
}
}
static lean_object* _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__24(void){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__23));
v___x_714_ = l_String_toRawSubstring_x27(v___x_713_);
return v___x_714_;
}
}
static lean_object* _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__38(void){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = ((lean_object*)(l_Lean_Parser_Command_registerLabelAttr___closed__2));
v___x_751_ = l_String_toRawSubstring_x27(v___x_750_);
return v___x_751_;
}
}
static lean_object* _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__51(void){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l_Array_mkArray0(lean_box(0));
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1(lean_object* v_x_789_, lean_object* v_a_790_, lean_object* v_a_791_){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_866_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___y_874_; lean_object* v___y_875_; lean_object* v___y_876_; lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___x_927_; uint8_t v___x_928_; 
v___x_792_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__0));
v___x_793_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__1));
v___x_927_ = ((lean_object*)(l_Lean_Parser_Command_registerLabelAttr___closed__3));
lean_inc(v_x_789_);
v___x_928_ = l_Lean_Syntax_isOfKind(v_x_789_, v___x_927_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; lean_object* v___x_930_; 
lean_dec(v_x_789_);
v___x_929_ = lean_box(1);
v___x_930_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
lean_ctor_set(v___x_930_, 1, v_a_791_);
return v___x_930_;
}
else
{
lean_object* v___x_931_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___y_936_; uint8_t v___y_937_; lean_object* v___y_938_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v_id_956_; lean_object* v___y_958_; lean_object* v___x_969_; 
v___x_931_ = lean_unsigned_to_nat(0u);
v___x_954_ = l_Lean_Syntax_getArg(v_x_789_, v___x_931_);
v___x_955_ = lean_unsigned_to_nat(2u);
v_id_956_ = l_Lean_Syntax_getArg(v_x_789_, v___x_955_);
lean_dec(v_x_789_);
v___x_969_ = l_Lean_Syntax_getOptional_x3f(v___x_954_);
lean_dec(v___x_954_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v___x_970_; 
v___x_970_ = lean_box(0);
v___y_958_ = v___x_970_;
goto v___jp_957_;
}
else
{
lean_object* v_val_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_978_; 
v_val_971_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_978_ == 0)
{
v___x_973_ = v___x_969_;
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_val_971_);
lean_dec(v___x_969_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_976_; 
if (v_isShared_974_ == 0)
{
v___x_976_ = v___x_973_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_val_971_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
v___y_958_ = v___x_976_;
goto v___jp_957_;
}
}
}
v___jp_932_:
{
lean_object* v_quotContext_939_; lean_object* v_currMacroScope_940_; lean_object* v_ref_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v_quotContext_939_ = lean_ctor_get(v_a_790_, 1);
v_currMacroScope_940_ = lean_ctor_get(v_a_790_, 2);
v_ref_941_ = lean_ctor_get(v_a_790_, 5);
v___x_942_ = l_String_removeLeadingSpaces(v___y_938_);
v___x_943_ = lean_box(2);
v___x_944_ = l_Lean_Syntax_mkStrLit(v___x_942_, v___x_943_);
v___x_945_ = l_Lean_SourceInfo_fromRef(v_ref_941_, v___y_937_);
v___x_946_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__9));
v___x_947_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__47));
v___x_948_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__48));
v___x_949_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__50));
v___x_950_ = lean_obj_once(&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__51, &l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__51_once, _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__51);
if (lean_obj_tag(v___y_936_) == 1)
{
lean_object* v_val_951_; lean_object* v___x_952_; 
v_val_951_ = lean_ctor_get(v___y_936_, 0);
lean_inc(v_val_951_);
lean_dec_ref_known(v___y_936_, 1);
v___x_952_ = l_Array_mkArray1___redArg(v_val_951_);
v___y_866_ = v___x_948_;
v___y_867_ = v___y_933_;
v___y_868_ = v_currMacroScope_940_;
v___y_869_ = v_quotContext_939_;
v___y_870_ = v___x_949_;
v___y_871_ = v___x_944_;
v___y_872_ = v___x_946_;
v___y_873_ = v___y_934_;
v___y_874_ = v___x_950_;
v___y_875_ = v___x_947_;
v___y_876_ = v___x_945_;
v___y_877_ = v___x_943_;
v___y_878_ = v___y_935_;
v___y_879_ = v___x_952_;
goto v___jp_865_;
}
else
{
lean_object* v___x_953_; 
lean_dec(v___y_936_);
v___x_953_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__5));
v___y_866_ = v___x_948_;
v___y_867_ = v___y_933_;
v___y_868_ = v_currMacroScope_940_;
v___y_869_ = v_quotContext_939_;
v___y_870_ = v___x_949_;
v___y_871_ = v___x_944_;
v___y_872_ = v___x_946_;
v___y_873_ = v___y_934_;
v___y_874_ = v___x_950_;
v___y_875_ = v___x_947_;
v___y_876_ = v___x_945_;
v___y_877_ = v___x_943_;
v___y_878_ = v___y_935_;
v___y_879_ = v___x_953_;
goto v___jp_865_;
}
}
v___jp_957_:
{
lean_object* v___x_959_; lean_object* v_str_960_; lean_object* v___x_961_; lean_object* v___x_962_; uint8_t v___x_963_; lean_object* v_idParser_964_; 
v___x_959_ = l_Lean_TSyntax_getId(v_id_956_);
lean_inc_n(v___x_959_, 2);
v_str_960_ = l_Lean_Name_toString(v___x_959_, v___x_928_);
v___x_961_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__53));
v___x_962_ = l_Lean_Name_append(v___x_961_, v___x_959_);
v___x_963_ = 0;
v_idParser_964_ = l_Lean_mkIdentFrom(v_id_956_, v___x_962_, v___x_963_);
lean_dec(v_id_956_);
if (lean_obj_tag(v___y_958_) == 0)
{
lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_965_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__54));
v___x_966_ = lean_string_append(v___x_965_, v_str_960_);
v___y_933_ = v_str_960_;
v___y_934_ = v___x_959_;
v___y_935_ = v_idParser_964_;
v___y_936_ = v___y_958_;
v___y_937_ = v___x_963_;
v___y_938_ = v___x_966_;
goto v___jp_932_;
}
else
{
lean_object* v_val_967_; lean_object* v___x_968_; 
v_val_967_ = lean_ctor_get(v___y_958_, 0);
v___x_968_ = l_Lean_TSyntax_getDocString(v_val_967_);
v___y_933_ = v_str_960_;
v___y_934_ = v___x_959_;
v___y_935_ = v_idParser_964_;
v___y_936_ = v___y_958_;
v___y_937_ = v___x_963_;
v___y_938_ = v___x_968_;
goto v___jp_932_;
}
}
}
v___jp_794_:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
lean_inc(v___y_817_);
lean_inc_n(v___y_802_, 5);
lean_inc_n(v___y_808_, 19);
v___x_818_ = l_Lean_Syntax_node3(v___y_808_, v___y_802_, v___y_817_, v___y_801_, v___y_817_);
lean_inc(v___y_809_);
v___x_819_ = l_Lean_Syntax_node2(v___y_808_, v___y_809_, v___y_807_, v___x_818_);
lean_inc(v___y_815_);
v___x_820_ = l_Lean_Syntax_node1(v___y_808_, v___y_815_, v___x_819_);
lean_inc_n(v___y_811_, 4);
lean_inc(v___y_798_);
v___x_821_ = l_Lean_Syntax_node2(v___y_808_, v___y_798_, v___x_820_, v___y_811_);
v___x_822_ = l_Lean_Syntax_node1(v___y_808_, v___y_802_, v___x_821_);
lean_inc(v___y_799_);
v___x_823_ = l_Lean_Syntax_node1(v___y_808_, v___y_799_, v___x_822_);
lean_inc(v___y_795_);
v___x_824_ = l_Lean_Syntax_node4(v___y_808_, v___y_795_, v___y_803_, v___y_800_, v___y_814_, v___x_823_);
v___x_825_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__0));
v___x_826_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__1));
v___x_827_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__2));
lean_inc_ref(v___y_804_);
v___x_828_ = l_Lean_Name_mkStr4(v___x_792_, v___x_793_, v___y_804_, v___x_827_);
v___x_829_ = l_Lean_Syntax_node1(v___y_808_, v___x_828_, v___y_811_);
v___x_830_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_830_, 0, v___y_808_);
lean_ctor_set(v___x_830_, 1, v___x_825_);
v___x_831_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__4));
v___x_832_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__5));
v___x_833_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_833_, 0, v___y_808_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
v___x_834_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__6));
v___x_835_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_835_, 0, v___y_808_);
lean_ctor_set(v___x_835_, 1, v___x_834_);
v___x_836_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__7));
v___x_837_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_837_, 0, v___y_808_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
v___x_838_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__8));
v___x_839_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_839_, 0, v___y_808_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
v___x_840_ = l_Lean_Syntax_node5(v___y_808_, v___x_831_, v___x_833_, v___x_835_, v___x_837_, v___y_812_, v___x_839_);
v___x_841_ = l_Lean_Syntax_node1(v___y_808_, v___y_802_, v___x_840_);
v___x_842_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__11));
v___x_843_ = l_Lean_Syntax_mkStrLit(v___y_796_, v___y_810_);
v___x_844_ = l_Lean_Syntax_node1(v___y_808_, v___x_842_, v___x_843_);
v___x_845_ = l_Lean_Syntax_node1(v___y_808_, v___y_802_, v___x_844_);
v___x_846_ = lean_obj_once(&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__13, &l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__13_once, _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__13);
v___x_847_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__14));
lean_inc(v___y_797_);
lean_inc(v___y_805_);
v___x_848_ = l_Lean_addMacroScope(v___y_805_, v___x_847_, v___y_797_);
v___x_849_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_849_, 0, v___y_808_);
lean_ctor_set(v___x_849_, 1, v___x_846_);
lean_ctor_set(v___x_849_, 2, v___x_848_);
lean_ctor_set(v___x_849_, 3, v___y_806_);
v___x_850_ = lean_unsigned_to_nat(10u);
v___x_851_ = lean_mk_empty_array_with_capacity(v___x_850_);
v___x_852_ = lean_array_push(v___x_851_, v___y_813_);
v___x_853_ = lean_array_push(v___x_852_, v___y_811_);
v___x_854_ = lean_array_push(v___x_853_, v___x_829_);
v___x_855_ = lean_array_push(v___x_854_, v___x_830_);
v___x_856_ = lean_array_push(v___x_855_, v___y_811_);
v___x_857_ = lean_array_push(v___x_856_, v___x_841_);
v___x_858_ = lean_array_push(v___x_857_, v___y_811_);
v___x_859_ = lean_array_push(v___x_858_, v___x_845_);
v___x_860_ = lean_array_push(v___x_859_, v___y_816_);
v___x_861_ = lean_array_push(v___x_860_, v___x_849_);
v___x_862_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_862_, 0, v___y_808_);
lean_ctor_set(v___x_862_, 1, v___x_826_);
lean_ctor_set(v___x_862_, 2, v___x_861_);
v___x_863_ = l_Lean_Syntax_node2(v___y_808_, v___y_802_, v___x_824_, v___x_862_);
v___x_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
lean_ctor_set(v___x_864_, 1, v_a_791_);
return v___x_864_;
}
v___jp_865_:
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
lean_inc_ref_n(v___y_874_, 2);
v___x_880_ = l_Array_append___redArg(v___y_874_, v___y_879_);
lean_dec_ref(v___y_879_);
lean_inc_n(v___y_872_, 3);
lean_inc_n(v___y_876_, 12);
v___x_881_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_881_, 0, v___y_876_);
lean_ctor_set(v___x_881_, 1, v___y_872_);
lean_ctor_set(v___x_881_, 2, v___x_880_);
v___x_882_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_882_, 0, v___y_876_);
lean_ctor_set(v___x_882_, 1, v___y_872_);
lean_ctor_set(v___x_882_, 2, v___y_874_);
lean_inc_ref_n(v___x_882_, 6);
lean_inc_ref(v___x_881_);
lean_inc(v___y_870_);
v___x_883_ = l_Lean_Syntax_node7(v___y_876_, v___y_870_, v___x_881_, v___x_882_, v___x_882_, v___x_882_, v___x_882_, v___x_882_, v___x_882_);
v___x_884_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__16));
lean_inc_ref(v___y_875_);
v___x_885_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_885_, 0, v___y_876_);
lean_ctor_set(v___x_885_, 1, v___y_875_);
v___x_886_ = l_Lean_Syntax_node1(v___y_876_, v___x_884_, v___x_885_);
v___x_887_ = lean_obj_once(&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__18, &l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__18_once, _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__18);
v___x_888_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__19));
lean_inc_n(v___y_868_, 3);
lean_inc_n(v___y_869_, 3);
v___x_889_ = l_Lean_addMacroScope(v___y_869_, v___x_888_, v___y_868_);
v___x_890_ = lean_box(0);
v___x_891_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_891_, 0, v___y_876_);
lean_ctor_set(v___x_891_, 1, v___x_887_);
lean_ctor_set(v___x_891_, 2, v___x_889_);
lean_ctor_set(v___x_891_, 3, v___x_890_);
v___x_892_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__14));
v___x_893_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__21));
v___x_894_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__22));
v___x_895_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_895_, 0, v___y_876_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
v___x_896_ = lean_obj_once(&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__24, &l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__24_once, _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__24);
v___x_897_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__26));
v___x_898_ = l_Lean_addMacroScope(v___y_869_, v___x_897_, v___y_868_);
v___x_899_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__28));
v___x_900_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_900_, 0, v___y_876_);
lean_ctor_set(v___x_900_, 1, v___x_896_);
lean_ctor_set(v___x_900_, 2, v___x_898_);
lean_ctor_set(v___x_900_, 3, v___x_899_);
lean_inc_ref(v___x_895_);
v___x_901_ = l_Lean_Syntax_node2(v___y_876_, v___x_893_, v___x_895_, v___x_900_);
v___x_902_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__29));
v___x_903_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_903_, 0, v___y_876_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v___x_904_ = l_Lean_Syntax_node3(v___y_876_, v___y_872_, v___x_891_, v___x_901_, v___x_903_);
v___x_905_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__31));
v___x_906_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__33));
v___x_907_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__35));
v___x_908_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__37));
v___x_909_ = lean_obj_once(&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__38, &l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__38_once, _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__38);
v___x_910_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__39));
v___x_911_ = l_Lean_addMacroScope(v___y_869_, v___x_910_, v___y_868_);
v___x_912_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__42));
v___x_913_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_913_, 0, v___y_876_);
lean_ctor_set(v___x_913_, 1, v___x_909_);
lean_ctor_set(v___x_913_, 2, v___x_911_);
lean_ctor_set(v___x_913_, 3, v___x_912_);
lean_inc(v___y_873_);
v___x_914_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_890_, v___y_873_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v___x_915_; 
v___x_915_ = l_Lean_quoteNameMk(v___y_873_);
v___y_795_ = v___y_866_;
v___y_796_ = v___y_867_;
v___y_797_ = v___y_868_;
v___y_798_ = v___x_906_;
v___y_799_ = v___x_905_;
v___y_800_ = v___x_886_;
v___y_801_ = v___y_871_;
v___y_802_ = v___y_872_;
v___y_803_ = v___x_883_;
v___y_804_ = v___x_892_;
v___y_805_ = v___y_869_;
v___y_806_ = v___x_890_;
v___y_807_ = v___x_913_;
v___y_808_ = v___y_876_;
v___y_809_ = v___x_908_;
v___y_810_ = v___y_877_;
v___y_811_ = v___x_882_;
v___y_812_ = v___y_878_;
v___y_813_ = v___x_881_;
v___y_814_ = v___x_904_;
v___y_815_ = v___x_907_;
v___y_816_ = v___x_895_;
v___y_817_ = v___x_915_;
goto v___jp_794_;
}
else
{
lean_object* v_val_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
lean_dec(v___y_873_);
v_val_916_ = lean_ctor_get(v___x_914_, 0);
lean_inc(v_val_916_);
lean_dec_ref_known(v___x_914_, 1);
v___x_917_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__44));
v___x_918_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__45));
v___x_919_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__46));
v___x_920_ = lean_string_intercalate(v___x_919_, v_val_916_);
v___x_921_ = lean_string_append(v___x_918_, v___x_920_);
lean_dec_ref(v___x_920_);
lean_inc_n(v___y_877_, 2);
v___x_922_ = l_Lean_Syntax_mkNameLit(v___x_921_, v___y_877_);
v___x_923_ = lean_unsigned_to_nat(1u);
v___x_924_ = lean_mk_empty_array_with_capacity(v___x_923_);
v___x_925_ = lean_array_push(v___x_924_, v___x_922_);
v___x_926_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_926_, 0, v___y_877_);
lean_ctor_set(v___x_926_, 1, v___x_917_);
lean_ctor_set(v___x_926_, 2, v___x_925_);
v___y_795_ = v___y_866_;
v___y_796_ = v___y_867_;
v___y_797_ = v___y_868_;
v___y_798_ = v___x_906_;
v___y_799_ = v___x_905_;
v___y_800_ = v___x_886_;
v___y_801_ = v___y_871_;
v___y_802_ = v___y_872_;
v___y_803_ = v___x_883_;
v___y_804_ = v___x_892_;
v___y_805_ = v___y_869_;
v___y_806_ = v___x_890_;
v___y_807_ = v___x_913_;
v___y_808_ = v___y_876_;
v___y_809_ = v___x_908_;
v___y_810_ = v___y_877_;
v___y_811_ = v___x_882_;
v___y_812_ = v___y_878_;
v___y_813_ = v___x_881_;
v___y_814_ = v___x_904_;
v___y_815_ = v___x_907_;
v___y_816_ = v___x_895_;
v___y_817_ = v___x_926_;
goto v___jp_794_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___boxed(lean_object* v_x_979_, lean_object* v_a_980_, lean_object* v_a_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1(v_x_979_, v_a_980_, v_a_981_);
lean_dec_ref(v_a_980_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0___redArg(lean_object* v_m_983_, lean_object* v_query_984_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerLabelAttr_spec__0___redArg(v_m_983_, v_query_984_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v_index_986_; lean_object* v_key_987_; lean_object* v_value_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
v_index_986_ = lean_ctor_get(v___x_985_, 0);
v_key_987_ = lean_ctor_get(v___x_985_, 1);
v_value_988_ = lean_ctor_get(v___x_985_, 2);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_985_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_value_988_);
lean_inc(v_key_987_);
lean_inc(v_index_986_);
lean_dec(v___x_985_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_index_986_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v_key_987_);
lean_ctor_set(v_reuseFailAlloc_994_, 2, v_value_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
else
{
lean_object* v___x_996_; 
lean_dec(v___x_985_);
v___x_996_ = lean_box(1);
return v___x_996_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0___redArg___boxed(lean_object* v_m_997_, lean_object* v_query_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0___redArg(v_m_997_, v_query_998_);
lean_dec(v_query_998_);
lean_dec_ref(v_m_997_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0___redArg(lean_object* v_m_1000_, lean_object* v_a_1001_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0___redArg(v_m_1000_, v_a_1001_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_value_1003_; lean_object* v___x_1004_; 
v_value_1003_ = lean_ctor_get(v___x_1002_, 2);
lean_inc(v_value_1003_);
lean_dec_ref_known(v___x_1002_, 3);
v___x_1004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1004_, 0, v_value_1003_);
return v___x_1004_;
}
else
{
lean_object* v___x_1005_; 
v___x_1005_ = lean_box(0);
return v___x_1005_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0___redArg___boxed(lean_object* v_m_1006_, lean_object* v_a_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0___redArg(v_m_1006_, v_a_1007_);
lean_dec(v_a_1007_);
lean_dec_ref(v_m_1006_);
return v_res_1008_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1009_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__0);
v___x_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
return v___x_1011_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1012_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__1);
v___x_1013_ = lean_unsigned_to_nat(0u);
v___x_1014_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
lean_ctor_set(v___x_1014_, 2, v___x_1013_);
lean_ctor_set(v___x_1014_, 3, v___x_1013_);
lean_ctor_set(v___x_1014_, 4, v___x_1012_);
lean_ctor_set(v___x_1014_, 5, v___x_1012_);
lean_ctor_set(v___x_1014_, 6, v___x_1012_);
lean_ctor_set(v___x_1014_, 7, v___x_1012_);
lean_ctor_set(v___x_1014_, 8, v___x_1012_);
lean_ctor_set(v___x_1014_, 9, v___x_1012_);
lean_ctor_set(v___x_1014_, 10, v___x_1012_);
return v___x_1014_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1015_ = lean_unsigned_to_nat(32u);
v___x_1016_ = lean_mk_empty_array_with_capacity(v___x_1015_);
v___x_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
return v___x_1017_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__4(void){
_start:
{
size_t v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1018_ = ((size_t)5ULL);
v___x_1019_ = lean_unsigned_to_nat(0u);
v___x_1020_ = lean_unsigned_to_nat(32u);
v___x_1021_ = lean_mk_empty_array_with_capacity(v___x_1020_);
v___x_1022_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__3);
v___x_1023_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
lean_ctor_set(v___x_1023_, 1, v___x_1021_);
lean_ctor_set(v___x_1023_, 2, v___x_1019_);
lean_ctor_set(v___x_1023_, 3, v___x_1019_);
lean_ctor_set_usize(v___x_1023_, 4, v___x_1018_);
return v___x_1023_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__5(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1024_ = lean_box(1);
v___x_1025_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__4);
v___x_1026_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__1);
v___x_1027_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
lean_ctor_set(v___x_1027_, 1, v___x_1025_);
lean_ctor_set(v___x_1027_, 2, v___x_1024_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2(lean_object* v_msgData_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v___x_1032_; lean_object* v_env_1033_; lean_object* v_options_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1032_ = lean_st_ref_get(v___y_1030_);
v_env_1033_ = lean_ctor_get(v___x_1032_, 0);
lean_inc_ref(v_env_1033_);
lean_dec(v___x_1032_);
v_options_1034_ = lean_ctor_get(v___y_1029_, 2);
v___x_1035_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__2);
v___x_1036_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__5);
lean_inc_ref(v_options_1034_);
v___x_1037_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1037_, 0, v_env_1033_);
lean_ctor_set(v___x_1037_, 1, v___x_1035_);
lean_ctor_set(v___x_1037_, 2, v___x_1036_);
lean_ctor_set(v___x_1037_, 3, v_options_1034_);
v___x_1038_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
lean_ctor_set(v___x_1038_, 1, v_msgData_1028_);
v___x_1039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___boxed(lean_object* v_msgData_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2(v_msgData_1040_, v___y_1041_, v___y_1042_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_labelled_spec__1___redArg(lean_object* v_msg_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v_ref_1049_; lean_object* v___x_1050_; lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1059_; 
v_ref_1049_ = lean_ctor_get(v___y_1046_, 5);
v___x_1050_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2(v_msg_1045_, v___y_1046_, v___y_1047_);
v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1053_ = v___x_1050_;
v_isShared_1054_ = v_isSharedCheck_1059_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_1050_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1059_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1055_; lean_object* v___x_1057_; 
lean_inc(v_ref_1049_);
v___x_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1055_, 0, v_ref_1049_);
lean_ctor_set(v___x_1055_, 1, v_a_1051_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set_tag(v___x_1053_, 1);
lean_ctor_set(v___x_1053_, 0, v___x_1055_);
v___x_1057_ = v___x_1053_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1055_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_labelled_spec__1___redArg___boxed(lean_object* v_msg_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Lean_throwError___at___00Lean_labelled_spec__1___redArg(v_msg_1060_, v___y_1061_, v___y_1062_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
return v_res_1064_;
}
}
static lean_object* _init_l_Lean_labelled___closed__1(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = ((lean_object*)(l_Lean_labelled___closed__0));
v___x_1067_ = l_Lean_stringToMessageData(v___x_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_labelled(lean_object* v_attrName_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_){
_start:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1072_ = l_Lean_labelExtensionMapRef;
v___x_1073_ = lean_st_ref_get(v___x_1072_);
v___x_1074_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0___redArg(v___x_1073_, v_attrName_1068_);
lean_dec(v___x_1073_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1075_ = lean_obj_once(&l_Lean_labelled___closed__1, &l_Lean_labelled___closed__1_once, _init_l_Lean_labelled___closed__1);
v___x_1076_ = l_Lean_MessageData_ofName(v_attrName_1068_);
v___x_1077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1075_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
v___x_1078_ = l_Lean_throwError___at___00Lean_labelled_spec__1___redArg(v___x_1077_, v_a_1069_, v_a_1070_);
return v___x_1078_;
}
else
{
lean_object* v_val_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1093_; 
lean_dec(v_attrName_1068_);
v_val_1079_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1081_ = v___x_1074_;
v_isShared_1082_ = v_isSharedCheck_1093_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_val_1079_);
lean_dec(v___x_1074_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1093_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1083_; lean_object* v_ext_1084_; lean_object* v_toEnvExtension_1085_; lean_object* v_env_1086_; lean_object* v_asyncMode_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1091_; 
v___x_1083_ = lean_st_ref_get(v_a_1070_);
v_ext_1084_ = lean_ctor_get(v_val_1079_, 1);
v_toEnvExtension_1085_ = lean_ctor_get(v_ext_1084_, 0);
v_env_1086_ = lean_ctor_get(v___x_1083_, 0);
lean_inc_ref(v_env_1086_);
lean_dec(v___x_1083_);
v_asyncMode_1087_ = lean_ctor_get(v_toEnvExtension_1085_, 2);
lean_inc(v_asyncMode_1087_);
v___x_1088_ = lean_obj_once(&l_Lean_mkLabelAttr___closed__0, &l_Lean_mkLabelAttr___closed__0_once, _init_l_Lean_mkLabelAttr___closed__0);
v___x_1089_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1088_, v_val_1079_, v_env_1086_, v_asyncMode_1087_);
lean_dec(v_asyncMode_1087_);
lean_dec(v_val_1079_);
if (v_isShared_1082_ == 0)
{
lean_ctor_set_tag(v___x_1081_, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1089_);
v___x_1091_ = v___x_1081_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1089_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_labelled___boxed(lean_object* v_attrName_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_Lean_labelled(v_attrName_1094_, v_a_1095_, v_a_1096_);
lean_dec(v_a_1096_);
lean_dec_ref(v_a_1095_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0(lean_object* v_00_u03b2_1099_, lean_object* v_m_1100_, lean_object* v_a_1101_){
_start:
{
lean_object* v___x_1102_; 
v___x_1102_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0___redArg(v_m_1100_, v_a_1101_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0___boxed(lean_object* v_00_u03b2_1103_, lean_object* v_m_1104_, lean_object* v_a_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0(v_00_u03b2_1103_, v_m_1104_, v_a_1105_);
lean_dec(v_a_1105_);
lean_dec_ref(v_m_1104_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_labelled_spec__1(lean_object* v_00_u03b1_1107_, lean_object* v_msg_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
lean_object* v___x_1112_; 
v___x_1112_ = l_Lean_throwError___at___00Lean_labelled_spec__1___redArg(v_msg_1108_, v___y_1109_, v___y_1110_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_labelled_spec__1___boxed(lean_object* v_00_u03b1_1113_, lean_object* v_msg_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l_Lean_throwError___at___00Lean_labelled_spec__1(v_00_u03b1_1113_, v_msg_1114_, v___y_1115_, v___y_1116_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0(lean_object* v_00_u03b2_1119_, lean_object* v_m_1120_, lean_object* v_query_1121_){
_start:
{
lean_object* v___x_1122_; 
v___x_1122_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0___redArg(v_m_1120_, v_query_1121_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1123_, lean_object* v_m_1124_, lean_object* v_query_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0(v_00_u03b2_1123_, v_m_1124_, v_query_1125_);
lean_dec(v_query_1125_);
lean_dec_ref(v_m_1124_);
return v_res_1126_;
}
}
lean_object* runtime_initialize_Lean_DocString(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_LabelAttribute(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_DocString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_LabelAttribute_0__Lean_initFn_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_labelExtensionMapRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_labelExtensionMapRef);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Data_String_Extra(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Name(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_LabelAttribute(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Data_String_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_mkLabelExt___auto__1 = _init_l_Lean_mkLabelExt___auto__1();
lean_mark_persistent(l_Lean_mkLabelExt___auto__1);
l_Lean_mkLabelAttr___auto__1 = _init_l_Lean_mkLabelAttr___auto__1();
lean_mark_persistent(l_Lean_mkLabelAttr___auto__1);
l_Lean_registerLabelAttr___auto__1 = _init_l_Lean_registerLabelAttr___auto__1();
lean_mark_persistent(l_Lean_registerLabelAttr___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_DocString(uint8_t builtin);
lean_object* initialize_Init_Data_String_Extra(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Name(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_LabelAttribute(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_DocString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_LabelAttribute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_LabelAttribute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_LabelAttribute(builtin);
}
#ifdef __cplusplus
}
#endif
