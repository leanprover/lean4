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
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
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
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerLabelAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerLabelAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_LabelAttribute_0__Lean_initFn___closed__0_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = lean_unsigned_to_nat(16u);
v___x_3_ = lean_mk_array(v___x_2_, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_l___private_Lean_LabelAttribute_0__Lean_initFn___closed__1_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_obj_once(&l___private_Lean_LabelAttribute_0__Lean_initFn___closed__0_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2_, &l___private_Lean_LabelAttribute_0__Lean_initFn___closed__0_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2__once, _init_l___private_Lean_LabelAttribute_0__Lean_initFn___closed__0_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2_);
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_4_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LabelAttribute_0__Lean_initFn_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_8_ = lean_obj_once(&l___private_Lean_LabelAttribute_0__Lean_initFn___closed__1_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2_, &l___private_Lean_LabelAttribute_0__Lean_initFn___closed__1_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2__once, _init_l___private_Lean_LabelAttribute_0__Lean_initFn___closed__1_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2_);
v___x_9_ = lean_st_mk_ref(v___x_8_);
v___x_10_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LabelAttribute_0__Lean_initFn_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2____boxed(lean_object* v_a_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l___private_Lean_LabelAttribute_0__Lean_initFn_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2_();
return v_res_12_;
}
}
static lean_object* _init_l_Lean_mkLabelExt___auto__1___closed__12(void){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_39_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__10));
v___x_40_ = l_Lean_mkAtom(v___x_39_);
return v___x_40_;
}
}
static lean_object* _init_l_Lean_mkLabelExt___auto__1___closed__13(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_41_ = lean_obj_once(&l_Lean_mkLabelExt___auto__1___closed__12, &l_Lean_mkLabelExt___auto__1___closed__12_once, _init_l_Lean_mkLabelExt___auto__1___closed__12);
v___x_42_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__5));
v___x_43_ = lean_array_push(v___x_42_, v___x_41_);
return v___x_43_;
}
}
static lean_object* _init_l_Lean_mkLabelExt___auto__1___closed__18(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__17));
v___x_53_ = l_Lean_mkAtom(v___x_52_);
return v___x_53_;
}
}
static lean_object* _init_l_Lean_mkLabelExt___auto__1___closed__19(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_54_ = lean_obj_once(&l_Lean_mkLabelExt___auto__1___closed__18, &l_Lean_mkLabelExt___auto__1___closed__18_once, _init_l_Lean_mkLabelExt___auto__1___closed__18);
v___x_55_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__5));
v___x_56_ = lean_array_push(v___x_55_, v___x_54_);
return v___x_56_;
}
}
static lean_object* _init_l_Lean_mkLabelExt___auto__1___closed__20(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_57_ = lean_obj_once(&l_Lean_mkLabelExt___auto__1___closed__19, &l_Lean_mkLabelExt___auto__1___closed__19_once, _init_l_Lean_mkLabelExt___auto__1___closed__19);
v___x_58_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__16));
v___x_59_ = lean_box(2);
v___x_60_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
lean_ctor_set(v___x_60_, 1, v___x_58_);
lean_ctor_set(v___x_60_, 2, v___x_57_);
return v___x_60_;
}
}
static lean_object* _init_l_Lean_mkLabelExt___auto__1___closed__21(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_61_ = lean_obj_once(&l_Lean_mkLabelExt___auto__1___closed__20, &l_Lean_mkLabelExt___auto__1___closed__20_once, _init_l_Lean_mkLabelExt___auto__1___closed__20);
v___x_62_ = lean_obj_once(&l_Lean_mkLabelExt___auto__1___closed__13, &l_Lean_mkLabelExt___auto__1___closed__13_once, _init_l_Lean_mkLabelExt___auto__1___closed__13);
v___x_63_ = lean_array_push(v___x_62_, v___x_61_);
return v___x_63_;
}
}
static lean_object* _init_l_Lean_mkLabelExt___auto__1___closed__22(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_64_ = lean_obj_once(&l_Lean_mkLabelExt___auto__1___closed__21, &l_Lean_mkLabelExt___auto__1___closed__21_once, _init_l_Lean_mkLabelExt___auto__1___closed__21);
v___x_65_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__11));
v___x_66_ = lean_box(2);
v___x_67_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
lean_ctor_set(v___x_67_, 1, v___x_65_);
lean_ctor_set(v___x_67_, 2, v___x_64_);
return v___x_67_;
}
}
static lean_object* _init_l_Lean_mkLabelExt___auto__1___closed__23(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_68_ = lean_obj_once(&l_Lean_mkLabelExt___auto__1___closed__22, &l_Lean_mkLabelExt___auto__1___closed__22_once, _init_l_Lean_mkLabelExt___auto__1___closed__22);
v___x_69_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__5));
v___x_70_ = lean_array_push(v___x_69_, v___x_68_);
return v___x_70_;
}
}
static lean_object* _init_l_Lean_mkLabelExt___auto__1___closed__24(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_71_ = lean_obj_once(&l_Lean_mkLabelExt___auto__1___closed__23, &l_Lean_mkLabelExt___auto__1___closed__23_once, _init_l_Lean_mkLabelExt___auto__1___closed__23);
v___x_72_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__9));
v___x_73_ = lean_box(2);
v___x_74_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
lean_ctor_set(v___x_74_, 1, v___x_72_);
lean_ctor_set(v___x_74_, 2, v___x_71_);
return v___x_74_;
}
}
static lean_object* _init_l_Lean_mkLabelExt___auto__1___closed__25(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_75_ = lean_obj_once(&l_Lean_mkLabelExt___auto__1___closed__24, &l_Lean_mkLabelExt___auto__1___closed__24_once, _init_l_Lean_mkLabelExt___auto__1___closed__24);
v___x_76_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__5));
v___x_77_ = lean_array_push(v___x_76_, v___x_75_);
return v___x_77_;
}
}
static lean_object* _init_l_Lean_mkLabelExt___auto__1___closed__26(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_78_ = lean_obj_once(&l_Lean_mkLabelExt___auto__1___closed__25, &l_Lean_mkLabelExt___auto__1___closed__25_once, _init_l_Lean_mkLabelExt___auto__1___closed__25);
v___x_79_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__7));
v___x_80_ = lean_box(2);
v___x_81_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set(v___x_81_, 1, v___x_79_);
lean_ctor_set(v___x_81_, 2, v___x_78_);
return v___x_81_;
}
}
static lean_object* _init_l_Lean_mkLabelExt___auto__1___closed__27(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_82_ = lean_obj_once(&l_Lean_mkLabelExt___auto__1___closed__26, &l_Lean_mkLabelExt___auto__1___closed__26_once, _init_l_Lean_mkLabelExt___auto__1___closed__26);
v___x_83_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__5));
v___x_84_ = lean_array_push(v___x_83_, v___x_82_);
return v___x_84_;
}
}
static lean_object* _init_l_Lean_mkLabelExt___auto__1___closed__28(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_85_ = lean_obj_once(&l_Lean_mkLabelExt___auto__1___closed__27, &l_Lean_mkLabelExt___auto__1___closed__27_once, _init_l_Lean_mkLabelExt___auto__1___closed__27);
v___x_86_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__4));
v___x_87_ = lean_box(2);
v___x_88_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
lean_ctor_set(v___x_88_, 1, v___x_86_);
lean_ctor_set(v___x_88_, 2, v___x_85_);
return v___x_88_;
}
}
static lean_object* _init_l_Lean_mkLabelExt___auto__1(void){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = lean_obj_once(&l_Lean_mkLabelExt___auto__1___closed__28, &l_Lean_mkLabelExt___auto__1___closed__28_once, _init_l_Lean_mkLabelExt___auto__1___closed__28);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelExt___lam__0(lean_object* v_x_90_, lean_object* v_a_91_){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_92_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_92_, 0, v_a_91_);
lean_inc_ref_n(v___x_92_, 2);
v___x_93_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
lean_ctor_set(v___x_93_, 2, v___x_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelExt___lam__0___boxed(lean_object* v_x_94_, lean_object* v_a_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_mkLabelExt___lam__0(v_x_94_, v_a_95_);
lean_dec_ref(v_x_94_);
return v_res_96_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_mkLabelExt_spec__0_spec__0(lean_object* v_a_97_, lean_object* v_as_98_, size_t v_i_99_, size_t v_stop_100_){
_start:
{
uint8_t v___x_101_; 
v___x_101_ = lean_usize_dec_eq(v_i_99_, v_stop_100_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_102_ = lean_array_uget_borrowed(v_as_98_, v_i_99_);
v___x_103_ = lean_name_eq(v_a_97_, v___x_102_);
if (v___x_103_ == 0)
{
size_t v___x_104_; size_t v___x_105_; 
v___x_104_ = ((size_t)1ULL);
v___x_105_ = lean_usize_add(v_i_99_, v___x_104_);
v_i_99_ = v___x_105_;
goto _start;
}
else
{
return v___x_103_;
}
}
else
{
uint8_t v___x_107_; 
v___x_107_ = 0;
return v___x_107_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_mkLabelExt_spec__0_spec__0___boxed(lean_object* v_a_108_, lean_object* v_as_109_, lean_object* v_i_110_, lean_object* v_stop_111_){
_start:
{
size_t v_i_boxed_112_; size_t v_stop_boxed_113_; uint8_t v_res_114_; lean_object* v_r_115_; 
v_i_boxed_112_ = lean_unbox_usize(v_i_110_);
lean_dec(v_i_110_);
v_stop_boxed_113_ = lean_unbox_usize(v_stop_111_);
lean_dec(v_stop_111_);
v_res_114_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_mkLabelExt_spec__0_spec__0(v_a_108_, v_as_109_, v_i_boxed_112_, v_stop_boxed_113_);
lean_dec_ref(v_as_109_);
lean_dec(v_a_108_);
v_r_115_ = lean_box(v_res_114_);
return v_r_115_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_mkLabelExt_spec__0(lean_object* v_as_116_, lean_object* v_a_117_){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_118_ = lean_unsigned_to_nat(0u);
v___x_119_ = lean_array_get_size(v_as_116_);
v___x_120_ = lean_nat_dec_lt(v___x_118_, v___x_119_);
if (v___x_120_ == 0)
{
return v___x_120_;
}
else
{
if (v___x_120_ == 0)
{
return v___x_120_;
}
else
{
size_t v___x_121_; size_t v___x_122_; uint8_t v___x_123_; 
v___x_121_ = ((size_t)0ULL);
v___x_122_ = lean_usize_of_nat(v___x_119_);
v___x_123_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_mkLabelExt_spec__0_spec__0(v_a_117_, v_as_116_, v___x_121_, v___x_122_);
return v___x_123_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_mkLabelExt_spec__0___boxed(lean_object* v_as_124_, lean_object* v_a_125_){
_start:
{
uint8_t v_res_126_; lean_object* v_r_127_; 
v_res_126_ = l_Array_contains___at___00Lean_mkLabelExt_spec__0(v_as_124_, v_a_125_);
lean_dec(v_a_125_);
lean_dec_ref(v_as_124_);
v_r_127_ = lean_box(v_res_126_);
return v_r_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelExt___lam__1(lean_object* v_d_128_, lean_object* v_e_129_){
_start:
{
uint8_t v___x_130_; 
v___x_130_ = l_Array_contains___at___00Lean_mkLabelExt_spec__0(v_d_128_, v_e_129_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; 
v___x_131_ = lean_array_push(v_d_128_, v_e_129_);
return v___x_131_;
}
else
{
lean_dec(v_e_129_);
return v_d_128_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelExt___lam__2(lean_object* v___y_132_){
_start:
{
lean_inc_ref(v___y_132_);
return v___y_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelExt___lam__2___boxed(lean_object* v___y_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Lean_mkLabelExt___lam__2(v___y_133_);
lean_dec_ref(v___y_133_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelExt(lean_object* v_name_140_){
_start:
{
lean_object* v___f_142_; lean_object* v___f_143_; lean_object* v___f_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___f_142_ = ((lean_object*)(l_Lean_mkLabelExt___closed__0));
v___f_143_ = ((lean_object*)(l_Lean_mkLabelExt___closed__1));
v___f_144_ = ((lean_object*)(l_Lean_mkLabelExt___closed__2));
v___x_145_ = ((lean_object*)(l_Lean_mkLabelExt___closed__3));
v___x_146_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_146_, 0, v_name_140_);
lean_ctor_set(v___x_146_, 1, v___f_143_);
lean_ctor_set(v___x_146_, 2, v___x_145_);
lean_ctor_set(v___x_146_, 3, v___f_144_);
lean_ctor_set(v___x_146_, 4, v___f_142_);
v___x_147_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelExt___boxed(lean_object* v_name_148_, lean_object* v_a_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Lean_mkLabelExt(v_name_148_);
return v_res_150_;
}
}
static lean_object* _init_l_Lean_mkLabelAttr___auto__1(void){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = lean_obj_once(&l_Lean_mkLabelExt___auto__1___closed__28, &l_Lean_mkLabelExt___auto__1___closed__28_once, _init_l_Lean_mkLabelExt___auto__1___closed__28);
return v___x_151_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_152_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__0);
v___x_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
return v___x_154_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__1);
v___x_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
lean_ctor_set(v___x_156_, 1, v___x_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg(lean_object* v_ext_157_, lean_object* v_b_158_, uint8_t v_kind_159_, lean_object* v___y_160_, lean_object* v___y_161_){
_start:
{
lean_object* v_currNamespace_163_; lean_object* v___x_164_; lean_object* v_env_165_; lean_object* v_nextMacroScope_166_; lean_object* v_ngen_167_; lean_object* v_auxDeclNGen_168_; lean_object* v_traceState_169_; lean_object* v_messages_170_; lean_object* v_infoState_171_; lean_object* v_snapshotTasks_172_; lean_object* v_newDecls_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_185_; 
v_currNamespace_163_ = lean_ctor_get(v___y_160_, 6);
v___x_164_ = lean_st_ref_take(v___y_161_);
v_env_165_ = lean_ctor_get(v___x_164_, 0);
v_nextMacroScope_166_ = lean_ctor_get(v___x_164_, 1);
v_ngen_167_ = lean_ctor_get(v___x_164_, 2);
v_auxDeclNGen_168_ = lean_ctor_get(v___x_164_, 3);
v_traceState_169_ = lean_ctor_get(v___x_164_, 4);
v_messages_170_ = lean_ctor_get(v___x_164_, 6);
v_infoState_171_ = lean_ctor_get(v___x_164_, 7);
v_snapshotTasks_172_ = lean_ctor_get(v___x_164_, 8);
v_newDecls_173_ = lean_ctor_get(v___x_164_, 9);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_164_);
if (v_isSharedCheck_185_ == 0)
{
lean_object* v_unused_186_; 
v_unused_186_ = lean_ctor_get(v___x_164_, 5);
lean_dec(v_unused_186_);
v___x_175_ = v___x_164_;
v_isShared_176_ = v_isSharedCheck_185_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_newDecls_173_);
lean_inc(v_snapshotTasks_172_);
lean_inc(v_infoState_171_);
lean_inc(v_messages_170_);
lean_inc(v_traceState_169_);
lean_inc(v_auxDeclNGen_168_);
lean_inc(v_ngen_167_);
lean_inc(v_nextMacroScope_166_);
lean_inc(v_env_165_);
lean_dec(v___x_164_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_185_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_180_; 
lean_inc(v_currNamespace_163_);
v___x_177_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_165_, v_ext_157_, v_b_158_, v_kind_159_, v_currNamespace_163_);
v___x_178_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__2);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 5, v___x_178_);
lean_ctor_set(v___x_175_, 0, v___x_177_);
v___x_180_ = v___x_175_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___x_177_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v_nextMacroScope_166_);
lean_ctor_set(v_reuseFailAlloc_184_, 2, v_ngen_167_);
lean_ctor_set(v_reuseFailAlloc_184_, 3, v_auxDeclNGen_168_);
lean_ctor_set(v_reuseFailAlloc_184_, 4, v_traceState_169_);
lean_ctor_set(v_reuseFailAlloc_184_, 5, v___x_178_);
lean_ctor_set(v_reuseFailAlloc_184_, 6, v_messages_170_);
lean_ctor_set(v_reuseFailAlloc_184_, 7, v_infoState_171_);
lean_ctor_set(v_reuseFailAlloc_184_, 8, v_snapshotTasks_172_);
lean_ctor_set(v_reuseFailAlloc_184_, 9, v_newDecls_173_);
v___x_180_ = v_reuseFailAlloc_184_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_181_ = lean_st_ref_set(v___y_161_, v___x_180_);
v___x_182_ = lean_box(0);
v___x_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
return v___x_183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___boxed(lean_object* v_ext_187_, lean_object* v_b_188_, lean_object* v_kind_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_){
_start:
{
uint8_t v_kind_boxed_193_; lean_object* v_res_194_; 
v_kind_boxed_193_ = lean_unbox(v_kind_189_);
v_res_194_ = l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg(v_ext_187_, v_b_188_, v_kind_boxed_193_, v___y_190_, v___y_191_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0(lean_object* v_00_u03b1_195_, lean_object* v_00_u03b2_196_, lean_object* v_00_u03c3_197_, lean_object* v_ext_198_, lean_object* v_b_199_, uint8_t v_kind_200_, lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg(v_ext_198_, v_b_199_, v_kind_200_, v___y_201_, v___y_202_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___boxed(lean_object* v_00_u03b1_205_, lean_object* v_00_u03b2_206_, lean_object* v_00_u03c3_207_, lean_object* v_ext_208_, lean_object* v_b_209_, lean_object* v_kind_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
uint8_t v_kind_boxed_214_; lean_object* v_res_215_; 
v_kind_boxed_214_ = lean_unbox(v_kind_210_);
v_res_215_ = l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0(v_00_u03b1_205_, v_00_u03b2_206_, v_00_u03c3_207_, v_ext_208_, v_b_209_, v_kind_boxed_214_, v___y_211_, v___y_212_);
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelAttr___lam__0(lean_object* v_ext_216_, lean_object* v_declName_217_, lean_object* v_x_218_, uint8_t v_kind_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg(v_ext_216_, v_declName_217_, v_kind_219_, v___y_220_, v___y_221_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelAttr___lam__0___boxed(lean_object* v_ext_224_, lean_object* v_declName_225_, lean_object* v_x_226_, lean_object* v_kind_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_){
_start:
{
uint8_t v_kind_boxed_231_; lean_object* v_res_232_; 
v_kind_boxed_231_ = lean_unbox(v_kind_227_);
v_res_232_ = l_Lean_mkLabelAttr___lam__0(v_ext_224_, v_declName_225_, v_x_226_, v_kind_boxed_231_, v___y_228_, v___y_229_);
lean_dec(v___y_229_);
lean_dec_ref(v___y_228_);
lean_dec(v_x_226_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_mkLabelAttr_spec__1_spec__1_spec__2(lean_object* v_xs_233_, lean_object* v_v_234_, lean_object* v_i_235_){
_start:
{
lean_object* v___x_236_; uint8_t v___x_237_; 
v___x_236_ = lean_array_get_size(v_xs_233_);
v___x_237_ = lean_nat_dec_lt(v_i_235_, v___x_236_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; 
lean_dec(v_i_235_);
v___x_238_ = lean_box(0);
return v___x_238_;
}
else
{
lean_object* v___x_239_; uint8_t v___x_240_; 
v___x_239_ = lean_array_fget_borrowed(v_xs_233_, v_i_235_);
v___x_240_ = lean_name_eq(v___x_239_, v_v_234_);
if (v___x_240_ == 0)
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = lean_unsigned_to_nat(1u);
v___x_242_ = lean_nat_add(v_i_235_, v___x_241_);
lean_dec(v_i_235_);
v_i_235_ = v___x_242_;
goto _start;
}
else
{
lean_object* v___x_244_; 
v___x_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_244_, 0, v_i_235_);
return v___x_244_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_mkLabelAttr_spec__1_spec__1_spec__2___boxed(lean_object* v_xs_245_, lean_object* v_v_246_, lean_object* v_i_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_mkLabelAttr_spec__1_spec__1_spec__2(v_xs_245_, v_v_246_, v_i_247_);
lean_dec(v_v_246_);
lean_dec_ref(v_xs_245_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_mkLabelAttr_spec__1_spec__1(lean_object* v_xs_249_, lean_object* v_v_250_){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = lean_unsigned_to_nat(0u);
v___x_252_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_mkLabelAttr_spec__1_spec__1_spec__2(v_xs_249_, v_v_250_, v___x_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_mkLabelAttr_spec__1_spec__1___boxed(lean_object* v_xs_253_, lean_object* v_v_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_mkLabelAttr_spec__1_spec__1(v_xs_253_, v_v_254_);
lean_dec(v_v_254_);
lean_dec_ref(v_xs_253_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Array_erase___at___00Lean_mkLabelAttr_spec__1(lean_object* v_as_256_, lean_object* v_a_257_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = l_Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_mkLabelAttr_spec__1_spec__1(v_as_256_, v_a_257_);
if (lean_obj_tag(v___x_258_) == 0)
{
return v_as_256_;
}
else
{
lean_object* v_val_259_; lean_object* v___x_260_; 
v_val_259_ = lean_ctor_get(v___x_258_, 0);
lean_inc(v_val_259_);
lean_dec_ref(v___x_258_);
v___x_260_ = l_Array_eraseIdx___redArg(v_as_256_, v_val_259_);
return v___x_260_;
}
}
}
LEAN_EXPORT lean_object* l_Array_erase___at___00Lean_mkLabelAttr_spec__1___boxed(lean_object* v_as_261_, lean_object* v_a_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Array_erase___at___00Lean_mkLabelAttr_spec__1(v_as_261_, v_a_262_);
lean_dec(v_a_262_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelAttr___lam__1(lean_object* v___x_264_, lean_object* v_declName_265_, lean_object* v_x_266_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l_Array_erase___at___00Lean_mkLabelAttr_spec__1(v___x_264_, v_declName_265_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelAttr___lam__1___boxed(lean_object* v___x_268_, lean_object* v_declName_269_, lean_object* v_x_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Lean_mkLabelAttr___lam__1(v___x_268_, v_declName_269_, v_x_270_);
lean_dec_ref(v_x_270_);
lean_dec(v_declName_269_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelAttr___lam__2(lean_object* v_ext_272_, lean_object* v___x_273_, lean_object* v_declName_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v_ext_280_; lean_object* v_toEnvExtension_281_; lean_object* v_env_282_; lean_object* v_asyncMode_283_; lean_object* v_env_284_; lean_object* v_nextMacroScope_285_; lean_object* v_ngen_286_; lean_object* v_auxDeclNGen_287_; lean_object* v_traceState_288_; lean_object* v_messages_289_; lean_object* v_infoState_290_; lean_object* v_snapshotTasks_291_; lean_object* v_newDecls_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_306_; 
v___x_278_ = lean_st_ref_get(v___y_276_);
v___x_279_ = lean_st_ref_take(v___y_276_);
v_ext_280_ = lean_ctor_get(v_ext_272_, 1);
v_toEnvExtension_281_ = lean_ctor_get(v_ext_280_, 0);
v_env_282_ = lean_ctor_get(v___x_278_, 0);
lean_inc_ref(v_env_282_);
lean_dec(v___x_278_);
v_asyncMode_283_ = lean_ctor_get(v_toEnvExtension_281_, 2);
v_env_284_ = lean_ctor_get(v___x_279_, 0);
v_nextMacroScope_285_ = lean_ctor_get(v___x_279_, 1);
v_ngen_286_ = lean_ctor_get(v___x_279_, 2);
v_auxDeclNGen_287_ = lean_ctor_get(v___x_279_, 3);
v_traceState_288_ = lean_ctor_get(v___x_279_, 4);
v_messages_289_ = lean_ctor_get(v___x_279_, 6);
v_infoState_290_ = lean_ctor_get(v___x_279_, 7);
v_snapshotTasks_291_ = lean_ctor_get(v___x_279_, 8);
v_newDecls_292_ = lean_ctor_get(v___x_279_, 9);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_306_ == 0)
{
lean_object* v_unused_307_; 
v_unused_307_ = lean_ctor_get(v___x_279_, 5);
lean_dec(v_unused_307_);
v___x_294_ = v___x_279_;
v_isShared_295_ = v_isSharedCheck_306_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_newDecls_292_);
lean_inc(v_snapshotTasks_291_);
lean_inc(v_infoState_290_);
lean_inc(v_messages_289_);
lean_inc(v_traceState_288_);
lean_inc(v_auxDeclNGen_287_);
lean_inc(v_ngen_286_);
lean_inc(v_nextMacroScope_285_);
lean_inc(v_env_284_);
lean_dec(v___x_279_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_306_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_296_; lean_object* v___f_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_301_; 
v___x_296_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_273_, v_ext_272_, v_env_282_, v_asyncMode_283_);
v___f_297_ = lean_alloc_closure((void*)(l_Lean_mkLabelAttr___lam__1___boxed), 3, 2);
lean_closure_set(v___f_297_, 0, v___x_296_);
lean_closure_set(v___f_297_, 1, v_declName_274_);
v___x_298_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_272_, v_env_284_, v___f_297_);
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
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v___x_298_);
lean_ctor_set(v_reuseFailAlloc_305_, 1, v_nextMacroScope_285_);
lean_ctor_set(v_reuseFailAlloc_305_, 2, v_ngen_286_);
lean_ctor_set(v_reuseFailAlloc_305_, 3, v_auxDeclNGen_287_);
lean_ctor_set(v_reuseFailAlloc_305_, 4, v_traceState_288_);
lean_ctor_set(v_reuseFailAlloc_305_, 5, v___x_299_);
lean_ctor_set(v_reuseFailAlloc_305_, 6, v_messages_289_);
lean_ctor_set(v_reuseFailAlloc_305_, 7, v_infoState_290_);
lean_ctor_set(v_reuseFailAlloc_305_, 8, v_snapshotTasks_291_);
lean_ctor_set(v_reuseFailAlloc_305_, 9, v_newDecls_292_);
v___x_301_ = v_reuseFailAlloc_305_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_302_ = lean_st_ref_set(v___y_276_, v___x_301_);
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
static uint64_t _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_335_; uint64_t v___x_336_; 
v___x_335_ = lean_unsigned_to_nat(1723u);
v___x_336_ = lean_uint64_of_nat(v___x_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_337_, lean_object* v_x_338_){
_start:
{
if (lean_obj_tag(v_x_338_) == 0)
{
return v_x_337_;
}
else
{
lean_object* v_key_339_; lean_object* v_value_340_; lean_object* v_tail_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_367_; 
v_key_339_ = lean_ctor_get(v_x_338_, 0);
v_value_340_ = lean_ctor_get(v_x_338_, 1);
v_tail_341_ = lean_ctor_get(v_x_338_, 2);
v_isSharedCheck_367_ = !lean_is_exclusive(v_x_338_);
if (v_isSharedCheck_367_ == 0)
{
v___x_343_ = v_x_338_;
v_isShared_344_ = v_isSharedCheck_367_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_tail_341_);
lean_inc(v_value_340_);
lean_inc(v_key_339_);
lean_dec(v_x_338_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_367_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_345_; uint64_t v___y_347_; 
v___x_345_ = lean_array_get_size(v_x_337_);
if (lean_obj_tag(v_key_339_) == 0)
{
uint64_t v___x_365_; 
v___x_365_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2_spec__3___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
v___y_347_ = v___x_365_;
goto v___jp_346_;
}
else
{
uint64_t v_hash_366_; 
v_hash_366_ = lean_ctor_get_uint64(v_key_339_, sizeof(void*)*2);
v___y_347_ = v_hash_366_;
goto v___jp_346_;
}
v___jp_346_:
{
uint64_t v___x_348_; uint64_t v___x_349_; uint64_t v_fold_350_; uint64_t v___x_351_; uint64_t v___x_352_; uint64_t v___x_353_; size_t v___x_354_; size_t v___x_355_; size_t v___x_356_; size_t v___x_357_; size_t v___x_358_; lean_object* v___x_359_; lean_object* v___x_361_; 
v___x_348_ = 32ULL;
v___x_349_ = lean_uint64_shift_right(v___y_347_, v___x_348_);
v_fold_350_ = lean_uint64_xor(v___y_347_, v___x_349_);
v___x_351_ = 16ULL;
v___x_352_ = lean_uint64_shift_right(v_fold_350_, v___x_351_);
v___x_353_ = lean_uint64_xor(v_fold_350_, v___x_352_);
v___x_354_ = lean_uint64_to_usize(v___x_353_);
v___x_355_ = lean_usize_of_nat(v___x_345_);
v___x_356_ = ((size_t)1ULL);
v___x_357_ = lean_usize_sub(v___x_355_, v___x_356_);
v___x_358_ = lean_usize_land(v___x_354_, v___x_357_);
v___x_359_ = lean_array_uget_borrowed(v_x_337_, v___x_358_);
lean_inc(v___x_359_);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 2, v___x_359_);
v___x_361_ = v___x_343_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_key_339_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v_value_340_);
lean_ctor_set(v_reuseFailAlloc_364_, 2, v___x_359_);
v___x_361_ = v_reuseFailAlloc_364_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
lean_object* v___x_362_; 
v___x_362_ = lean_array_uset(v_x_337_, v___x_358_, v___x_361_);
v_x_337_ = v___x_362_;
v_x_338_ = v_tail_341_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2___redArg(lean_object* v_i_368_, lean_object* v_source_369_, lean_object* v_target_370_){
_start:
{
lean_object* v___x_371_; uint8_t v___x_372_; 
v___x_371_ = lean_array_get_size(v_source_369_);
v___x_372_ = lean_nat_dec_lt(v_i_368_, v___x_371_);
if (v___x_372_ == 0)
{
lean_dec_ref(v_source_369_);
lean_dec(v_i_368_);
return v_target_370_;
}
else
{
lean_object* v_es_373_; lean_object* v___x_374_; lean_object* v_source_375_; lean_object* v_target_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v_es_373_ = lean_array_fget(v_source_369_, v_i_368_);
v___x_374_ = lean_box(0);
v_source_375_ = lean_array_fset(v_source_369_, v_i_368_, v___x_374_);
v_target_376_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_target_370_, v_es_373_);
v___x_377_ = lean_unsigned_to_nat(1u);
v___x_378_ = lean_nat_add(v_i_368_, v___x_377_);
lean_dec(v_i_368_);
v_i_368_ = v___x_378_;
v_source_369_ = v_source_375_;
v_target_370_ = v_target_376_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1___redArg(lean_object* v_data_380_){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v_nbuckets_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_381_ = lean_array_get_size(v_data_380_);
v___x_382_ = lean_unsigned_to_nat(2u);
v_nbuckets_383_ = lean_nat_mul(v___x_381_, v___x_382_);
v___x_384_ = lean_unsigned_to_nat(0u);
v___x_385_ = lean_box(0);
v___x_386_ = lean_mk_array(v_nbuckets_383_, v___x_385_);
v___x_387_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2___redArg(v___x_384_, v_data_380_, v___x_386_);
return v___x_387_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__0___redArg(lean_object* v_a_388_, lean_object* v_x_389_){
_start:
{
if (lean_obj_tag(v_x_389_) == 0)
{
uint8_t v___x_390_; 
v___x_390_ = 0;
return v___x_390_;
}
else
{
lean_object* v_key_391_; lean_object* v_tail_392_; uint8_t v___x_393_; 
v_key_391_ = lean_ctor_get(v_x_389_, 0);
v_tail_392_ = lean_ctor_get(v_x_389_, 2);
v___x_393_ = lean_name_eq(v_key_391_, v_a_388_);
if (v___x_393_ == 0)
{
v_x_389_ = v_tail_392_;
goto _start;
}
else
{
return v___x_393_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__0___redArg___boxed(lean_object* v_a_395_, lean_object* v_x_396_){
_start:
{
uint8_t v_res_397_; lean_object* v_r_398_; 
v_res_397_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__0___redArg(v_a_395_, v_x_396_);
lean_dec(v_x_396_);
lean_dec(v_a_395_);
v_r_398_ = lean_box(v_res_397_);
return v_r_398_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__2___redArg(lean_object* v_a_399_, lean_object* v_b_400_, lean_object* v_x_401_){
_start:
{
if (lean_obj_tag(v_x_401_) == 0)
{
lean_dec(v_b_400_);
lean_dec(v_a_399_);
return v_x_401_;
}
else
{
lean_object* v_key_402_; lean_object* v_value_403_; lean_object* v_tail_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_416_; 
v_key_402_ = lean_ctor_get(v_x_401_, 0);
v_value_403_ = lean_ctor_get(v_x_401_, 1);
v_tail_404_ = lean_ctor_get(v_x_401_, 2);
v_isSharedCheck_416_ = !lean_is_exclusive(v_x_401_);
if (v_isSharedCheck_416_ == 0)
{
v___x_406_ = v_x_401_;
v_isShared_407_ = v_isSharedCheck_416_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_tail_404_);
lean_inc(v_value_403_);
lean_inc(v_key_402_);
lean_dec(v_x_401_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_416_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
uint8_t v___x_408_; 
v___x_408_ = lean_name_eq(v_key_402_, v_a_399_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; lean_object* v___x_411_; 
v___x_409_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__2___redArg(v_a_399_, v_b_400_, v_tail_404_);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 2, v___x_409_);
v___x_411_ = v___x_406_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_key_402_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v_value_403_);
lean_ctor_set(v_reuseFailAlloc_412_, 2, v___x_409_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
else
{
lean_object* v___x_414_; 
lean_dec(v_value_403_);
lean_dec(v_key_402_);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 1, v_b_400_);
lean_ctor_set(v___x_406_, 0, v_a_399_);
v___x_414_ = v___x_406_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_a_399_);
lean_ctor_set(v_reuseFailAlloc_415_, 1, v_b_400_);
lean_ctor_set(v_reuseFailAlloc_415_, 2, v_tail_404_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0___redArg(lean_object* v_m_417_, lean_object* v_a_418_, lean_object* v_b_419_){
_start:
{
lean_object* v_size_420_; lean_object* v_buckets_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_467_; 
v_size_420_ = lean_ctor_get(v_m_417_, 0);
v_buckets_421_ = lean_ctor_get(v_m_417_, 1);
v_isSharedCheck_467_ = !lean_is_exclusive(v_m_417_);
if (v_isSharedCheck_467_ == 0)
{
v___x_423_ = v_m_417_;
v_isShared_424_ = v_isSharedCheck_467_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_buckets_421_);
lean_inc(v_size_420_);
lean_dec(v_m_417_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_467_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_425_; uint64_t v___y_427_; 
v___x_425_ = lean_array_get_size(v_buckets_421_);
if (lean_obj_tag(v_a_418_) == 0)
{
uint64_t v___x_465_; 
v___x_465_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2_spec__3___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
v___y_427_ = v___x_465_;
goto v___jp_426_;
}
else
{
uint64_t v_hash_466_; 
v_hash_466_ = lean_ctor_get_uint64(v_a_418_, sizeof(void*)*2);
v___y_427_ = v_hash_466_;
goto v___jp_426_;
}
v___jp_426_:
{
uint64_t v___x_428_; uint64_t v___x_429_; uint64_t v_fold_430_; uint64_t v___x_431_; uint64_t v___x_432_; uint64_t v___x_433_; size_t v___x_434_; size_t v___x_435_; size_t v___x_436_; size_t v___x_437_; size_t v___x_438_; lean_object* v_bkt_439_; uint8_t v___x_440_; 
v___x_428_ = 32ULL;
v___x_429_ = lean_uint64_shift_right(v___y_427_, v___x_428_);
v_fold_430_ = lean_uint64_xor(v___y_427_, v___x_429_);
v___x_431_ = 16ULL;
v___x_432_ = lean_uint64_shift_right(v_fold_430_, v___x_431_);
v___x_433_ = lean_uint64_xor(v_fold_430_, v___x_432_);
v___x_434_ = lean_uint64_to_usize(v___x_433_);
v___x_435_ = lean_usize_of_nat(v___x_425_);
v___x_436_ = ((size_t)1ULL);
v___x_437_ = lean_usize_sub(v___x_435_, v___x_436_);
v___x_438_ = lean_usize_land(v___x_434_, v___x_437_);
v_bkt_439_ = lean_array_uget_borrowed(v_buckets_421_, v___x_438_);
v___x_440_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__0___redArg(v_a_418_, v_bkt_439_);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; lean_object* v_size_x27_442_; lean_object* v___x_443_; lean_object* v_buckets_x27_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; uint8_t v___x_450_; 
v___x_441_ = lean_unsigned_to_nat(1u);
v_size_x27_442_ = lean_nat_add(v_size_420_, v___x_441_);
lean_dec(v_size_420_);
lean_inc(v_bkt_439_);
v___x_443_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_443_, 0, v_a_418_);
lean_ctor_set(v___x_443_, 1, v_b_419_);
lean_ctor_set(v___x_443_, 2, v_bkt_439_);
v_buckets_x27_444_ = lean_array_uset(v_buckets_421_, v___x_438_, v___x_443_);
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
v_val_451_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1___redArg(v_buckets_x27_444_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 1, v_val_451_);
lean_ctor_set(v___x_423_, 0, v_size_x27_442_);
v___x_453_ = v___x_423_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_size_x27_442_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_val_451_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
else
{
lean_object* v___x_456_; 
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 1, v_buckets_x27_444_);
lean_ctor_set(v___x_423_, 0, v_size_x27_442_);
v___x_456_ = v___x_423_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_size_x27_442_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v_buckets_x27_444_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
else
{
lean_object* v___x_458_; lean_object* v_buckets_x27_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_463_; 
lean_inc(v_bkt_439_);
v___x_458_ = lean_box(0);
v_buckets_x27_459_ = lean_array_uset(v_buckets_421_, v___x_438_, v___x_458_);
v___x_460_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__2___redArg(v_a_418_, v_b_419_, v_bkt_439_);
v___x_461_ = lean_array_uset(v_buckets_x27_459_, v___x_438_, v___x_460_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 1, v___x_461_);
v___x_463_ = v___x_423_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_size_420_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v___x_461_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerLabelAttr(lean_object* v_attrName_468_, lean_object* v_attrDescr_469_, lean_object* v_ref_470_){
_start:
{
lean_object* v___x_472_; 
lean_inc(v_ref_470_);
v___x_472_ = l_Lean_mkLabelExt(v_ref_470_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; lean_object* v___x_474_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc_n(v_a_473_, 2);
lean_dec_ref(v___x_472_);
lean_inc(v_attrName_468_);
v___x_474_ = l_Lean_mkLabelAttr(v_attrName_468_, v_attrDescr_469_, v_a_473_, v_ref_470_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_485_; 
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_485_ == 0)
{
lean_object* v_unused_486_; 
v_unused_486_ = lean_ctor_get(v___x_474_, 0);
lean_dec(v_unused_486_);
v___x_476_ = v___x_474_;
v_isShared_477_ = v_isSharedCheck_485_;
goto v_resetjp_475_;
}
else
{
lean_dec(v___x_474_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_485_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_483_; 
v___x_478_ = l_Lean_labelExtensionMapRef;
v___x_479_ = lean_st_ref_take(v___x_478_);
lean_inc(v_a_473_);
v___x_480_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0___redArg(v___x_479_, v_attrName_468_, v_a_473_);
v___x_481_ = lean_st_ref_set(v___x_478_, v___x_480_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 0, v_a_473_);
v___x_483_ = v___x_476_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_a_473_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
else
{
lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_494_; 
lean_dec(v_a_473_);
lean_dec(v_attrName_468_);
v_a_487_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_494_ == 0)
{
v___x_489_ = v___x_474_;
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v___x_474_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_492_; 
if (v_isShared_490_ == 0)
{
v___x_492_ = v___x_489_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_a_487_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
}
else
{
lean_dec(v_ref_470_);
lean_dec_ref(v_attrDescr_469_);
lean_dec(v_attrName_468_);
return v___x_472_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerLabelAttr___boxed(lean_object* v_attrName_495_, lean_object* v_attrDescr_496_, lean_object* v_ref_497_, lean_object* v_a_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Lean_registerLabelAttr(v_attrName_495_, v_attrDescr_496_, v_ref_497_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0(lean_object* v_00_u03b2_500_, lean_object* v_m_501_, lean_object* v_a_502_, lean_object* v_b_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0___redArg(v_m_501_, v_a_502_, v_b_503_);
return v___x_504_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__0(lean_object* v_00_u03b2_505_, lean_object* v_a_506_, lean_object* v_x_507_){
_start:
{
uint8_t v___x_508_; 
v___x_508_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__0___redArg(v_a_506_, v_x_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_509_, lean_object* v_a_510_, lean_object* v_x_511_){
_start:
{
uint8_t v_res_512_; lean_object* v_r_513_; 
v_res_512_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__0(v_00_u03b2_509_, v_a_510_, v_x_511_);
lean_dec(v_x_511_);
lean_dec(v_a_510_);
v_r_513_ = lean_box(v_res_512_);
return v_r_513_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1(lean_object* v_00_u03b2_514_, lean_object* v_data_515_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1___redArg(v_data_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__2(lean_object* v_00_u03b2_517_, lean_object* v_a_518_, lean_object* v_b_519_, lean_object* v_x_520_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__2___redArg(v_a_518_, v_b_519_, v_x_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_522_, lean_object* v_i_523_, lean_object* v_source_524_, lean_object* v_target_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2___redArg(v_i_523_, v_source_524_, v_target_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_527_, lean_object* v_x_528_, lean_object* v_x_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_x_528_, v_x_529_);
return v___x_530_;
}
}
static lean_object* _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__13(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__12));
v___x_601_ = l_String_toRawSubstring_x27(v___x_600_);
return v___x_601_;
}
}
static lean_object* _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__18(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__17));
v___x_612_ = l_String_toRawSubstring_x27(v___x_611_);
return v___x_612_;
}
}
static lean_object* _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__24(void){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__23));
v___x_624_ = l_String_toRawSubstring_x27(v___x_623_);
return v___x_624_;
}
}
static lean_object* _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__38(void){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_660_ = ((lean_object*)(l_Lean_Parser_Command_registerLabelAttr___closed__2));
v___x_661_ = l_String_toRawSubstring_x27(v___x_660_);
return v___x_661_;
}
}
static lean_object* _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__51(void){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l_Array_mkArray0(lean_box(0));
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1(lean_object* v_x_699_, lean_object* v_a_700_, lean_object* v_a_701_){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v___y_720_; lean_object* v___y_721_; lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v___y_724_; lean_object* v___y_725_; lean_object* v___y_726_; lean_object* v___y_727_; lean_object* v___y_776_; lean_object* v___y_777_; lean_object* v___y_778_; lean_object* v___y_779_; lean_object* v___y_780_; lean_object* v___y_781_; lean_object* v___y_782_; lean_object* v___y_783_; lean_object* v___y_784_; lean_object* v___y_785_; lean_object* v___y_786_; lean_object* v___y_787_; lean_object* v___y_788_; lean_object* v___y_789_; lean_object* v___x_837_; uint8_t v___x_838_; 
v___x_702_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__0));
v___x_703_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__1));
v___x_837_ = ((lean_object*)(l_Lean_Parser_Command_registerLabelAttr___closed__3));
lean_inc(v_x_699_);
v___x_838_ = l_Lean_Syntax_isOfKind(v_x_699_, v___x_837_);
if (v___x_838_ == 0)
{
lean_object* v___x_839_; lean_object* v___x_840_; 
lean_dec(v_x_699_);
v___x_839_ = lean_box(1);
v___x_840_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
lean_ctor_set(v___x_840_, 1, v_a_701_);
return v___x_840_;
}
else
{
lean_object* v___x_841_; lean_object* v___y_843_; lean_object* v___y_844_; uint8_t v___y_845_; lean_object* v___y_846_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v_id_866_; lean_object* v___y_868_; lean_object* v___x_879_; 
v___x_841_ = lean_unsigned_to_nat(0u);
v___x_864_ = l_Lean_Syntax_getArg(v_x_699_, v___x_841_);
v___x_865_ = lean_unsigned_to_nat(2u);
v_id_866_ = l_Lean_Syntax_getArg(v_x_699_, v___x_865_);
lean_dec(v_x_699_);
v___x_879_ = l_Lean_Syntax_getOptional_x3f(v___x_864_);
lean_dec(v___x_864_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v___x_880_; 
v___x_880_ = lean_box(0);
v___y_868_ = v___x_880_;
goto v___jp_867_;
}
else
{
lean_object* v_val_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
v_val_881_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_879_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_val_881_);
lean_dec(v___x_879_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_val_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
v___y_868_ = v___x_886_;
goto v___jp_867_;
}
}
}
v___jp_842_:
{
lean_object* v_quotContext_849_; lean_object* v_currMacroScope_850_; lean_object* v_ref_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v_quotContext_849_ = lean_ctor_get(v_a_700_, 1);
v_currMacroScope_850_ = lean_ctor_get(v_a_700_, 2);
v_ref_851_ = lean_ctor_get(v_a_700_, 5);
v___x_852_ = l_String_removeLeadingSpaces(v___y_848_);
v___x_853_ = lean_box(2);
v___x_854_ = l_Lean_Syntax_mkStrLit(v___x_852_, v___x_853_);
v___x_855_ = l_Lean_SourceInfo_fromRef(v_ref_851_, v___y_845_);
v___x_856_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__9));
v___x_857_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__47));
v___x_858_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__48));
v___x_859_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__50));
v___x_860_ = lean_obj_once(&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__51, &l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__51_once, _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__51);
if (lean_obj_tag(v___y_847_) == 1)
{
lean_object* v_val_861_; lean_object* v___x_862_; 
v_val_861_ = lean_ctor_get(v___y_847_, 0);
lean_inc(v_val_861_);
lean_dec_ref(v___y_847_);
v___x_862_ = l_Array_mkArray1___redArg(v_val_861_);
v___y_776_ = v___y_844_;
v___y_777_ = v___x_856_;
v___y_778_ = v___y_846_;
v___y_779_ = v___x_859_;
v___y_780_ = v___x_857_;
v___y_781_ = v___x_855_;
v___y_782_ = v___y_843_;
v___y_783_ = v_quotContext_849_;
v___y_784_ = v___x_854_;
v___y_785_ = v_currMacroScope_850_;
v___y_786_ = v___x_860_;
v___y_787_ = v___x_853_;
v___y_788_ = v___x_858_;
v___y_789_ = v___x_862_;
goto v___jp_775_;
}
else
{
lean_object* v___x_863_; 
lean_dec(v___y_847_);
v___x_863_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__5));
v___y_776_ = v___y_844_;
v___y_777_ = v___x_856_;
v___y_778_ = v___y_846_;
v___y_779_ = v___x_859_;
v___y_780_ = v___x_857_;
v___y_781_ = v___x_855_;
v___y_782_ = v___y_843_;
v___y_783_ = v_quotContext_849_;
v___y_784_ = v___x_854_;
v___y_785_ = v_currMacroScope_850_;
v___y_786_ = v___x_860_;
v___y_787_ = v___x_853_;
v___y_788_ = v___x_858_;
v___y_789_ = v___x_863_;
goto v___jp_775_;
}
}
v___jp_867_:
{
lean_object* v___x_869_; lean_object* v_str_870_; lean_object* v___x_871_; lean_object* v___x_872_; uint8_t v___x_873_; lean_object* v_idParser_874_; 
v___x_869_ = l_Lean_TSyntax_getId(v_id_866_);
lean_inc_n(v___x_869_, 2);
v_str_870_ = l_Lean_Name_toString(v___x_869_, v___x_838_);
v___x_871_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__53));
v___x_872_ = l_Lean_Name_append(v___x_871_, v___x_869_);
v___x_873_ = 0;
v_idParser_874_ = l_Lean_mkIdentFrom(v_id_866_, v___x_872_, v___x_873_);
lean_dec(v_id_866_);
if (lean_obj_tag(v___y_868_) == 0)
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__54));
v___x_876_ = lean_string_append(v___x_875_, v_str_870_);
v___y_843_ = v_str_870_;
v___y_844_ = v___x_869_;
v___y_845_ = v___x_873_;
v___y_846_ = v_idParser_874_;
v___y_847_ = v___y_868_;
v___y_848_ = v___x_876_;
goto v___jp_842_;
}
else
{
lean_object* v_val_877_; lean_object* v___x_878_; 
v_val_877_ = lean_ctor_get(v___y_868_, 0);
v___x_878_ = l_Lean_TSyntax_getDocString(v_val_877_);
v___y_843_ = v_str_870_;
v___y_844_ = v___x_869_;
v___y_845_ = v___x_873_;
v___y_846_ = v_idParser_874_;
v___y_847_ = v___y_868_;
v___y_848_ = v___x_878_;
goto v___jp_842_;
}
}
}
v___jp_704_:
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
lean_inc(v___y_727_);
lean_inc_n(v___y_709_, 5);
lean_inc_n(v___y_713_, 19);
v___x_728_ = l_Lean_Syntax_node3(v___y_713_, v___y_709_, v___y_727_, v___y_716_, v___y_727_);
lean_inc(v___y_724_);
v___x_729_ = l_Lean_Syntax_node2(v___y_713_, v___y_724_, v___y_712_, v___x_728_);
lean_inc(v___y_717_);
v___x_730_ = l_Lean_Syntax_node1(v___y_713_, v___y_717_, v___x_729_);
lean_inc_n(v___y_725_, 4);
lean_inc(v___y_718_);
v___x_731_ = l_Lean_Syntax_node2(v___y_713_, v___y_718_, v___x_730_, v___y_725_);
v___x_732_ = l_Lean_Syntax_node1(v___y_713_, v___y_709_, v___x_731_);
lean_inc(v___y_705_);
v___x_733_ = l_Lean_Syntax_node1(v___y_713_, v___y_705_, v___x_732_);
lean_inc(v___y_726_);
v___x_734_ = l_Lean_Syntax_node4(v___y_713_, v___y_726_, v___y_711_, v___y_722_, v___y_719_, v___x_733_);
v___x_735_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__0));
v___x_736_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__1));
v___x_737_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__2));
lean_inc_ref(v___y_707_);
v___x_738_ = l_Lean_Name_mkStr4(v___x_702_, v___x_703_, v___y_707_, v___x_737_);
v___x_739_ = l_Lean_Syntax_node1(v___y_713_, v___x_738_, v___y_725_);
v___x_740_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_740_, 0, v___y_713_);
lean_ctor_set(v___x_740_, 1, v___x_735_);
v___x_741_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__4));
v___x_742_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__5));
v___x_743_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_743_, 0, v___y_713_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
v___x_744_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__6));
v___x_745_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_745_, 0, v___y_713_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
v___x_746_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__7));
v___x_747_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_747_, 0, v___y_713_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
v___x_748_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__8));
v___x_749_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_749_, 0, v___y_713_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
v___x_750_ = l_Lean_Syntax_node5(v___y_713_, v___x_741_, v___x_743_, v___x_745_, v___x_747_, v___y_708_, v___x_749_);
v___x_751_ = l_Lean_Syntax_node1(v___y_713_, v___y_709_, v___x_750_);
v___x_752_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__11));
v___x_753_ = l_Lean_Syntax_mkStrLit(v___y_714_, v___y_723_);
v___x_754_ = l_Lean_Syntax_node1(v___y_713_, v___x_752_, v___x_753_);
v___x_755_ = l_Lean_Syntax_node1(v___y_713_, v___y_709_, v___x_754_);
v___x_756_ = lean_obj_once(&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__13, &l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__13_once, _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__13);
v___x_757_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__14));
lean_inc(v___y_721_);
lean_inc(v___y_715_);
v___x_758_ = l_Lean_addMacroScope(v___y_715_, v___x_757_, v___y_721_);
v___x_759_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_759_, 0, v___y_713_);
lean_ctor_set(v___x_759_, 1, v___x_756_);
lean_ctor_set(v___x_759_, 2, v___x_758_);
lean_ctor_set(v___x_759_, 3, v___y_706_);
v___x_760_ = lean_unsigned_to_nat(10u);
v___x_761_ = lean_mk_empty_array_with_capacity(v___x_760_);
v___x_762_ = lean_array_push(v___x_761_, v___y_710_);
v___x_763_ = lean_array_push(v___x_762_, v___y_725_);
v___x_764_ = lean_array_push(v___x_763_, v___x_739_);
v___x_765_ = lean_array_push(v___x_764_, v___x_740_);
v___x_766_ = lean_array_push(v___x_765_, v___y_725_);
v___x_767_ = lean_array_push(v___x_766_, v___x_751_);
v___x_768_ = lean_array_push(v___x_767_, v___y_725_);
v___x_769_ = lean_array_push(v___x_768_, v___x_755_);
v___x_770_ = lean_array_push(v___x_769_, v___y_720_);
v___x_771_ = lean_array_push(v___x_770_, v___x_759_);
v___x_772_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_772_, 0, v___y_713_);
lean_ctor_set(v___x_772_, 1, v___x_736_);
lean_ctor_set(v___x_772_, 2, v___x_771_);
v___x_773_ = l_Lean_Syntax_node2(v___y_713_, v___y_709_, v___x_734_, v___x_772_);
v___x_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
lean_ctor_set(v___x_774_, 1, v_a_701_);
return v___x_774_;
}
v___jp_775_:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
lean_inc_ref_n(v___y_786_, 2);
v___x_790_ = l_Array_append___redArg(v___y_786_, v___y_789_);
lean_dec_ref(v___y_789_);
lean_inc_n(v___y_777_, 3);
lean_inc_n(v___y_781_, 12);
v___x_791_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_791_, 0, v___y_781_);
lean_ctor_set(v___x_791_, 1, v___y_777_);
lean_ctor_set(v___x_791_, 2, v___x_790_);
v___x_792_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_792_, 0, v___y_781_);
lean_ctor_set(v___x_792_, 1, v___y_777_);
lean_ctor_set(v___x_792_, 2, v___y_786_);
lean_inc_ref_n(v___x_792_, 6);
lean_inc_ref(v___x_791_);
lean_inc(v___y_779_);
v___x_793_ = l_Lean_Syntax_node7(v___y_781_, v___y_779_, v___x_791_, v___x_792_, v___x_792_, v___x_792_, v___x_792_, v___x_792_, v___x_792_);
v___x_794_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__16));
lean_inc_ref(v___y_780_);
v___x_795_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_795_, 0, v___y_781_);
lean_ctor_set(v___x_795_, 1, v___y_780_);
v___x_796_ = l_Lean_Syntax_node1(v___y_781_, v___x_794_, v___x_795_);
v___x_797_ = lean_obj_once(&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__18, &l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__18_once, _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__18);
v___x_798_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__19));
lean_inc_n(v___y_785_, 3);
lean_inc_n(v___y_783_, 3);
v___x_799_ = l_Lean_addMacroScope(v___y_783_, v___x_798_, v___y_785_);
v___x_800_ = lean_box(0);
v___x_801_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_801_, 0, v___y_781_);
lean_ctor_set(v___x_801_, 1, v___x_797_);
lean_ctor_set(v___x_801_, 2, v___x_799_);
lean_ctor_set(v___x_801_, 3, v___x_800_);
v___x_802_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__14));
v___x_803_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__21));
v___x_804_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__22));
v___x_805_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_805_, 0, v___y_781_);
lean_ctor_set(v___x_805_, 1, v___x_804_);
v___x_806_ = lean_obj_once(&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__24, &l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__24_once, _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__24);
v___x_807_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__26));
v___x_808_ = l_Lean_addMacroScope(v___y_783_, v___x_807_, v___y_785_);
v___x_809_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__28));
v___x_810_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_810_, 0, v___y_781_);
lean_ctor_set(v___x_810_, 1, v___x_806_);
lean_ctor_set(v___x_810_, 2, v___x_808_);
lean_ctor_set(v___x_810_, 3, v___x_809_);
lean_inc_ref(v___x_805_);
v___x_811_ = l_Lean_Syntax_node2(v___y_781_, v___x_803_, v___x_805_, v___x_810_);
v___x_812_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__29));
v___x_813_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_813_, 0, v___y_781_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
v___x_814_ = l_Lean_Syntax_node3(v___y_781_, v___y_777_, v___x_801_, v___x_811_, v___x_813_);
v___x_815_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__31));
v___x_816_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__33));
v___x_817_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__35));
v___x_818_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__37));
v___x_819_ = lean_obj_once(&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__38, &l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__38_once, _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__38);
v___x_820_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__39));
v___x_821_ = l_Lean_addMacroScope(v___y_783_, v___x_820_, v___y_785_);
v___x_822_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__42));
v___x_823_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_823_, 0, v___y_781_);
lean_ctor_set(v___x_823_, 1, v___x_819_);
lean_ctor_set(v___x_823_, 2, v___x_821_);
lean_ctor_set(v___x_823_, 3, v___x_822_);
lean_inc(v___y_776_);
v___x_824_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_800_, v___y_776_);
if (lean_obj_tag(v___x_824_) == 0)
{
lean_object* v___x_825_; 
v___x_825_ = l_Lean_quoteNameMk(v___y_776_);
v___y_705_ = v___x_815_;
v___y_706_ = v___x_800_;
v___y_707_ = v___x_802_;
v___y_708_ = v___y_778_;
v___y_709_ = v___y_777_;
v___y_710_ = v___x_791_;
v___y_711_ = v___x_793_;
v___y_712_ = v___x_823_;
v___y_713_ = v___y_781_;
v___y_714_ = v___y_782_;
v___y_715_ = v___y_783_;
v___y_716_ = v___y_784_;
v___y_717_ = v___x_817_;
v___y_718_ = v___x_816_;
v___y_719_ = v___x_814_;
v___y_720_ = v___x_805_;
v___y_721_ = v___y_785_;
v___y_722_ = v___x_796_;
v___y_723_ = v___y_787_;
v___y_724_ = v___x_818_;
v___y_725_ = v___x_792_;
v___y_726_ = v___y_788_;
v___y_727_ = v___x_825_;
goto v___jp_704_;
}
else
{
lean_object* v_val_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
lean_dec(v___y_776_);
v_val_826_ = lean_ctor_get(v___x_824_, 0);
lean_inc(v_val_826_);
lean_dec_ref(v___x_824_);
v___x_827_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__44));
v___x_828_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__45));
v___x_829_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__46));
v___x_830_ = lean_string_intercalate(v___x_829_, v_val_826_);
v___x_831_ = lean_string_append(v___x_828_, v___x_830_);
lean_dec_ref(v___x_830_);
lean_inc_n(v___y_787_, 2);
v___x_832_ = l_Lean_Syntax_mkNameLit(v___x_831_, v___y_787_);
v___x_833_ = lean_unsigned_to_nat(1u);
v___x_834_ = lean_mk_empty_array_with_capacity(v___x_833_);
v___x_835_ = lean_array_push(v___x_834_, v___x_832_);
v___x_836_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_836_, 0, v___y_787_);
lean_ctor_set(v___x_836_, 1, v___x_827_);
lean_ctor_set(v___x_836_, 2, v___x_835_);
v___y_705_ = v___x_815_;
v___y_706_ = v___x_800_;
v___y_707_ = v___x_802_;
v___y_708_ = v___y_778_;
v___y_709_ = v___y_777_;
v___y_710_ = v___x_791_;
v___y_711_ = v___x_793_;
v___y_712_ = v___x_823_;
v___y_713_ = v___y_781_;
v___y_714_ = v___y_782_;
v___y_715_ = v___y_783_;
v___y_716_ = v___y_784_;
v___y_717_ = v___x_817_;
v___y_718_ = v___x_816_;
v___y_719_ = v___x_814_;
v___y_720_ = v___x_805_;
v___y_721_ = v___y_785_;
v___y_722_ = v___x_796_;
v___y_723_ = v___y_787_;
v___y_724_ = v___x_818_;
v___y_725_ = v___x_792_;
v___y_726_ = v___y_788_;
v___y_727_ = v___x_836_;
goto v___jp_704_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___boxed(lean_object* v_x_889_, lean_object* v_a_890_, lean_object* v_a_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1(v_x_889_, v_a_890_, v_a_891_);
lean_dec_ref(v_a_890_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0___redArg(lean_object* v_a_893_, lean_object* v_x_894_){
_start:
{
if (lean_obj_tag(v_x_894_) == 0)
{
lean_object* v___x_895_; 
v___x_895_ = lean_box(0);
return v___x_895_;
}
else
{
lean_object* v_key_896_; lean_object* v_value_897_; lean_object* v_tail_898_; uint8_t v___x_899_; 
v_key_896_ = lean_ctor_get(v_x_894_, 0);
v_value_897_ = lean_ctor_get(v_x_894_, 1);
v_tail_898_ = lean_ctor_get(v_x_894_, 2);
v___x_899_ = lean_name_eq(v_key_896_, v_a_893_);
if (v___x_899_ == 0)
{
v_x_894_ = v_tail_898_;
goto _start;
}
else
{
lean_object* v___x_901_; 
lean_inc(v_value_897_);
v___x_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_901_, 0, v_value_897_);
return v___x_901_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0___redArg___boxed(lean_object* v_a_902_, lean_object* v_x_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0___redArg(v_a_902_, v_x_903_);
lean_dec(v_x_903_);
lean_dec(v_a_902_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0___redArg(lean_object* v_m_905_, lean_object* v_a_906_){
_start:
{
lean_object* v_buckets_907_; lean_object* v___x_908_; uint64_t v___y_910_; 
v_buckets_907_ = lean_ctor_get(v_m_905_, 1);
v___x_908_ = lean_array_get_size(v_buckets_907_);
if (lean_obj_tag(v_a_906_) == 0)
{
uint64_t v___x_924_; 
v___x_924_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2_spec__3___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
v___y_910_ = v___x_924_;
goto v___jp_909_;
}
else
{
uint64_t v_hash_925_; 
v_hash_925_ = lean_ctor_get_uint64(v_a_906_, sizeof(void*)*2);
v___y_910_ = v_hash_925_;
goto v___jp_909_;
}
v___jp_909_:
{
uint64_t v___x_911_; uint64_t v___x_912_; uint64_t v_fold_913_; uint64_t v___x_914_; uint64_t v___x_915_; uint64_t v___x_916_; size_t v___x_917_; size_t v___x_918_; size_t v___x_919_; size_t v___x_920_; size_t v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_911_ = 32ULL;
v___x_912_ = lean_uint64_shift_right(v___y_910_, v___x_911_);
v_fold_913_ = lean_uint64_xor(v___y_910_, v___x_912_);
v___x_914_ = 16ULL;
v___x_915_ = lean_uint64_shift_right(v_fold_913_, v___x_914_);
v___x_916_ = lean_uint64_xor(v_fold_913_, v___x_915_);
v___x_917_ = lean_uint64_to_usize(v___x_916_);
v___x_918_ = lean_usize_of_nat(v___x_908_);
v___x_919_ = ((size_t)1ULL);
v___x_920_ = lean_usize_sub(v___x_918_, v___x_919_);
v___x_921_ = lean_usize_land(v___x_917_, v___x_920_);
v___x_922_ = lean_array_uget_borrowed(v_buckets_907_, v___x_921_);
v___x_923_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0___redArg(v_a_906_, v___x_922_);
return v___x_923_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0___redArg___boxed(lean_object* v_m_926_, lean_object* v_a_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0___redArg(v_m_926_, v_a_927_);
lean_dec(v_a_927_);
lean_dec_ref(v_m_926_);
return v_res_928_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_929_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_930_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__0);
v___x_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_931_, 0, v___x_930_);
return v___x_931_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_932_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__1);
v___x_933_ = lean_unsigned_to_nat(0u);
v___x_934_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
lean_ctor_set(v___x_934_, 2, v___x_933_);
lean_ctor_set(v___x_934_, 3, v___x_933_);
lean_ctor_set(v___x_934_, 4, v___x_932_);
lean_ctor_set(v___x_934_, 5, v___x_932_);
lean_ctor_set(v___x_934_, 6, v___x_932_);
lean_ctor_set(v___x_934_, 7, v___x_932_);
lean_ctor_set(v___x_934_, 8, v___x_932_);
lean_ctor_set(v___x_934_, 9, v___x_932_);
return v___x_934_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_935_ = lean_unsigned_to_nat(32u);
v___x_936_ = lean_mk_empty_array_with_capacity(v___x_935_);
v___x_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
return v___x_937_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__4(void){
_start:
{
size_t v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_938_ = ((size_t)5ULL);
v___x_939_ = lean_unsigned_to_nat(0u);
v___x_940_ = lean_unsigned_to_nat(32u);
v___x_941_ = lean_mk_empty_array_with_capacity(v___x_940_);
v___x_942_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__3);
v___x_943_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_943_, 0, v___x_942_);
lean_ctor_set(v___x_943_, 1, v___x_941_);
lean_ctor_set(v___x_943_, 2, v___x_939_);
lean_ctor_set(v___x_943_, 3, v___x_939_);
lean_ctor_set_usize(v___x_943_, 4, v___x_938_);
return v___x_943_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__5(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_944_ = lean_box(1);
v___x_945_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__4);
v___x_946_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__1);
v___x_947_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
lean_ctor_set(v___x_947_, 1, v___x_945_);
lean_ctor_set(v___x_947_, 2, v___x_944_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2(lean_object* v_msgData_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v___x_952_; lean_object* v_env_953_; lean_object* v_options_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_952_ = lean_st_ref_get(v___y_950_);
v_env_953_ = lean_ctor_get(v___x_952_, 0);
lean_inc_ref(v_env_953_);
lean_dec(v___x_952_);
v_options_954_ = lean_ctor_get(v___y_949_, 2);
v___x_955_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__2);
v___x_956_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__5);
lean_inc_ref(v_options_954_);
v___x_957_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_957_, 0, v_env_953_);
lean_ctor_set(v___x_957_, 1, v___x_955_);
lean_ctor_set(v___x_957_, 2, v___x_956_);
lean_ctor_set(v___x_957_, 3, v_options_954_);
v___x_958_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
lean_ctor_set(v___x_958_, 1, v_msgData_948_);
v___x_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___boxed(lean_object* v_msgData_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2(v_msgData_960_, v___y_961_, v___y_962_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_labelled_spec__1___redArg(lean_object* v_msg_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v_ref_969_; lean_object* v___x_970_; lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_979_; 
v_ref_969_ = lean_ctor_get(v___y_966_, 5);
v___x_970_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2(v_msg_965_, v___y_966_, v___y_967_);
v_a_971_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_979_ == 0)
{
v___x_973_ = v___x_970_;
v_isShared_974_ = v_isSharedCheck_979_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___x_970_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_979_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_975_; lean_object* v___x_977_; 
lean_inc(v_ref_969_);
v___x_975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_975_, 0, v_ref_969_);
lean_ctor_set(v___x_975_, 1, v_a_971_);
if (v_isShared_974_ == 0)
{
lean_ctor_set_tag(v___x_973_, 1);
lean_ctor_set(v___x_973_, 0, v___x_975_);
v___x_977_ = v___x_973_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_975_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_labelled_spec__1___redArg___boxed(lean_object* v_msg_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Lean_throwError___at___00Lean_labelled_spec__1___redArg(v_msg_980_, v___y_981_, v___y_982_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
return v_res_984_;
}
}
static lean_object* _init_l_Lean_labelled___closed__1(void){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = ((lean_object*)(l_Lean_labelled___closed__0));
v___x_987_ = l_Lean_stringToMessageData(v___x_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_labelled(lean_object* v_attrName_988_, lean_object* v_a_989_, lean_object* v_a_990_){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_992_ = l_Lean_labelExtensionMapRef;
v___x_993_ = lean_st_ref_get(v___x_992_);
v___x_994_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0___redArg(v___x_993_, v_attrName_988_);
lean_dec(v___x_993_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_995_ = lean_obj_once(&l_Lean_labelled___closed__1, &l_Lean_labelled___closed__1_once, _init_l_Lean_labelled___closed__1);
v___x_996_ = l_Lean_MessageData_ofName(v_attrName_988_);
v___x_997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_995_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
v___x_998_ = l_Lean_throwError___at___00Lean_labelled_spec__1___redArg(v___x_997_, v_a_989_, v_a_990_);
return v___x_998_;
}
else
{
lean_object* v_val_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1013_; 
lean_dec(v_attrName_988_);
v_val_999_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1001_ = v___x_994_;
v_isShared_1002_ = v_isSharedCheck_1013_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_val_999_);
lean_dec(v___x_994_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1013_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1003_; lean_object* v_ext_1004_; lean_object* v_toEnvExtension_1005_; lean_object* v_env_1006_; lean_object* v_asyncMode_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1011_; 
v___x_1003_ = lean_st_ref_get(v_a_990_);
v_ext_1004_ = lean_ctor_get(v_val_999_, 1);
v_toEnvExtension_1005_ = lean_ctor_get(v_ext_1004_, 0);
v_env_1006_ = lean_ctor_get(v___x_1003_, 0);
lean_inc_ref(v_env_1006_);
lean_dec(v___x_1003_);
v_asyncMode_1007_ = lean_ctor_get(v_toEnvExtension_1005_, 2);
lean_inc(v_asyncMode_1007_);
v___x_1008_ = lean_obj_once(&l_Lean_mkLabelAttr___closed__0, &l_Lean_mkLabelAttr___closed__0_once, _init_l_Lean_mkLabelAttr___closed__0);
v___x_1009_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1008_, v_val_999_, v_env_1006_, v_asyncMode_1007_);
lean_dec(v_asyncMode_1007_);
lean_dec(v_val_999_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set_tag(v___x_1001_, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1009_);
v___x_1011_ = v___x_1001_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_1009_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_labelled___boxed(lean_object* v_attrName_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Lean_labelled(v_attrName_1014_, v_a_1015_, v_a_1016_);
lean_dec(v_a_1016_);
lean_dec_ref(v_a_1015_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0(lean_object* v_00_u03b2_1019_, lean_object* v_m_1020_, lean_object* v_a_1021_){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0___redArg(v_m_1020_, v_a_1021_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0___boxed(lean_object* v_00_u03b2_1023_, lean_object* v_m_1024_, lean_object* v_a_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0(v_00_u03b2_1023_, v_m_1024_, v_a_1025_);
lean_dec(v_a_1025_);
lean_dec_ref(v_m_1024_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_labelled_spec__1(lean_object* v_00_u03b1_1027_, lean_object* v_msg_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_Lean_throwError___at___00Lean_labelled_spec__1___redArg(v_msg_1028_, v___y_1029_, v___y_1030_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_labelled_spec__1___boxed(lean_object* v_00_u03b1_1033_, lean_object* v_msg_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lean_throwError___at___00Lean_labelled_spec__1(v_00_u03b1_1033_, v_msg_1034_, v___y_1035_, v___y_1036_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0(lean_object* v_00_u03b2_1039_, lean_object* v_a_1040_, lean_object* v_x_1041_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0___redArg(v_a_1040_, v_x_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1043_, lean_object* v_a_1044_, lean_object* v_x_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0(v_00_u03b2_1043_, v_a_1044_, v_x_1045_);
lean_dec(v_x_1045_);
lean_dec(v_a_1044_);
return v_res_1046_;
}
}
lean_object* runtime_initialize_Lean_DocString(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_LabelAttribute(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
