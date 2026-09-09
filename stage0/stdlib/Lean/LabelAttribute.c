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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* v_toCold_163_; lean_object* v_currNamespace_164_; lean_object* v___x_165_; lean_object* v_env_166_; lean_object* v_nextMacroScope_167_; lean_object* v_ngen_168_; lean_object* v_auxDeclNGen_169_; lean_object* v_traceState_170_; lean_object* v_messages_171_; lean_object* v_infoState_172_; lean_object* v_snapshotTasks_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_185_; 
v_toCold_163_ = lean_ctor_get(v___y_160_, 0);
v_currNamespace_164_ = lean_ctor_get(v_toCold_163_, 4);
v___x_165_ = lean_st_ref_take(v___y_161_);
v_env_166_ = lean_ctor_get(v___x_165_, 0);
v_nextMacroScope_167_ = lean_ctor_get(v___x_165_, 1);
v_ngen_168_ = lean_ctor_get(v___x_165_, 2);
v_auxDeclNGen_169_ = lean_ctor_get(v___x_165_, 3);
v_traceState_170_ = lean_ctor_get(v___x_165_, 4);
v_messages_171_ = lean_ctor_get(v___x_165_, 6);
v_infoState_172_ = lean_ctor_get(v___x_165_, 7);
v_snapshotTasks_173_ = lean_ctor_get(v___x_165_, 8);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_165_);
if (v_isSharedCheck_185_ == 0)
{
lean_object* v_unused_186_; 
v_unused_186_ = lean_ctor_get(v___x_165_, 5);
lean_dec(v_unused_186_);
v___x_175_ = v___x_165_;
v_isShared_176_ = v_isSharedCheck_185_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_snapshotTasks_173_);
lean_inc(v_infoState_172_);
lean_inc(v_messages_171_);
lean_inc(v_traceState_170_);
lean_inc(v_auxDeclNGen_169_);
lean_inc(v_ngen_168_);
lean_inc(v_nextMacroScope_167_);
lean_inc(v_env_166_);
lean_dec(v___x_165_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_185_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_180_; 
lean_inc(v_currNamespace_164_);
v___x_177_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_166_, v_ext_157_, v_b_158_, v_kind_159_, v_currNamespace_164_);
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
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___x_177_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v_nextMacroScope_167_);
lean_ctor_set(v_reuseFailAlloc_184_, 2, v_ngen_168_);
lean_ctor_set(v_reuseFailAlloc_184_, 3, v_auxDeclNGen_169_);
lean_ctor_set(v_reuseFailAlloc_184_, 4, v_traceState_170_);
lean_ctor_set(v_reuseFailAlloc_184_, 5, v___x_178_);
lean_ctor_set(v_reuseFailAlloc_184_, 6, v_messages_171_);
lean_ctor_set(v_reuseFailAlloc_184_, 7, v_infoState_172_);
lean_ctor_set(v_reuseFailAlloc_184_, 8, v_snapshotTasks_173_);
v___x_180_ = v_reuseFailAlloc_184_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_181_ = lean_st_ref_put(v___y_161_, v___x_180_);
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
lean_dec_ref_known(v___x_258_, 1);
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
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v_ext_280_; lean_object* v_toEnvExtension_281_; lean_object* v_env_282_; lean_object* v_asyncMode_283_; lean_object* v_env_284_; lean_object* v_nextMacroScope_285_; lean_object* v_ngen_286_; lean_object* v_auxDeclNGen_287_; lean_object* v_traceState_288_; lean_object* v_messages_289_; lean_object* v_infoState_290_; lean_object* v_snapshotTasks_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_305_; 
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
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_305_ == 0)
{
lean_object* v_unused_306_; 
v_unused_306_ = lean_ctor_get(v___x_279_, 5);
lean_dec(v_unused_306_);
v___x_293_ = v___x_279_;
v_isShared_294_ = v_isSharedCheck_305_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_snapshotTasks_291_);
lean_inc(v_infoState_290_);
lean_inc(v_messages_289_);
lean_inc(v_traceState_288_);
lean_inc(v_auxDeclNGen_287_);
lean_inc(v_ngen_286_);
lean_inc(v_nextMacroScope_285_);
lean_inc(v_env_284_);
lean_dec(v___x_279_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_305_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_295_; lean_object* v___f_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_300_; 
v___x_295_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_273_, v_ext_272_, v_env_282_, v_asyncMode_283_);
v___f_296_ = lean_alloc_closure((void*)(l_Lean_mkLabelAttr___lam__1___boxed), 3, 2);
lean_closure_set(v___f_296_, 0, v___x_295_);
lean_closure_set(v___f_296_, 1, v_declName_274_);
v___x_297_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_272_, v_env_284_, v___f_296_);
v___x_298_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__2);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 5, v___x_298_);
lean_ctor_set(v___x_293_, 0, v___x_297_);
v___x_300_ = v___x_293_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v___x_297_);
lean_ctor_set(v_reuseFailAlloc_304_, 1, v_nextMacroScope_285_);
lean_ctor_set(v_reuseFailAlloc_304_, 2, v_ngen_286_);
lean_ctor_set(v_reuseFailAlloc_304_, 3, v_auxDeclNGen_287_);
lean_ctor_set(v_reuseFailAlloc_304_, 4, v_traceState_288_);
lean_ctor_set(v_reuseFailAlloc_304_, 5, v___x_298_);
lean_ctor_set(v_reuseFailAlloc_304_, 6, v_messages_289_);
lean_ctor_set(v_reuseFailAlloc_304_, 7, v_infoState_290_);
lean_ctor_set(v_reuseFailAlloc_304_, 8, v_snapshotTasks_291_);
v___x_300_ = v_reuseFailAlloc_304_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_301_ = lean_st_ref_put(v___y_276_, v___x_300_);
v___x_302_ = lean_box(0);
v___x_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
return v___x_303_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelAttr___lam__2___boxed(lean_object* v_ext_307_, lean_object* v___x_308_, lean_object* v_declName_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lean_mkLabelAttr___lam__2(v_ext_307_, v___x_308_, v_declName_309_, v___y_310_, v___y_311_);
lean_dec(v___y_311_);
lean_dec_ref(v___y_310_);
lean_dec_ref(v___x_308_);
return v_res_313_;
}
}
static lean_object* _init_l_Lean_mkLabelAttr___closed__0(void){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l_Array_instInhabited(lean_box(0));
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelAttr(lean_object* v_attrName_315_, lean_object* v_attrDescr_316_, lean_object* v_ext_317_, lean_object* v_ref_318_){
_start:
{
lean_object* v___f_320_; lean_object* v___x_321_; lean_object* v___f_322_; uint8_t v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
lean_inc_ref(v_ext_317_);
v___f_320_ = lean_alloc_closure((void*)(l_Lean_mkLabelAttr___lam__0___boxed), 7, 1);
lean_closure_set(v___f_320_, 0, v_ext_317_);
v___x_321_ = lean_obj_once(&l_Lean_mkLabelAttr___closed__0, &l_Lean_mkLabelAttr___closed__0_once, _init_l_Lean_mkLabelAttr___closed__0);
v___f_322_ = lean_alloc_closure((void*)(l_Lean_mkLabelAttr___lam__2___boxed), 6, 2);
lean_closure_set(v___f_322_, 0, v_ext_317_);
lean_closure_set(v___f_322_, 1, v___x_321_);
v___x_323_ = 1;
v___x_324_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_324_, 0, v_ref_318_);
lean_ctor_set(v___x_324_, 1, v_attrName_315_);
lean_ctor_set(v___x_324_, 2, v_attrDescr_316_);
lean_ctor_set_uint8(v___x_324_, sizeof(void*)*3, v___x_323_);
v___x_325_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
lean_ctor_set(v___x_325_, 1, v___f_320_);
lean_ctor_set(v___x_325_, 2, v___f_322_);
v___x_326_ = l_Lean_registerBuiltinAttribute(v___x_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelAttr___boxed(lean_object* v_attrName_327_, lean_object* v_attrDescr_328_, lean_object* v_ext_329_, lean_object* v_ref_330_, lean_object* v_a_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Lean_mkLabelAttr(v_attrName_327_, v_attrDescr_328_, v_ext_329_, v_ref_330_);
return v_res_332_;
}
}
static lean_object* _init_l_Lean_registerLabelAttr___auto__1(void){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = lean_obj_once(&l_Lean_mkLabelExt___auto__1___closed__28, &l_Lean_mkLabelExt___auto__1___closed__28_once, _init_l_Lean_mkLabelExt___auto__1___closed__28);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_334_, lean_object* v_x_335_){
_start:
{
if (lean_obj_tag(v_x_335_) == 0)
{
return v_x_334_;
}
else
{
lean_object* v_key_336_; lean_object* v_value_337_; lean_object* v_tail_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_364_; 
v_key_336_ = lean_ctor_get(v_x_335_, 0);
v_value_337_ = lean_ctor_get(v_x_335_, 1);
v_tail_338_ = lean_ctor_get(v_x_335_, 2);
v_isSharedCheck_364_ = !lean_is_exclusive(v_x_335_);
if (v_isSharedCheck_364_ == 0)
{
v___x_340_ = v_x_335_;
v_isShared_341_ = v_isSharedCheck_364_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_tail_338_);
lean_inc(v_value_337_);
lean_inc(v_key_336_);
lean_dec(v_x_335_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_364_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_342_; uint64_t v___y_344_; 
v___x_342_ = lean_array_get_size(v_x_334_);
if (lean_obj_tag(v_key_336_) == 0)
{
uint64_t v___x_362_; 
v___x_362_ = 1723ULL;
v___y_344_ = v___x_362_;
goto v___jp_343_;
}
else
{
uint64_t v_hash_363_; 
v_hash_363_ = lean_ctor_get_uint64(v_key_336_, sizeof(void*)*2);
v___y_344_ = v_hash_363_;
goto v___jp_343_;
}
v___jp_343_:
{
uint64_t v___x_345_; uint64_t v___x_346_; uint64_t v_fold_347_; uint64_t v___x_348_; uint64_t v___x_349_; uint64_t v___x_350_; size_t v___x_351_; size_t v___x_352_; size_t v___x_353_; size_t v___x_354_; size_t v___x_355_; lean_object* v___x_356_; lean_object* v___x_358_; 
v___x_345_ = 32ULL;
v___x_346_ = lean_uint64_shift_right(v___y_344_, v___x_345_);
v_fold_347_ = lean_uint64_xor(v___y_344_, v___x_346_);
v___x_348_ = 16ULL;
v___x_349_ = lean_uint64_shift_right(v_fold_347_, v___x_348_);
v___x_350_ = lean_uint64_xor(v_fold_347_, v___x_349_);
v___x_351_ = lean_uint64_to_usize(v___x_350_);
v___x_352_ = lean_usize_of_nat(v___x_342_);
v___x_353_ = ((size_t)1ULL);
v___x_354_ = lean_usize_sub(v___x_352_, v___x_353_);
v___x_355_ = lean_usize_land(v___x_351_, v___x_354_);
v___x_356_ = lean_array_uget_borrowed(v_x_334_, v___x_355_);
lean_inc(v___x_356_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 2, v___x_356_);
v___x_358_ = v___x_340_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_key_336_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v_value_337_);
lean_ctor_set(v_reuseFailAlloc_361_, 2, v___x_356_);
v___x_358_ = v_reuseFailAlloc_361_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
lean_object* v___x_359_; 
v___x_359_ = lean_array_uset(v_x_334_, v___x_355_, v___x_358_);
v_x_334_ = v___x_359_;
v_x_335_ = v_tail_338_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2___redArg(lean_object* v_i_365_, lean_object* v_source_366_, lean_object* v_target_367_){
_start:
{
lean_object* v___x_368_; uint8_t v___x_369_; 
v___x_368_ = lean_array_get_size(v_source_366_);
v___x_369_ = lean_nat_dec_lt(v_i_365_, v___x_368_);
if (v___x_369_ == 0)
{
lean_dec_ref(v_source_366_);
lean_dec(v_i_365_);
return v_target_367_;
}
else
{
lean_object* v_es_370_; lean_object* v___x_371_; lean_object* v_source_372_; lean_object* v_target_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v_es_370_ = lean_array_fget(v_source_366_, v_i_365_);
v___x_371_ = lean_box(0);
v_source_372_ = lean_array_fset(v_source_366_, v_i_365_, v___x_371_);
v_target_373_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_target_367_, v_es_370_);
v___x_374_ = lean_unsigned_to_nat(1u);
v___x_375_ = lean_nat_add(v_i_365_, v___x_374_);
lean_dec(v_i_365_);
v_i_365_ = v___x_375_;
v_source_366_ = v_source_372_;
v_target_367_ = v_target_373_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1___redArg(lean_object* v_data_377_){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v_nbuckets_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_378_ = lean_array_get_size(v_data_377_);
v___x_379_ = lean_unsigned_to_nat(2u);
v_nbuckets_380_ = lean_nat_mul(v___x_378_, v___x_379_);
v___x_381_ = lean_unsigned_to_nat(0u);
v___x_382_ = lean_box(0);
v___x_383_ = lean_mk_array(v_nbuckets_380_, v___x_382_);
v___x_384_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2___redArg(v___x_381_, v_data_377_, v___x_383_);
return v___x_384_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__0___redArg(lean_object* v_a_385_, lean_object* v_x_386_){
_start:
{
if (lean_obj_tag(v_x_386_) == 0)
{
uint8_t v___x_387_; 
v___x_387_ = 0;
return v___x_387_;
}
else
{
lean_object* v_key_388_; lean_object* v_tail_389_; uint8_t v___x_390_; 
v_key_388_ = lean_ctor_get(v_x_386_, 0);
v_tail_389_ = lean_ctor_get(v_x_386_, 2);
v___x_390_ = lean_name_eq(v_key_388_, v_a_385_);
if (v___x_390_ == 0)
{
v_x_386_ = v_tail_389_;
goto _start;
}
else
{
return v___x_390_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__0___redArg___boxed(lean_object* v_a_392_, lean_object* v_x_393_){
_start:
{
uint8_t v_res_394_; lean_object* v_r_395_; 
v_res_394_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__0___redArg(v_a_392_, v_x_393_);
lean_dec(v_x_393_);
lean_dec(v_a_392_);
v_r_395_ = lean_box(v_res_394_);
return v_r_395_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__2___redArg(lean_object* v_a_396_, lean_object* v_b_397_, lean_object* v_x_398_){
_start:
{
if (lean_obj_tag(v_x_398_) == 0)
{
lean_dec(v_b_397_);
lean_dec(v_a_396_);
return v_x_398_;
}
else
{
lean_object* v_key_399_; lean_object* v_value_400_; lean_object* v_tail_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_413_; 
v_key_399_ = lean_ctor_get(v_x_398_, 0);
v_value_400_ = lean_ctor_get(v_x_398_, 1);
v_tail_401_ = lean_ctor_get(v_x_398_, 2);
v_isSharedCheck_413_ = !lean_is_exclusive(v_x_398_);
if (v_isSharedCheck_413_ == 0)
{
v___x_403_ = v_x_398_;
v_isShared_404_ = v_isSharedCheck_413_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_tail_401_);
lean_inc(v_value_400_);
lean_inc(v_key_399_);
lean_dec(v_x_398_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_413_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
uint8_t v___x_405_; 
v___x_405_ = lean_name_eq(v_key_399_, v_a_396_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; lean_object* v___x_408_; 
v___x_406_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__2___redArg(v_a_396_, v_b_397_, v_tail_401_);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 2, v___x_406_);
v___x_408_ = v___x_403_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_key_399_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v_value_400_);
lean_ctor_set(v_reuseFailAlloc_409_, 2, v___x_406_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
else
{
lean_object* v___x_411_; 
lean_dec(v_value_400_);
lean_dec(v_key_399_);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 1, v_b_397_);
lean_ctor_set(v___x_403_, 0, v_a_396_);
v___x_411_ = v___x_403_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_a_396_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v_b_397_);
lean_ctor_set(v_reuseFailAlloc_412_, 2, v_tail_401_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0___redArg(lean_object* v_m_414_, lean_object* v_a_415_, lean_object* v_b_416_){
_start:
{
lean_object* v_size_417_; lean_object* v_buckets_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_464_; 
v_size_417_ = lean_ctor_get(v_m_414_, 0);
v_buckets_418_ = lean_ctor_get(v_m_414_, 1);
v_isSharedCheck_464_ = !lean_is_exclusive(v_m_414_);
if (v_isSharedCheck_464_ == 0)
{
v___x_420_ = v_m_414_;
v_isShared_421_ = v_isSharedCheck_464_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_buckets_418_);
lean_inc(v_size_417_);
lean_dec(v_m_414_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_464_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_422_; uint64_t v___y_424_; 
v___x_422_ = lean_array_get_size(v_buckets_418_);
if (lean_obj_tag(v_a_415_) == 0)
{
uint64_t v___x_462_; 
v___x_462_ = 1723ULL;
v___y_424_ = v___x_462_;
goto v___jp_423_;
}
else
{
uint64_t v_hash_463_; 
v_hash_463_ = lean_ctor_get_uint64(v_a_415_, sizeof(void*)*2);
v___y_424_ = v_hash_463_;
goto v___jp_423_;
}
v___jp_423_:
{
uint64_t v___x_425_; uint64_t v___x_426_; uint64_t v_fold_427_; uint64_t v___x_428_; uint64_t v___x_429_; uint64_t v___x_430_; size_t v___x_431_; size_t v___x_432_; size_t v___x_433_; size_t v___x_434_; size_t v___x_435_; lean_object* v_bkt_436_; uint8_t v___x_437_; 
v___x_425_ = 32ULL;
v___x_426_ = lean_uint64_shift_right(v___y_424_, v___x_425_);
v_fold_427_ = lean_uint64_xor(v___y_424_, v___x_426_);
v___x_428_ = 16ULL;
v___x_429_ = lean_uint64_shift_right(v_fold_427_, v___x_428_);
v___x_430_ = lean_uint64_xor(v_fold_427_, v___x_429_);
v___x_431_ = lean_uint64_to_usize(v___x_430_);
v___x_432_ = lean_usize_of_nat(v___x_422_);
v___x_433_ = ((size_t)1ULL);
v___x_434_ = lean_usize_sub(v___x_432_, v___x_433_);
v___x_435_ = lean_usize_land(v___x_431_, v___x_434_);
v_bkt_436_ = lean_array_uget_borrowed(v_buckets_418_, v___x_435_);
v___x_437_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__0___redArg(v_a_415_, v_bkt_436_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; lean_object* v_size_x27_439_; lean_object* v___x_440_; lean_object* v_buckets_x27_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_438_ = lean_unsigned_to_nat(1u);
v_size_x27_439_ = lean_nat_add(v_size_417_, v___x_438_);
lean_dec(v_size_417_);
lean_inc(v_bkt_436_);
v___x_440_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_440_, 0, v_a_415_);
lean_ctor_set(v___x_440_, 1, v_b_416_);
lean_ctor_set(v___x_440_, 2, v_bkt_436_);
v_buckets_x27_441_ = lean_array_uset(v_buckets_418_, v___x_435_, v___x_440_);
v___x_442_ = lean_unsigned_to_nat(4u);
v___x_443_ = lean_nat_mul(v_size_x27_439_, v___x_442_);
v___x_444_ = lean_unsigned_to_nat(3u);
v___x_445_ = lean_nat_div(v___x_443_, v___x_444_);
lean_dec(v___x_443_);
v___x_446_ = lean_array_get_size(v_buckets_x27_441_);
v___x_447_ = lean_nat_dec_le(v___x_445_, v___x_446_);
lean_dec(v___x_445_);
if (v___x_447_ == 0)
{
lean_object* v_val_448_; lean_object* v___x_450_; 
v_val_448_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1___redArg(v_buckets_x27_441_);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 1, v_val_448_);
lean_ctor_set(v___x_420_, 0, v_size_x27_439_);
v___x_450_ = v___x_420_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_size_x27_439_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v_val_448_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
else
{
lean_object* v___x_453_; 
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 1, v_buckets_x27_441_);
lean_ctor_set(v___x_420_, 0, v_size_x27_439_);
v___x_453_ = v___x_420_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_size_x27_439_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_buckets_x27_441_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
else
{
lean_object* v___x_455_; lean_object* v_buckets_x27_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_460_; 
lean_inc(v_bkt_436_);
v___x_455_ = lean_box(0);
v_buckets_x27_456_ = lean_array_uset(v_buckets_418_, v___x_435_, v___x_455_);
v___x_457_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__2___redArg(v_a_415_, v_b_416_, v_bkt_436_);
v___x_458_ = lean_array_uset(v_buckets_x27_456_, v___x_435_, v___x_457_);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 1, v___x_458_);
v___x_460_ = v___x_420_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_size_417_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v___x_458_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerLabelAttr(lean_object* v_attrName_465_, lean_object* v_attrDescr_466_, lean_object* v_ref_467_){
_start:
{
lean_object* v___x_469_; 
lean_inc(v_ref_467_);
v___x_469_ = l_Lean_mkLabelExt(v_ref_467_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_a_470_; lean_object* v___x_471_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc_n(v_a_470_, 2);
lean_dec_ref_known(v___x_469_, 1);
lean_inc(v_attrName_465_);
v___x_471_ = l_Lean_mkLabelAttr(v_attrName_465_, v_attrDescr_466_, v_a_470_, v_ref_467_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_482_; 
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_482_ == 0)
{
lean_object* v_unused_483_; 
v_unused_483_ = lean_ctor_get(v___x_471_, 0);
lean_dec(v_unused_483_);
v___x_473_ = v___x_471_;
v_isShared_474_ = v_isSharedCheck_482_;
goto v_resetjp_472_;
}
else
{
lean_dec(v___x_471_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_482_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_480_; 
v___x_475_ = l_Lean_labelExtensionMapRef;
v___x_476_ = lean_st_ref_take(v___x_475_);
lean_inc(v_a_470_);
v___x_477_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0___redArg(v___x_476_, v_attrName_465_, v_a_470_);
v___x_478_ = lean_st_ref_put(v___x_475_, v___x_477_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 0, v_a_470_);
v___x_480_ = v___x_473_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_470_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
else
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_491_; 
lean_dec(v_a_470_);
lean_dec(v_attrName_465_);
v_a_484_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_491_ == 0)
{
v___x_486_ = v___x_471_;
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_471_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_489_; 
if (v_isShared_487_ == 0)
{
v___x_489_ = v___x_486_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_a_484_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
}
else
{
lean_dec(v_ref_467_);
lean_dec_ref(v_attrDescr_466_);
lean_dec(v_attrName_465_);
return v___x_469_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerLabelAttr___boxed(lean_object* v_attrName_492_, lean_object* v_attrDescr_493_, lean_object* v_ref_494_, lean_object* v_a_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Lean_registerLabelAttr(v_attrName_492_, v_attrDescr_493_, v_ref_494_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0(lean_object* v_00_u03b2_497_, lean_object* v_m_498_, lean_object* v_a_499_, lean_object* v_b_500_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0___redArg(v_m_498_, v_a_499_, v_b_500_);
return v___x_501_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__0(lean_object* v_00_u03b2_502_, lean_object* v_a_503_, lean_object* v_x_504_){
_start:
{
uint8_t v___x_505_; 
v___x_505_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__0___redArg(v_a_503_, v_x_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_506_, lean_object* v_a_507_, lean_object* v_x_508_){
_start:
{
uint8_t v_res_509_; lean_object* v_r_510_; 
v_res_509_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__0(v_00_u03b2_506_, v_a_507_, v_x_508_);
lean_dec(v_x_508_);
lean_dec(v_a_507_);
v_r_510_ = lean_box(v_res_509_);
return v_r_510_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1(lean_object* v_00_u03b2_511_, lean_object* v_data_512_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1___redArg(v_data_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__2(lean_object* v_00_u03b2_514_, lean_object* v_a_515_, lean_object* v_b_516_, lean_object* v_x_517_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__2___redArg(v_a_515_, v_b_516_, v_x_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_519_, lean_object* v_i_520_, lean_object* v_source_521_, lean_object* v_target_522_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2___redArg(v_i_520_, v_source_521_, v_target_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_524_, lean_object* v_x_525_, lean_object* v_x_526_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_x_525_, v_x_526_);
return v___x_527_;
}
}
static lean_object* _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__13(void){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__12));
v___x_598_ = l_String_toRawSubstring_x27(v___x_597_);
return v___x_598_;
}
}
static lean_object* _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__18(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__17));
v___x_609_ = l_String_toRawSubstring_x27(v___x_608_);
return v___x_609_;
}
}
static lean_object* _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__24(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__23));
v___x_621_ = l_String_toRawSubstring_x27(v___x_620_);
return v___x_621_;
}
}
static lean_object* _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__38(void){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = ((lean_object*)(l_Lean_Parser_Command_registerLabelAttr___closed__2));
v___x_658_ = l_String_toRawSubstring_x27(v___x_657_);
return v___x_658_;
}
}
static lean_object* _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__51(void){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_Array_mkArray0(lean_box(0));
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1(lean_object* v_x_696_, lean_object* v_a_697_, lean_object* v_a_698_){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v___y_720_; lean_object* v___y_721_; lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v___y_724_; lean_object* v___y_773_; lean_object* v___y_774_; lean_object* v___y_775_; lean_object* v___y_776_; lean_object* v___y_777_; lean_object* v___y_778_; lean_object* v___y_779_; lean_object* v___y_780_; lean_object* v___y_781_; lean_object* v___y_782_; lean_object* v___y_783_; lean_object* v___y_784_; lean_object* v___y_785_; lean_object* v___y_786_; lean_object* v___x_834_; uint8_t v___x_835_; 
v___x_699_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__0));
v___x_700_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__1));
v___x_834_ = ((lean_object*)(l_Lean_Parser_Command_registerLabelAttr___closed__3));
lean_inc(v_x_696_);
v___x_835_ = l_Lean_Syntax_isOfKind(v_x_696_, v___x_834_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; lean_object* v___x_837_; 
lean_dec(v_x_696_);
v___x_836_ = lean_box(1);
v___x_837_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
lean_ctor_set(v___x_837_, 1, v_a_698_);
return v___x_837_;
}
else
{
lean_object* v___x_838_; lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v___y_842_; uint8_t v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v_id_863_; lean_object* v___y_865_; lean_object* v___x_876_; 
v___x_838_ = lean_unsigned_to_nat(0u);
v___x_861_ = l_Lean_Syntax_getArg(v_x_696_, v___x_838_);
v___x_862_ = lean_unsigned_to_nat(2u);
v_id_863_ = l_Lean_Syntax_getArg(v_x_696_, v___x_862_);
lean_dec(v_x_696_);
v___x_876_ = l_Lean_Syntax_getOptional_x3f(v___x_861_);
lean_dec(v___x_861_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v___x_877_; 
v___x_877_ = lean_box(0);
v___y_865_ = v___x_877_;
goto v___jp_864_;
}
else
{
lean_object* v_val_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
v_val_878_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_885_ == 0)
{
v___x_880_ = v___x_876_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_val_878_);
lean_dec(v___x_876_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_val_878_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
v___y_865_ = v___x_883_;
goto v___jp_864_;
}
}
}
v___jp_839_:
{
lean_object* v_quotContext_846_; lean_object* v_currMacroScope_847_; lean_object* v_ref_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v_quotContext_846_ = lean_ctor_get(v_a_697_, 1);
v_currMacroScope_847_ = lean_ctor_get(v_a_697_, 2);
v_ref_848_ = lean_ctor_get(v_a_697_, 5);
v___x_849_ = l_String_removeLeadingSpaces(v___y_845_);
v___x_850_ = lean_box(2);
v___x_851_ = l_Lean_Syntax_mkStrLit(v___x_849_, v___x_850_);
v___x_852_ = l_Lean_SourceInfo_fromRef(v_ref_848_, v___y_843_);
v___x_853_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__9));
v___x_854_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__47));
v___x_855_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__48));
v___x_856_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__50));
v___x_857_ = lean_obj_once(&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__51, &l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__51_once, _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__51);
if (lean_obj_tag(v___y_840_) == 1)
{
lean_object* v_val_858_; lean_object* v___x_859_; 
v_val_858_ = lean_ctor_get(v___y_840_, 0);
lean_inc(v_val_858_);
lean_dec_ref_known(v___y_840_, 1);
v___x_859_ = l_Array_mkArray1___redArg(v_val_858_);
v___y_773_ = v___x_851_;
v___y_774_ = v___x_854_;
v___y_775_ = v___x_855_;
v___y_776_ = v___x_850_;
v___y_777_ = v___x_853_;
v___y_778_ = v_currMacroScope_847_;
v___y_779_ = v___x_857_;
v___y_780_ = v___x_856_;
v___y_781_ = v___y_841_;
v___y_782_ = v___y_842_;
v___y_783_ = v___x_852_;
v___y_784_ = v_quotContext_846_;
v___y_785_ = v___y_844_;
v___y_786_ = v___x_859_;
goto v___jp_772_;
}
else
{
lean_object* v___x_860_; 
lean_dec(v___y_840_);
v___x_860_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__5));
v___y_773_ = v___x_851_;
v___y_774_ = v___x_854_;
v___y_775_ = v___x_855_;
v___y_776_ = v___x_850_;
v___y_777_ = v___x_853_;
v___y_778_ = v_currMacroScope_847_;
v___y_779_ = v___x_857_;
v___y_780_ = v___x_856_;
v___y_781_ = v___y_841_;
v___y_782_ = v___y_842_;
v___y_783_ = v___x_852_;
v___y_784_ = v_quotContext_846_;
v___y_785_ = v___y_844_;
v___y_786_ = v___x_860_;
goto v___jp_772_;
}
}
v___jp_864_:
{
lean_object* v___x_866_; lean_object* v_str_867_; lean_object* v___x_868_; lean_object* v___x_869_; uint8_t v___x_870_; lean_object* v_idParser_871_; 
v___x_866_ = l_Lean_TSyntax_getId(v_id_863_);
lean_inc_n(v___x_866_, 2);
v_str_867_ = l_Lean_Name_toString(v___x_866_, v___x_835_);
v___x_868_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__53));
v___x_869_ = l_Lean_Name_append(v___x_868_, v___x_866_);
v___x_870_ = 0;
v_idParser_871_ = l_Lean_mkIdentFrom(v_id_863_, v___x_869_, v___x_870_);
lean_dec(v_id_863_);
if (lean_obj_tag(v___y_865_) == 0)
{
lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_872_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__54));
v___x_873_ = lean_string_append(v___x_872_, v_str_867_);
v___y_840_ = v___y_865_;
v___y_841_ = v_idParser_871_;
v___y_842_ = v___x_866_;
v___y_843_ = v___x_870_;
v___y_844_ = v_str_867_;
v___y_845_ = v___x_873_;
goto v___jp_839_;
}
else
{
lean_object* v_val_874_; lean_object* v___x_875_; 
v_val_874_ = lean_ctor_get(v___y_865_, 0);
v___x_875_ = l_Lean_TSyntax_getDocString(v_val_874_);
v___y_840_ = v___y_865_;
v___y_841_ = v_idParser_871_;
v___y_842_ = v___x_866_;
v___y_843_ = v___x_870_;
v___y_844_ = v_str_867_;
v___y_845_ = v___x_875_;
goto v___jp_839_;
}
}
}
v___jp_701_:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
lean_inc(v___y_724_);
lean_inc_n(v___y_710_, 5);
lean_inc_n(v___y_721_, 19);
v___x_725_ = l_Lean_Syntax_node3(v___y_721_, v___y_710_, v___y_724_, v___y_702_, v___y_724_);
lean_inc(v___y_713_);
v___x_726_ = l_Lean_Syntax_node2(v___y_721_, v___y_713_, v___y_719_, v___x_725_);
lean_inc(v___y_709_);
v___x_727_ = l_Lean_Syntax_node1(v___y_721_, v___y_709_, v___x_726_);
lean_inc_n(v___y_717_, 4);
lean_inc(v___y_703_);
v___x_728_ = l_Lean_Syntax_node2(v___y_721_, v___y_703_, v___x_727_, v___y_717_);
v___x_729_ = l_Lean_Syntax_node1(v___y_721_, v___y_710_, v___x_728_);
lean_inc(v___y_711_);
v___x_730_ = l_Lean_Syntax_node1(v___y_721_, v___y_711_, v___x_729_);
lean_inc(v___y_704_);
v___x_731_ = l_Lean_Syntax_node4(v___y_721_, v___y_704_, v___y_706_, v___y_716_, v___y_708_, v___x_730_);
v___x_732_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__0));
v___x_733_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__1));
v___x_734_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__2));
lean_inc_ref(v___y_705_);
v___x_735_ = l_Lean_Name_mkStr4(v___x_699_, v___x_700_, v___y_705_, v___x_734_);
v___x_736_ = l_Lean_Syntax_node1(v___y_721_, v___x_735_, v___y_717_);
v___x_737_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_737_, 0, v___y_721_);
lean_ctor_set(v___x_737_, 1, v___x_732_);
v___x_738_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__4));
v___x_739_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__5));
v___x_740_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_740_, 0, v___y_721_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
v___x_741_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__6));
v___x_742_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_742_, 0, v___y_721_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v___x_743_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__7));
v___x_744_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_744_, 0, v___y_721_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
v___x_745_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__8));
v___x_746_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_746_, 0, v___y_721_);
lean_ctor_set(v___x_746_, 1, v___x_745_);
v___x_747_ = l_Lean_Syntax_node5(v___y_721_, v___x_738_, v___x_740_, v___x_742_, v___x_744_, v___y_720_, v___x_746_);
v___x_748_ = l_Lean_Syntax_node1(v___y_721_, v___y_710_, v___x_747_);
v___x_749_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__11));
v___x_750_ = l_Lean_Syntax_mkStrLit(v___y_723_, v___y_707_);
v___x_751_ = l_Lean_Syntax_node1(v___y_721_, v___x_749_, v___x_750_);
v___x_752_ = l_Lean_Syntax_node1(v___y_721_, v___y_710_, v___x_751_);
v___x_753_ = lean_obj_once(&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__13, &l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__13_once, _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__13);
v___x_754_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__14));
lean_inc(v___y_714_);
lean_inc(v___y_722_);
v___x_755_ = l_Lean_addMacroScope(v___y_722_, v___x_754_, v___y_714_);
v___x_756_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_756_, 0, v___y_721_);
lean_ctor_set(v___x_756_, 1, v___x_753_);
lean_ctor_set(v___x_756_, 2, v___x_755_);
lean_ctor_set(v___x_756_, 3, v___y_712_);
v___x_757_ = lean_unsigned_to_nat(10u);
v___x_758_ = lean_mk_empty_array_with_capacity(v___x_757_);
v___x_759_ = lean_array_push(v___x_758_, v___y_718_);
v___x_760_ = lean_array_push(v___x_759_, v___y_717_);
v___x_761_ = lean_array_push(v___x_760_, v___x_736_);
v___x_762_ = lean_array_push(v___x_761_, v___x_737_);
v___x_763_ = lean_array_push(v___x_762_, v___y_717_);
v___x_764_ = lean_array_push(v___x_763_, v___x_748_);
v___x_765_ = lean_array_push(v___x_764_, v___y_717_);
v___x_766_ = lean_array_push(v___x_765_, v___x_752_);
v___x_767_ = lean_array_push(v___x_766_, v___y_715_);
v___x_768_ = lean_array_push(v___x_767_, v___x_756_);
v___x_769_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_769_, 0, v___y_721_);
lean_ctor_set(v___x_769_, 1, v___x_733_);
lean_ctor_set(v___x_769_, 2, v___x_768_);
v___x_770_ = l_Lean_Syntax_node2(v___y_721_, v___y_710_, v___x_731_, v___x_769_);
v___x_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
lean_ctor_set(v___x_771_, 1, v_a_698_);
return v___x_771_;
}
v___jp_772_:
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
lean_inc_ref_n(v___y_779_, 2);
v___x_787_ = l_Array_append___redArg(v___y_779_, v___y_786_);
lean_dec_ref(v___y_786_);
lean_inc_n(v___y_777_, 3);
lean_inc_n(v___y_783_, 12);
v___x_788_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_788_, 0, v___y_783_);
lean_ctor_set(v___x_788_, 1, v___y_777_);
lean_ctor_set(v___x_788_, 2, v___x_787_);
v___x_789_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_789_, 0, v___y_783_);
lean_ctor_set(v___x_789_, 1, v___y_777_);
lean_ctor_set(v___x_789_, 2, v___y_779_);
lean_inc_ref_n(v___x_789_, 6);
lean_inc_ref(v___x_788_);
lean_inc(v___y_780_);
v___x_790_ = l_Lean_Syntax_node7(v___y_783_, v___y_780_, v___x_788_, v___x_789_, v___x_789_, v___x_789_, v___x_789_, v___x_789_, v___x_789_);
v___x_791_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__16));
lean_inc_ref(v___y_774_);
v___x_792_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_792_, 0, v___y_783_);
lean_ctor_set(v___x_792_, 1, v___y_774_);
v___x_793_ = l_Lean_Syntax_node1(v___y_783_, v___x_791_, v___x_792_);
v___x_794_ = lean_obj_once(&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__18, &l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__18_once, _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__18);
v___x_795_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__19));
lean_inc_n(v___y_778_, 3);
lean_inc_n(v___y_784_, 3);
v___x_796_ = l_Lean_addMacroScope(v___y_784_, v___x_795_, v___y_778_);
v___x_797_ = lean_box(0);
v___x_798_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_798_, 0, v___y_783_);
lean_ctor_set(v___x_798_, 1, v___x_794_);
lean_ctor_set(v___x_798_, 2, v___x_796_);
lean_ctor_set(v___x_798_, 3, v___x_797_);
v___x_799_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__14));
v___x_800_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__21));
v___x_801_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__22));
v___x_802_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_802_, 0, v___y_783_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
v___x_803_ = lean_obj_once(&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__24, &l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__24_once, _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__24);
v___x_804_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__26));
v___x_805_ = l_Lean_addMacroScope(v___y_784_, v___x_804_, v___y_778_);
v___x_806_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__28));
v___x_807_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_807_, 0, v___y_783_);
lean_ctor_set(v___x_807_, 1, v___x_803_);
lean_ctor_set(v___x_807_, 2, v___x_805_);
lean_ctor_set(v___x_807_, 3, v___x_806_);
lean_inc_ref(v___x_802_);
v___x_808_ = l_Lean_Syntax_node2(v___y_783_, v___x_800_, v___x_802_, v___x_807_);
v___x_809_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__29));
v___x_810_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_810_, 0, v___y_783_);
lean_ctor_set(v___x_810_, 1, v___x_809_);
v___x_811_ = l_Lean_Syntax_node3(v___y_783_, v___y_777_, v___x_798_, v___x_808_, v___x_810_);
v___x_812_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__31));
v___x_813_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__33));
v___x_814_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__35));
v___x_815_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__37));
v___x_816_ = lean_obj_once(&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__38, &l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__38_once, _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__38);
v___x_817_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__39));
v___x_818_ = l_Lean_addMacroScope(v___y_784_, v___x_817_, v___y_778_);
v___x_819_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__42));
v___x_820_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_820_, 0, v___y_783_);
lean_ctor_set(v___x_820_, 1, v___x_816_);
lean_ctor_set(v___x_820_, 2, v___x_818_);
lean_ctor_set(v___x_820_, 3, v___x_819_);
lean_inc(v___y_782_);
v___x_821_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_797_, v___y_782_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v___x_822_; 
v___x_822_ = l_Lean_quoteNameMk(v___y_782_);
v___y_702_ = v___y_773_;
v___y_703_ = v___x_813_;
v___y_704_ = v___y_775_;
v___y_705_ = v___x_799_;
v___y_706_ = v___x_790_;
v___y_707_ = v___y_776_;
v___y_708_ = v___x_811_;
v___y_709_ = v___x_814_;
v___y_710_ = v___y_777_;
v___y_711_ = v___x_812_;
v___y_712_ = v___x_797_;
v___y_713_ = v___x_815_;
v___y_714_ = v___y_778_;
v___y_715_ = v___x_802_;
v___y_716_ = v___x_793_;
v___y_717_ = v___x_789_;
v___y_718_ = v___x_788_;
v___y_719_ = v___x_820_;
v___y_720_ = v___y_781_;
v___y_721_ = v___y_783_;
v___y_722_ = v___y_784_;
v___y_723_ = v___y_785_;
v___y_724_ = v___x_822_;
goto v___jp_701_;
}
else
{
lean_object* v_val_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
lean_dec(v___y_782_);
v_val_823_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_val_823_);
lean_dec_ref_known(v___x_821_, 1);
v___x_824_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__44));
v___x_825_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__45));
v___x_826_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__46));
v___x_827_ = lean_string_intercalate(v___x_826_, v_val_823_);
v___x_828_ = lean_string_append(v___x_825_, v___x_827_);
lean_dec_ref(v___x_827_);
lean_inc_n(v___y_776_, 2);
v___x_829_ = l_Lean_Syntax_mkNameLit(v___x_828_, v___y_776_);
v___x_830_ = lean_unsigned_to_nat(1u);
v___x_831_ = lean_mk_empty_array_with_capacity(v___x_830_);
v___x_832_ = lean_array_push(v___x_831_, v___x_829_);
v___x_833_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_833_, 0, v___y_776_);
lean_ctor_set(v___x_833_, 1, v___x_824_);
lean_ctor_set(v___x_833_, 2, v___x_832_);
v___y_702_ = v___y_773_;
v___y_703_ = v___x_813_;
v___y_704_ = v___y_775_;
v___y_705_ = v___x_799_;
v___y_706_ = v___x_790_;
v___y_707_ = v___y_776_;
v___y_708_ = v___x_811_;
v___y_709_ = v___x_814_;
v___y_710_ = v___y_777_;
v___y_711_ = v___x_812_;
v___y_712_ = v___x_797_;
v___y_713_ = v___x_815_;
v___y_714_ = v___y_778_;
v___y_715_ = v___x_802_;
v___y_716_ = v___x_793_;
v___y_717_ = v___x_789_;
v___y_718_ = v___x_788_;
v___y_719_ = v___x_820_;
v___y_720_ = v___y_781_;
v___y_721_ = v___y_783_;
v___y_722_ = v___y_784_;
v___y_723_ = v___y_785_;
v___y_724_ = v___x_833_;
goto v___jp_701_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___boxed(lean_object* v_x_886_, lean_object* v_a_887_, lean_object* v_a_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1(v_x_886_, v_a_887_, v_a_888_);
lean_dec_ref(v_a_887_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0___redArg(lean_object* v_a_890_, lean_object* v_x_891_){
_start:
{
if (lean_obj_tag(v_x_891_) == 0)
{
lean_object* v___x_892_; 
v___x_892_ = lean_box(0);
return v___x_892_;
}
else
{
lean_object* v_key_893_; lean_object* v_value_894_; lean_object* v_tail_895_; uint8_t v___x_896_; 
v_key_893_ = lean_ctor_get(v_x_891_, 0);
v_value_894_ = lean_ctor_get(v_x_891_, 1);
v_tail_895_ = lean_ctor_get(v_x_891_, 2);
v___x_896_ = lean_name_eq(v_key_893_, v_a_890_);
if (v___x_896_ == 0)
{
v_x_891_ = v_tail_895_;
goto _start;
}
else
{
lean_object* v___x_898_; 
lean_inc(v_value_894_);
v___x_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_898_, 0, v_value_894_);
return v___x_898_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0___redArg___boxed(lean_object* v_a_899_, lean_object* v_x_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0___redArg(v_a_899_, v_x_900_);
lean_dec(v_x_900_);
lean_dec(v_a_899_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0___redArg(lean_object* v_m_902_, lean_object* v_a_903_){
_start:
{
lean_object* v_buckets_904_; lean_object* v___x_905_; uint64_t v___y_907_; 
v_buckets_904_ = lean_ctor_get(v_m_902_, 1);
v___x_905_ = lean_array_get_size(v_buckets_904_);
if (lean_obj_tag(v_a_903_) == 0)
{
uint64_t v___x_921_; 
v___x_921_ = 1723ULL;
v___y_907_ = v___x_921_;
goto v___jp_906_;
}
else
{
uint64_t v_hash_922_; 
v_hash_922_ = lean_ctor_get_uint64(v_a_903_, sizeof(void*)*2);
v___y_907_ = v_hash_922_;
goto v___jp_906_;
}
v___jp_906_:
{
uint64_t v___x_908_; uint64_t v___x_909_; uint64_t v_fold_910_; uint64_t v___x_911_; uint64_t v___x_912_; uint64_t v___x_913_; size_t v___x_914_; size_t v___x_915_; size_t v___x_916_; size_t v___x_917_; size_t v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_908_ = 32ULL;
v___x_909_ = lean_uint64_shift_right(v___y_907_, v___x_908_);
v_fold_910_ = lean_uint64_xor(v___y_907_, v___x_909_);
v___x_911_ = 16ULL;
v___x_912_ = lean_uint64_shift_right(v_fold_910_, v___x_911_);
v___x_913_ = lean_uint64_xor(v_fold_910_, v___x_912_);
v___x_914_ = lean_uint64_to_usize(v___x_913_);
v___x_915_ = lean_usize_of_nat(v___x_905_);
v___x_916_ = ((size_t)1ULL);
v___x_917_ = lean_usize_sub(v___x_915_, v___x_916_);
v___x_918_ = lean_usize_land(v___x_914_, v___x_917_);
v___x_919_ = lean_array_uget_borrowed(v_buckets_904_, v___x_918_);
v___x_920_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0___redArg(v_a_903_, v___x_919_);
return v___x_920_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0___redArg___boxed(lean_object* v_m_923_, lean_object* v_a_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0___redArg(v_m_923_, v_a_924_);
lean_dec(v_a_924_);
lean_dec_ref(v_m_923_);
return v_res_925_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_926_; 
v___x_926_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_926_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_927_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__0);
v___x_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
return v___x_928_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_929_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__1);
v___x_930_ = lean_unsigned_to_nat(0u);
v___x_931_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_931_, 0, v___x_930_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
lean_ctor_set(v___x_931_, 2, v___x_930_);
lean_ctor_set(v___x_931_, 3, v___x_930_);
lean_ctor_set(v___x_931_, 4, v___x_929_);
lean_ctor_set(v___x_931_, 5, v___x_929_);
lean_ctor_set(v___x_931_, 6, v___x_929_);
lean_ctor_set(v___x_931_, 7, v___x_929_);
lean_ctor_set(v___x_931_, 8, v___x_929_);
lean_ctor_set(v___x_931_, 9, v___x_929_);
lean_ctor_set(v___x_931_, 10, v___x_929_);
return v___x_931_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_932_ = lean_unsigned_to_nat(32u);
v___x_933_ = lean_mk_empty_array_with_capacity(v___x_932_);
v___x_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
return v___x_934_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__4(void){
_start:
{
size_t v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_935_ = ((size_t)5ULL);
v___x_936_ = lean_unsigned_to_nat(0u);
v___x_937_ = lean_unsigned_to_nat(32u);
v___x_938_ = lean_mk_empty_array_with_capacity(v___x_937_);
v___x_939_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__3);
v___x_940_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_940_, 0, v___x_939_);
lean_ctor_set(v___x_940_, 1, v___x_938_);
lean_ctor_set(v___x_940_, 2, v___x_936_);
lean_ctor_set(v___x_940_, 3, v___x_936_);
lean_ctor_set_usize(v___x_940_, 4, v___x_935_);
return v___x_940_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__5(void){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_941_ = lean_box(1);
v___x_942_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__4);
v___x_943_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__1);
v___x_944_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
lean_ctor_set(v___x_944_, 1, v___x_942_);
lean_ctor_set(v___x_944_, 2, v___x_941_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2(lean_object* v_msgData_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v___x_949_; lean_object* v_toCold_950_; lean_object* v_env_951_; lean_object* v_options_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_949_ = lean_st_ref_get(v___y_947_);
v_toCold_950_ = lean_ctor_get(v___y_946_, 0);
v_env_951_ = lean_ctor_get(v___x_949_, 0);
lean_inc_ref(v_env_951_);
lean_dec(v___x_949_);
v_options_952_ = lean_ctor_get(v_toCold_950_, 2);
v___x_953_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__2);
v___x_954_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__5);
lean_inc_ref(v_options_952_);
v___x_955_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_955_, 0, v_env_951_);
lean_ctor_set(v___x_955_, 1, v___x_953_);
lean_ctor_set(v___x_955_, 2, v___x_954_);
lean_ctor_set(v___x_955_, 3, v_options_952_);
v___x_956_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
lean_ctor_set(v___x_956_, 1, v_msgData_945_);
v___x_957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___boxed(lean_object* v_msgData_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2(v_msgData_958_, v___y_959_, v___y_960_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_labelled_spec__1___redArg(lean_object* v_msg_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v_ref_967_; lean_object* v___x_968_; lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_977_; 
v_ref_967_ = lean_ctor_get(v___y_964_, 2);
v___x_968_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2(v_msg_963_, v___y_964_, v___y_965_);
v_a_969_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_977_ == 0)
{
v___x_971_ = v___x_968_;
v_isShared_972_ = v_isSharedCheck_977_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_968_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_977_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_973_; lean_object* v___x_975_; 
lean_inc(v_ref_967_);
v___x_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_973_, 0, v_ref_967_);
lean_ctor_set(v___x_973_, 1, v_a_969_);
if (v_isShared_972_ == 0)
{
lean_ctor_set_tag(v___x_971_, 1);
lean_ctor_set(v___x_971_, 0, v___x_973_);
v___x_975_ = v___x_971_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_973_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_labelled_spec__1___redArg___boxed(lean_object* v_msg_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Lean_throwError___at___00Lean_labelled_spec__1___redArg(v_msg_978_, v___y_979_, v___y_980_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
return v_res_982_;
}
}
static lean_object* _init_l_Lean_labelled___closed__1(void){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = ((lean_object*)(l_Lean_labelled___closed__0));
v___x_985_ = l_Lean_stringToMessageData(v___x_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_labelled(lean_object* v_attrName_986_, lean_object* v_a_987_, lean_object* v_a_988_){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_990_ = l_Lean_labelExtensionMapRef;
v___x_991_ = lean_st_ref_get(v___x_990_);
v___x_992_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0___redArg(v___x_991_, v_attrName_986_);
lean_dec(v___x_991_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_993_ = lean_obj_once(&l_Lean_labelled___closed__1, &l_Lean_labelled___closed__1_once, _init_l_Lean_labelled___closed__1);
v___x_994_ = l_Lean_MessageData_ofName(v_attrName_986_);
v___x_995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_993_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
v___x_996_ = l_Lean_throwError___at___00Lean_labelled_spec__1___redArg(v___x_995_, v_a_987_, v_a_988_);
return v___x_996_;
}
else
{
lean_object* v_val_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1011_; 
lean_dec(v_attrName_986_);
v_val_997_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_999_ = v___x_992_;
v_isShared_1000_ = v_isSharedCheck_1011_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_val_997_);
lean_dec(v___x_992_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1011_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1001_; lean_object* v_ext_1002_; lean_object* v_toEnvExtension_1003_; lean_object* v_env_1004_; lean_object* v_asyncMode_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1009_; 
v___x_1001_ = lean_st_ref_get(v_a_988_);
v_ext_1002_ = lean_ctor_get(v_val_997_, 1);
v_toEnvExtension_1003_ = lean_ctor_get(v_ext_1002_, 0);
v_env_1004_ = lean_ctor_get(v___x_1001_, 0);
lean_inc_ref(v_env_1004_);
lean_dec(v___x_1001_);
v_asyncMode_1005_ = lean_ctor_get(v_toEnvExtension_1003_, 2);
lean_inc(v_asyncMode_1005_);
v___x_1006_ = lean_obj_once(&l_Lean_mkLabelAttr___closed__0, &l_Lean_mkLabelAttr___closed__0_once, _init_l_Lean_mkLabelAttr___closed__0);
v___x_1007_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1006_, v_val_997_, v_env_1004_, v_asyncMode_1005_);
lean_dec(v_asyncMode_1005_);
lean_dec(v_val_997_);
if (v_isShared_1000_ == 0)
{
lean_ctor_set_tag(v___x_999_, 0);
lean_ctor_set(v___x_999_, 0, v___x_1007_);
v___x_1009_ = v___x_999_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1007_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_labelled___boxed(lean_object* v_attrName_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Lean_labelled(v_attrName_1012_, v_a_1013_, v_a_1014_);
lean_dec(v_a_1014_);
lean_dec_ref(v_a_1013_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0(lean_object* v_00_u03b2_1017_, lean_object* v_m_1018_, lean_object* v_a_1019_){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0___redArg(v_m_1018_, v_a_1019_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0___boxed(lean_object* v_00_u03b2_1021_, lean_object* v_m_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0(v_00_u03b2_1021_, v_m_1022_, v_a_1023_);
lean_dec(v_a_1023_);
lean_dec_ref(v_m_1022_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_labelled_spec__1(lean_object* v_00_u03b1_1025_, lean_object* v_msg_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Lean_throwError___at___00Lean_labelled_spec__1___redArg(v_msg_1026_, v___y_1027_, v___y_1028_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_labelled_spec__1___boxed(lean_object* v_00_u03b1_1031_, lean_object* v_msg_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Lean_throwError___at___00Lean_labelled_spec__1(v_00_u03b1_1031_, v_msg_1032_, v___y_1033_, v___y_1034_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0(lean_object* v_00_u03b2_1037_, lean_object* v_a_1038_, lean_object* v_x_1039_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0___redArg(v_a_1038_, v_x_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1041_, lean_object* v_a_1042_, lean_object* v_x_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0(v_00_u03b2_1041_, v_a_1042_, v_x_1043_);
lean_dec(v_x_1043_);
lean_dec(v_a_1042_);
return v_res_1044_;
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
