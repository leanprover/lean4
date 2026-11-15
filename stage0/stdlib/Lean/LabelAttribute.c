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
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Array_instInhabited___redArg();
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addImportedGlobals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* l_Array_mkArray0___redArg();
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
LEAN_EXPORT lean_object* l_Lean_mkLabelExt___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLabelExt___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_mkLabelExt_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_mkLabelExt_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_mkLabelExt_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_mkLabelExt_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLabelExt___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLabelExt___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLabelExt___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLabelExt___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLabelExt___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLabelExt___lam__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLabelExt___lam__4___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_mkLabelExt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkLabelExt___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_mkLabelExt___closed__0 = (const lean_object*)&l_Lean_mkLabelExt___closed__0_value;
static const lean_closure_object l_Lean_mkLabelExt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkLabelExt___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_mkLabelExt___closed__1 = (const lean_object*)&l_Lean_mkLabelExt___closed__1_value;
static const lean_closure_object l_Lean_mkLabelExt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkLabelExt___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_mkLabelExt___closed__2 = (const lean_object*)&l_Lean_mkLabelExt___closed__2_value;
static const lean_closure_object l_Lean_mkLabelExt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkLabelExt___lam__3___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_mkLabelExt___closed__3 = (const lean_object*)&l_Lean_mkLabelExt___closed__3_value;
static const lean_array_object l_Lean_mkLabelExt___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_mkLabelExt___closed__4 = (const lean_object*)&l_Lean_mkLabelExt___closed__4_value;
static const lean_closure_object l_Lean_mkLabelExt___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkLabelExt___lam__4___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_mkLabelExt___closed__4_value)} };
static const lean_object* l_Lean_mkLabelExt___closed__5 = (const lean_object*)&l_Lean_mkLabelExt___closed__5_value;
static const lean_closure_object l_Lean_mkLabelExt___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ScopedEnvExtension_addImportedGlobals___boxed, .m_arity = 9, .m_num_fixed = 6, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkLabelExt___closed__5_value),((lean_object*)&l_Lean_mkLabelExt___closed__3_value),((lean_object*)&l_Lean_mkLabelExt___closed__1_value)} };
static const lean_object* l_Lean_mkLabelExt___closed__6 = (const lean_object*)&l_Lean_mkLabelExt___closed__6_value;
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
LEAN_EXPORT lean_object* l_Lean_mkLabelExt___lam__0(lean_object* v___y_90_){
_start:
{
lean_inc_ref(v___y_90_);
return v___y_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelExt___lam__0___boxed(lean_object* v___y_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Lean_mkLabelExt___lam__0(v___y_91_);
lean_dec_ref(v___y_91_);
return v_res_92_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_mkLabelExt_spec__0_spec__0(lean_object* v_a_93_, lean_object* v_as_94_, size_t v_i_95_, size_t v_stop_96_){
_start:
{
uint8_t v___x_97_; 
v___x_97_ = lean_usize_dec_eq(v_i_95_, v_stop_96_);
if (v___x_97_ == 0)
{
lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_98_ = lean_array_uget_borrowed(v_as_94_, v_i_95_);
v___x_99_ = lean_name_eq(v_a_93_, v___x_98_);
if (v___x_99_ == 0)
{
size_t v___x_100_; size_t v___x_101_; 
v___x_100_ = ((size_t)1ULL);
v___x_101_ = lean_usize_add(v_i_95_, v___x_100_);
v_i_95_ = v___x_101_;
goto _start;
}
else
{
return v___x_99_;
}
}
else
{
uint8_t v___x_103_; 
v___x_103_ = 0;
return v___x_103_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_mkLabelExt_spec__0_spec__0___boxed(lean_object* v_a_104_, lean_object* v_as_105_, lean_object* v_i_106_, lean_object* v_stop_107_){
_start:
{
size_t v_i_boxed_108_; size_t v_stop_boxed_109_; uint8_t v_res_110_; lean_object* v_r_111_; 
v_i_boxed_108_ = lean_unbox_usize(v_i_106_);
lean_dec(v_i_106_);
v_stop_boxed_109_ = lean_unbox_usize(v_stop_107_);
lean_dec(v_stop_107_);
v_res_110_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_mkLabelExt_spec__0_spec__0(v_a_104_, v_as_105_, v_i_boxed_108_, v_stop_boxed_109_);
lean_dec_ref(v_as_105_);
lean_dec(v_a_104_);
v_r_111_ = lean_box(v_res_110_);
return v_r_111_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_mkLabelExt_spec__0(lean_object* v_as_112_, lean_object* v_a_113_){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; uint8_t v___x_116_; 
v___x_114_ = lean_unsigned_to_nat(0u);
v___x_115_ = lean_array_get_size(v_as_112_);
v___x_116_ = lean_nat_dec_lt(v___x_114_, v___x_115_);
if (v___x_116_ == 0)
{
return v___x_116_;
}
else
{
size_t v___x_117_; size_t v___x_118_; uint8_t v___x_119_; 
v___x_117_ = ((size_t)0ULL);
v___x_118_ = lean_usize_of_nat(v___x_115_);
v___x_119_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_mkLabelExt_spec__0_spec__0(v_a_113_, v_as_112_, v___x_117_, v___x_118_);
return v___x_119_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_mkLabelExt_spec__0___boxed(lean_object* v_as_120_, lean_object* v_a_121_){
_start:
{
uint8_t v_res_122_; lean_object* v_r_123_; 
v_res_122_ = l_Array_contains___at___00Lean_mkLabelExt_spec__0(v_as_120_, v_a_121_);
lean_dec(v_a_121_);
lean_dec_ref(v_as_120_);
v_r_123_ = lean_box(v_res_122_);
return v_r_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelExt___lam__1(lean_object* v_d_124_, lean_object* v_e_125_){
_start:
{
uint8_t v___x_126_; 
v___x_126_ = l_Array_contains___at___00Lean_mkLabelExt_spec__0(v_d_124_, v_e_125_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; 
v___x_127_ = lean_array_push(v_d_124_, v_e_125_);
return v___x_127_;
}
else
{
lean_dec(v_e_125_);
return v_d_124_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelExt___lam__2(lean_object* v_x_128_, lean_object* v_a_129_){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_130_, 0, v_a_129_);
lean_inc_ref_n(v___x_130_, 2);
v___x_131_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
lean_ctor_set(v___x_131_, 1, v___x_130_);
lean_ctor_set(v___x_131_, 2, v___x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelExt___lam__2___boxed(lean_object* v_x_132_, lean_object* v_a_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Lean_mkLabelExt___lam__2(v_x_132_, v_a_133_);
lean_dec_ref(v_x_132_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelExt___lam__3(lean_object* v_x_135_, lean_object* v_a_136_, lean_object* v___y_137_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_139_, 0, v_a_136_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelExt___lam__3___boxed(lean_object* v_x_140_, lean_object* v_a_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_mkLabelExt___lam__3(v_x_140_, v_a_141_, v___y_142_);
lean_dec_ref(v___y_142_);
lean_dec_ref(v_x_140_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelExt___lam__4(lean_object* v___x_145_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_147_, 0, v___x_145_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelExt___lam__4___boxed(lean_object* v___x_148_, lean_object* v___y_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Lean_mkLabelExt___lam__4(v___x_148_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelExt(lean_object* v_name_163_){
_start:
{
lean_object* v___f_165_; lean_object* v___f_166_; lean_object* v___f_167_; lean_object* v___x_168_; uint8_t v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___f_165_ = ((lean_object*)(l_Lean_mkLabelExt___closed__0));
v___f_166_ = ((lean_object*)(l_Lean_mkLabelExt___closed__1));
v___f_167_ = ((lean_object*)(l_Lean_mkLabelExt___closed__2));
v___x_168_ = ((lean_object*)(l_Lean_mkLabelExt___closed__4));
v___x_169_ = 0;
v___x_170_ = lean_box(0);
v___x_171_ = ((lean_object*)(l_Lean_mkLabelExt___closed__6));
v___x_172_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_172_, 0, v_name_163_);
lean_ctor_set(v___x_172_, 1, v___f_166_);
lean_ctor_set(v___x_172_, 2, v___f_166_);
lean_ctor_set(v___x_172_, 3, v___x_168_);
lean_ctor_set(v___x_172_, 4, v___f_165_);
lean_ctor_set(v___x_172_, 5, v___f_167_);
lean_ctor_set(v___x_172_, 6, v___x_170_);
lean_ctor_set(v___x_172_, 7, v___x_171_);
lean_ctor_set_uint8(v___x_172_, sizeof(void*)*8, v___x_169_);
lean_ctor_set_uint8(v___x_172_, sizeof(void*)*8 + 1, v___x_169_);
v___x_173_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelExt___boxed(lean_object* v_name_174_, lean_object* v_a_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lean_mkLabelExt(v_name_174_);
return v_res_176_;
}
}
static lean_object* _init_l_Lean_mkLabelAttr___auto__1(void){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = lean_obj_once(&l_Lean_mkLabelExt___auto__1___closed__28, &l_Lean_mkLabelExt___auto__1___closed__28_once, _init_l_Lean_mkLabelExt___auto__1___closed__28);
return v___x_177_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_178_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_179_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__0);
v___x_180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
return v___x_180_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__1);
v___x_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg(lean_object* v_ext_183_, lean_object* v_b_184_, uint8_t v_kind_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
lean_object* v_toCold_189_; lean_object* v_currNamespace_190_; lean_object* v___x_191_; lean_object* v_env_192_; lean_object* v_nextMacroScope_193_; lean_object* v_ngen_194_; lean_object* v_auxDeclNGen_195_; lean_object* v_traceState_196_; lean_object* v_recordedDeps_197_; lean_object* v_messages_198_; lean_object* v_infoState_199_; lean_object* v_snapshotTasks_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_212_; 
v_toCold_189_ = lean_ctor_get(v___y_186_, 0);
v_currNamespace_190_ = lean_ctor_get(v_toCold_189_, 4);
v___x_191_ = lean_st_ref_take(v___y_187_);
v_env_192_ = lean_ctor_get(v___x_191_, 0);
v_nextMacroScope_193_ = lean_ctor_get(v___x_191_, 1);
v_ngen_194_ = lean_ctor_get(v___x_191_, 2);
v_auxDeclNGen_195_ = lean_ctor_get(v___x_191_, 3);
v_traceState_196_ = lean_ctor_get(v___x_191_, 4);
v_recordedDeps_197_ = lean_ctor_get(v___x_191_, 6);
v_messages_198_ = lean_ctor_get(v___x_191_, 7);
v_infoState_199_ = lean_ctor_get(v___x_191_, 8);
v_snapshotTasks_200_ = lean_ctor_get(v___x_191_, 9);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_212_ == 0)
{
lean_object* v_unused_213_; 
v_unused_213_ = lean_ctor_get(v___x_191_, 5);
lean_dec(v_unused_213_);
v___x_202_ = v___x_191_;
v_isShared_203_ = v_isSharedCheck_212_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_snapshotTasks_200_);
lean_inc(v_infoState_199_);
lean_inc(v_messages_198_);
lean_inc(v_recordedDeps_197_);
lean_inc(v_traceState_196_);
lean_inc(v_auxDeclNGen_195_);
lean_inc(v_ngen_194_);
lean_inc(v_nextMacroScope_193_);
lean_inc(v_env_192_);
lean_dec(v___x_191_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_212_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_208_; 
v___x_204_ = lean_box(0);
lean_inc(v_currNamespace_190_);
v___x_205_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_192_, v_ext_183_, v_b_184_, v_kind_185_, v_currNamespace_190_);
v___x_206_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__2);
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 5, v___x_206_);
lean_ctor_set(v___x_202_, 0, v___x_205_);
v___x_208_ = v___x_202_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v___x_205_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v_nextMacroScope_193_);
lean_ctor_set(v_reuseFailAlloc_211_, 2, v_ngen_194_);
lean_ctor_set(v_reuseFailAlloc_211_, 3, v_auxDeclNGen_195_);
lean_ctor_set(v_reuseFailAlloc_211_, 4, v_traceState_196_);
lean_ctor_set(v_reuseFailAlloc_211_, 5, v___x_206_);
lean_ctor_set(v_reuseFailAlloc_211_, 6, v_recordedDeps_197_);
lean_ctor_set(v_reuseFailAlloc_211_, 7, v_messages_198_);
lean_ctor_set(v_reuseFailAlloc_211_, 8, v_infoState_199_);
lean_ctor_set(v_reuseFailAlloc_211_, 9, v_snapshotTasks_200_);
v___x_208_ = v_reuseFailAlloc_211_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = lean_st_ref_put(v___y_187_, v___x_208_);
v___x_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_210_, 0, v___x_204_);
return v___x_210_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___boxed(lean_object* v_ext_214_, lean_object* v_b_215_, lean_object* v_kind_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
uint8_t v_kind_boxed_220_; lean_object* v_res_221_; 
v_kind_boxed_220_ = lean_unbox(v_kind_216_);
v_res_221_ = l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg(v_ext_214_, v_b_215_, v_kind_boxed_220_, v___y_217_, v___y_218_);
lean_dec(v___y_218_);
lean_dec_ref(v___y_217_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0(lean_object* v_00_u03b1_222_, lean_object* v_00_u03b2_223_, lean_object* v_00_u03c3_224_, lean_object* v_ext_225_, lean_object* v_b_226_, uint8_t v_kind_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg(v_ext_225_, v_b_226_, v_kind_227_, v___y_228_, v___y_229_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___boxed(lean_object* v_00_u03b1_232_, lean_object* v_00_u03b2_233_, lean_object* v_00_u03c3_234_, lean_object* v_ext_235_, lean_object* v_b_236_, lean_object* v_kind_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
uint8_t v_kind_boxed_241_; lean_object* v_res_242_; 
v_kind_boxed_241_ = lean_unbox(v_kind_237_);
v_res_242_ = l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0(v_00_u03b1_232_, v_00_u03b2_233_, v_00_u03c3_234_, v_ext_235_, v_b_236_, v_kind_boxed_241_, v___y_238_, v___y_239_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelAttr___lam__0(lean_object* v_ext_243_, lean_object* v_declName_244_, lean_object* v_x_245_, uint8_t v_kind_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg(v_ext_243_, v_declName_244_, v_kind_246_, v___y_247_, v___y_248_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelAttr___lam__0___boxed(lean_object* v_ext_251_, lean_object* v_declName_252_, lean_object* v_x_253_, lean_object* v_kind_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
uint8_t v_kind_boxed_258_; lean_object* v_res_259_; 
v_kind_boxed_258_ = lean_unbox(v_kind_254_);
v_res_259_ = l_Lean_mkLabelAttr___lam__0(v_ext_251_, v_declName_252_, v_x_253_, v_kind_boxed_258_, v___y_255_, v___y_256_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
lean_dec(v_x_253_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_mkLabelAttr_spec__1_spec__1_spec__2(lean_object* v_xs_260_, lean_object* v_v_261_, lean_object* v_i_262_){
_start:
{
lean_object* v___x_263_; uint8_t v___x_264_; 
v___x_263_ = lean_array_get_size(v_xs_260_);
v___x_264_ = lean_nat_dec_lt(v_i_262_, v___x_263_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; 
lean_dec(v_i_262_);
v___x_265_ = lean_box(0);
return v___x_265_;
}
else
{
lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_266_ = lean_array_fget_borrowed(v_xs_260_, v_i_262_);
v___x_267_ = lean_name_eq(v___x_266_, v_v_261_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = lean_unsigned_to_nat(1u);
v___x_269_ = lean_nat_add(v_i_262_, v___x_268_);
lean_dec(v_i_262_);
v_i_262_ = v___x_269_;
goto _start;
}
else
{
lean_object* v___x_271_; 
v___x_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_271_, 0, v_i_262_);
return v___x_271_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_mkLabelAttr_spec__1_spec__1_spec__2___boxed(lean_object* v_xs_272_, lean_object* v_v_273_, lean_object* v_i_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_mkLabelAttr_spec__1_spec__1_spec__2(v_xs_272_, v_v_273_, v_i_274_);
lean_dec(v_v_273_);
lean_dec_ref(v_xs_272_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_mkLabelAttr_spec__1_spec__1(lean_object* v_xs_276_, lean_object* v_v_277_){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = lean_unsigned_to_nat(0u);
v___x_279_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_mkLabelAttr_spec__1_spec__1_spec__2(v_xs_276_, v_v_277_, v___x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_mkLabelAttr_spec__1_spec__1___boxed(lean_object* v_xs_280_, lean_object* v_v_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_mkLabelAttr_spec__1_spec__1(v_xs_280_, v_v_281_);
lean_dec(v_v_281_);
lean_dec_ref(v_xs_280_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Array_erase___at___00Lean_mkLabelAttr_spec__1(lean_object* v_as_283_, lean_object* v_a_284_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = l_Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_mkLabelAttr_spec__1_spec__1(v_as_283_, v_a_284_);
if (lean_obj_tag(v___x_285_) == 0)
{
return v_as_283_;
}
else
{
lean_object* v_val_286_; lean_object* v___x_287_; 
v_val_286_ = lean_ctor_get(v___x_285_, 0);
lean_inc(v_val_286_);
lean_dec_ref_known(v___x_285_, 1);
v___x_287_ = l_Array_eraseIdx___redArg(v_as_283_, v_val_286_);
return v___x_287_;
}
}
}
LEAN_EXPORT lean_object* l_Array_erase___at___00Lean_mkLabelAttr_spec__1___boxed(lean_object* v_as_288_, lean_object* v_a_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Array_erase___at___00Lean_mkLabelAttr_spec__1(v_as_288_, v_a_289_);
lean_dec(v_a_289_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelAttr___lam__1(lean_object* v___x_291_, lean_object* v_declName_292_, lean_object* v_x_293_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = l_Array_erase___at___00Lean_mkLabelAttr_spec__1(v___x_291_, v_declName_292_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelAttr___lam__1___boxed(lean_object* v___x_295_, lean_object* v_declName_296_, lean_object* v_x_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Lean_mkLabelAttr___lam__1(v___x_295_, v_declName_296_, v_x_297_);
lean_dec_ref(v_x_297_);
lean_dec(v_declName_296_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelAttr___lam__2(lean_object* v_ext_299_, lean_object* v___x_300_, lean_object* v_declName_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v___x_305_; lean_object* v_ext_306_; lean_object* v_toEnvExtension_307_; lean_object* v_env_308_; lean_object* v_asyncMode_309_; uint8_t v___x_310_; lean_object* v___x_311_; lean_object* v___f_312_; lean_object* v___x_313_; lean_object* v_env_314_; lean_object* v_nextMacroScope_315_; lean_object* v_ngen_316_; lean_object* v_auxDeclNGen_317_; lean_object* v_traceState_318_; lean_object* v_recordedDeps_319_; lean_object* v_messages_320_; lean_object* v_infoState_321_; lean_object* v_snapshotTasks_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_334_; 
v___x_305_ = lean_st_ref_get(v___y_303_);
v_ext_306_ = lean_ctor_get(v_ext_299_, 1);
v_toEnvExtension_307_ = lean_ctor_get(v_ext_306_, 0);
v_env_308_ = lean_ctor_get(v___x_305_, 0);
lean_inc_ref(v_env_308_);
lean_dec(v___x_305_);
v_asyncMode_309_ = lean_ctor_get(v_toEnvExtension_307_, 2);
v___x_310_ = 0;
v___x_311_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_300_, v_ext_299_, v_env_308_, v_asyncMode_309_, v___x_310_);
v___f_312_ = lean_alloc_closure((void*)(l_Lean_mkLabelAttr___lam__1___boxed), 3, 2);
lean_closure_set(v___f_312_, 0, v___x_311_);
lean_closure_set(v___f_312_, 1, v_declName_301_);
v___x_313_ = lean_st_ref_take(v___y_303_);
v_env_314_ = lean_ctor_get(v___x_313_, 0);
v_nextMacroScope_315_ = lean_ctor_get(v___x_313_, 1);
v_ngen_316_ = lean_ctor_get(v___x_313_, 2);
v_auxDeclNGen_317_ = lean_ctor_get(v___x_313_, 3);
v_traceState_318_ = lean_ctor_get(v___x_313_, 4);
v_recordedDeps_319_ = lean_ctor_get(v___x_313_, 6);
v_messages_320_ = lean_ctor_get(v___x_313_, 7);
v_infoState_321_ = lean_ctor_get(v___x_313_, 8);
v_snapshotTasks_322_ = lean_ctor_get(v___x_313_, 9);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_334_ == 0)
{
lean_object* v_unused_335_; 
v_unused_335_ = lean_ctor_get(v___x_313_, 5);
lean_dec(v_unused_335_);
v___x_324_ = v___x_313_;
v_isShared_325_ = v_isSharedCheck_334_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_snapshotTasks_322_);
lean_inc(v_infoState_321_);
lean_inc(v_messages_320_);
lean_inc(v_recordedDeps_319_);
lean_inc(v_traceState_318_);
lean_inc(v_auxDeclNGen_317_);
lean_inc(v_ngen_316_);
lean_inc(v_nextMacroScope_315_);
lean_inc(v_env_314_);
lean_dec(v___x_313_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_334_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_330_; 
v___x_326_ = lean_box(0);
v___x_327_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_299_, v_env_314_, v___f_312_);
v___x_328_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__2);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 5, v___x_328_);
lean_ctor_set(v___x_324_, 0, v___x_327_);
v___x_330_ = v___x_324_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_327_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v_nextMacroScope_315_);
lean_ctor_set(v_reuseFailAlloc_333_, 2, v_ngen_316_);
lean_ctor_set(v_reuseFailAlloc_333_, 3, v_auxDeclNGen_317_);
lean_ctor_set(v_reuseFailAlloc_333_, 4, v_traceState_318_);
lean_ctor_set(v_reuseFailAlloc_333_, 5, v___x_328_);
lean_ctor_set(v_reuseFailAlloc_333_, 6, v_recordedDeps_319_);
lean_ctor_set(v_reuseFailAlloc_333_, 7, v_messages_320_);
lean_ctor_set(v_reuseFailAlloc_333_, 8, v_infoState_321_);
lean_ctor_set(v_reuseFailAlloc_333_, 9, v_snapshotTasks_322_);
v___x_330_ = v_reuseFailAlloc_333_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = lean_st_ref_put(v___y_303_, v___x_330_);
v___x_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_332_, 0, v___x_326_);
return v___x_332_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelAttr___lam__2___boxed(lean_object* v_ext_336_, lean_object* v___x_337_, lean_object* v_declName_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_mkLabelAttr___lam__2(v_ext_336_, v___x_337_, v_declName_338_, v___y_339_, v___y_340_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec_ref(v___x_337_);
return v_res_342_;
}
}
static lean_object* _init_l_Lean_mkLabelAttr___closed__0(void){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l_Array_instInhabited___redArg();
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelAttr(lean_object* v_attrName_344_, lean_object* v_attrDescr_345_, lean_object* v_ext_346_, lean_object* v_ref_347_){
_start:
{
lean_object* v___f_349_; lean_object* v___x_350_; lean_object* v___f_351_; uint8_t v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
lean_inc_ref(v_ext_346_);
v___f_349_ = lean_alloc_closure((void*)(l_Lean_mkLabelAttr___lam__0___boxed), 7, 1);
lean_closure_set(v___f_349_, 0, v_ext_346_);
v___x_350_ = lean_obj_once(&l_Lean_mkLabelAttr___closed__0, &l_Lean_mkLabelAttr___closed__0_once, _init_l_Lean_mkLabelAttr___closed__0);
v___f_351_ = lean_alloc_closure((void*)(l_Lean_mkLabelAttr___lam__2___boxed), 6, 2);
lean_closure_set(v___f_351_, 0, v_ext_346_);
lean_closure_set(v___f_351_, 1, v___x_350_);
v___x_352_ = 1;
v___x_353_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_353_, 0, v_ref_347_);
lean_ctor_set(v___x_353_, 1, v_attrName_344_);
lean_ctor_set(v___x_353_, 2, v_attrDescr_345_);
lean_ctor_set_uint8(v___x_353_, sizeof(void*)*3, v___x_352_);
v___x_354_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
lean_ctor_set(v___x_354_, 1, v___f_349_);
lean_ctor_set(v___x_354_, 2, v___f_351_);
v___x_355_ = l_Lean_registerBuiltinAttribute(v___x_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLabelAttr___boxed(lean_object* v_attrName_356_, lean_object* v_attrDescr_357_, lean_object* v_ext_358_, lean_object* v_ref_359_, lean_object* v_a_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_mkLabelAttr(v_attrName_356_, v_attrDescr_357_, v_ext_358_, v_ref_359_);
return v_res_361_;
}
}
static lean_object* _init_l_Lean_registerLabelAttr___auto__1(void){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = lean_obj_once(&l_Lean_mkLabelExt___auto__1___closed__28, &l_Lean_mkLabelExt___auto__1___closed__28_once, _init_l_Lean_mkLabelExt___auto__1___closed__28);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_363_, lean_object* v_x_364_){
_start:
{
if (lean_obj_tag(v_x_364_) == 0)
{
return v_x_363_;
}
else
{
lean_object* v_key_365_; lean_object* v_value_366_; lean_object* v_tail_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_393_; 
v_key_365_ = lean_ctor_get(v_x_364_, 0);
v_value_366_ = lean_ctor_get(v_x_364_, 1);
v_tail_367_ = lean_ctor_get(v_x_364_, 2);
v_isSharedCheck_393_ = !lean_is_exclusive(v_x_364_);
if (v_isSharedCheck_393_ == 0)
{
v___x_369_ = v_x_364_;
v_isShared_370_ = v_isSharedCheck_393_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_tail_367_);
lean_inc(v_value_366_);
lean_inc(v_key_365_);
lean_dec(v_x_364_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_393_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_371_; uint64_t v___y_373_; 
v___x_371_ = lean_array_get_size(v_x_363_);
if (lean_obj_tag(v_key_365_) == 0)
{
uint64_t v___x_391_; 
v___x_391_ = 1723ULL;
v___y_373_ = v___x_391_;
goto v___jp_372_;
}
else
{
uint64_t v_hash_392_; 
v_hash_392_ = lean_ctor_get_uint64(v_key_365_, sizeof(void*)*2);
v___y_373_ = v_hash_392_;
goto v___jp_372_;
}
v___jp_372_:
{
uint64_t v___x_374_; uint64_t v___x_375_; uint64_t v_fold_376_; uint64_t v___x_377_; uint64_t v___x_378_; uint64_t v___x_379_; size_t v___x_380_; size_t v___x_381_; size_t v___x_382_; size_t v___x_383_; size_t v___x_384_; lean_object* v___x_385_; lean_object* v___x_387_; 
v___x_374_ = 32ULL;
v___x_375_ = lean_uint64_shift_right(v___y_373_, v___x_374_);
v_fold_376_ = lean_uint64_xor(v___y_373_, v___x_375_);
v___x_377_ = 16ULL;
v___x_378_ = lean_uint64_shift_right(v_fold_376_, v___x_377_);
v___x_379_ = lean_uint64_xor(v_fold_376_, v___x_378_);
v___x_380_ = lean_uint64_to_usize(v___x_379_);
v___x_381_ = lean_usize_of_nat(v___x_371_);
v___x_382_ = ((size_t)1ULL);
v___x_383_ = lean_usize_sub(v___x_381_, v___x_382_);
v___x_384_ = lean_usize_land(v___x_380_, v___x_383_);
v___x_385_ = lean_array_uget_borrowed(v_x_363_, v___x_384_);
lean_inc(v___x_385_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 2, v___x_385_);
v___x_387_ = v___x_369_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_key_365_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v_value_366_);
lean_ctor_set(v_reuseFailAlloc_390_, 2, v___x_385_);
v___x_387_ = v_reuseFailAlloc_390_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
lean_object* v___x_388_; 
v___x_388_ = lean_array_uset(v_x_363_, v___x_384_, v___x_387_);
v_x_363_ = v___x_388_;
v_x_364_ = v_tail_367_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2___redArg(lean_object* v_i_394_, lean_object* v_source_395_, lean_object* v_target_396_){
_start:
{
lean_object* v___x_397_; uint8_t v___x_398_; 
v___x_397_ = lean_array_get_size(v_source_395_);
v___x_398_ = lean_nat_dec_lt(v_i_394_, v___x_397_);
if (v___x_398_ == 0)
{
lean_dec_ref(v_source_395_);
lean_dec(v_i_394_);
return v_target_396_;
}
else
{
lean_object* v_es_399_; lean_object* v___x_400_; lean_object* v_source_401_; lean_object* v_target_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v_es_399_ = lean_array_fget(v_source_395_, v_i_394_);
v___x_400_ = lean_box(0);
v_source_401_ = lean_array_fset(v_source_395_, v_i_394_, v___x_400_);
v_target_402_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_target_396_, v_es_399_);
v___x_403_ = lean_unsigned_to_nat(1u);
v___x_404_ = lean_nat_add(v_i_394_, v___x_403_);
lean_dec(v_i_394_);
v_i_394_ = v___x_404_;
v_source_395_ = v_source_401_;
v_target_396_ = v_target_402_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1___redArg(lean_object* v_data_406_){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v_nbuckets_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_407_ = lean_array_get_size(v_data_406_);
v___x_408_ = lean_unsigned_to_nat(2u);
v_nbuckets_409_ = lean_nat_mul(v___x_407_, v___x_408_);
v___x_410_ = lean_unsigned_to_nat(0u);
v___x_411_ = lean_box(0);
v___x_412_ = lean_mk_array(v_nbuckets_409_, v___x_411_);
v___x_413_ = lean_array_propagate_mark(v_data_406_, v___x_412_);
v___x_414_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2___redArg(v___x_410_, v_data_406_, v___x_413_);
return v___x_414_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__0___redArg(lean_object* v_a_415_, lean_object* v_x_416_){
_start:
{
if (lean_obj_tag(v_x_416_) == 0)
{
uint8_t v___x_417_; 
v___x_417_ = 0;
return v___x_417_;
}
else
{
lean_object* v_key_418_; lean_object* v_tail_419_; uint8_t v___x_420_; 
v_key_418_ = lean_ctor_get(v_x_416_, 0);
v_tail_419_ = lean_ctor_get(v_x_416_, 2);
v___x_420_ = lean_name_eq(v_key_418_, v_a_415_);
if (v___x_420_ == 0)
{
v_x_416_ = v_tail_419_;
goto _start;
}
else
{
return v___x_420_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__0___redArg___boxed(lean_object* v_a_422_, lean_object* v_x_423_){
_start:
{
uint8_t v_res_424_; lean_object* v_r_425_; 
v_res_424_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__0___redArg(v_a_422_, v_x_423_);
lean_dec(v_x_423_);
lean_dec(v_a_422_);
v_r_425_ = lean_box(v_res_424_);
return v_r_425_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__2___redArg(lean_object* v_a_426_, lean_object* v_b_427_, lean_object* v_x_428_){
_start:
{
if (lean_obj_tag(v_x_428_) == 0)
{
lean_dec(v_b_427_);
lean_dec(v_a_426_);
return v_x_428_;
}
else
{
lean_object* v_key_429_; lean_object* v_value_430_; lean_object* v_tail_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_443_; 
v_key_429_ = lean_ctor_get(v_x_428_, 0);
v_value_430_ = lean_ctor_get(v_x_428_, 1);
v_tail_431_ = lean_ctor_get(v_x_428_, 2);
v_isSharedCheck_443_ = !lean_is_exclusive(v_x_428_);
if (v_isSharedCheck_443_ == 0)
{
v___x_433_ = v_x_428_;
v_isShared_434_ = v_isSharedCheck_443_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_tail_431_);
lean_inc(v_value_430_);
lean_inc(v_key_429_);
lean_dec(v_x_428_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_443_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
uint8_t v___x_435_; 
v___x_435_ = lean_name_eq(v_key_429_, v_a_426_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; lean_object* v___x_438_; 
v___x_436_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__2___redArg(v_a_426_, v_b_427_, v_tail_431_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 2, v___x_436_);
v___x_438_ = v___x_433_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_key_429_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v_value_430_);
lean_ctor_set(v_reuseFailAlloc_439_, 2, v___x_436_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
else
{
lean_object* v___x_441_; 
lean_dec(v_value_430_);
lean_dec(v_key_429_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 1, v_b_427_);
lean_ctor_set(v___x_433_, 0, v_a_426_);
v___x_441_ = v___x_433_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_a_426_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v_b_427_);
lean_ctor_set(v_reuseFailAlloc_442_, 2, v_tail_431_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0___redArg(lean_object* v_m_444_, lean_object* v_a_445_, lean_object* v_b_446_){
_start:
{
lean_object* v_size_447_; lean_object* v_buckets_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_494_; 
v_size_447_ = lean_ctor_get(v_m_444_, 0);
v_buckets_448_ = lean_ctor_get(v_m_444_, 1);
v_isSharedCheck_494_ = !lean_is_exclusive(v_m_444_);
if (v_isSharedCheck_494_ == 0)
{
v___x_450_ = v_m_444_;
v_isShared_451_ = v_isSharedCheck_494_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_buckets_448_);
lean_inc(v_size_447_);
lean_dec(v_m_444_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_494_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_452_; uint64_t v___y_454_; 
v___x_452_ = lean_array_get_size(v_buckets_448_);
if (lean_obj_tag(v_a_445_) == 0)
{
uint64_t v___x_492_; 
v___x_492_ = 1723ULL;
v___y_454_ = v___x_492_;
goto v___jp_453_;
}
else
{
uint64_t v_hash_493_; 
v_hash_493_ = lean_ctor_get_uint64(v_a_445_, sizeof(void*)*2);
v___y_454_ = v_hash_493_;
goto v___jp_453_;
}
v___jp_453_:
{
uint64_t v___x_455_; uint64_t v___x_456_; uint64_t v_fold_457_; uint64_t v___x_458_; uint64_t v___x_459_; uint64_t v___x_460_; size_t v___x_461_; size_t v___x_462_; size_t v___x_463_; size_t v___x_464_; size_t v___x_465_; lean_object* v_bkt_466_; uint8_t v___x_467_; 
v___x_455_ = 32ULL;
v___x_456_ = lean_uint64_shift_right(v___y_454_, v___x_455_);
v_fold_457_ = lean_uint64_xor(v___y_454_, v___x_456_);
v___x_458_ = 16ULL;
v___x_459_ = lean_uint64_shift_right(v_fold_457_, v___x_458_);
v___x_460_ = lean_uint64_xor(v_fold_457_, v___x_459_);
v___x_461_ = lean_uint64_to_usize(v___x_460_);
v___x_462_ = lean_usize_of_nat(v___x_452_);
v___x_463_ = ((size_t)1ULL);
v___x_464_ = lean_usize_sub(v___x_462_, v___x_463_);
v___x_465_ = lean_usize_land(v___x_461_, v___x_464_);
v_bkt_466_ = lean_array_uget_borrowed(v_buckets_448_, v___x_465_);
v___x_467_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__0___redArg(v_a_445_, v_bkt_466_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; lean_object* v_size_x27_469_; lean_object* v___x_470_; lean_object* v_buckets_x27_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_468_ = lean_unsigned_to_nat(1u);
v_size_x27_469_ = lean_nat_add(v_size_447_, v___x_468_);
lean_dec(v_size_447_);
lean_inc(v_bkt_466_);
v___x_470_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_470_, 0, v_a_445_);
lean_ctor_set(v___x_470_, 1, v_b_446_);
lean_ctor_set(v___x_470_, 2, v_bkt_466_);
v_buckets_x27_471_ = lean_array_uset(v_buckets_448_, v___x_465_, v___x_470_);
v___x_472_ = lean_unsigned_to_nat(4u);
v___x_473_ = lean_nat_mul(v_size_x27_469_, v___x_472_);
v___x_474_ = lean_unsigned_to_nat(3u);
v___x_475_ = lean_nat_div(v___x_473_, v___x_474_);
lean_dec(v___x_473_);
v___x_476_ = lean_array_get_size(v_buckets_x27_471_);
v___x_477_ = lean_nat_dec_le(v___x_475_, v___x_476_);
lean_dec(v___x_475_);
if (v___x_477_ == 0)
{
lean_object* v_val_478_; lean_object* v___x_480_; 
v_val_478_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1___redArg(v_buckets_x27_471_);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 1, v_val_478_);
lean_ctor_set(v___x_450_, 0, v_size_x27_469_);
v___x_480_ = v___x_450_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_size_x27_469_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v_val_478_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
else
{
lean_object* v___x_483_; 
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 1, v_buckets_x27_471_);
lean_ctor_set(v___x_450_, 0, v_size_x27_469_);
v___x_483_ = v___x_450_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_size_x27_469_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v_buckets_x27_471_);
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
lean_object* v___x_485_; lean_object* v_buckets_x27_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_490_; 
lean_inc(v_bkt_466_);
v___x_485_ = lean_box(0);
v_buckets_x27_486_ = lean_array_uset(v_buckets_448_, v___x_465_, v___x_485_);
v___x_487_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__2___redArg(v_a_445_, v_b_446_, v_bkt_466_);
v___x_488_ = lean_array_uset(v_buckets_x27_486_, v___x_465_, v___x_487_);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 1, v___x_488_);
v___x_490_ = v___x_450_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_size_447_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v___x_488_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerLabelAttr(lean_object* v_attrName_495_, lean_object* v_attrDescr_496_, lean_object* v_ref_497_){
_start:
{
lean_object* v___x_499_; 
lean_inc(v_ref_497_);
v___x_499_ = l_Lean_mkLabelExt(v_ref_497_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_a_500_; lean_object* v___x_501_; 
v_a_500_ = lean_ctor_get(v___x_499_, 0);
lean_inc_n(v_a_500_, 2);
lean_dec_ref_known(v___x_499_, 1);
lean_inc(v_attrName_495_);
v___x_501_ = l_Lean_mkLabelAttr(v_attrName_495_, v_attrDescr_496_, v_a_500_, v_ref_497_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_512_; 
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_512_ == 0)
{
lean_object* v_unused_513_; 
v_unused_513_ = lean_ctor_get(v___x_501_, 0);
lean_dec(v_unused_513_);
v___x_503_ = v___x_501_;
v_isShared_504_ = v_isSharedCheck_512_;
goto v_resetjp_502_;
}
else
{
lean_dec(v___x_501_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_512_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_510_; 
v___x_505_ = l_Lean_labelExtensionMapRef;
v___x_506_ = lean_st_ref_take(v___x_505_);
lean_inc(v_a_500_);
v___x_507_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0___redArg(v___x_506_, v_attrName_495_, v_a_500_);
v___x_508_ = lean_st_ref_put(v___x_505_, v___x_507_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 0, v_a_500_);
v___x_510_ = v___x_503_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_500_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
else
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_521_; 
lean_dec(v_a_500_);
lean_dec(v_attrName_495_);
v_a_514_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_521_ == 0)
{
v___x_516_ = v___x_501_;
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_501_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_519_; 
if (v_isShared_517_ == 0)
{
v___x_519_ = v___x_516_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_a_514_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
}
else
{
lean_dec(v_ref_497_);
lean_dec_ref(v_attrDescr_496_);
lean_dec(v_attrName_495_);
return v___x_499_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerLabelAttr___boxed(lean_object* v_attrName_522_, lean_object* v_attrDescr_523_, lean_object* v_ref_524_, lean_object* v_a_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Lean_registerLabelAttr(v_attrName_522_, v_attrDescr_523_, v_ref_524_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0(lean_object* v_00_u03b2_527_, lean_object* v_m_528_, lean_object* v_a_529_, lean_object* v_b_530_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0___redArg(v_m_528_, v_a_529_, v_b_530_);
return v___x_531_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__0(lean_object* v_00_u03b2_532_, lean_object* v_a_533_, lean_object* v_x_534_){
_start:
{
uint8_t v___x_535_; 
v___x_535_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__0___redArg(v_a_533_, v_x_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_536_, lean_object* v_a_537_, lean_object* v_x_538_){
_start:
{
uint8_t v_res_539_; lean_object* v_r_540_; 
v_res_539_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__0(v_00_u03b2_536_, v_a_537_, v_x_538_);
lean_dec(v_x_538_);
lean_dec(v_a_537_);
v_r_540_ = lean_box(v_res_539_);
return v_r_540_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1(lean_object* v_00_u03b2_541_, lean_object* v_data_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1___redArg(v_data_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__2(lean_object* v_00_u03b2_544_, lean_object* v_a_545_, lean_object* v_b_546_, lean_object* v_x_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__2___redArg(v_a_545_, v_b_546_, v_x_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_549_, lean_object* v_i_550_, lean_object* v_source_551_, lean_object* v_target_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2___redArg(v_i_550_, v_source_551_, v_target_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_554_, lean_object* v_x_555_, lean_object* v_x_556_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_x_555_, v_x_556_);
return v___x_557_;
}
}
static lean_object* _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__13(void){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__12));
v___x_628_ = l_String_toRawSubstring_x27(v___x_627_);
return v___x_628_;
}
}
static lean_object* _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__18(void){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__17));
v___x_639_ = l_String_toRawSubstring_x27(v___x_638_);
return v___x_639_;
}
}
static lean_object* _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__24(void){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__23));
v___x_651_ = l_String_toRawSubstring_x27(v___x_650_);
return v___x_651_;
}
}
static lean_object* _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__38(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = ((lean_object*)(l_Lean_Parser_Command_registerLabelAttr___closed__2));
v___x_688_ = l_String_toRawSubstring_x27(v___x_687_);
return v___x_688_;
}
}
static lean_object* _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__51(void){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_Array_mkArray0___redArg();
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1(lean_object* v_x_726_, lean_object* v_a_727_, lean_object* v_a_728_){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___y_744_; lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v___y_747_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___x_864_; uint8_t v___x_865_; 
v___x_729_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__0));
v___x_730_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__1));
v___x_864_ = ((lean_object*)(l_Lean_Parser_Command_registerLabelAttr___closed__3));
lean_inc(v_x_726_);
v___x_865_ = l_Lean_Syntax_isOfKind(v_x_726_, v___x_864_);
if (v___x_865_ == 0)
{
lean_object* v___x_866_; lean_object* v___x_867_; 
lean_dec(v_x_726_);
v___x_866_ = lean_box(1);
v___x_867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
lean_ctor_set(v___x_867_, 1, v_a_728_);
return v___x_867_;
}
else
{
lean_object* v___x_868_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_872_; uint8_t v___y_873_; lean_object* v___y_874_; lean_object* v___y_875_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v_id_893_; lean_object* v___y_895_; lean_object* v___x_906_; 
v___x_868_ = lean_unsigned_to_nat(0u);
v___x_891_ = l_Lean_Syntax_getArg(v_x_726_, v___x_868_);
v___x_892_ = lean_unsigned_to_nat(2u);
v_id_893_ = l_Lean_Syntax_getArg(v_x_726_, v___x_892_);
lean_dec(v_x_726_);
v___x_906_ = l_Lean_Syntax_getOptional_x3f(v___x_891_);
lean_dec(v___x_891_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v___x_907_; 
v___x_907_ = lean_box(0);
v___y_895_ = v___x_907_;
goto v___jp_894_;
}
else
{
lean_object* v_val_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_915_; 
v_val_908_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_915_ == 0)
{
v___x_910_ = v___x_906_;
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_val_908_);
lean_dec(v___x_906_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_913_; 
if (v_isShared_911_ == 0)
{
v___x_913_ = v___x_910_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_val_908_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
v___y_895_ = v___x_913_;
goto v___jp_894_;
}
}
}
v___jp_869_:
{
lean_object* v_quotContext_876_; lean_object* v_currMacroScope_877_; lean_object* v_ref_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v_quotContext_876_ = lean_ctor_get(v_a_727_, 1);
v_currMacroScope_877_ = lean_ctor_get(v_a_727_, 2);
v_ref_878_ = lean_ctor_get(v_a_727_, 5);
v___x_879_ = l_String_removeLeadingSpaces(v___y_875_);
v___x_880_ = lean_box(2);
v___x_881_ = l_Lean_Syntax_mkStrLit(v___x_879_, v___x_880_);
v___x_882_ = l_Lean_SourceInfo_fromRef(v_ref_878_, v___y_873_);
v___x_883_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__9));
v___x_884_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__47));
v___x_885_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__48));
v___x_886_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__50));
v___x_887_ = lean_obj_once(&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__51, &l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__51_once, _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__51);
if (lean_obj_tag(v___y_870_) == 1)
{
lean_object* v_val_888_; lean_object* v___x_889_; 
v_val_888_ = lean_ctor_get(v___y_870_, 0);
lean_inc(v_val_888_);
lean_dec_ref_known(v___y_870_, 1);
v___x_889_ = l_Array_mkArray1___redArg(v_val_888_);
v___y_803_ = v___x_884_;
v___y_804_ = v_currMacroScope_877_;
v___y_805_ = v___y_872_;
v___y_806_ = v___x_887_;
v___y_807_ = v___x_882_;
v___y_808_ = v___x_883_;
v___y_809_ = v_quotContext_876_;
v___y_810_ = v___y_874_;
v___y_811_ = v___x_880_;
v___y_812_ = v___y_871_;
v___y_813_ = v___x_885_;
v___y_814_ = v___x_881_;
v___y_815_ = v___x_886_;
v___y_816_ = v___x_889_;
goto v___jp_802_;
}
else
{
lean_object* v___x_890_; 
lean_dec(v___y_870_);
v___x_890_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__5));
v___y_803_ = v___x_884_;
v___y_804_ = v_currMacroScope_877_;
v___y_805_ = v___y_872_;
v___y_806_ = v___x_887_;
v___y_807_ = v___x_882_;
v___y_808_ = v___x_883_;
v___y_809_ = v_quotContext_876_;
v___y_810_ = v___y_874_;
v___y_811_ = v___x_880_;
v___y_812_ = v___y_871_;
v___y_813_ = v___x_885_;
v___y_814_ = v___x_881_;
v___y_815_ = v___x_886_;
v___y_816_ = v___x_890_;
goto v___jp_802_;
}
}
v___jp_894_:
{
lean_object* v___x_896_; lean_object* v_str_897_; lean_object* v___x_898_; lean_object* v___x_899_; uint8_t v___x_900_; lean_object* v_idParser_901_; 
v___x_896_ = l_Lean_TSyntax_getId(v_id_893_);
lean_inc_n(v___x_896_, 2);
v_str_897_ = l_Lean_Name_toString(v___x_896_, v___x_865_);
v___x_898_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__53));
v___x_899_ = l_Lean_Name_append(v___x_898_, v___x_896_);
v___x_900_ = 0;
v_idParser_901_ = l_Lean_mkIdentFrom(v_id_893_, v___x_899_, v___x_900_);
lean_dec(v_id_893_);
if (lean_obj_tag(v___y_895_) == 0)
{
lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_902_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__54));
v___x_903_ = lean_string_append(v___x_902_, v_str_897_);
v___y_870_ = v___y_895_;
v___y_871_ = v_str_897_;
v___y_872_ = v_idParser_901_;
v___y_873_ = v___x_900_;
v___y_874_ = v___x_896_;
v___y_875_ = v___x_903_;
goto v___jp_869_;
}
else
{
lean_object* v_val_904_; lean_object* v___x_905_; 
v_val_904_ = lean_ctor_get(v___y_895_, 0);
v___x_905_ = l_Lean_TSyntax_getDocString(v_val_904_);
v___y_870_ = v___y_895_;
v___y_871_ = v_str_897_;
v___y_872_ = v_idParser_901_;
v___y_873_ = v___x_900_;
v___y_874_ = v___x_896_;
v___y_875_ = v___x_905_;
goto v___jp_869_;
}
}
}
v___jp_731_:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
lean_inc(v___y_754_);
lean_inc_n(v___y_740_, 5);
lean_inc_n(v___y_738_, 19);
v___x_755_ = l_Lean_Syntax_node3(v___y_738_, v___y_740_, v___y_754_, v___y_749_, v___y_754_);
lean_inc(v___y_732_);
v___x_756_ = l_Lean_Syntax_node2(v___y_738_, v___y_732_, v___y_752_, v___x_755_);
lean_inc(v___y_736_);
v___x_757_ = l_Lean_Syntax_node1(v___y_738_, v___y_736_, v___x_756_);
lean_inc_n(v___y_750_, 4);
lean_inc(v___y_742_);
v___x_758_ = l_Lean_Syntax_node2(v___y_738_, v___y_742_, v___x_757_, v___y_750_);
v___x_759_ = l_Lean_Syntax_node1(v___y_738_, v___y_740_, v___x_758_);
lean_inc(v___y_751_);
v___x_760_ = l_Lean_Syntax_node1(v___y_738_, v___y_751_, v___x_759_);
lean_inc(v___y_747_);
v___x_761_ = l_Lean_Syntax_node4(v___y_738_, v___y_747_, v___y_743_, v___y_737_, v___y_734_, v___x_760_);
v___x_762_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__0));
v___x_763_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__1));
v___x_764_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__2));
lean_inc_ref(v___y_753_);
v___x_765_ = l_Lean_Name_mkStr4(v___x_729_, v___x_730_, v___y_753_, v___x_764_);
v___x_766_ = l_Lean_Syntax_node1(v___y_738_, v___x_765_, v___y_750_);
v___x_767_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_767_, 0, v___y_738_);
lean_ctor_set(v___x_767_, 1, v___x_762_);
v___x_768_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__4));
v___x_769_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__5));
v___x_770_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_770_, 0, v___y_738_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
v___x_771_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__6));
v___x_772_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_772_, 0, v___y_738_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
v___x_773_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__7));
v___x_774_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_774_, 0, v___y_738_);
lean_ctor_set(v___x_774_, 1, v___x_773_);
v___x_775_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__8));
v___x_776_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_776_, 0, v___y_738_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
v___x_777_ = l_Lean_Syntax_node5(v___y_738_, v___x_768_, v___x_770_, v___x_772_, v___x_774_, v___y_735_, v___x_776_);
v___x_778_ = l_Lean_Syntax_node1(v___y_738_, v___y_740_, v___x_777_);
v___x_779_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__11));
v___x_780_ = l_Lean_Syntax_mkStrLit(v___y_745_, v___y_741_);
v___x_781_ = l_Lean_Syntax_node1(v___y_738_, v___x_779_, v___x_780_);
v___x_782_ = l_Lean_Syntax_node1(v___y_738_, v___y_740_, v___x_781_);
v___x_783_ = lean_obj_once(&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__13, &l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__13_once, _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__13);
v___x_784_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__14));
lean_inc(v___y_733_);
lean_inc(v___y_739_);
v___x_785_ = l_Lean_addMacroScope(v___y_739_, v___x_784_, v___y_733_);
v___x_786_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_786_, 0, v___y_738_);
lean_ctor_set(v___x_786_, 1, v___x_783_);
lean_ctor_set(v___x_786_, 2, v___x_785_);
lean_ctor_set(v___x_786_, 3, v___y_744_);
v___x_787_ = lean_unsigned_to_nat(10u);
v___x_788_ = lean_mk_empty_array_with_capacity(v___x_787_);
v___x_789_ = lean_array_push(v___x_788_, v___y_748_);
v___x_790_ = lean_array_push(v___x_789_, v___y_750_);
v___x_791_ = lean_array_push(v___x_790_, v___x_766_);
v___x_792_ = lean_array_push(v___x_791_, v___x_767_);
v___x_793_ = lean_array_push(v___x_792_, v___y_750_);
v___x_794_ = lean_array_push(v___x_793_, v___x_778_);
v___x_795_ = lean_array_push(v___x_794_, v___y_750_);
v___x_796_ = lean_array_push(v___x_795_, v___x_782_);
v___x_797_ = lean_array_push(v___x_796_, v___y_746_);
v___x_798_ = lean_array_push(v___x_797_, v___x_786_);
v___x_799_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_799_, 0, v___y_738_);
lean_ctor_set(v___x_799_, 1, v___x_763_);
lean_ctor_set(v___x_799_, 2, v___x_798_);
v___x_800_ = l_Lean_Syntax_node2(v___y_738_, v___y_740_, v___x_761_, v___x_799_);
v___x_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
lean_ctor_set(v___x_801_, 1, v_a_728_);
return v___x_801_;
}
v___jp_802_:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
lean_inc_ref_n(v___y_806_, 2);
v___x_817_ = l_Array_append___redArg(v___y_806_, v___y_816_);
lean_dec_ref(v___y_816_);
lean_inc_n(v___y_808_, 3);
lean_inc_n(v___y_807_, 12);
v___x_818_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_818_, 0, v___y_807_);
lean_ctor_set(v___x_818_, 1, v___y_808_);
lean_ctor_set(v___x_818_, 2, v___x_817_);
v___x_819_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_819_, 0, v___y_807_);
lean_ctor_set(v___x_819_, 1, v___y_808_);
lean_ctor_set(v___x_819_, 2, v___y_806_);
lean_inc_ref_n(v___x_819_, 6);
lean_inc_ref(v___x_818_);
lean_inc(v___y_815_);
v___x_820_ = l_Lean_Syntax_node7(v___y_807_, v___y_815_, v___x_818_, v___x_819_, v___x_819_, v___x_819_, v___x_819_, v___x_819_, v___x_819_);
v___x_821_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__16));
lean_inc_ref(v___y_803_);
v___x_822_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_822_, 0, v___y_807_);
lean_ctor_set(v___x_822_, 1, v___y_803_);
v___x_823_ = l_Lean_Syntax_node1(v___y_807_, v___x_821_, v___x_822_);
v___x_824_ = lean_obj_once(&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__18, &l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__18_once, _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__18);
v___x_825_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__19));
lean_inc_n(v___y_804_, 3);
lean_inc_n(v___y_809_, 3);
v___x_826_ = l_Lean_addMacroScope(v___y_809_, v___x_825_, v___y_804_);
v___x_827_ = lean_box(0);
v___x_828_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_828_, 0, v___y_807_);
lean_ctor_set(v___x_828_, 1, v___x_824_);
lean_ctor_set(v___x_828_, 2, v___x_826_);
lean_ctor_set(v___x_828_, 3, v___x_827_);
v___x_829_ = ((lean_object*)(l_Lean_mkLabelExt___auto__1___closed__14));
v___x_830_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__21));
v___x_831_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__22));
v___x_832_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_832_, 0, v___y_807_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = lean_obj_once(&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__24, &l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__24_once, _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__24);
v___x_834_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__26));
v___x_835_ = l_Lean_addMacroScope(v___y_809_, v___x_834_, v___y_804_);
v___x_836_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__28));
v___x_837_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_837_, 0, v___y_807_);
lean_ctor_set(v___x_837_, 1, v___x_833_);
lean_ctor_set(v___x_837_, 2, v___x_835_);
lean_ctor_set(v___x_837_, 3, v___x_836_);
lean_inc_ref(v___x_832_);
v___x_838_ = l_Lean_Syntax_node2(v___y_807_, v___x_830_, v___x_832_, v___x_837_);
v___x_839_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__29));
v___x_840_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_840_, 0, v___y_807_);
lean_ctor_set(v___x_840_, 1, v___x_839_);
v___x_841_ = l_Lean_Syntax_node3(v___y_807_, v___y_808_, v___x_828_, v___x_838_, v___x_840_);
v___x_842_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__31));
v___x_843_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__33));
v___x_844_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__35));
v___x_845_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__37));
v___x_846_ = lean_obj_once(&l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__38, &l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__38_once, _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__38);
v___x_847_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__39));
v___x_848_ = l_Lean_addMacroScope(v___y_809_, v___x_847_, v___y_804_);
v___x_849_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__42));
v___x_850_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_850_, 0, v___y_807_);
lean_ctor_set(v___x_850_, 1, v___x_846_);
lean_ctor_set(v___x_850_, 2, v___x_848_);
lean_ctor_set(v___x_850_, 3, v___x_849_);
lean_inc(v___y_810_);
v___x_851_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_827_, v___y_810_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v___x_852_; 
v___x_852_ = l_Lean_quoteNameMk(v___y_810_);
v___y_732_ = v___x_845_;
v___y_733_ = v___y_804_;
v___y_734_ = v___x_841_;
v___y_735_ = v___y_805_;
v___y_736_ = v___x_844_;
v___y_737_ = v___x_823_;
v___y_738_ = v___y_807_;
v___y_739_ = v___y_809_;
v___y_740_ = v___y_808_;
v___y_741_ = v___y_811_;
v___y_742_ = v___x_843_;
v___y_743_ = v___x_820_;
v___y_744_ = v___x_827_;
v___y_745_ = v___y_812_;
v___y_746_ = v___x_832_;
v___y_747_ = v___y_813_;
v___y_748_ = v___x_818_;
v___y_749_ = v___y_814_;
v___y_750_ = v___x_819_;
v___y_751_ = v___x_842_;
v___y_752_ = v___x_850_;
v___y_753_ = v___x_829_;
v___y_754_ = v___x_852_;
goto v___jp_731_;
}
else
{
lean_object* v_val_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
lean_dec(v___y_810_);
v_val_853_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_val_853_);
lean_dec_ref_known(v___x_851_, 1);
v___x_854_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__44));
v___x_855_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__45));
v___x_856_ = ((lean_object*)(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__46));
v___x_857_ = lean_string_intercalate(v___x_856_, v_val_853_);
v___x_858_ = lean_string_append(v___x_855_, v___x_857_);
lean_dec_ref(v___x_857_);
lean_inc_n(v___y_811_, 2);
v___x_859_ = l_Lean_Syntax_mkNameLit(v___x_858_, v___y_811_);
v___x_860_ = lean_unsigned_to_nat(1u);
v___x_861_ = lean_mk_empty_array_with_capacity(v___x_860_);
v___x_862_ = lean_array_push(v___x_861_, v___x_859_);
v___x_863_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_863_, 0, v___y_811_);
lean_ctor_set(v___x_863_, 1, v___x_854_);
lean_ctor_set(v___x_863_, 2, v___x_862_);
v___y_732_ = v___x_845_;
v___y_733_ = v___y_804_;
v___y_734_ = v___x_841_;
v___y_735_ = v___y_805_;
v___y_736_ = v___x_844_;
v___y_737_ = v___x_823_;
v___y_738_ = v___y_807_;
v___y_739_ = v___y_809_;
v___y_740_ = v___y_808_;
v___y_741_ = v___y_811_;
v___y_742_ = v___x_843_;
v___y_743_ = v___x_820_;
v___y_744_ = v___x_827_;
v___y_745_ = v___y_812_;
v___y_746_ = v___x_832_;
v___y_747_ = v___y_813_;
v___y_748_ = v___x_818_;
v___y_749_ = v___y_814_;
v___y_750_ = v___x_819_;
v___y_751_ = v___x_842_;
v___y_752_ = v___x_850_;
v___y_753_ = v___x_829_;
v___y_754_ = v___x_863_;
goto v___jp_731_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___boxed(lean_object* v_x_916_, lean_object* v_a_917_, lean_object* v_a_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1(v_x_916_, v_a_917_, v_a_918_);
lean_dec_ref(v_a_917_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0___redArg(lean_object* v_a_920_, lean_object* v_x_921_){
_start:
{
if (lean_obj_tag(v_x_921_) == 0)
{
lean_object* v___x_922_; 
v___x_922_ = lean_box(0);
return v___x_922_;
}
else
{
lean_object* v_key_923_; lean_object* v_value_924_; lean_object* v_tail_925_; uint8_t v___x_926_; 
v_key_923_ = lean_ctor_get(v_x_921_, 0);
v_value_924_ = lean_ctor_get(v_x_921_, 1);
v_tail_925_ = lean_ctor_get(v_x_921_, 2);
v___x_926_ = lean_name_eq(v_key_923_, v_a_920_);
if (v___x_926_ == 0)
{
v_x_921_ = v_tail_925_;
goto _start;
}
else
{
lean_object* v___x_928_; 
lean_inc(v_value_924_);
v___x_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_928_, 0, v_value_924_);
return v___x_928_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0___redArg___boxed(lean_object* v_a_929_, lean_object* v_x_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0___redArg(v_a_929_, v_x_930_);
lean_dec(v_x_930_);
lean_dec(v_a_929_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0___redArg(lean_object* v_m_932_, lean_object* v_a_933_){
_start:
{
lean_object* v_buckets_934_; lean_object* v___x_935_; uint64_t v___y_937_; 
v_buckets_934_ = lean_ctor_get(v_m_932_, 1);
v___x_935_ = lean_array_get_size(v_buckets_934_);
if (lean_obj_tag(v_a_933_) == 0)
{
uint64_t v___x_951_; 
v___x_951_ = 1723ULL;
v___y_937_ = v___x_951_;
goto v___jp_936_;
}
else
{
uint64_t v_hash_952_; 
v_hash_952_ = lean_ctor_get_uint64(v_a_933_, sizeof(void*)*2);
v___y_937_ = v_hash_952_;
goto v___jp_936_;
}
v___jp_936_:
{
uint64_t v___x_938_; uint64_t v___x_939_; uint64_t v_fold_940_; uint64_t v___x_941_; uint64_t v___x_942_; uint64_t v___x_943_; size_t v___x_944_; size_t v___x_945_; size_t v___x_946_; size_t v___x_947_; size_t v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_938_ = 32ULL;
v___x_939_ = lean_uint64_shift_right(v___y_937_, v___x_938_);
v_fold_940_ = lean_uint64_xor(v___y_937_, v___x_939_);
v___x_941_ = 16ULL;
v___x_942_ = lean_uint64_shift_right(v_fold_940_, v___x_941_);
v___x_943_ = lean_uint64_xor(v_fold_940_, v___x_942_);
v___x_944_ = lean_uint64_to_usize(v___x_943_);
v___x_945_ = lean_usize_of_nat(v___x_935_);
v___x_946_ = ((size_t)1ULL);
v___x_947_ = lean_usize_sub(v___x_945_, v___x_946_);
v___x_948_ = lean_usize_land(v___x_944_, v___x_947_);
v___x_949_ = lean_array_uget_borrowed(v_buckets_934_, v___x_948_);
v___x_950_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0___redArg(v_a_933_, v___x_949_);
return v___x_950_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0___redArg___boxed(lean_object* v_m_953_, lean_object* v_a_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0___redArg(v_m_953_, v_a_954_);
lean_dec(v_a_954_);
lean_dec_ref(v_m_953_);
return v_res_955_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__0);
v___x_957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
return v___x_957_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_958_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__0);
v___x_959_ = lean_unsigned_to_nat(0u);
v___x_960_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
lean_ctor_set(v___x_960_, 1, v___x_959_);
lean_ctor_set(v___x_960_, 2, v___x_959_);
lean_ctor_set(v___x_960_, 3, v___x_959_);
lean_ctor_set(v___x_960_, 4, v___x_958_);
lean_ctor_set(v___x_960_, 5, v___x_958_);
lean_ctor_set(v___x_960_, 6, v___x_958_);
lean_ctor_set(v___x_960_, 7, v___x_958_);
lean_ctor_set(v___x_960_, 8, v___x_958_);
lean_ctor_set(v___x_960_, 9, v___x_958_);
lean_ctor_set(v___x_960_, 10, v___x_958_);
return v___x_960_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_961_ = lean_unsigned_to_nat(32u);
v___x_962_ = lean_mk_empty_array_with_capacity(v___x_961_);
v___x_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_963_, 0, v___x_962_);
return v___x_963_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__3(void){
_start:
{
size_t v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_964_ = ((size_t)5ULL);
v___x_965_ = lean_unsigned_to_nat(0u);
v___x_966_ = lean_unsigned_to_nat(32u);
v___x_967_ = lean_mk_empty_array_with_capacity(v___x_966_);
v___x_968_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__2);
v___x_969_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_969_, 0, v___x_968_);
lean_ctor_set(v___x_969_, 1, v___x_967_);
lean_ctor_set(v___x_969_, 2, v___x_965_);
lean_ctor_set(v___x_969_, 3, v___x_965_);
lean_ctor_set_usize(v___x_969_, 4, v___x_964_);
return v___x_969_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__4(void){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_970_ = lean_box(1);
v___x_971_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__3);
v___x_972_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__0);
v___x_973_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
lean_ctor_set(v___x_973_, 1, v___x_971_);
lean_ctor_set(v___x_973_, 2, v___x_970_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2(lean_object* v_msgData_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v___x_978_; lean_object* v_toCold_979_; lean_object* v_env_980_; lean_object* v_options_981_; uint8_t v___x_982_; lean_object* v_env_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_978_ = lean_st_ref_get(v___y_976_);
v_toCold_979_ = lean_ctor_get(v___y_975_, 0);
v_env_980_ = lean_ctor_get(v___x_978_, 0);
lean_inc_ref(v_env_980_);
lean_dec(v___x_978_);
v_options_981_ = lean_ctor_get(v_toCold_979_, 2);
v___x_982_ = 0;
v_env_983_ = l_Lean_Environment_setRecordingDeps(v_env_980_, v___x_982_);
v___x_984_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__1);
v___x_985_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__4);
lean_inc_ref(v_options_981_);
v___x_986_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_986_, 0, v_env_983_);
lean_ctor_set(v___x_986_, 1, v___x_984_);
lean_ctor_set(v___x_986_, 2, v___x_985_);
lean_ctor_set(v___x_986_, 3, v_options_981_);
v___x_987_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_986_);
lean_ctor_set(v___x_987_, 1, v_msgData_974_);
v___x_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___boxed(lean_object* v_msgData_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2(v_msgData_989_, v___y_990_, v___y_991_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_labelled_spec__1___redArg(lean_object* v_msg_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v_ref_998_; lean_object* v___x_999_; lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1008_; 
v_ref_998_ = lean_ctor_get(v___y_995_, 2);
v___x_999_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2(v_msg_994_, v___y_995_, v___y_996_);
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1002_ = v___x_999_;
v_isShared_1003_ = v_isSharedCheck_1008_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_999_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1008_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1004_; lean_object* v___x_1006_; 
lean_inc(v_ref_998_);
v___x_1004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1004_, 0, v_ref_998_);
lean_ctor_set(v___x_1004_, 1, v_a_1000_);
if (v_isShared_1003_ == 0)
{
lean_ctor_set_tag(v___x_1002_, 1);
lean_ctor_set(v___x_1002_, 0, v___x_1004_);
v___x_1006_ = v___x_1002_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_1004_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_labelled_spec__1___redArg___boxed(lean_object* v_msg_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_Lean_throwError___at___00Lean_labelled_spec__1___redArg(v_msg_1009_, v___y_1010_, v___y_1011_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
return v_res_1013_;
}
}
static lean_object* _init_l_Lean_labelled___closed__1(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = ((lean_object*)(l_Lean_labelled___closed__0));
v___x_1016_ = l_Lean_stringToMessageData(v___x_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_labelled(lean_object* v_attrName_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1021_ = lean_obj_once(&l_Lean_mkLabelAttr___closed__0, &l_Lean_mkLabelAttr___closed__0_once, _init_l_Lean_mkLabelAttr___closed__0);
v___x_1022_ = l_Lean_labelExtensionMapRef;
v___x_1023_ = lean_st_ref_get(v___x_1022_);
v___x_1024_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0___redArg(v___x_1023_, v_attrName_1017_);
lean_dec(v___x_1023_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1025_ = lean_obj_once(&l_Lean_labelled___closed__1, &l_Lean_labelled___closed__1_once, _init_l_Lean_labelled___closed__1);
v___x_1026_ = l_Lean_MessageData_ofName(v_attrName_1017_);
v___x_1027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1025_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
v___x_1028_ = l_Lean_throwError___at___00Lean_labelled_spec__1___redArg(v___x_1027_, v_a_1018_, v_a_1019_);
return v___x_1028_;
}
else
{
lean_object* v_val_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1043_; 
lean_dec(v_attrName_1017_);
v_val_1029_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1031_ = v___x_1024_;
v_isShared_1032_ = v_isSharedCheck_1043_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_val_1029_);
lean_dec(v___x_1024_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1043_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1033_; lean_object* v_ext_1034_; lean_object* v_toEnvExtension_1035_; lean_object* v_env_1036_; lean_object* v_asyncMode_1037_; uint8_t v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1041_; 
v___x_1033_ = lean_st_ref_get(v_a_1019_);
v_ext_1034_ = lean_ctor_get(v_val_1029_, 1);
v_toEnvExtension_1035_ = lean_ctor_get(v_ext_1034_, 0);
v_env_1036_ = lean_ctor_get(v___x_1033_, 0);
lean_inc_ref(v_env_1036_);
lean_dec(v___x_1033_);
v_asyncMode_1037_ = lean_ctor_get(v_toEnvExtension_1035_, 2);
lean_inc(v_asyncMode_1037_);
v___x_1038_ = 0;
v___x_1039_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1021_, v_val_1029_, v_env_1036_, v_asyncMode_1037_, v___x_1038_);
lean_dec(v_asyncMode_1037_);
lean_dec(v_val_1029_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set_tag(v___x_1031_, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1039_);
v___x_1041_ = v___x_1031_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_labelled___boxed(lean_object* v_attrName_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Lean_labelled(v_attrName_1044_, v_a_1045_, v_a_1046_);
lean_dec(v_a_1046_);
lean_dec_ref(v_a_1045_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0(lean_object* v_00_u03b2_1049_, lean_object* v_m_1050_, lean_object* v_a_1051_){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0___redArg(v_m_1050_, v_a_1051_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0___boxed(lean_object* v_00_u03b2_1053_, lean_object* v_m_1054_, lean_object* v_a_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0(v_00_u03b2_1053_, v_m_1054_, v_a_1055_);
lean_dec(v_a_1055_);
lean_dec_ref(v_m_1054_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_labelled_spec__1(lean_object* v_00_u03b1_1057_, lean_object* v_msg_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Lean_throwError___at___00Lean_labelled_spec__1___redArg(v_msg_1058_, v___y_1059_, v___y_1060_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_labelled_spec__1___boxed(lean_object* v_00_u03b1_1063_, lean_object* v_msg_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_Lean_throwError___at___00Lean_labelled_spec__1(v_00_u03b1_1063_, v_msg_1064_, v___y_1065_, v___y_1066_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0(lean_object* v_00_u03b2_1069_, lean_object* v_a_1070_, lean_object* v_x_1071_){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0___redArg(v_a_1070_, v_x_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1073_, lean_object* v_a_1074_, lean_object* v_x_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0(v_00_u03b2_1073_, v_a_1074_, v_x_1075_);
lean_dec(v_x_1075_);
lean_dec(v_a_1074_);
return v_res_1076_;
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
