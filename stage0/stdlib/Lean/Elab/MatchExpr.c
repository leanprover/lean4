// Lean compiler output
// Module: Lean.Elab.MatchExpr
// Imports: public import Lean.Elab.Term
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
lean_object* l_Lean_TSyntax_getId(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_array_to_list(lean_object*);
uint8_t lean_bool_not(uint8_t);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value;
static const lean_string_object l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value;
static const lean_string_object l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value;
static const lean_string_object l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "matchExprElseAlt"};
static const lean_object* l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__3 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(249, 132, 98, 23, 98, 205, 167, 22)}};
static const lean_object* l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__4 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f(lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__0_value;
static const lean_ctor_object l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1_value_aux_2),((lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "matchExprAlt"};
static const lean_object* l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__0 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(156, 165, 255, 22, 123, 199, 70, 61)}};
static const lean_object* l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__1 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__1_value;
static const lean_string_object l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__2 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__3 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__3_value;
static const lean_string_object l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "matchExprPat"};
static const lean_object* l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__4 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(34, 152, 68, 102, 242, 224, 57, 35)}};
static const lean_object* l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__5 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_toAlt_x3f(lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch___closed__0 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Elab_Term_MatchExpr_shouldSaveActual_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Elab_Term_MatchExpr_shouldSaveActual_spec__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Term_MatchExpr_shouldSaveActual(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_shouldSaveActual___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Elab_Term_MatchExpr_getAltFor_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Elab_Term_MatchExpr_getAltFor_x3f_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getAltFor_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getAltFor_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Elab_Term_MatchExpr_next_spec__0(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Term_MatchExpr_next___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Term_MatchExpr_next___closed__0 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_next___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_next(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_MatchExpr_initK___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "__do_jp"};
static const lean_object* l_Lean_Elab_Term_MatchExpr_initK___closed__0 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_initK___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Term_MatchExpr_initK___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_MatchExpr_initK___closed__1;
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_initK___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_MatchExpr_initK___closed__0_value),LEAN_SCALAR_PTR_LITERAL(186, 121, 241, 59, 37, 189, 140, 219)}};
static const lean_object* l_Lean_Elab_Term_MatchExpr_initK___closed__2 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_initK___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_initK(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_initK___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_MatchExpr_getParams_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_MatchExpr_getParams_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "explicitBinder"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 119, 193, 23, 170, 93, 183, 238)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Expr"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__7;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(237, 218, 74, 184, 29, 214, 185, 80)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__8_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__9_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(84, 208, 74, 211, 93, 83, 88, 82)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__9_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__10_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__9_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__11_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__12_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__10_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__12_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__13_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_MatchExpr_getParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Elab_Term_MatchExpr_getParams___closed__0 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_getParams___closed__0_value;
static const lean_string_object l_Lean_Elab_Term_MatchExpr_getParams___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Unit"};
static const lean_object* l_Lean_Elab_Term_MatchExpr_getParams___closed__1 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_getParams___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Term_MatchExpr_getParams___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_MatchExpr_getParams___closed__2;
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_getParams___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_MatchExpr_getParams___closed__1_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_object* l_Lean_Elab_Term_MatchExpr_getParams___closed__3 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_getParams___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_getParams___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_getParams___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_MatchExpr_getParams___closed__4 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_getParams___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_getParams___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_getParams___closed__3_value)}};
static const lean_object* l_Lean_Elab_Term_MatchExpr_getParams___closed__5 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_getParams___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_getParams___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_getParams___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_MatchExpr_getParams___closed__6 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_getParams___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_getParams___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_getParams___closed__4_value),((lean_object*)&l_Lean_Elab_Term_MatchExpr_getParams___closed__6_value)}};
static const lean_object* l_Lean_Elab_Term_MatchExpr_getParams___closed__7 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_getParams___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getParams(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getParams___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_MatchExpr_getActuals___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "tuple"};
static const lean_object* l_Lean_Elab_Term_MatchExpr_getActuals___closed__0 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_getActuals___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_getActuals___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_getActuals___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_getActuals___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__0_value),LEAN_SCALAR_PTR_LITERAL(191, 24, 88, 245, 200, 250, 27, 217)}};
static const lean_object* l_Lean_Elab_Term_MatchExpr_getActuals___closed__1 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__1_value;
static const lean_string_object l_Lean_Elab_Term_MatchExpr_getActuals___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Lean_Elab_Term_MatchExpr_getActuals___closed__2 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_getActuals___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_getActuals___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_getActuals___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_getActuals___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__2_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_Lean_Elab_Term_MatchExpr_getActuals___closed__3 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__3_value;
static const lean_string_object l_Lean_Elab_Term_MatchExpr_getActuals___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Lean_Elab_Term_MatchExpr_getActuals___closed__4 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_getActuals___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__4_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Lean_Elab_Term_MatchExpr_getActuals___closed__5 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__5_value;
static const lean_string_object l_Lean_Elab_Term_MatchExpr_getActuals___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Elab_Term_MatchExpr_getActuals___closed__6 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Term_MatchExpr_getActuals___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_MatchExpr_getActuals___closed__7;
static const lean_string_object l_Lean_Elab_Term_MatchExpr_getActuals___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Term_MatchExpr_getActuals___closed__8 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__8_value;
static const lean_string_object l_Lean_Elab_Term_MatchExpr_getActuals___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "MatchExpr"};
static const lean_object* l_Lean_Elab_Term_MatchExpr_getActuals___closed__9 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_getActuals___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_getActuals___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__10_value_aux_0),((lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__8_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_getActuals___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__10_value_aux_1),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_getActuals___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__10_value_aux_2),((lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__9_value),LEAN_SCALAR_PTR_LITERAL(19, 93, 49, 96, 250, 188, 70, 43)}};
static const lean_object* l_Lean_Elab_Term_MatchExpr_getActuals___closed__10 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_getActuals___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__10_value)}};
static const lean_object* l_Lean_Elab_Term_MatchExpr_getActuals___closed__11 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_getActuals___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_getActuals___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__12_value_aux_0),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_getActuals___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__12_value_aux_1),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_object* l_Lean_Elab_Term_MatchExpr_getActuals___closed__12 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_getActuals___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__12_value)}};
static const lean_object* l_Lean_Elab_Term_MatchExpr_getActuals___closed__13 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_getActuals___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_getActuals___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__14_value_aux_0),((lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__8_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_getActuals___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__14_value_aux_1),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_object* l_Lean_Elab_Term_MatchExpr_getActuals___closed__14 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_getActuals___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__14_value)}};
static const lean_object* l_Lean_Elab_Term_MatchExpr_getActuals___closed__15 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_getActuals___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_getActuals___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__16_value_aux_0),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_object* l_Lean_Elab_Term_MatchExpr_getActuals___closed__16 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__16_value;
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_getActuals___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__16_value)}};
static const lean_object* l_Lean_Elab_Term_MatchExpr_getActuals___closed__17 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__17_value;
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_getActuals___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__17_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_MatchExpr_getActuals___closed__18 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__18_value;
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_getActuals___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__15_value),((lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__18_value)}};
static const lean_object* l_Lean_Elab_Term_MatchExpr_getActuals___closed__19 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__19_value;
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_getActuals___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__13_value),((lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__19_value)}};
static const lean_object* l_Lean_Elab_Term_MatchExpr_getActuals___closed__20 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__20_value;
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_getActuals___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__11_value),((lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__20_value)}};
static const lean_object* l_Lean_Elab_Term_MatchExpr_getActuals___closed__21 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__21_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getActuals(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getActuals___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "doubleQuotedName"};
static const lean_object* l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__0 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(194, 121, 78, 150, 98, 156, 35, 157)}};
static const lean_object* l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__1 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__1_value;
static const lean_string_object l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__2 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__3;
static lean_once_cell_t l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__4;
static lean_once_cell_t l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___lam__0(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "if"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__1_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2_value_aux_2),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__3_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__4_value_aux_2),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 149, 207, 196, 17, 4, 77, 74)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__4 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__4_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__5 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__5_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__6_value_aux_2),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__6 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__6_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__7 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__7_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "isConstOf"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__8 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__8_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__9;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(27, 40, 205, 144, 248, 209, 112, 151)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__10 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__10_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "termIfThenElse"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__11 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__11_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(225, 209, 193, 165, 165, 31, 104, 198)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__12 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__12_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "then"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__13 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__13_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "else"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__14 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__14_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "__discr"};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__0 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__1;
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 107, 223, 4, 107, 76, 58, 232)}};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__2 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__2_value;
static const lean_string_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "termDepIfThenElse"};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__3 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 94, 17, 11, 145, 108, 236, 173)}};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__4 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__4_value;
static const lean_string_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "binderIdent"};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__5 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__5_value),LEAN_SCALAR_PTR_LITERAL(37, 194, 68, 106, 254, 181, 31, 191)}};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__6 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__6_value;
static const lean_string_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__7 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__8;
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__7_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__9 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__9_value;
static const lean_string_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "isApp"};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__10 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__10_value;
static lean_once_cell_t l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__11;
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__10_value),LEAN_SCALAR_PTR_LITERAL(106, 177, 134, 72, 179, 173, 226, 211)}};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__12 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__12_value;
static const lean_string_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "let"};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__13 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__14_value_aux_0),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__14_value_aux_1),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__14_value_aux_2),((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__13_value),LEAN_SCALAR_PTR_LITERAL(155, 166, 195, 152, 24, 103, 8, 2)}};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__14 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__14_value;
static const lean_string_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letConfig"};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__15 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__16_value_aux_0),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__16_value_aux_1),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__16_value_aux_2),((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__15_value),LEAN_SCALAR_PTR_LITERAL(5, 186, 227, 151, 19, 40, 136, 241)}};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__16 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__16_value;
static const lean_string_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letDecl"};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__17 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__17_value;
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18_value_aux_0),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18_value_aux_1),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18_value_aux_2),((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__17_value),LEAN_SCALAR_PTR_LITERAL(61, 47, 121, 206, 37, 68, 134, 111)}};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18_value;
static const lean_string_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letIdDecl"};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__19 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__19_value;
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20_value_aux_0),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20_value_aux_1),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20_value_aux_2),((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__19_value),LEAN_SCALAR_PTR_LITERAL(82, 96, 243, 36, 251, 209, 136, 237)}};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20_value;
static const lean_string_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "letId"};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__21 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__21_value;
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22_value_aux_0),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22_value_aux_1),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22_value_aux_2),((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__21_value),LEAN_SCALAR_PTR_LITERAL(67, 92, 92, 51, 38, 250, 60, 190)}};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22_value;
static const lean_string_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__23 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__23_value;
static const lean_string_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Expr.appFnCleanup"};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__24 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__24_value;
static lean_once_cell_t l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__25;
static const lean_string_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "appFnCleanup"};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__26 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__26_value;
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(237, 218, 74, 184, 29, 214, 185, 80)}};
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__27_value_aux_0),((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__26_value),LEAN_SCALAR_PTR_LITERAL(123, 55, 75, 50, 107, 106, 52, 36)}};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__27 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__27_value;
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__28_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(84, 208, 74, 211, 93, 83, 88, 82)}};
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__28_value_aux_1),((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__26_value),LEAN_SCALAR_PTR_LITERAL(174, 132, 215, 81, 209, 85, 130, 115)}};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__28 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__28_value;
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__28_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__29 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__29_value;
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__29_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__30 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__30_value;
static const lean_string_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__31 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__31_value;
static const lean_string_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__32 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__32_value;
static lean_once_cell_t l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__33;
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__32_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__34 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__34_value;
static const lean_string_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Expr.appArg"};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__35 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__35_value;
static lean_once_cell_t l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__36;
static const lean_string_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "appArg"};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__37 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__37_value;
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(237, 218, 74, 184, 29, 214, 185, 80)}};
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__38_value_aux_0),((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__37_value),LEAN_SCALAR_PTR_LITERAL(143, 39, 209, 64, 239, 249, 76, 198)}};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__38 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__38_value;
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__39_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(84, 208, 74, 211, 93, 83, 88, 82)}};
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__39_value_aux_1),((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__37_value),LEAN_SCALAR_PTR_LITERAL(114, 135, 152, 65, 17, 31, 173, 106)}};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__39 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__39_value;
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__39_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__40 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__40_value;
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__39_value)}};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__41 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__41_value;
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__41_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__42 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__42_value;
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__40_value),((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__42_value)}};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__43 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__43_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_generate___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_generate___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "let_delayed"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__1_value_aux_2),((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 71, 139, 72, 47, 176, 139, 254)}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_generate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_getParams___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_MatchExpr_generate___closed__0 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_generate___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_generate___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_getParams___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_MatchExpr_generate___closed__1 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_generate___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_generate___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_generate___closed__0_value),((lean_object*)&l_Lean_Elab_Term_MatchExpr_generate___closed__1_value)}};
static const lean_object* l_Lean_Elab_Term_MatchExpr_generate___closed__2 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_generate___closed__2_value;
static const lean_string_object l_Lean_Elab_Term_MatchExpr_generate___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Expr.cleanupAnnotations"};
static const lean_object* l_Lean_Elab_Term_MatchExpr_generate___closed__3 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_generate___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Term_MatchExpr_generate___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_MatchExpr_generate___closed__4;
static const lean_string_object l_Lean_Elab_Term_MatchExpr_generate___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "cleanupAnnotations"};
static const lean_object* l_Lean_Elab_Term_MatchExpr_generate___closed__5 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_generate___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_generate___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(237, 218, 74, 184, 29, 214, 185, 80)}};
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_generate___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_generate___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Term_MatchExpr_generate___closed__5_value),LEAN_SCALAR_PTR_LITERAL(8, 214, 177, 247, 224, 185, 177, 113)}};
static const lean_object* l_Lean_Elab_Term_MatchExpr_generate___closed__6 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_generate___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_generate___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_generate___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_generate___closed__7_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(84, 208, 74, 211, 93, 83, 88, 82)}};
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_generate___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_generate___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Term_MatchExpr_generate___closed__5_value),LEAN_SCALAR_PTR_LITERAL(37, 61, 193, 84, 254, 95, 16, 56)}};
static const lean_object* l_Lean_Elab_Term_MatchExpr_generate___closed__7 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_generate___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_generate___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_generate___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_MatchExpr_generate___closed__8 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_generate___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Term_MatchExpr_generate___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_MatchExpr_generate___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_MatchExpr_generate___closed__9 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_generate___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_generate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_generate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_main_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "unexpected `match_expr` alternative"};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_main_spec__0___closed__0 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_main_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_main_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_main_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_MatchExpr_main___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "unexpected `match_expr` else-alternative"};
static const lean_object* l_Lean_Elab_Term_MatchExpr_main___closed__0 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_main___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_expandMatchExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchExpr"};
static const lean_object* l_Lean_Elab_Term_expandMatchExpr___closed__0 = (const lean_object*)&l_Lean_Elab_Term_expandMatchExpr___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_expandMatchExpr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_expandMatchExpr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandMatchExpr___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_expandMatchExpr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandMatchExpr___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_expandMatchExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandMatchExpr___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_expandMatchExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(72, 125, 75, 13, 242, 250, 162, 88)}};
static const lean_object* l_Lean_Elab_Term_expandMatchExpr___closed__1 = (const lean_object*)&l_Lean_Elab_Term_expandMatchExpr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchExpr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchExpr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "expandMatchExpr"};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__8_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(36, 0, 221, 127, 140, 97, 148, 247)}};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(203) << 1) | 1)),((lean_object*)(((size_t)(44) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(207) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__0_value),((lean_object*)(((size_t)(44) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(203) << 1) | 1)),((lean_object*)(((size_t)(48) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(203) << 1) | 1)),((lean_object*)(((size_t)(63) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__3_value),((lean_object*)(((size_t)(48) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__4_value),((lean_object*)(((size_t)(63) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Term_expandLetExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letExpr"};
static const lean_object* l_Lean_Elab_Term_expandLetExpr___closed__0 = (const lean_object*)&l_Lean_Elab_Term_expandLetExpr___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_expandLetExpr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_expandLetExpr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandLetExpr___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_expandLetExpr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandLetExpr___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_expandLetExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandLetExpr___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_expandLetExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(234, 202, 86, 214, 6, 188, 214, 137)}};
static const lean_object* l_Lean_Elab_Term_expandLetExpr___closed__1 = (const lean_object*)&l_Lean_Elab_Term_expandLetExpr___closed__1_value;
static const lean_string_object l_Lean_Elab_Term_expandLetExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "match_expr"};
static const lean_object* l_Lean_Elab_Term_expandLetExpr___closed__2 = (const lean_object*)&l_Lean_Elab_Term_expandLetExpr___closed__2_value;
static const lean_string_object l_Lean_Elab_Term_expandLetExpr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l_Lean_Elab_Term_expandLetExpr___closed__3 = (const lean_object*)&l_Lean_Elab_Term_expandLetExpr___closed__3_value;
static const lean_string_object l_Lean_Elab_Term_expandLetExpr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "matchExprAlts"};
static const lean_object* l_Lean_Elab_Term_expandLetExpr___closed__4 = (const lean_object*)&l_Lean_Elab_Term_expandLetExpr___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Term_expandLetExpr___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_expandLetExpr___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandLetExpr___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_expandLetExpr___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandLetExpr___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_expandLetExpr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandLetExpr___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Term_expandLetExpr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(88, 158, 245, 158, 91, 207, 89, 187)}};
static const lean_object* l_Lean_Elab_Term_expandLetExpr___closed__5 = (const lean_object*)&l_Lean_Elab_Term_expandLetExpr___closed__5_value;
static const lean_string_object l_Lean_Elab_Term_expandLetExpr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l_Lean_Elab_Term_expandLetExpr___closed__6 = (const lean_object*)&l_Lean_Elab_Term_expandLetExpr___closed__6_value;
static const lean_string_object l_Lean_Elab_Term_expandLetExpr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_Lean_Elab_Term_expandLetExpr___closed__7 = (const lean_object*)&l_Lean_Elab_Term_expandLetExpr___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandLetExpr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandLetExpr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expandLetExpr"};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__8_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(146, 223, 197, 206, 64, 44, 35, 96)}};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(209) << 1) | 1)),((lean_object*)(((size_t)(42) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(215) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__0_value),((lean_object*)(((size_t)(42) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(209) << 1) | 1)),((lean_object*)(((size_t)(46) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(209) << 1) | 1)),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__3_value),((lean_object*)(((size_t)(46) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__4_value),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f(lean_object* v_stx_10_){
_start:
{
lean_object* v___x_11_; uint8_t v___x_12_; uint8_t v___x_13_; 
v___x_11_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__4));
lean_inc(v_stx_10_);
v___x_12_ = l_Lean_Syntax_isOfKind(v_stx_10_, v___x_11_);
v___x_13_ = lean_bool_not(v___x_12_);
if (v___x_13_ == 0)
{
lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_14_ = lean_unsigned_to_nat(3u);
v___x_15_ = l_Lean_Syntax_getArg(v_stx_10_, v___x_14_);
lean_dec(v_stx_10_);
v___x_16_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
return v___x_16_;
}
else
{
lean_object* v___x_17_; 
lean_dec(v_stx_10_);
v___x_17_ = lean_box(0);
return v___x_17_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0(lean_object* v_a_24_, lean_object* v_a_25_){
_start:
{
if (lean_obj_tag(v_a_24_) == 0)
{
lean_object* v___x_26_; 
v___x_26_ = l_List_reverse___redArg(v_a_25_);
return v___x_26_;
}
else
{
lean_object* v_head_27_; lean_object* v_tail_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_42_; 
v_head_27_ = lean_ctor_get(v_a_24_, 0);
v_tail_28_ = lean_ctor_get(v_a_24_, 1);
v_isSharedCheck_42_ = !lean_is_exclusive(v_a_24_);
if (v_isSharedCheck_42_ == 0)
{
v___x_30_ = v_a_24_;
v_isShared_31_ = v_isSharedCheck_42_;
goto v_resetjp_29_;
}
else
{
lean_inc(v_tail_28_);
lean_inc(v_head_27_);
lean_dec(v_a_24_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_42_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
lean_object* v___y_33_; lean_object* v___x_38_; uint8_t v___x_39_; 
v___x_38_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1));
lean_inc(v_head_27_);
v___x_39_ = l_Lean_Syntax_isOfKind(v_head_27_, v___x_38_);
if (v___x_39_ == 0)
{
lean_object* v___x_40_; 
v___x_40_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_40_, 0, v_head_27_);
v___y_33_ = v___x_40_;
goto v___jp_32_;
}
else
{
lean_object* v___x_41_; 
lean_dec(v_head_27_);
v___x_41_ = lean_box(0);
v___y_33_ = v___x_41_;
goto v___jp_32_;
}
v___jp_32_:
{
lean_object* v___x_35_; 
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 1, v_a_25_);
lean_ctor_set(v___x_30_, 0, v___y_33_);
v___x_35_ = v___x_30_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v___y_33_);
lean_ctor_set(v_reuseFailAlloc_37_, 1, v_a_25_);
v___x_35_ = v_reuseFailAlloc_37_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
v_a_24_ = v_tail_28_;
v_a_25_ = v___x_35_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_toAlt_x3f(lean_object* v_stx_58_){
_start:
{
lean_object* v___x_59_; uint8_t v___x_60_; uint8_t v___x_61_; 
v___x_59_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__1));
lean_inc(v_stx_58_);
v___x_60_ = l_Lean_Syntax_isOfKind(v_stx_58_, v___x_59_);
v___x_61_ = lean_bool_not(v___x_60_);
if (v___x_61_ == 0)
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v_var_x3f_65_; lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_62_ = lean_unsigned_to_nat(1u);
v___x_63_ = l_Lean_Syntax_getArg(v_stx_58_, v___x_62_);
v___x_82_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__5));
lean_inc(v___x_63_);
v___x_83_ = l_Lean_Syntax_isOfKind(v___x_63_, v___x_82_);
if (v___x_83_ == 0)
{
lean_object* v___x_84_; 
lean_dec(v___x_63_);
lean_dec(v_stx_58_);
v___x_84_ = lean_box(0);
return v___x_84_;
}
else
{
lean_object* v___x_85_; lean_object* v___x_86_; uint8_t v___x_87_; 
v___x_85_ = lean_unsigned_to_nat(0u);
v___x_86_ = l_Lean_Syntax_getArg(v___x_63_, v___x_85_);
v___x_87_ = l_Lean_Syntax_isNone(v___x_86_);
if (v___x_87_ == 0)
{
lean_object* v___x_88_; uint8_t v___x_89_; 
v___x_88_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_86_);
v___x_89_ = l_Lean_Syntax_matchesNull(v___x_86_, v___x_88_);
if (v___x_89_ == 0)
{
lean_object* v___x_90_; 
lean_dec(v___x_86_);
lean_dec(v___x_63_);
lean_dec(v_stx_58_);
v___x_90_ = lean_box(0);
return v___x_90_;
}
else
{
lean_object* v_var_x3f_91_; lean_object* v___x_92_; 
v_var_x3f_91_ = l_Lean_Syntax_getArg(v___x_86_, v___x_85_);
lean_dec(v___x_86_);
v___x_92_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_92_, 0, v_var_x3f_91_);
v_var_x3f_65_ = v___x_92_;
goto v___jp_64_;
}
}
else
{
lean_object* v___x_93_; 
lean_dec(v___x_86_);
v___x_93_ = lean_box(0);
v_var_x3f_65_ = v___x_93_;
goto v___jp_64_;
}
}
v___jp_64_:
{
lean_object* v_funName_66_; lean_object* v___x_67_; uint8_t v___x_68_; 
v_funName_66_ = l_Lean_Syntax_getArg(v___x_63_, v___x_62_);
v___x_67_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__3));
lean_inc(v_funName_66_);
v___x_68_ = l_Lean_Syntax_isOfKind(v_funName_66_, v___x_67_);
if (v___x_68_ == 0)
{
lean_object* v___x_69_; 
lean_dec(v_funName_66_);
lean_dec(v_var_x3f_65_);
lean_dec(v___x_63_);
lean_dec(v_stx_58_);
v___x_69_ = lean_box(0);
return v___x_69_;
}
else
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v_pvars_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v_pvars_76_; lean_object* v___x_77_; lean_object* v_rhs_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_70_ = lean_unsigned_to_nat(2u);
v___x_71_ = l_Lean_Syntax_getArg(v___x_63_, v___x_70_);
lean_dec(v___x_63_);
v_pvars_72_ = l_Lean_Syntax_getArgs(v___x_71_);
lean_dec(v___x_71_);
v___x_73_ = lean_array_to_list(v_pvars_72_);
v___x_74_ = l_List_reverse___redArg(v___x_73_);
v___x_75_ = lean_box(0);
v_pvars_76_ = l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0(v___x_74_, v___x_75_);
v___x_77_ = lean_unsigned_to_nat(3u);
v_rhs_78_ = l_Lean_Syntax_getArg(v_stx_58_, v___x_77_);
lean_dec(v_stx_58_);
v___x_79_ = lean_box(0);
v___x_80_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_80_, 0, v_var_x3f_65_);
lean_ctor_set(v___x_80_, 1, v_funName_66_);
lean_ctor_set(v___x_80_, 2, v_pvars_76_);
lean_ctor_set(v___x_80_, 3, v_rhs_78_);
lean_ctor_set(v___x_80_, 4, v___x_79_);
lean_ctor_set(v___x_80_, 5, v___x_75_);
v___x_81_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
return v___x_81_;
}
}
}
else
{
lean_object* v___x_94_; 
lean_dec(v_stx_58_);
v___x_94_ = lean_box(0);
return v___x_94_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0(lean_object* v_a_98_, lean_object* v_as_99_, size_t v_sz_100_, size_t v_i_101_, lean_object* v_b_102_){
_start:
{
uint8_t v___x_103_; 
v___x_103_ = lean_usize_dec_lt(v_i_101_, v_sz_100_);
if (v___x_103_ == 0)
{
lean_inc_ref(v_b_102_);
return v_b_102_;
}
else
{
lean_object* v_funName_104_; lean_object* v___x_105_; lean_object* v_a_106_; lean_object* v___x_107_; lean_object* v___x_108_; uint8_t v___x_109_; 
v_funName_104_ = lean_ctor_get(v_a_98_, 1);
v___x_105_ = lean_box(0);
v_a_106_ = lean_array_uget_borrowed(v_as_99_, v_i_101_);
v___x_107_ = l_Lean_TSyntax_getId(v_a_106_);
v___x_108_ = l_Lean_TSyntax_getId(v_funName_104_);
v___x_109_ = lean_name_eq(v___x_107_, v___x_108_);
lean_dec(v___x_108_);
lean_dec(v___x_107_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; size_t v___x_111_; size_t v___x_112_; 
v___x_110_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0___closed__0));
v___x_111_ = ((size_t)1ULL);
v___x_112_ = lean_usize_add(v_i_101_, v___x_111_);
v_i_101_ = v___x_112_;
v_b_102_ = v___x_110_;
goto _start;
}
else
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
lean_inc(v_a_106_);
v___x_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_114_, 0, v_a_106_);
v___x_115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
v___x_116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
lean_ctor_set(v___x_116_, 1, v___x_105_);
return v___x_116_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0___boxed(lean_object* v_a_117_, lean_object* v_as_118_, lean_object* v_sz_119_, lean_object* v_i_120_, lean_object* v_b_121_){
_start:
{
size_t v_sz_boxed_122_; size_t v_i_boxed_123_; lean_object* v_res_124_; 
v_sz_boxed_122_ = lean_unbox_usize(v_sz_119_);
lean_dec(v_sz_119_);
v_i_boxed_123_ = lean_unbox_usize(v_i_120_);
lean_dec(v_i_120_);
v_res_124_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0(v_a_117_, v_as_118_, v_sz_boxed_122_, v_i_boxed_123_, v_b_121_);
lean_dec_ref(v_b_121_);
lean_dec_ref(v_as_118_);
lean_dec_ref(v_a_117_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1___redArg(lean_object* v_as_x27_125_, lean_object* v_b_126_){
_start:
{
if (lean_obj_tag(v_as_x27_125_) == 0)
{
return v_b_126_;
}
else
{
lean_object* v_head_127_; lean_object* v_tail_128_; lean_object* v_funName_129_; lean_object* v_pvars_130_; uint8_t v___x_131_; 
v_head_127_ = lean_ctor_get(v_as_x27_125_, 0);
v_tail_128_ = lean_ctor_get(v_as_x27_125_, 1);
v_funName_129_ = lean_ctor_get(v_head_127_, 1);
v_pvars_130_ = lean_ctor_get(v_head_127_, 2);
v___x_131_ = l_List_isEmpty___redArg(v_pvars_130_);
if (v___x_131_ == 0)
{
v_as_x27_125_ = v_tail_128_;
goto _start;
}
else
{
lean_object* v___x_137_; size_t v_sz_138_; size_t v___x_139_; lean_object* v___x_140_; lean_object* v_fst_141_; 
v___x_137_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0___closed__0));
v_sz_138_ = lean_array_size(v_b_126_);
v___x_139_ = ((size_t)0ULL);
v___x_140_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0(v_head_127_, v_b_126_, v_sz_138_, v___x_139_, v___x_137_);
v_fst_141_ = lean_ctor_get(v___x_140_, 0);
lean_inc(v_fst_141_);
lean_dec_ref(v___x_140_);
if (lean_obj_tag(v_fst_141_) == 0)
{
goto v___jp_132_;
}
else
{
lean_object* v_val_142_; 
v_val_142_ = lean_ctor_get(v_fst_141_, 0);
lean_inc(v_val_142_);
lean_dec_ref_known(v_fst_141_, 1);
if (lean_obj_tag(v_val_142_) == 0)
{
goto v___jp_132_;
}
else
{
lean_dec_ref_known(v_val_142_, 1);
v_as_x27_125_ = v_tail_128_;
goto _start;
}
}
}
v___jp_132_:
{
if (v___x_131_ == 0)
{
v_as_x27_125_ = v_tail_128_;
goto _start;
}
else
{
lean_object* v___x_134_; 
lean_inc(v_funName_129_);
v___x_134_ = lean_array_push(v_b_126_, v_funName_129_);
v_as_x27_125_ = v_tail_128_;
v_b_126_ = v___x_134_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1___redArg___boxed(lean_object* v_as_x27_144_, lean_object* v_b_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1___redArg(v_as_x27_144_, v_b_145_);
lean_dec(v_as_x27_144_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch(lean_object* v_alts_149_){
_start:
{
lean_object* v_funNames_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v_funNames_150_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch___closed__0));
v___x_151_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1___redArg(v_alts_149_, v_funNames_150_);
v___x_152_ = lean_array_to_list(v___x_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch___boxed(lean_object* v_alts_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch(v_alts_153_);
lean_dec(v_alts_153_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1(lean_object* v_as_155_, lean_object* v_as_x27_156_, lean_object* v_b_157_, lean_object* v_a_158_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1___redArg(v_as_x27_156_, v_b_157_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1___boxed(lean_object* v_as_160_, lean_object* v_as_x27_161_, lean_object* v_b_162_, lean_object* v_a_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1(v_as_160_, v_as_x27_161_, v_b_162_, v_a_163_);
lean_dec(v_as_x27_161_);
lean_dec(v_as_160_);
return v_res_164_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Elab_Term_MatchExpr_shouldSaveActual_spec__0(lean_object* v_x_165_){
_start:
{
if (lean_obj_tag(v_x_165_) == 0)
{
uint8_t v___x_166_; 
v___x_166_ = 0;
return v___x_166_;
}
else
{
lean_object* v_head_167_; lean_object* v_pvars_168_; 
v_head_167_ = lean_ctor_get(v_x_165_, 0);
v_pvars_168_ = lean_ctor_get(v_head_167_, 2);
if (lean_obj_tag(v_pvars_168_) == 1)
{
lean_object* v_head_169_; 
v_head_169_ = lean_ctor_get(v_pvars_168_, 0);
if (lean_obj_tag(v_head_169_) == 1)
{
uint8_t v___x_170_; 
v___x_170_ = 1;
return v___x_170_;
}
else
{
lean_object* v_tail_171_; 
v_tail_171_ = lean_ctor_get(v_x_165_, 1);
v_x_165_ = v_tail_171_;
goto _start;
}
}
else
{
lean_object* v_tail_173_; 
v_tail_173_ = lean_ctor_get(v_x_165_, 1);
v_x_165_ = v_tail_173_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Elab_Term_MatchExpr_shouldSaveActual_spec__0___boxed(lean_object* v_x_175_){
_start:
{
uint8_t v_res_176_; lean_object* v_r_177_; 
v_res_176_ = l_List_any___at___00Lean_Elab_Term_MatchExpr_shouldSaveActual_spec__0(v_x_175_);
lean_dec(v_x_175_);
v_r_177_ = lean_box(v_res_176_);
return v_r_177_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_MatchExpr_shouldSaveActual(lean_object* v_alts_178_){
_start:
{
uint8_t v___x_179_; 
v___x_179_ = l_List_any___at___00Lean_Elab_Term_MatchExpr_shouldSaveActual_spec__0(v_alts_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_shouldSaveActual___boxed(lean_object* v_alts_180_){
_start:
{
uint8_t v_res_181_; lean_object* v_r_182_; 
v_res_181_ = l_Lean_Elab_Term_MatchExpr_shouldSaveActual(v_alts_180_);
lean_dec(v_alts_180_);
v_r_182_ = lean_box(v_res_181_);
return v_r_182_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Elab_Term_MatchExpr_getAltFor_x3f_spec__0(lean_object* v_funName_183_, lean_object* v_x_184_){
_start:
{
if (lean_obj_tag(v_x_184_) == 0)
{
lean_object* v___x_185_; 
v___x_185_ = lean_box(0);
return v___x_185_;
}
else
{
lean_object* v_head_186_; lean_object* v_tail_187_; uint8_t v___y_189_; lean_object* v_funName_192_; lean_object* v_pvars_193_; lean_object* v___x_194_; lean_object* v___x_195_; uint8_t v___x_196_; 
v_head_186_ = lean_ctor_get(v_x_184_, 0);
v_tail_187_ = lean_ctor_get(v_x_184_, 1);
v_funName_192_ = lean_ctor_get(v_head_186_, 1);
v_pvars_193_ = lean_ctor_get(v_head_186_, 2);
v___x_194_ = l_Lean_TSyntax_getId(v_funName_192_);
v___x_195_ = l_Lean_TSyntax_getId(v_funName_183_);
v___x_196_ = lean_name_eq(v___x_194_, v___x_195_);
lean_dec(v___x_195_);
lean_dec(v___x_194_);
if (v___x_196_ == 0)
{
v___y_189_ = v___x_196_;
goto v___jp_188_;
}
else
{
uint8_t v___x_197_; 
v___x_197_ = l_List_isEmpty___redArg(v_pvars_193_);
v___y_189_ = v___x_197_;
goto v___jp_188_;
}
v___jp_188_:
{
if (v___y_189_ == 0)
{
v_x_184_ = v_tail_187_;
goto _start;
}
else
{
lean_object* v___x_191_; 
lean_inc(v_head_186_);
v___x_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_191_, 0, v_head_186_);
return v___x_191_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Elab_Term_MatchExpr_getAltFor_x3f_spec__0___boxed(lean_object* v_funName_198_, lean_object* v_x_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_List_find_x3f___at___00Lean_Elab_Term_MatchExpr_getAltFor_x3f_spec__0(v_funName_198_, v_x_199_);
lean_dec(v_x_199_);
lean_dec(v_funName_198_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getAltFor_x3f(lean_object* v_alts_201_, lean_object* v_funName_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_List_find_x3f___at___00Lean_Elab_Term_MatchExpr_getAltFor_x3f_spec__0(v_funName_202_, v_alts_201_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getAltFor_x3f___boxed(lean_object* v_alts_204_, lean_object* v_funName_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lean_Elab_Term_MatchExpr_getAltFor_x3f(v_alts_204_, v_funName_205_);
lean_dec(v_funName_205_);
lean_dec(v_alts_204_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Elab_Term_MatchExpr_next_spec__0(lean_object* v_actual_207_, lean_object* v_a_208_, lean_object* v_a_209_){
_start:
{
if (lean_obj_tag(v_a_208_) == 0)
{
lean_object* v___x_210_; 
lean_dec(v_actual_207_);
v___x_210_ = lean_array_to_list(v_a_209_);
return v___x_210_;
}
else
{
lean_object* v_head_211_; lean_object* v_tail_212_; lean_object* v_val_214_; lean_object* v_var_x3f_217_; lean_object* v_funName_218_; lean_object* v_pvars_219_; lean_object* v_rhs_220_; lean_object* v_k_221_; lean_object* v_actuals_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_245_; 
v_head_211_ = lean_ctor_get(v_a_208_, 0);
lean_inc(v_head_211_);
v_tail_212_ = lean_ctor_get(v_a_208_, 1);
lean_inc(v_tail_212_);
lean_dec_ref_known(v_a_208_, 2);
v_var_x3f_217_ = lean_ctor_get(v_head_211_, 0);
v_funName_218_ = lean_ctor_get(v_head_211_, 1);
v_pvars_219_ = lean_ctor_get(v_head_211_, 2);
v_rhs_220_ = lean_ctor_get(v_head_211_, 3);
v_k_221_ = lean_ctor_get(v_head_211_, 4);
v_actuals_222_ = lean_ctor_get(v_head_211_, 5);
v_isSharedCheck_245_ = !lean_is_exclusive(v_head_211_);
if (v_isSharedCheck_245_ == 0)
{
v___x_224_ = v_head_211_;
v_isShared_225_ = v_isSharedCheck_245_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_actuals_222_);
lean_inc(v_k_221_);
lean_inc(v_rhs_220_);
lean_inc(v_pvars_219_);
lean_inc(v_funName_218_);
lean_inc(v_var_x3f_217_);
lean_dec(v_head_211_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_245_;
goto v_resetjp_223_;
}
v___jp_213_:
{
lean_object* v___x_215_; 
v___x_215_ = lean_array_push(v_a_209_, v_val_214_);
v_a_208_ = v_tail_212_;
v_a_209_ = v___x_215_;
goto _start;
}
v_resetjp_223_:
{
if (lean_obj_tag(v_pvars_219_) == 1)
{
lean_object* v_head_234_; 
v_head_234_ = lean_ctor_get(v_pvars_219_, 0);
if (lean_obj_tag(v_head_234_) == 1)
{
lean_object* v_tail_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_243_; 
lean_del_object(v___x_224_);
v_tail_235_ = lean_ctor_get(v_pvars_219_, 1);
v_isSharedCheck_243_ = !lean_is_exclusive(v_pvars_219_);
if (v_isSharedCheck_243_ == 0)
{
lean_object* v_unused_244_; 
v_unused_244_ = lean_ctor_get(v_pvars_219_, 0);
lean_dec(v_unused_244_);
v___x_237_ = v_pvars_219_;
v_isShared_238_ = v_isSharedCheck_243_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_tail_235_);
lean_dec(v_pvars_219_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_243_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_240_; 
lean_inc(v_actual_207_);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 1, v_actuals_222_);
lean_ctor_set(v___x_237_, 0, v_actual_207_);
v___x_240_ = v___x_237_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_actual_207_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_actuals_222_);
v___x_240_ = v_reuseFailAlloc_242_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
lean_object* v___x_241_; 
v___x_241_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_241_, 0, v_var_x3f_217_);
lean_ctor_set(v___x_241_, 1, v_funName_218_);
lean_ctor_set(v___x_241_, 2, v_tail_235_);
lean_ctor_set(v___x_241_, 3, v_rhs_220_);
lean_ctor_set(v___x_241_, 4, v_k_221_);
lean_ctor_set(v___x_241_, 5, v___x_240_);
v_val_214_ = v___x_241_;
goto v___jp_213_;
}
}
}
else
{
goto v___jp_226_;
}
}
else
{
goto v___jp_226_;
}
v___jp_226_:
{
if (lean_obj_tag(v_pvars_219_) == 1)
{
lean_object* v_head_227_; 
v_head_227_ = lean_ctor_get(v_pvars_219_, 0);
if (lean_obj_tag(v_head_227_) == 0)
{
lean_object* v_tail_228_; lean_object* v___x_230_; 
v_tail_228_ = lean_ctor_get(v_pvars_219_, 1);
lean_inc(v_tail_228_);
lean_dec_ref_known(v_pvars_219_, 2);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 2, v_tail_228_);
v___x_230_ = v___x_224_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_var_x3f_217_);
lean_ctor_set(v_reuseFailAlloc_231_, 1, v_funName_218_);
lean_ctor_set(v_reuseFailAlloc_231_, 2, v_tail_228_);
lean_ctor_set(v_reuseFailAlloc_231_, 3, v_rhs_220_);
lean_ctor_set(v_reuseFailAlloc_231_, 4, v_k_221_);
lean_ctor_set(v_reuseFailAlloc_231_, 5, v_actuals_222_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
v_val_214_ = v___x_230_;
goto v___jp_213_;
}
}
else
{
lean_dec_ref_known(v_pvars_219_, 2);
lean_del_object(v___x_224_);
lean_dec(v_actuals_222_);
lean_dec(v_k_221_);
lean_dec(v_rhs_220_);
lean_dec(v_funName_218_);
lean_dec(v_var_x3f_217_);
v_a_208_ = v_tail_212_;
goto _start;
}
}
else
{
lean_del_object(v___x_224_);
lean_dec(v_actuals_222_);
lean_dec(v_k_221_);
lean_dec(v_rhs_220_);
lean_dec(v_pvars_219_);
lean_dec(v_funName_218_);
lean_dec(v_var_x3f_217_);
v_a_208_ = v_tail_212_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_next(lean_object* v_alts_248_, lean_object* v_actual_249_){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_next___closed__0));
v___x_251_ = l_List_filterMapTR_go___at___00Lean_Elab_Term_MatchExpr_next_spec__0(v_actual_249_, v_alts_248_, v___x_250_);
return v___x_251_;
}
}
static lean_object* _init_l_Lean_Elab_Term_MatchExpr_initK___closed__1(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_initK___closed__0));
v___x_254_ = l_String_toRawSubstring_x27(v___x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_initK(lean_object* v_alt_257_, lean_object* v_a_258_, lean_object* v_a_259_){
_start:
{
lean_object* v_macroScope_260_; lean_object* v_traceMsgs_261_; lean_object* v_expandedMacroDecls_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_294_; 
v_macroScope_260_ = lean_ctor_get(v_a_259_, 0);
v_traceMsgs_261_ = lean_ctor_get(v_a_259_, 1);
v_expandedMacroDecls_262_ = lean_ctor_get(v_a_259_, 2);
v_isSharedCheck_294_ = !lean_is_exclusive(v_a_259_);
if (v_isSharedCheck_294_ == 0)
{
v___x_264_ = v_a_259_;
v_isShared_265_ = v_isSharedCheck_294_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_expandedMacroDecls_262_);
lean_inc(v_traceMsgs_261_);
lean_inc(v_macroScope_260_);
lean_dec(v_a_259_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_294_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v_quotContext_266_; lean_object* v_ref_267_; lean_object* v_var_x3f_268_; lean_object* v_funName_269_; lean_object* v_pvars_270_; lean_object* v_rhs_271_; lean_object* v_actuals_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_292_; 
v_quotContext_266_ = lean_ctor_get(v_a_258_, 1);
v_ref_267_ = lean_ctor_get(v_a_258_, 5);
v_var_x3f_268_ = lean_ctor_get(v_alt_257_, 0);
v_funName_269_ = lean_ctor_get(v_alt_257_, 1);
v_pvars_270_ = lean_ctor_get(v_alt_257_, 2);
v_rhs_271_ = lean_ctor_get(v_alt_257_, 3);
v_actuals_272_ = lean_ctor_get(v_alt_257_, 5);
v_isSharedCheck_292_ = !lean_is_exclusive(v_alt_257_);
if (v_isSharedCheck_292_ == 0)
{
lean_object* v_unused_293_; 
v_unused_293_ = lean_ctor_get(v_alt_257_, 4);
lean_dec(v_unused_293_);
v___x_274_ = v_alt_257_;
v_isShared_275_ = v_isSharedCheck_292_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_actuals_272_);
lean_inc(v_rhs_271_);
lean_inc(v_pvars_270_);
lean_inc(v_funName_269_);
lean_inc(v_var_x3f_268_);
lean_dec(v_alt_257_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_292_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_280_; 
v___x_276_ = lean_unsigned_to_nat(1u);
v___x_277_ = lean_nat_add(v_macroScope_260_, v___x_276_);
v___x_278_ = lean_obj_once(&l_Lean_Elab_Term_MatchExpr_initK___closed__1, &l_Lean_Elab_Term_MatchExpr_initK___closed__1_once, _init_l_Lean_Elab_Term_MatchExpr_initK___closed__1);
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 0, v___x_277_);
v___x_280_ = v___x_264_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v___x_277_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v_traceMsgs_261_);
lean_ctor_set(v_reuseFailAlloc_291_, 2, v_expandedMacroDecls_262_);
v___x_280_ = v_reuseFailAlloc_291_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
uint8_t v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_288_; 
v___x_281_ = 0;
v___x_282_ = l_Lean_SourceInfo_fromRef(v_ref_267_, v___x_281_);
v___x_283_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_initK___closed__2));
lean_inc(v_quotContext_266_);
v___x_284_ = l_Lean_addMacroScope(v_quotContext_266_, v___x_283_, v_macroScope_260_);
v___x_285_ = lean_box(0);
v___x_286_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_286_, 0, v___x_282_);
lean_ctor_set(v___x_286_, 1, v___x_278_);
lean_ctor_set(v___x_286_, 2, v___x_284_);
lean_ctor_set(v___x_286_, 3, v___x_285_);
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 4, v___x_286_);
v___x_288_ = v___x_274_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_var_x3f_268_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v_funName_269_);
lean_ctor_set(v_reuseFailAlloc_290_, 2, v_pvars_270_);
lean_ctor_set(v_reuseFailAlloc_290_, 3, v_rhs_271_);
lean_ctor_set(v_reuseFailAlloc_290_, 4, v___x_286_);
lean_ctor_set(v_reuseFailAlloc_290_, 5, v_actuals_272_);
v___x_288_ = v_reuseFailAlloc_290_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
lean_object* v___x_289_; 
v___x_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
lean_ctor_set(v___x_289_, 1, v___x_280_);
return v___x_289_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_initK___boxed(lean_object* v_alt_295_, lean_object* v_a_296_, lean_object* v_a_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Lean_Elab_Term_MatchExpr_initK(v_alt_295_, v_a_296_, v_a_297_);
lean_dec_ref(v_a_296_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_MatchExpr_getParams_spec__1(size_t v_sz_299_, size_t v_i_300_, lean_object* v_bs_301_){
_start:
{
uint8_t v___x_302_; 
v___x_302_ = lean_usize_dec_lt(v_i_300_, v_sz_299_);
if (v___x_302_ == 0)
{
return v_bs_301_;
}
else
{
lean_object* v_v_303_; lean_object* v___x_304_; lean_object* v_bs_x27_305_; size_t v___x_306_; size_t v___x_307_; lean_object* v___x_308_; 
v_v_303_ = lean_array_uget(v_bs_301_, v_i_300_);
v___x_304_ = lean_unsigned_to_nat(0u);
v_bs_x27_305_ = lean_array_uset(v_bs_301_, v_i_300_, v___x_304_);
v___x_306_ = ((size_t)1ULL);
v___x_307_ = lean_usize_add(v_i_300_, v___x_306_);
v___x_308_ = lean_array_uset(v_bs_x27_305_, v_i_300_, v_v_303_);
v_i_300_ = v___x_307_;
v_bs_301_ = v___x_308_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_MatchExpr_getParams_spec__1___boxed(lean_object* v_sz_310_, lean_object* v_i_311_, lean_object* v_bs_312_){
_start:
{
size_t v_sz_boxed_313_; size_t v_i_boxed_314_; lean_object* v_res_315_; 
v_sz_boxed_313_ = lean_unbox_usize(v_sz_310_);
lean_dec(v_sz_310_);
v_i_boxed_314_ = lean_unbox_usize(v_i_311_);
lean_dec(v_i_311_);
v_res_315_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_MatchExpr_getParams_spec__1(v_sz_boxed_313_, v_i_boxed_314_, v_bs_312_);
return v_res_315_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__7(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__6));
v___x_329_ = l_String_toRawSubstring_x27(v___x_328_);
return v___x_329_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14(void){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l_Array_mkArray0(lean_box(0));
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0(lean_object* v_as_348_, size_t v_i_349_, size_t v_stop_350_, lean_object* v_b_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
lean_object* v_a_355_; lean_object* v_a_356_; uint8_t v___x_360_; 
v___x_360_ = lean_usize_dec_eq(v_i_349_, v_stop_350_);
if (v___x_360_ == 0)
{
lean_object* v___x_361_; 
v___x_361_ = lean_array_uget_borrowed(v_as_348_, v_i_349_);
if (lean_obj_tag(v___x_361_) == 0)
{
v_a_355_ = v_b_351_;
v_a_356_ = v___y_353_;
goto v___jp_354_;
}
else
{
lean_object* v_val_362_; lean_object* v_quotContext_363_; lean_object* v_currMacroScope_364_; lean_object* v_ref_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v_val_362_ = lean_ctor_get(v___x_361_, 0);
v_quotContext_363_ = lean_ctor_get(v___y_352_, 1);
v_currMacroScope_364_ = lean_ctor_get(v___y_352_, 2);
v_ref_365_ = lean_ctor_get(v___y_352_, 5);
v___x_366_ = l_Lean_SourceInfo_fromRef(v_ref_365_, v___x_360_);
v___x_367_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1));
v___x_368_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2));
lean_inc_n(v___x_366_, 7);
v___x_369_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_369_, 0, v___x_366_);
lean_ctor_set(v___x_369_, 1, v___x_368_);
v___x_370_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4));
lean_inc(v_val_362_);
v___x_371_ = l_Lean_Syntax_node1(v___x_366_, v___x_370_, v_val_362_);
v___x_372_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__5));
v___x_373_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_366_);
lean_ctor_set(v___x_373_, 1, v___x_372_);
v___x_374_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__7);
v___x_375_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__8));
lean_inc(v_currMacroScope_364_);
lean_inc(v_quotContext_363_);
v___x_376_ = l_Lean_addMacroScope(v_quotContext_363_, v___x_375_, v_currMacroScope_364_);
v___x_377_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__13));
v___x_378_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_378_, 0, v___x_366_);
lean_ctor_set(v___x_378_, 1, v___x_374_);
lean_ctor_set(v___x_378_, 2, v___x_376_);
lean_ctor_set(v___x_378_, 3, v___x_377_);
v___x_379_ = l_Lean_Syntax_node2(v___x_366_, v___x_370_, v___x_373_, v___x_378_);
v___x_380_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
v___x_381_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_381_, 0, v___x_366_);
lean_ctor_set(v___x_381_, 1, v___x_370_);
lean_ctor_set(v___x_381_, 2, v___x_380_);
v___x_382_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15));
v___x_383_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_383_, 0, v___x_366_);
lean_ctor_set(v___x_383_, 1, v___x_382_);
v___x_384_ = l_Lean_Syntax_node5(v___x_366_, v___x_367_, v___x_369_, v___x_371_, v___x_379_, v___x_381_, v___x_383_);
v___x_385_ = lean_array_push(v_b_351_, v___x_384_);
v_a_355_ = v___x_385_;
v_a_356_ = v___y_353_;
goto v___jp_354_;
}
}
else
{
lean_object* v___x_386_; 
v___x_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_386_, 0, v_b_351_);
lean_ctor_set(v___x_386_, 1, v___y_353_);
return v___x_386_;
}
v___jp_354_:
{
size_t v___x_357_; size_t v___x_358_; 
v___x_357_ = ((size_t)1ULL);
v___x_358_ = lean_usize_add(v_i_349_, v___x_357_);
v_i_349_ = v___x_358_;
v_b_351_ = v_a_355_;
v___y_353_ = v_a_356_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___boxed(lean_object* v_as_387_, lean_object* v_i_388_, lean_object* v_stop_389_, lean_object* v_b_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
size_t v_i_boxed_393_; size_t v_stop_boxed_394_; lean_object* v_res_395_; 
v_i_boxed_393_ = lean_unbox_usize(v_i_388_);
lean_dec(v_i_388_);
v_stop_boxed_394_ = lean_unbox_usize(v_stop_389_);
lean_dec(v_stop_389_);
v_res_395_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0(v_as_387_, v_i_boxed_393_, v_stop_boxed_394_, v_b_390_, v___y_391_, v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec_ref(v_as_387_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0(lean_object* v_as_396_, lean_object* v_start_397_, lean_object* v_stop_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v___x_401_; uint8_t v___x_402_; 
v___x_401_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch___closed__0));
v___x_402_ = lean_nat_dec_lt(v_start_397_, v_stop_398_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; 
v___x_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_401_);
lean_ctor_set(v___x_403_, 1, v___y_400_);
return v___x_403_;
}
else
{
lean_object* v___x_404_; uint8_t v___x_405_; 
v___x_404_ = lean_array_get_size(v_as_396_);
v___x_405_ = lean_nat_dec_le(v_stop_398_, v___x_404_);
if (v___x_405_ == 0)
{
uint8_t v___x_406_; 
v___x_406_ = lean_nat_dec_lt(v_start_397_, v___x_404_);
if (v___x_406_ == 0)
{
lean_object* v___x_407_; 
v___x_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_401_);
lean_ctor_set(v___x_407_, 1, v___y_400_);
return v___x_407_;
}
else
{
size_t v___x_408_; size_t v___x_409_; lean_object* v___x_410_; 
v___x_408_ = lean_usize_of_nat(v_start_397_);
v___x_409_ = lean_usize_of_nat(v___x_404_);
v___x_410_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0(v_as_396_, v___x_408_, v___x_409_, v___x_401_, v___y_399_, v___y_400_);
return v___x_410_;
}
}
else
{
size_t v___x_411_; size_t v___x_412_; lean_object* v___x_413_; 
v___x_411_ = lean_usize_of_nat(v_start_397_);
v___x_412_ = lean_usize_of_nat(v_stop_398_);
v___x_413_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0(v_as_396_, v___x_411_, v___x_412_, v___x_401_, v___y_399_, v___y_400_);
return v___x_413_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0___boxed(lean_object* v_as_414_, lean_object* v_start_415_, lean_object* v_stop_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0(v_as_414_, v_start_415_, v_stop_416_, v___y_417_, v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v_stop_416_);
lean_dec(v_start_415_);
lean_dec_ref(v_as_414_);
return v_res_419_;
}
}
static lean_object* _init_l_Lean_Elab_Term_MatchExpr_getParams___closed__2(void){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getParams___closed__1));
v___x_423_ = l_String_toRawSubstring_x27(v___x_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getParams(lean_object* v_alt_437_, lean_object* v_a_438_, lean_object* v_a_439_){
_start:
{
lean_object* v_var_x3f_440_; lean_object* v_pvars_441_; lean_object* v_params_443_; lean_object* v___y_444_; lean_object* v___y_445_; lean_object* v_params_499_; 
v_var_x3f_440_ = lean_ctor_get(v_alt_437_, 0);
lean_inc(v_var_x3f_440_);
v_pvars_441_ = lean_ctor_get(v_alt_437_, 2);
lean_inc(v_pvars_441_);
lean_dec_ref(v_alt_437_);
v_params_499_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch___closed__0));
if (lean_obj_tag(v_var_x3f_440_) == 1)
{
lean_object* v_val_500_; lean_object* v_quotContext_501_; lean_object* v_currMacroScope_502_; lean_object* v_ref_503_; uint8_t v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v_val_500_ = lean_ctor_get(v_var_x3f_440_, 0);
lean_inc(v_val_500_);
lean_dec_ref_known(v_var_x3f_440_, 1);
v_quotContext_501_ = lean_ctor_get(v_a_438_, 1);
v_currMacroScope_502_ = lean_ctor_get(v_a_438_, 2);
v_ref_503_ = lean_ctor_get(v_a_438_, 5);
v___x_504_ = 0;
v___x_505_ = l_Lean_SourceInfo_fromRef(v_ref_503_, v___x_504_);
v___x_506_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1));
v___x_507_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2));
lean_inc_n(v___x_505_, 7);
v___x_508_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_508_, 0, v___x_505_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
v___x_509_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4));
v___x_510_ = l_Lean_Syntax_node1(v___x_505_, v___x_509_, v_val_500_);
v___x_511_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__5));
v___x_512_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_512_, 0, v___x_505_);
lean_ctor_set(v___x_512_, 1, v___x_511_);
v___x_513_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__7);
v___x_514_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__8));
lean_inc(v_currMacroScope_502_);
lean_inc(v_quotContext_501_);
v___x_515_ = l_Lean_addMacroScope(v_quotContext_501_, v___x_514_, v_currMacroScope_502_);
v___x_516_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__13));
v___x_517_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_517_, 0, v___x_505_);
lean_ctor_set(v___x_517_, 1, v___x_513_);
lean_ctor_set(v___x_517_, 2, v___x_515_);
lean_ctor_set(v___x_517_, 3, v___x_516_);
v___x_518_ = l_Lean_Syntax_node2(v___x_505_, v___x_509_, v___x_512_, v___x_517_);
v___x_519_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
v___x_520_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_520_, 0, v___x_505_);
lean_ctor_set(v___x_520_, 1, v___x_509_);
lean_ctor_set(v___x_520_, 2, v___x_519_);
v___x_521_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15));
v___x_522_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_505_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
v___x_523_ = l_Lean_Syntax_node5(v___x_505_, v___x_506_, v___x_508_, v___x_510_, v___x_518_, v___x_520_, v___x_522_);
v___x_524_ = lean_array_push(v_params_499_, v___x_523_);
v_params_443_ = v___x_524_;
v___y_444_ = v_a_438_;
v___y_445_ = v_a_439_;
goto v___jp_442_;
}
else
{
lean_dec(v_var_x3f_440_);
v_params_443_ = v_params_499_;
v___y_444_ = v_a_438_;
v___y_445_ = v_a_439_;
goto v___jp_442_;
}
v___jp_442_:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_446_ = lean_array_mk(v_pvars_441_);
v___x_447_ = l_Array_reverse___redArg(v___x_446_);
v___x_448_ = lean_unsigned_to_nat(0u);
v___x_449_ = lean_array_get_size(v___x_447_);
v___x_450_ = l_Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0(v___x_447_, v___x_448_, v___x_449_, v___y_444_, v___y_445_);
lean_dec_ref(v___x_447_);
if (lean_obj_tag(v___x_450_) == 0)
{
lean_object* v_a_451_; lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_498_; 
v_a_451_ = lean_ctor_get(v___x_450_, 0);
v_a_452_ = lean_ctor_get(v___x_450_, 1);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_498_ == 0)
{
v___x_454_ = v___x_450_;
v_isShared_455_ = v_isSharedCheck_498_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_inc(v_a_451_);
lean_dec(v___x_450_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_498_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_456_; lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_456_ = l_Array_append___redArg(v_params_443_, v_a_451_);
lean_dec(v_a_451_);
v___x_457_ = lean_array_get_size(v___x_456_);
v___x_458_ = lean_nat_dec_eq(v___x_457_, v___x_448_);
if (v___x_458_ == 0)
{
size_t v_sz_459_; size_t v___x_460_; lean_object* v___x_461_; lean_object* v___x_463_; 
v_sz_459_ = lean_array_size(v___x_456_);
v___x_460_ = ((size_t)0ULL);
v___x_461_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_MatchExpr_getParams_spec__1(v_sz_459_, v___x_460_, v___x_456_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v___x_461_);
v___x_463_ = v___x_454_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_461_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v_a_452_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
else
{
lean_object* v_quotContext_465_; lean_object* v_currMacroScope_466_; lean_object* v_ref_467_; uint8_t v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_496_; 
lean_dec_ref(v___x_456_);
v_quotContext_465_ = lean_ctor_get(v___y_444_, 1);
v_currMacroScope_466_ = lean_ctor_get(v___y_444_, 2);
v_ref_467_ = lean_ctor_get(v___y_444_, 5);
v___x_468_ = 0;
v___x_469_ = l_Lean_SourceInfo_fromRef(v_ref_467_, v___x_468_);
v___x_470_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1));
v___x_471_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2));
lean_inc_n(v___x_469_, 9);
v___x_472_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_469_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
v___x_473_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4));
v___x_474_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1));
v___x_475_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getParams___closed__0));
v___x_476_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_476_, 0, v___x_469_);
lean_ctor_set(v___x_476_, 1, v___x_475_);
v___x_477_ = l_Lean_Syntax_node1(v___x_469_, v___x_474_, v___x_476_);
v___x_478_ = l_Lean_Syntax_node1(v___x_469_, v___x_473_, v___x_477_);
v___x_479_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__5));
v___x_480_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_480_, 0, v___x_469_);
lean_ctor_set(v___x_480_, 1, v___x_479_);
v___x_481_ = lean_obj_once(&l_Lean_Elab_Term_MatchExpr_getParams___closed__2, &l_Lean_Elab_Term_MatchExpr_getParams___closed__2_once, _init_l_Lean_Elab_Term_MatchExpr_getParams___closed__2);
v___x_482_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getParams___closed__3));
lean_inc(v_currMacroScope_466_);
lean_inc(v_quotContext_465_);
v___x_483_ = l_Lean_addMacroScope(v_quotContext_465_, v___x_482_, v_currMacroScope_466_);
v___x_484_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getParams___closed__7));
v___x_485_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_485_, 0, v___x_469_);
lean_ctor_set(v___x_485_, 1, v___x_481_);
lean_ctor_set(v___x_485_, 2, v___x_483_);
lean_ctor_set(v___x_485_, 3, v___x_484_);
v___x_486_ = l_Lean_Syntax_node2(v___x_469_, v___x_473_, v___x_480_, v___x_485_);
v___x_487_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
v___x_488_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_488_, 0, v___x_469_);
lean_ctor_set(v___x_488_, 1, v___x_473_);
lean_ctor_set(v___x_488_, 2, v___x_487_);
v___x_489_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15));
v___x_490_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_490_, 0, v___x_469_);
lean_ctor_set(v___x_490_, 1, v___x_489_);
v___x_491_ = l_Lean_Syntax_node5(v___x_469_, v___x_470_, v___x_472_, v___x_478_, v___x_486_, v___x_488_, v___x_490_);
v___x_492_ = lean_unsigned_to_nat(1u);
v___x_493_ = lean_mk_empty_array_with_capacity(v___x_492_);
v___x_494_ = lean_array_push(v___x_493_, v___x_491_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v___x_494_);
v___x_496_ = v___x_454_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v___x_494_);
lean_ctor_set(v_reuseFailAlloc_497_, 1, v_a_452_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
else
{
lean_dec_ref(v_params_443_);
return v___x_450_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getParams___boxed(lean_object* v_alt_525_, lean_object* v_a_526_, lean_object* v_a_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Lean_Elab_Term_MatchExpr_getParams(v_alt_525_, v_a_526_, v_a_527_);
lean_dec_ref(v_a_526_);
return v_res_528_;
}
}
static lean_object* _init_l_Lean_Elab_Term_MatchExpr_getActuals___closed__7(void){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__6));
v___x_546_ = l_String_toRawSubstring_x27(v___x_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getActuals(lean_object* v_discr_585_, lean_object* v_alt_586_, lean_object* v_a_587_, lean_object* v_a_588_){
_start:
{
lean_object* v_var_x3f_589_; lean_object* v_actuals_590_; lean_object* v_actuals_592_; lean_object* v___y_593_; lean_object* v___y_594_; lean_object* v_actuals_628_; 
v_var_x3f_589_ = lean_ctor_get(v_alt_586_, 0);
lean_inc(v_var_x3f_589_);
v_actuals_590_ = lean_ctor_get(v_alt_586_, 5);
lean_inc(v_actuals_590_);
lean_dec_ref(v_alt_586_);
v_actuals_628_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch___closed__0));
if (lean_obj_tag(v_var_x3f_589_) == 0)
{
lean_dec(v_discr_585_);
v_actuals_592_ = v_actuals_628_;
v___y_593_ = v_a_587_;
v___y_594_ = v_a_588_;
goto v___jp_591_;
}
else
{
lean_object* v_actuals_629_; 
lean_dec_ref_known(v_var_x3f_589_, 1);
v_actuals_629_ = lean_array_push(v_actuals_628_, v_discr_585_);
v_actuals_592_ = v_actuals_629_;
v___y_593_ = v_a_587_;
v___y_594_ = v_a_588_;
goto v___jp_591_;
}
v___jp_591_:
{
lean_object* v___x_595_; lean_object* v_actuals_596_; lean_object* v___x_597_; lean_object* v___x_598_; uint8_t v___x_599_; 
v___x_595_ = lean_array_mk(v_actuals_590_);
v_actuals_596_ = l_Array_append___redArg(v_actuals_592_, v___x_595_);
lean_dec_ref(v___x_595_);
v___x_597_ = lean_array_get_size(v_actuals_596_);
v___x_598_ = lean_unsigned_to_nat(0u);
v___x_599_ = lean_nat_dec_eq(v___x_597_, v___x_598_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; 
v___x_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_600_, 0, v_actuals_596_);
lean_ctor_set(v___x_600_, 1, v___y_594_);
return v___x_600_;
}
else
{
lean_object* v_quotContext_601_; lean_object* v_currMacroScope_602_; lean_object* v_ref_603_; uint8_t v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
lean_dec_ref(v_actuals_596_);
v_quotContext_601_ = lean_ctor_get(v___y_593_, 1);
v_currMacroScope_602_ = lean_ctor_get(v___y_593_, 2);
v_ref_603_ = lean_ctor_get(v___y_593_, 5);
v___x_604_ = 0;
v___x_605_ = l_Lean_SourceInfo_fromRef(v_ref_603_, v___x_604_);
v___x_606_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__1));
v___x_607_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__3));
v___x_608_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2));
lean_inc_n(v___x_605_, 6);
v___x_609_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_605_);
lean_ctor_set(v___x_609_, 1, v___x_608_);
v___x_610_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__5));
v___x_611_ = lean_obj_once(&l_Lean_Elab_Term_MatchExpr_getActuals___closed__7, &l_Lean_Elab_Term_MatchExpr_getActuals___closed__7_once, _init_l_Lean_Elab_Term_MatchExpr_getActuals___closed__7);
v___x_612_ = lean_box(0);
lean_inc(v_currMacroScope_602_);
lean_inc(v_quotContext_601_);
v___x_613_ = l_Lean_addMacroScope(v_quotContext_601_, v___x_612_, v_currMacroScope_602_);
v___x_614_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__21));
v___x_615_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_615_, 0, v___x_605_);
lean_ctor_set(v___x_615_, 1, v___x_611_);
lean_ctor_set(v___x_615_, 2, v___x_613_);
lean_ctor_set(v___x_615_, 3, v___x_614_);
v___x_616_ = l_Lean_Syntax_node1(v___x_605_, v___x_610_, v___x_615_);
v___x_617_ = l_Lean_Syntax_node2(v___x_605_, v___x_607_, v___x_609_, v___x_616_);
v___x_618_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4));
v___x_619_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
v___x_620_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_620_, 0, v___x_605_);
lean_ctor_set(v___x_620_, 1, v___x_618_);
lean_ctor_set(v___x_620_, 2, v___x_619_);
v___x_621_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15));
v___x_622_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_605_);
lean_ctor_set(v___x_622_, 1, v___x_621_);
v___x_623_ = l_Lean_Syntax_node3(v___x_605_, v___x_606_, v___x_617_, v___x_620_, v___x_622_);
v___x_624_ = lean_unsigned_to_nat(1u);
v___x_625_ = lean_mk_empty_array_with_capacity(v___x_624_);
v___x_626_ = lean_array_push(v___x_625_, v___x_623_);
v___x_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
lean_ctor_set(v___x_627_, 1, v___y_594_);
return v___x_627_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getActuals___boxed(lean_object* v_discr_630_, lean_object* v_alt_631_, lean_object* v_a_632_, lean_object* v_a_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lean_Elab_Term_MatchExpr_getActuals(v_discr_630_, v_alt_631_, v_a_632_, v_a_633_);
lean_dec_ref(v_a_632_);
return v_res_634_;
}
}
static lean_object* _init_l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__3(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__2));
v___x_643_ = l_Lean_mkAtom(v___x_642_);
return v___x_643_;
}
}
static lean_object* _init_l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__4(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_644_ = lean_obj_once(&l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__3, &l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__3_once, _init_l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__3);
v___x_645_ = lean_unsigned_to_nat(3u);
v___x_646_ = lean_mk_empty_array_with_capacity(v___x_645_);
v___x_647_ = lean_array_push(v___x_646_, v___x_644_);
return v___x_647_;
}
}
static lean_object* _init_l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__5(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_648_ = lean_obj_once(&l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__3, &l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__3_once, _init_l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__3);
v___x_649_ = lean_obj_once(&l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__4, &l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__4_once, _init_l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__4);
v___x_650_ = lean_array_push(v___x_649_, v___x_648_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName(lean_object* v_ident_651_){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_652_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__1));
v___x_653_ = lean_obj_once(&l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__5, &l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__5_once, _init_l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__5);
v___x_654_ = lean_array_push(v___x_653_, v_ident_651_);
v___x_655_ = lean_box(2);
v___x_656_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
lean_ctor_set(v___x_656_, 1, v___x_652_);
lean_ctor_set(v___x_656_, 2, v___x_654_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___lam__0(uint8_t v___x_657_, lean_object* v_____do__lift_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = l_Lean_SourceInfo_fromRef(v_____do__lift_658_, v___x_657_);
v___x_662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_661_);
lean_ctor_set(v___x_662_, 1, v___y_660_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___lam__0___boxed(lean_object* v___x_663_, lean_object* v_____do__lift_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
uint8_t v___x_21046__boxed_667_; lean_object* v_res_668_; 
v___x_21046__boxed_667_ = lean_unbox(v___x_663_);
v_res_668_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___lam__0(v___x_21046__boxed_667_, v_____do__lift_664_, v___y_665_, v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec(v_____do__lift_664_);
return v_res_668_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__9(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__8));
v___x_691_ = l_String_toRawSubstring_x27(v___x_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg(lean_object* v_alts_699_, lean_object* v_discr_700_, lean_object* v_as_x27_701_, lean_object* v_b_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
if (lean_obj_tag(v_as_x27_701_) == 0)
{
lean_object* v___x_705_; 
lean_dec(v_discr_700_);
v___x_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_705_, 0, v_b_702_);
lean_ctor_set(v___x_705_, 1, v___y_704_);
return v___x_705_;
}
else
{
lean_object* v_head_706_; lean_object* v_tail_707_; lean_object* v___x_708_; 
v_head_706_ = lean_ctor_get(v_as_x27_701_, 0);
v_tail_707_ = lean_ctor_get(v_as_x27_701_, 1);
v___x_708_ = l_List_find_x3f___at___00Lean_Elab_Term_MatchExpr_getAltFor_x3f_spec__0(v_head_706_, v_alts_699_);
if (lean_obj_tag(v___x_708_) == 1)
{
lean_object* v_val_709_; lean_object* v___x_710_; lean_object* v_a_711_; lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_766_; 
v_val_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc_n(v_val_709_, 2);
lean_dec_ref_known(v___x_708_, 1);
lean_inc(v_discr_700_);
v___x_710_ = l_Lean_Elab_Term_MatchExpr_getActuals(v_discr_700_, v_val_709_, v___y_703_, v___y_704_);
v_a_711_ = lean_ctor_get(v___x_710_, 0);
v_a_712_ = lean_ctor_get(v___x_710_, 1);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_710_);
if (v_isSharedCheck_766_ == 0)
{
v___x_714_ = v___x_710_;
v_isShared_715_ = v_isSharedCheck_766_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_inc(v_a_711_);
lean_dec(v___x_710_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_766_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v_quotContext_716_; lean_object* v_currMacroScope_717_; lean_object* v_ref_718_; uint8_t v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_723_; 
v_quotContext_716_ = lean_ctor_get(v___y_703_, 1);
v_currMacroScope_717_ = lean_ctor_get(v___y_703_, 2);
v_ref_718_ = lean_ctor_get(v___y_703_, 5);
v___x_719_ = 0;
v___x_720_ = l_Lean_SourceInfo_fromRef(v_ref_718_, v___x_719_);
v___x_721_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__0));
lean_inc(v___x_720_);
if (v_isShared_715_ == 0)
{
lean_ctor_set_tag(v___x_714_, 2);
lean_ctor_set(v___x_714_, 1, v___x_721_);
lean_ctor_set(v___x_714_, 0, v___x_720_);
v___x_723_ = v___x_714_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_720_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v___x_721_);
v___x_723_ = v_reuseFailAlloc_765_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v_k_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_724_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2));
v___x_725_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__4));
v___x_726_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__6));
v___x_727_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__3));
v___x_728_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2));
lean_inc_n(v___x_720_, 15);
v___x_729_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_720_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
v___x_730_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__5));
v___x_731_ = lean_obj_once(&l_Lean_Elab_Term_MatchExpr_getActuals___closed__7, &l_Lean_Elab_Term_MatchExpr_getActuals___closed__7_once, _init_l_Lean_Elab_Term_MatchExpr_getActuals___closed__7);
v___x_732_ = lean_box(0);
lean_inc_n(v_currMacroScope_717_, 2);
lean_inc_n(v_quotContext_716_, 2);
v___x_733_ = l_Lean_addMacroScope(v_quotContext_716_, v___x_732_, v_currMacroScope_717_);
v___x_734_ = lean_box(0);
v___x_735_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__21));
v___x_736_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_736_, 0, v___x_720_);
lean_ctor_set(v___x_736_, 1, v___x_731_);
lean_ctor_set(v___x_736_, 2, v___x_733_);
lean_ctor_set(v___x_736_, 3, v___x_735_);
v___x_737_ = l_Lean_Syntax_node1(v___x_720_, v___x_730_, v___x_736_);
v___x_738_ = l_Lean_Syntax_node2(v___x_720_, v___x_727_, v___x_729_, v___x_737_);
v___x_739_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15));
v___x_740_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_720_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
lean_inc(v_discr_700_);
v___x_741_ = l_Lean_Syntax_node3(v___x_720_, v___x_726_, v___x_738_, v_discr_700_, v___x_740_);
v___x_742_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__7));
v___x_743_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_720_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
v___x_744_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__9, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__9_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__9);
v___x_745_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__10));
v___x_746_ = l_Lean_addMacroScope(v_quotContext_716_, v___x_745_, v_currMacroScope_717_);
v___x_747_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_747_, 0, v___x_720_);
lean_ctor_set(v___x_747_, 1, v___x_744_);
lean_ctor_set(v___x_747_, 2, v___x_746_);
lean_ctor_set(v___x_747_, 3, v___x_734_);
v___x_748_ = l_Lean_Syntax_node3(v___x_720_, v___x_725_, v___x_741_, v___x_743_, v___x_747_);
v___x_749_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4));
lean_inc(v_head_706_);
v___x_750_ = l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName(v_head_706_);
v___x_751_ = l_Lean_Syntax_node1(v___x_720_, v___x_749_, v___x_750_);
v_k_752_ = lean_ctor_get(v_val_709_, 4);
lean_inc(v_k_752_);
lean_dec(v_val_709_);
v___x_753_ = l_Lean_Syntax_node2(v___x_720_, v___x_724_, v___x_748_, v___x_751_);
v___x_754_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__12));
v___x_755_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__13));
v___x_756_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_756_, 0, v___x_720_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
v___x_757_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
v___x_758_ = l_Array_append___redArg(v___x_757_, v_a_711_);
lean_dec(v_a_711_);
v___x_759_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_759_, 0, v___x_720_);
lean_ctor_set(v___x_759_, 1, v___x_749_);
lean_ctor_set(v___x_759_, 2, v___x_758_);
v___x_760_ = l_Lean_Syntax_node2(v___x_720_, v___x_724_, v_k_752_, v___x_759_);
v___x_761_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__14));
v___x_762_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_762_, 0, v___x_720_);
lean_ctor_set(v___x_762_, 1, v___x_761_);
v___x_763_ = l_Lean_Syntax_node6(v___x_720_, v___x_754_, v___x_723_, v___x_753_, v___x_756_, v___x_760_, v___x_762_, v_b_702_);
v_as_x27_701_ = v_tail_707_;
v_b_702_ = v___x_763_;
v___y_704_ = v_a_712_;
goto _start;
}
}
}
else
{
lean_dec(v___x_708_);
v_as_x27_701_ = v_tail_707_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___boxed(lean_object* v_alts_768_, lean_object* v_discr_769_, lean_object* v_as_x27_770_, lean_object* v_b_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg(v_alts_768_, v_discr_769_, v_as_x27_770_, v_b_771_, v___y_772_, v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v_as_x27_770_);
lean_dec(v_alts_768_);
return v_res_774_;
}
}
static lean_object* _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__1(void){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__0));
v___x_777_ = l_String_toRawSubstring_x27(v___x_776_);
return v___x_777_;
}
}
static lean_object* _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__8(void){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__7));
v___x_789_ = l_String_toRawSubstring_x27(v___x_788_);
return v___x_789_;
}
}
static lean_object* _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__11(void){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__10));
v___x_794_ = l_String_toRawSubstring_x27(v___x_793_);
return v___x_794_;
}
}
static lean_object* _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__25(void){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_829_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__24));
v___x_830_ = l_String_toRawSubstring_x27(v___x_829_);
return v___x_830_;
}
}
static lean_object* _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__33(void){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__32));
v___x_848_ = l_String_toRawSubstring_x27(v___x_847_);
return v___x_848_;
}
}
static lean_object* _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__36(void){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_852_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__35));
v___x_853_ = l_String_toRawSubstring_x27(v___x_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop(lean_object* v_kElse_873_, lean_object* v_discr_874_, lean_object* v_alts_875_, lean_object* v_a_876_, lean_object* v_a_877_){
_start:
{
lean_object* v_macroScope_878_; lean_object* v_traceMsgs_879_; lean_object* v_expandedMacroDecls_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_1150_; 
v_macroScope_878_ = lean_ctor_get(v_a_877_, 0);
v_traceMsgs_879_ = lean_ctor_get(v_a_877_, 1);
v_expandedMacroDecls_880_ = lean_ctor_get(v_a_877_, 2);
v_isSharedCheck_1150_ = !lean_is_exclusive(v_a_877_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_882_ = v_a_877_;
v_isShared_883_ = v_isSharedCheck_1150_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_expandedMacroDecls_880_);
lean_inc(v_traceMsgs_879_);
lean_inc(v_macroScope_878_);
lean_dec(v_a_877_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_1150_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v_methods_884_; lean_object* v_quotContext_885_; lean_object* v_currRecDepth_886_; lean_object* v_maxRecDepth_887_; lean_object* v_ref_888_; lean_object* v_funNamesToMatch_889_; uint8_t v_saveActual_890_; lean_object* v_actual_892_; lean_object* v___y_893_; lean_object* v___y_894_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1135_; 
v_methods_884_ = lean_ctor_get(v_a_876_, 0);
v_quotContext_885_ = lean_ctor_get(v_a_876_, 1);
v_currRecDepth_886_ = lean_ctor_get(v_a_876_, 3);
v_maxRecDepth_887_ = lean_ctor_get(v_a_876_, 4);
v_ref_888_ = lean_ctor_get(v_a_876_, 5);
v_funNamesToMatch_889_ = l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch(v_alts_875_);
v_saveActual_890_ = l_List_any___at___00Lean_Elab_Term_MatchExpr_shouldSaveActual_spec__0(v_alts_875_);
v___x_1132_ = lean_unsigned_to_nat(1u);
v___x_1133_ = lean_nat_add(v_macroScope_878_, v___x_1132_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 0, v___x_1133_);
v___x_1135_ = v___x_882_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1133_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_traceMsgs_879_);
lean_ctor_set(v_reuseFailAlloc_1149_, 2, v_expandedMacroDecls_880_);
v___x_1135_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1134_;
}
v___jp_891_:
{
lean_object* v_altsNext_895_; uint8_t v___x_896_; 
lean_inc(v_alts_875_);
v_altsNext_895_ = l_Lean_Elab_Term_MatchExpr_next(v_alts_875_, v_actual_892_);
v___x_896_ = l_List_isEmpty___redArg(v_altsNext_895_);
if (v___x_896_ == 0)
{
lean_object* v_quotContext_897_; lean_object* v_currMacroScope_898_; lean_object* v_ref_899_; lean_object* v___x_900_; 
v_quotContext_897_ = lean_ctor_get(v___y_893_, 1);
v_currMacroScope_898_ = lean_ctor_get(v___y_893_, 2);
v_ref_899_ = lean_ctor_get(v___y_893_, 5);
v___x_900_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___lam__0(v___x_896_, v_ref_899_, v___y_893_, v___y_894_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v_a_901_; lean_object* v_a_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v_a_901_ = lean_ctor_get(v___x_900_, 0);
lean_inc(v_a_901_);
v_a_902_ = lean_ctor_get(v___x_900_, 1);
lean_inc(v_a_902_);
lean_dec_ref_known(v___x_900_, 2);
v___x_903_ = lean_obj_once(&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__1, &l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__1_once, _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__1);
v___x_904_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__2));
lean_inc(v_currMacroScope_898_);
lean_inc(v_quotContext_897_);
v___x_905_ = l_Lean_addMacroScope(v_quotContext_897_, v___x_904_, v_currMacroScope_898_);
v___x_906_ = lean_box(0);
lean_inc(v___x_905_);
v___x_907_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_907_, 0, v_a_901_);
lean_ctor_set(v___x_907_, 1, v___x_903_);
lean_ctor_set(v___x_907_, 2, v___x_905_);
lean_ctor_set(v___x_907_, 3, v___x_906_);
lean_inc(v_kElse_873_);
v___x_908_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop(v_kElse_873_, v___x_907_, v_altsNext_895_, v___y_893_, v_a_902_);
if (lean_obj_tag(v___x_908_) == 0)
{
if (v_saveActual_890_ == 0)
{
lean_object* v_a_909_; lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_989_; 
v_a_909_ = lean_ctor_get(v___x_908_, 0);
v_a_910_ = lean_ctor_get(v___x_908_, 1);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_989_ == 0)
{
v___x_912_ = v___x_908_;
v_isShared_913_ = v_isSharedCheck_989_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_inc(v_a_909_);
lean_dec(v___x_908_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_989_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_918_; 
v___x_914_ = l_Lean_SourceInfo_fromRef(v_ref_899_, v_saveActual_890_);
v___x_915_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__4));
v___x_916_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__0));
lean_inc(v___x_914_);
if (v_isShared_913_ == 0)
{
lean_ctor_set_tag(v___x_912_, 2);
lean_ctor_set(v___x_912_, 1, v___x_916_);
lean_ctor_set(v___x_912_, 0, v___x_914_);
v___x_918_ = v___x_912_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_914_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v___x_916_);
v___x_918_ = v_reuseFailAlloc_988_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_919_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__6));
v___x_920_ = lean_obj_once(&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__8, &l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__8_once, _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__8);
v___x_921_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__9));
lean_inc_n(v_currMacroScope_898_, 4);
lean_inc_n(v_quotContext_897_, 4);
v___x_922_ = l_Lean_addMacroScope(v_quotContext_897_, v___x_921_, v_currMacroScope_898_);
lean_inc_n(v___x_914_, 30);
v___x_923_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_923_, 0, v___x_914_);
lean_ctor_set(v___x_923_, 1, v___x_920_);
lean_ctor_set(v___x_923_, 2, v___x_922_);
lean_ctor_set(v___x_923_, 3, v___x_906_);
lean_inc_ref(v___x_923_);
v___x_924_ = l_Lean_Syntax_node1(v___x_914_, v___x_919_, v___x_923_);
v___x_925_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__5));
v___x_926_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_914_);
lean_ctor_set(v___x_926_, 1, v___x_925_);
v___x_927_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__4));
v___x_928_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__6));
v___x_929_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__3));
v___x_930_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2));
v___x_931_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_914_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
v___x_932_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__5));
v___x_933_ = lean_obj_once(&l_Lean_Elab_Term_MatchExpr_getActuals___closed__7, &l_Lean_Elab_Term_MatchExpr_getActuals___closed__7_once, _init_l_Lean_Elab_Term_MatchExpr_getActuals___closed__7);
v___x_934_ = lean_box(0);
v___x_935_ = l_Lean_addMacroScope(v_quotContext_897_, v___x_934_, v_currMacroScope_898_);
v___x_936_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__21));
v___x_937_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_937_, 0, v___x_914_);
lean_ctor_set(v___x_937_, 1, v___x_933_);
lean_ctor_set(v___x_937_, 2, v___x_935_);
lean_ctor_set(v___x_937_, 3, v___x_936_);
v___x_938_ = l_Lean_Syntax_node1(v___x_914_, v___x_932_, v___x_937_);
v___x_939_ = l_Lean_Syntax_node2(v___x_914_, v___x_929_, v___x_931_, v___x_938_);
v___x_940_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15));
v___x_941_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_914_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
lean_inc_ref(v___x_941_);
lean_inc_n(v_discr_874_, 2);
lean_inc(v___x_939_);
v___x_942_ = l_Lean_Syntax_node3(v___x_914_, v___x_928_, v___x_939_, v_discr_874_, v___x_941_);
v___x_943_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__7));
v___x_944_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_914_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
v___x_945_ = lean_obj_once(&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__11, &l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__11_once, _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__11);
v___x_946_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__12));
v___x_947_ = l_Lean_addMacroScope(v_quotContext_897_, v___x_946_, v_currMacroScope_898_);
v___x_948_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_948_, 0, v___x_914_);
lean_ctor_set(v___x_948_, 1, v___x_945_);
lean_ctor_set(v___x_948_, 2, v___x_947_);
lean_ctor_set(v___x_948_, 3, v___x_906_);
v___x_949_ = l_Lean_Syntax_node3(v___x_914_, v___x_927_, v___x_942_, v___x_944_, v___x_948_);
v___x_950_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__13));
v___x_951_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_914_);
lean_ctor_set(v___x_951_, 1, v___x_950_);
v___x_952_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__13));
v___x_953_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__14));
v___x_954_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_914_);
lean_ctor_set(v___x_954_, 1, v___x_952_);
v___x_955_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__16));
v___x_956_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4));
v___x_957_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
v___x_958_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_958_, 0, v___x_914_);
lean_ctor_set(v___x_958_, 1, v___x_956_);
lean_ctor_set(v___x_958_, 2, v___x_957_);
lean_inc_ref_n(v___x_958_, 3);
v___x_959_ = l_Lean_Syntax_node1(v___x_914_, v___x_955_, v___x_958_);
v___x_960_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18));
v___x_961_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20));
v___x_962_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22));
v___x_963_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_963_, 0, v___x_914_);
lean_ctor_set(v___x_963_, 1, v___x_903_);
lean_ctor_set(v___x_963_, 2, v___x_905_);
lean_ctor_set(v___x_963_, 3, v___x_906_);
v___x_964_ = l_Lean_Syntax_node1(v___x_914_, v___x_962_, v___x_963_);
v___x_965_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__23));
v___x_966_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_914_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2));
v___x_968_ = lean_obj_once(&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__25, &l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__25_once, _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__25);
v___x_969_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__27));
v___x_970_ = l_Lean_addMacroScope(v_quotContext_897_, v___x_969_, v_currMacroScope_898_);
v___x_971_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__30));
v___x_972_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_972_, 0, v___x_914_);
lean_ctor_set(v___x_972_, 1, v___x_968_);
lean_ctor_set(v___x_972_, 2, v___x_970_);
lean_ctor_set(v___x_972_, 3, v___x_971_);
v___x_973_ = l_Lean_Syntax_node2(v___x_914_, v___x_956_, v_discr_874_, v___x_923_);
v___x_974_ = l_Lean_Syntax_node2(v___x_914_, v___x_967_, v___x_972_, v___x_973_);
v___x_975_ = l_Lean_Syntax_node5(v___x_914_, v___x_961_, v___x_964_, v___x_958_, v___x_958_, v___x_966_, v___x_974_);
v___x_976_ = l_Lean_Syntax_node1(v___x_914_, v___x_960_, v___x_975_);
v___x_977_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__31));
v___x_978_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_914_);
lean_ctor_set(v___x_978_, 1, v___x_977_);
v___x_979_ = l_Lean_Syntax_node5(v___x_914_, v___x_953_, v___x_954_, v___x_959_, v___x_976_, v___x_978_, v_a_909_);
v___x_980_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__14));
v___x_981_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_914_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
v___x_982_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__1));
v___x_983_ = l_Lean_Syntax_node3(v___x_914_, v___x_982_, v___x_939_, v___x_958_, v___x_941_);
v___x_984_ = l_Lean_Syntax_node1(v___x_914_, v___x_956_, v___x_983_);
v___x_985_ = l_Lean_Syntax_node2(v___x_914_, v___x_967_, v_kElse_873_, v___x_984_);
v___x_986_ = l_Lean_Syntax_node8(v___x_914_, v___x_915_, v___x_918_, v___x_924_, v___x_926_, v___x_949_, v___x_951_, v___x_979_, v___x_981_, v___x_985_);
v___x_987_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg(v_alts_875_, v_discr_874_, v_funNamesToMatch_889_, v___x_986_, v___y_893_, v_a_910_);
lean_dec_ref(v___y_893_);
lean_dec(v_funNamesToMatch_889_);
lean_dec(v_alts_875_);
return v___x_987_;
}
}
}
else
{
lean_object* v_a_990_; lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1095_; 
v_a_990_ = lean_ctor_get(v___x_908_, 0);
v_a_991_ = lean_ctor_get(v___x_908_, 1);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_993_ = v___x_908_;
v_isShared_994_ = v_isSharedCheck_1095_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_inc(v_a_990_);
lean_dec(v___x_908_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1095_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_995_; 
v___x_995_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___lam__0(v___x_896_, v_ref_899_, v___y_893_, v_a_991_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_object* v_a_996_; lean_object* v_a_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1001_; 
v_a_996_ = lean_ctor_get(v___x_995_, 0);
lean_inc_n(v_a_996_, 2);
v_a_997_ = lean_ctor_get(v___x_995_, 1);
lean_inc(v_a_997_);
lean_dec_ref_known(v___x_995_, 2);
v___x_998_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__4));
v___x_999_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__0));
if (v_isShared_994_ == 0)
{
lean_ctor_set_tag(v___x_993_, 2);
lean_ctor_set(v___x_993_, 1, v___x_999_);
lean_ctor_set(v___x_993_, 0, v_a_996_);
v___x_1001_ = v___x_993_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_996_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v___x_999_);
v___x_1001_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1002_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__6));
v___x_1003_ = lean_obj_once(&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__8, &l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__8_once, _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__8);
v___x_1004_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__9));
lean_inc_n(v_currMacroScope_898_, 6);
lean_inc_n(v_quotContext_897_, 6);
v___x_1005_ = l_Lean_addMacroScope(v_quotContext_897_, v___x_1004_, v_currMacroScope_898_);
lean_inc_n(v_a_996_, 37);
v___x_1006_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1006_, 0, v_a_996_);
lean_ctor_set(v___x_1006_, 1, v___x_1003_);
lean_ctor_set(v___x_1006_, 2, v___x_1005_);
lean_ctor_set(v___x_1006_, 3, v___x_906_);
lean_inc_ref(v___x_1006_);
v___x_1007_ = l_Lean_Syntax_node1(v_a_996_, v___x_1002_, v___x_1006_);
v___x_1008_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__5));
v___x_1009_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1009_, 0, v_a_996_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__4));
v___x_1011_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__6));
v___x_1012_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__3));
v___x_1013_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2));
v___x_1014_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1014_, 0, v_a_996_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__5));
v___x_1016_ = lean_obj_once(&l_Lean_Elab_Term_MatchExpr_getActuals___closed__7, &l_Lean_Elab_Term_MatchExpr_getActuals___closed__7_once, _init_l_Lean_Elab_Term_MatchExpr_getActuals___closed__7);
v___x_1017_ = lean_box(0);
v___x_1018_ = l_Lean_addMacroScope(v_quotContext_897_, v___x_1017_, v_currMacroScope_898_);
v___x_1019_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__21));
v___x_1020_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1020_, 0, v_a_996_);
lean_ctor_set(v___x_1020_, 1, v___x_1016_);
lean_ctor_set(v___x_1020_, 2, v___x_1018_);
lean_ctor_set(v___x_1020_, 3, v___x_1019_);
v___x_1021_ = l_Lean_Syntax_node1(v_a_996_, v___x_1015_, v___x_1020_);
v___x_1022_ = l_Lean_Syntax_node2(v_a_996_, v___x_1012_, v___x_1014_, v___x_1021_);
v___x_1023_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15));
v___x_1024_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1024_, 0, v_a_996_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
lean_inc_ref(v___x_1024_);
lean_inc_n(v_discr_874_, 2);
lean_inc(v___x_1022_);
v___x_1025_ = l_Lean_Syntax_node3(v_a_996_, v___x_1011_, v___x_1022_, v_discr_874_, v___x_1024_);
v___x_1026_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__7));
v___x_1027_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1027_, 0, v_a_996_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
v___x_1028_ = lean_obj_once(&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__11, &l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__11_once, _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__11);
v___x_1029_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__12));
v___x_1030_ = l_Lean_addMacroScope(v_quotContext_897_, v___x_1029_, v_currMacroScope_898_);
v___x_1031_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1031_, 0, v_a_996_);
lean_ctor_set(v___x_1031_, 1, v___x_1028_);
lean_ctor_set(v___x_1031_, 2, v___x_1030_);
lean_ctor_set(v___x_1031_, 3, v___x_906_);
v___x_1032_ = l_Lean_Syntax_node3(v_a_996_, v___x_1010_, v___x_1025_, v___x_1027_, v___x_1031_);
v___x_1033_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__13));
v___x_1034_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1034_, 0, v_a_996_);
lean_ctor_set(v___x_1034_, 1, v___x_1033_);
v___x_1035_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__13));
v___x_1036_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__14));
v___x_1037_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1037_, 0, v_a_996_);
lean_ctor_set(v___x_1037_, 1, v___x_1035_);
v___x_1038_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__16));
v___x_1039_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4));
v___x_1040_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
v___x_1041_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1041_, 0, v_a_996_);
lean_ctor_set(v___x_1041_, 1, v___x_1039_);
lean_ctor_set(v___x_1041_, 2, v___x_1040_);
lean_inc_ref_n(v___x_1041_, 5);
v___x_1042_ = l_Lean_Syntax_node1(v_a_996_, v___x_1038_, v___x_1041_);
v___x_1043_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18));
v___x_1044_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20));
v___x_1045_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22));
v___x_1046_ = lean_obj_once(&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__33, &l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__33_once, _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__33);
v___x_1047_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__34));
v___x_1048_ = l_Lean_addMacroScope(v_quotContext_897_, v___x_1047_, v_currMacroScope_898_);
v___x_1049_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1049_, 0, v_a_996_);
lean_ctor_set(v___x_1049_, 1, v___x_1046_);
lean_ctor_set(v___x_1049_, 2, v___x_1048_);
lean_ctor_set(v___x_1049_, 3, v___x_906_);
v___x_1050_ = l_Lean_Syntax_node1(v_a_996_, v___x_1045_, v___x_1049_);
v___x_1051_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__23));
v___x_1052_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1052_, 0, v_a_996_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2));
v___x_1054_ = lean_obj_once(&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__36, &l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__36_once, _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__36);
v___x_1055_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__38));
v___x_1056_ = l_Lean_addMacroScope(v_quotContext_897_, v___x_1055_, v_currMacroScope_898_);
v___x_1057_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__43));
v___x_1058_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1058_, 0, v_a_996_);
lean_ctor_set(v___x_1058_, 1, v___x_1054_);
lean_ctor_set(v___x_1058_, 2, v___x_1056_);
lean_ctor_set(v___x_1058_, 3, v___x_1057_);
v___x_1059_ = l_Lean_Syntax_node2(v_a_996_, v___x_1039_, v_discr_874_, v___x_1006_);
lean_inc(v___x_1059_);
v___x_1060_ = l_Lean_Syntax_node2(v_a_996_, v___x_1053_, v___x_1058_, v___x_1059_);
lean_inc_ref(v___x_1052_);
v___x_1061_ = l_Lean_Syntax_node5(v_a_996_, v___x_1044_, v___x_1050_, v___x_1041_, v___x_1041_, v___x_1052_, v___x_1060_);
v___x_1062_ = l_Lean_Syntax_node1(v_a_996_, v___x_1043_, v___x_1061_);
v___x_1063_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__31));
v___x_1064_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1064_, 0, v_a_996_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
v___x_1065_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1065_, 0, v_a_996_);
lean_ctor_set(v___x_1065_, 1, v___x_903_);
lean_ctor_set(v___x_1065_, 2, v___x_905_);
lean_ctor_set(v___x_1065_, 3, v___x_906_);
v___x_1066_ = l_Lean_Syntax_node1(v_a_996_, v___x_1045_, v___x_1065_);
v___x_1067_ = lean_obj_once(&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__25, &l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__25_once, _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__25);
v___x_1068_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__27));
v___x_1069_ = l_Lean_addMacroScope(v_quotContext_897_, v___x_1068_, v_currMacroScope_898_);
v___x_1070_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__30));
v___x_1071_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1071_, 0, v_a_996_);
lean_ctor_set(v___x_1071_, 1, v___x_1067_);
lean_ctor_set(v___x_1071_, 2, v___x_1069_);
lean_ctor_set(v___x_1071_, 3, v___x_1070_);
v___x_1072_ = l_Lean_Syntax_node2(v_a_996_, v___x_1053_, v___x_1071_, v___x_1059_);
v___x_1073_ = l_Lean_Syntax_node5(v_a_996_, v___x_1044_, v___x_1066_, v___x_1041_, v___x_1041_, v___x_1052_, v___x_1072_);
v___x_1074_ = l_Lean_Syntax_node1(v_a_996_, v___x_1043_, v___x_1073_);
lean_inc_ref(v___x_1064_);
lean_inc(v___x_1042_);
lean_inc_ref(v___x_1037_);
v___x_1075_ = l_Lean_Syntax_node5(v_a_996_, v___x_1036_, v___x_1037_, v___x_1042_, v___x_1074_, v___x_1064_, v_a_990_);
v___x_1076_ = l_Lean_Syntax_node5(v_a_996_, v___x_1036_, v___x_1037_, v___x_1042_, v___x_1062_, v___x_1064_, v___x_1075_);
v___x_1077_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__14));
v___x_1078_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1078_, 0, v_a_996_);
lean_ctor_set(v___x_1078_, 1, v___x_1077_);
v___x_1079_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__1));
v___x_1080_ = l_Lean_Syntax_node3(v_a_996_, v___x_1079_, v___x_1022_, v___x_1041_, v___x_1024_);
v___x_1081_ = l_Lean_Syntax_node1(v_a_996_, v___x_1039_, v___x_1080_);
v___x_1082_ = l_Lean_Syntax_node2(v_a_996_, v___x_1053_, v_kElse_873_, v___x_1081_);
v___x_1083_ = l_Lean_Syntax_node8(v_a_996_, v___x_998_, v___x_1001_, v___x_1007_, v___x_1009_, v___x_1032_, v___x_1034_, v___x_1076_, v___x_1078_, v___x_1082_);
v___x_1084_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg(v_alts_875_, v_discr_874_, v_funNamesToMatch_889_, v___x_1083_, v___y_893_, v_a_997_);
lean_dec_ref(v___y_893_);
lean_dec(v_funNamesToMatch_889_);
lean_dec(v_alts_875_);
return v___x_1084_;
}
}
else
{
lean_object* v_a_1086_; lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
lean_del_object(v___x_993_);
lean_dec(v_a_990_);
lean_dec(v___x_905_);
lean_dec_ref(v___y_893_);
lean_dec(v_funNamesToMatch_889_);
lean_dec(v_alts_875_);
lean_dec(v_discr_874_);
lean_dec(v_kElse_873_);
v_a_1086_ = lean_ctor_get(v___x_995_, 0);
v_a_1087_ = lean_ctor_get(v___x_995_, 1);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_995_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_inc(v_a_1086_);
lean_dec(v___x_995_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1086_);
lean_ctor_set(v_reuseFailAlloc_1093_, 1, v_a_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
}
}
else
{
lean_dec(v___x_905_);
lean_dec_ref(v___y_893_);
lean_dec(v_funNamesToMatch_889_);
lean_dec(v_alts_875_);
lean_dec(v_discr_874_);
lean_dec(v_kElse_873_);
return v___x_908_;
}
}
else
{
lean_object* v_a_1096_; lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
lean_dec(v_altsNext_895_);
lean_dec_ref(v___y_893_);
lean_dec(v_funNamesToMatch_889_);
lean_dec(v_alts_875_);
lean_dec(v_discr_874_);
lean_dec(v_kElse_873_);
v_a_1096_ = lean_ctor_get(v___x_900_, 0);
v_a_1097_ = lean_ctor_get(v___x_900_, 1);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_900_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_inc(v_a_1096_);
lean_dec(v___x_900_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1096_);
lean_ctor_set(v_reuseFailAlloc_1103_, 1, v_a_1097_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
else
{
lean_object* v_quotContext_1105_; lean_object* v_currMacroScope_1106_; lean_object* v_ref_1107_; uint8_t v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
lean_dec(v_altsNext_895_);
v_quotContext_1105_ = lean_ctor_get(v___y_893_, 1);
v_currMacroScope_1106_ = lean_ctor_get(v___y_893_, 2);
v_ref_1107_ = lean_ctor_get(v___y_893_, 5);
v___x_1108_ = 0;
v___x_1109_ = l_Lean_SourceInfo_fromRef(v_ref_1107_, v___x_1108_);
v___x_1110_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2));
v___x_1111_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4));
v___x_1112_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__1));
v___x_1113_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__3));
v___x_1114_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2));
lean_inc_n(v___x_1109_, 8);
v___x_1115_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1109_);
lean_ctor_set(v___x_1115_, 1, v___x_1114_);
v___x_1116_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__5));
v___x_1117_ = lean_obj_once(&l_Lean_Elab_Term_MatchExpr_getActuals___closed__7, &l_Lean_Elab_Term_MatchExpr_getActuals___closed__7_once, _init_l_Lean_Elab_Term_MatchExpr_getActuals___closed__7);
v___x_1118_ = lean_box(0);
lean_inc(v_currMacroScope_1106_);
lean_inc(v_quotContext_1105_);
v___x_1119_ = l_Lean_addMacroScope(v_quotContext_1105_, v___x_1118_, v_currMacroScope_1106_);
v___x_1120_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__21));
v___x_1121_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1109_);
lean_ctor_set(v___x_1121_, 1, v___x_1117_);
lean_ctor_set(v___x_1121_, 2, v___x_1119_);
lean_ctor_set(v___x_1121_, 3, v___x_1120_);
v___x_1122_ = l_Lean_Syntax_node1(v___x_1109_, v___x_1116_, v___x_1121_);
v___x_1123_ = l_Lean_Syntax_node2(v___x_1109_, v___x_1113_, v___x_1115_, v___x_1122_);
v___x_1124_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
v___x_1125_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1109_);
lean_ctor_set(v___x_1125_, 1, v___x_1111_);
lean_ctor_set(v___x_1125_, 2, v___x_1124_);
v___x_1126_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15));
v___x_1127_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1109_);
lean_ctor_set(v___x_1127_, 1, v___x_1126_);
v___x_1128_ = l_Lean_Syntax_node3(v___x_1109_, v___x_1112_, v___x_1123_, v___x_1125_, v___x_1127_);
v___x_1129_ = l_Lean_Syntax_node1(v___x_1109_, v___x_1111_, v___x_1128_);
v___x_1130_ = l_Lean_Syntax_node2(v___x_1109_, v___x_1110_, v_kElse_873_, v___x_1129_);
v___x_1131_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg(v_alts_875_, v_discr_874_, v_funNamesToMatch_889_, v___x_1130_, v___y_893_, v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec(v_funNamesToMatch_889_);
lean_dec(v_alts_875_);
return v___x_1131_;
}
}
v_reusejp_1134_:
{
lean_object* v___x_1136_; 
lean_inc(v_ref_888_);
lean_inc(v_maxRecDepth_887_);
lean_inc(v_currRecDepth_886_);
lean_inc(v_macroScope_878_);
lean_inc(v_quotContext_885_);
lean_inc(v_methods_884_);
v___x_1136_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1136_, 0, v_methods_884_);
lean_ctor_set(v___x_1136_, 1, v_quotContext_885_);
lean_ctor_set(v___x_1136_, 2, v_macroScope_878_);
lean_ctor_set(v___x_1136_, 3, v_currRecDepth_886_);
lean_ctor_set(v___x_1136_, 4, v_maxRecDepth_887_);
lean_ctor_set(v___x_1136_, 5, v_ref_888_);
if (v_saveActual_890_ == 0)
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
lean_dec(v_macroScope_878_);
v___x_1137_ = l_Lean_SourceInfo_fromRef(v_ref_888_, v_saveActual_890_);
v___x_1138_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1));
v___x_1139_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getParams___closed__0));
lean_inc(v___x_1137_);
v___x_1140_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1137_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
v___x_1141_ = l_Lean_Syntax_node1(v___x_1137_, v___x_1138_, v___x_1140_);
v_actual_892_ = v___x_1141_;
v___y_893_ = v___x_1136_;
v___y_894_ = v___x_1135_;
goto v___jp_891_;
}
else
{
uint8_t v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1142_ = 0;
v___x_1143_ = l_Lean_SourceInfo_fromRef(v_ref_888_, v___x_1142_);
v___x_1144_ = lean_obj_once(&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__33, &l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__33_once, _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__33);
v___x_1145_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__34));
lean_inc(v_quotContext_885_);
v___x_1146_ = l_Lean_addMacroScope(v_quotContext_885_, v___x_1145_, v_macroScope_878_);
v___x_1147_ = lean_box(0);
v___x_1148_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1143_);
lean_ctor_set(v___x_1148_, 1, v___x_1144_);
lean_ctor_set(v___x_1148_, 2, v___x_1146_);
lean_ctor_set(v___x_1148_, 3, v___x_1147_);
v_actual_892_ = v___x_1148_;
v___y_893_ = v___x_1136_;
v___y_894_ = v___x_1135_;
goto v___jp_891_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___boxed(lean_object* v_kElse_1151_, lean_object* v_discr_1152_, lean_object* v_alts_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop(v_kElse_1151_, v_discr_1152_, v_alts_1153_, v_a_1154_, v_a_1155_);
lean_dec_ref(v_a_1154_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0(lean_object* v_alts_1157_, lean_object* v_discr_1158_, lean_object* v_as_1159_, lean_object* v_as_x27_1160_, lean_object* v_b_1161_, lean_object* v_a_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v___x_1165_; 
v___x_1165_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg(v_alts_1157_, v_discr_1158_, v_as_x27_1160_, v_b_1161_, v___y_1163_, v___y_1164_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___boxed(lean_object* v_alts_1166_, lean_object* v_discr_1167_, lean_object* v_as_1168_, lean_object* v_as_x27_1169_, lean_object* v_b_1170_, lean_object* v_a_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0(v_alts_1166_, v_discr_1167_, v_as_1168_, v_as_x27_1169_, v_b_1170_, v_a_1171_, v___y_1172_, v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v_as_x27_1169_);
lean_dec(v_as_1168_);
lean_dec(v_alts_1166_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_generate___lam__0(lean_object* v_____do__lift_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
uint8_t v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1178_ = 0;
v___x_1179_ = l_Lean_SourceInfo_fromRef(v_____do__lift_1175_, v___x_1178_);
v___x_1180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
lean_ctor_set(v___x_1180_, 1, v___y_1177_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_generate___lam__0___boxed(lean_object* v_____do__lift_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Lean_Elab_Term_MatchExpr_generate___lam__0(v_____do__lift_1181_, v___y_1182_, v___y_1183_);
lean_dec_ref(v___y_1182_);
lean_dec(v_____do__lift_1181_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg(lean_object* v_as_x27_1191_, lean_object* v_b_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
if (lean_obj_tag(v_as_x27_1191_) == 0)
{
lean_object* v___x_1195_; 
v___x_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1195_, 0, v_b_1192_);
lean_ctor_set(v___x_1195_, 1, v___y_1194_);
return v___x_1195_;
}
else
{
lean_object* v_head_1196_; lean_object* v_tail_1197_; lean_object* v___x_1198_; 
v_head_1196_ = lean_ctor_get(v_as_x27_1191_, 0);
v_tail_1197_ = lean_ctor_get(v_as_x27_1191_, 1);
lean_inc(v_head_1196_);
v___x_1198_ = l_Lean_Elab_Term_MatchExpr_getParams(v_head_1196_, v___y_1193_, v___y_1194_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_a_1199_; lean_object* v_a_1200_; lean_object* v_ref_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v_rhs_1205_; lean_object* v_k_1206_; lean_object* v___x_1207_; uint8_t v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
lean_inc(v_a_1199_);
v_a_1200_ = lean_ctor_get(v___x_1198_, 1);
lean_inc(v_a_1200_);
lean_dec_ref_known(v___x_1198_, 2);
v_ref_1201_ = lean_ctor_get(v___y_1193_, 5);
v___x_1202_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__0));
v___x_1203_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__1));
v___x_1204_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18));
v_rhs_1205_ = lean_ctor_get(v_head_1196_, 3);
v_k_1206_ = lean_ctor_get(v_head_1196_, 4);
v___x_1207_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20));
v___x_1208_ = 0;
v___x_1209_ = l_Lean_SourceInfo_fromRef(v_ref_1201_, v___x_1208_);
lean_inc_n(v___x_1209_, 8);
v___x_1210_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1209_);
lean_ctor_set(v___x_1210_, 1, v___x_1202_);
v___x_1211_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22));
lean_inc(v_k_1206_);
v___x_1212_ = l_Lean_Syntax_node1(v___x_1209_, v___x_1211_, v_k_1206_);
v___x_1213_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4));
v___x_1214_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
v___x_1215_ = l_Array_append___redArg(v___x_1214_, v_a_1199_);
lean_dec(v_a_1199_);
v___x_1216_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1209_);
lean_ctor_set(v___x_1216_, 1, v___x_1213_);
lean_ctor_set(v___x_1216_, 2, v___x_1215_);
v___x_1217_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1209_);
lean_ctor_set(v___x_1217_, 1, v___x_1213_);
lean_ctor_set(v___x_1217_, 2, v___x_1214_);
v___x_1218_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__23));
v___x_1219_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1209_);
lean_ctor_set(v___x_1219_, 1, v___x_1218_);
lean_inc(v_rhs_1205_);
v___x_1220_ = l_Lean_Syntax_node5(v___x_1209_, v___x_1207_, v___x_1212_, v___x_1216_, v___x_1217_, v___x_1219_, v_rhs_1205_);
v___x_1221_ = l_Lean_Syntax_node1(v___x_1209_, v___x_1204_, v___x_1220_);
v___x_1222_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__31));
v___x_1223_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1209_);
lean_ctor_set(v___x_1223_, 1, v___x_1222_);
v___x_1224_ = l_Lean_Syntax_node4(v___x_1209_, v___x_1203_, v___x_1210_, v___x_1221_, v___x_1223_, v_b_1192_);
v_as_x27_1191_ = v_tail_1197_;
v_b_1192_ = v___x_1224_;
v___y_1194_ = v_a_1200_;
goto _start;
}
else
{
lean_object* v_a_1226_; lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1234_; 
lean_dec(v_b_1192_);
v_a_1226_ = lean_ctor_get(v___x_1198_, 0);
v_a_1227_ = lean_ctor_get(v___x_1198_, 1);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1229_ = v___x_1198_;
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_inc(v_a_1226_);
lean_dec(v___x_1198_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
if (v_isShared_1230_ == 0)
{
v___x_1232_ = v___x_1229_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1226_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v_a_1227_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___boxed(lean_object* v_as_x27_1235_, lean_object* v_b_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg(v_as_x27_1235_, v_b_1236_, v___y_1237_, v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec(v_as_x27_1235_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__0(lean_object* v_x_1240_, lean_object* v_x_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
if (lean_obj_tag(v_x_1240_) == 0)
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = l_List_reverse___redArg(v_x_1241_);
v___x_1245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1244_);
lean_ctor_set(v___x_1245_, 1, v___y_1243_);
return v___x_1245_;
}
else
{
lean_object* v_head_1246_; lean_object* v_tail_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1258_; 
v_head_1246_ = lean_ctor_get(v_x_1240_, 0);
v_tail_1247_ = lean_ctor_get(v_x_1240_, 1);
v_isSharedCheck_1258_ = !lean_is_exclusive(v_x_1240_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1249_ = v_x_1240_;
v_isShared_1250_ = v_isSharedCheck_1258_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_tail_1247_);
lean_inc(v_head_1246_);
lean_dec(v_x_1240_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1258_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1251_; lean_object* v_a_1252_; lean_object* v_a_1253_; lean_object* v___x_1255_; 
v___x_1251_ = l_Lean_Elab_Term_MatchExpr_initK(v_head_1246_, v___y_1242_, v___y_1243_);
v_a_1252_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_a_1252_);
v_a_1253_ = lean_ctor_get(v___x_1251_, 1);
lean_inc(v_a_1253_);
lean_dec_ref(v___x_1251_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 1, v_x_1241_);
lean_ctor_set(v___x_1249_, 0, v_a_1252_);
v___x_1255_ = v___x_1249_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_a_1252_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v_x_1241_);
v___x_1255_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
v_x_1240_ = v_tail_1247_;
v_x_1241_ = v___x_1255_;
v___y_1243_ = v_a_1253_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__0___boxed(lean_object* v_x_1259_, lean_object* v_x_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__0(v_x_1259_, v_x_1260_, v___y_1261_, v___y_1262_);
lean_dec_ref(v___y_1261_);
return v_res_1263_;
}
}
static lean_object* _init_l_Lean_Elab_Term_MatchExpr_generate___closed__4(void){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1274_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_generate___closed__3));
v___x_1275_ = l_String_toRawSubstring_x27(v___x_1274_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_generate(lean_object* v_discr_1290_, lean_object* v_alts_1291_, lean_object* v_elseAlt_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = lean_box(0);
v___x_1296_ = l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__0(v_alts_1291_, v___x_1295_, v_a_1293_, v_a_1294_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; lean_object* v_a_1298_; lean_object* v_quotContext_1299_; lean_object* v_currMacroScope_1300_; lean_object* v_ref_1301_; lean_object* v___x_1302_; lean_object* v_a_1303_; lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1423_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc(v_a_1297_);
v_a_1298_ = lean_ctor_get(v___x_1296_, 1);
lean_inc(v_a_1298_);
lean_dec_ref_known(v___x_1296_, 2);
v_quotContext_1299_ = lean_ctor_get(v_a_1293_, 1);
v_currMacroScope_1300_ = lean_ctor_get(v_a_1293_, 2);
v_ref_1301_ = lean_ctor_get(v_a_1293_, 5);
v___x_1302_ = l_Lean_Elab_Term_MatchExpr_generate___lam__0(v_ref_1301_, v_a_1293_, v_a_1298_);
v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
v_a_1304_ = lean_ctor_get(v___x_1302_, 1);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1306_ = v___x_1302_;
v_isShared_1307_ = v_isSharedCheck_1423_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_inc(v_a_1303_);
lean_dec(v___x_1302_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1423_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1308_; lean_object* v_a_1309_; lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1422_; 
v___x_1308_ = l_Lean_Elab_Term_MatchExpr_generate___lam__0(v_ref_1301_, v_a_1293_, v_a_1304_);
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
v_a_1310_ = lean_ctor_get(v___x_1308_, 1);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1312_ = v___x_1308_;
v_isShared_1313_ = v_isSharedCheck_1422_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_inc(v_a_1309_);
lean_dec(v___x_1308_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1422_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1314_ = lean_obj_once(&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__1, &l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__1_once, _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__1);
v___x_1315_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__2));
lean_inc_n(v_currMacroScope_1300_, 2);
lean_inc_n(v_quotContext_1299_, 2);
v___x_1316_ = l_Lean_addMacroScope(v_quotContext_1299_, v___x_1315_, v_currMacroScope_1300_);
lean_inc(v___x_1316_);
v___x_1317_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1317_, 0, v_a_1303_);
lean_ctor_set(v___x_1317_, 1, v___x_1314_);
lean_ctor_set(v___x_1317_, 2, v___x_1316_);
lean_ctor_set(v___x_1317_, 3, v___x_1295_);
v___x_1318_ = lean_obj_once(&l_Lean_Elab_Term_MatchExpr_initK___closed__1, &l_Lean_Elab_Term_MatchExpr_initK___closed__1_once, _init_l_Lean_Elab_Term_MatchExpr_initK___closed__1);
v___x_1319_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_initK___closed__2));
v___x_1320_ = l_Lean_addMacroScope(v_quotContext_1299_, v___x_1319_, v_currMacroScope_1300_);
lean_inc(v___x_1320_);
v___x_1321_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1321_, 0, v_a_1309_);
lean_ctor_set(v___x_1321_, 1, v___x_1318_);
lean_ctor_set(v___x_1321_, 2, v___x_1320_);
lean_ctor_set(v___x_1321_, 3, v___x_1295_);
lean_inc(v_a_1297_);
v___x_1322_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop(v___x_1321_, v___x_1317_, v_a_1297_, v_a_1293_, v_a_1310_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_object* v_a_1323_; lean_object* v_a_1324_; lean_object* v___x_1325_; lean_object* v_a_1326_; lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1412_; 
v_a_1323_ = lean_ctor_get(v___x_1322_, 0);
lean_inc(v_a_1323_);
v_a_1324_ = lean_ctor_get(v___x_1322_, 1);
lean_inc(v_a_1324_);
lean_dec_ref_known(v___x_1322_, 2);
v___x_1325_ = l_Lean_Elab_Term_MatchExpr_generate___lam__0(v_ref_1301_, v_a_1293_, v_a_1324_);
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
v_a_1327_ = lean_ctor_get(v___x_1325_, 1);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1329_ = v___x_1325_;
v_isShared_1330_ = v_isSharedCheck_1412_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_inc(v_a_1326_);
lean_dec(v___x_1325_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1412_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1334_; 
v___x_1331_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__0));
v___x_1332_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__1));
lean_inc(v_a_1326_);
if (v_isShared_1330_ == 0)
{
lean_ctor_set_tag(v___x_1329_, 2);
lean_ctor_set(v___x_1329_, 1, v___x_1331_);
v___x_1334_ = v___x_1329_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1326_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v___x_1331_);
v___x_1334_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1344_; 
v___x_1335_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18));
v___x_1336_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20));
v___x_1337_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22));
lean_inc_n(v_a_1326_, 3);
v___x_1338_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1338_, 0, v_a_1326_);
lean_ctor_set(v___x_1338_, 1, v___x_1318_);
lean_ctor_set(v___x_1338_, 2, v___x_1320_);
lean_ctor_set(v___x_1338_, 3, v___x_1295_);
v___x_1339_ = l_Lean_Syntax_node1(v_a_1326_, v___x_1337_, v___x_1338_);
v___x_1340_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4));
v___x_1341_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1));
v___x_1342_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2));
if (v_isShared_1313_ == 0)
{
lean_ctor_set_tag(v___x_1312_, 2);
lean_ctor_set(v___x_1312_, 1, v___x_1342_);
lean_ctor_set(v___x_1312_, 0, v_a_1326_);
v___x_1344_ = v___x_1312_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_a_1326_);
lean_ctor_set(v_reuseFailAlloc_1410_, 1, v___x_1342_);
v___x_1344_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1348_; 
v___x_1345_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1));
v___x_1346_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getParams___closed__0));
lean_inc(v_a_1326_);
if (v_isShared_1307_ == 0)
{
lean_ctor_set_tag(v___x_1306_, 2);
lean_ctor_set(v___x_1306_, 1, v___x_1346_);
lean_ctor_set(v___x_1306_, 0, v_a_1326_);
v___x_1348_ = v___x_1306_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_a_1326_);
lean_ctor_set(v_reuseFailAlloc_1409_, 1, v___x_1346_);
v___x_1348_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
lean_inc_n(v_a_1326_, 23);
v___x_1349_ = l_Lean_Syntax_node1(v_a_1326_, v___x_1345_, v___x_1348_);
v___x_1350_ = l_Lean_Syntax_node1(v_a_1326_, v___x_1340_, v___x_1349_);
v___x_1351_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__5));
v___x_1352_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1352_, 0, v_a_1326_);
lean_ctor_set(v___x_1352_, 1, v___x_1351_);
v___x_1353_ = lean_obj_once(&l_Lean_Elab_Term_MatchExpr_getParams___closed__2, &l_Lean_Elab_Term_MatchExpr_getParams___closed__2_once, _init_l_Lean_Elab_Term_MatchExpr_getParams___closed__2);
v___x_1354_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getParams___closed__3));
lean_inc_n(v_currMacroScope_1300_, 2);
lean_inc_n(v_quotContext_1299_, 2);
v___x_1355_ = l_Lean_addMacroScope(v_quotContext_1299_, v___x_1354_, v_currMacroScope_1300_);
v___x_1356_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_generate___closed__2));
v___x_1357_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1357_, 0, v_a_1326_);
lean_ctor_set(v___x_1357_, 1, v___x_1353_);
lean_ctor_set(v___x_1357_, 2, v___x_1355_);
lean_ctor_set(v___x_1357_, 3, v___x_1356_);
v___x_1358_ = l_Lean_Syntax_node2(v_a_1326_, v___x_1340_, v___x_1352_, v___x_1357_);
v___x_1359_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
v___x_1360_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1360_, 0, v_a_1326_);
lean_ctor_set(v___x_1360_, 1, v___x_1340_);
lean_ctor_set(v___x_1360_, 2, v___x_1359_);
v___x_1361_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15));
v___x_1362_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1362_, 0, v_a_1326_);
lean_ctor_set(v___x_1362_, 1, v___x_1361_);
lean_inc_ref_n(v___x_1360_, 4);
v___x_1363_ = l_Lean_Syntax_node5(v_a_1326_, v___x_1341_, v___x_1344_, v___x_1350_, v___x_1358_, v___x_1360_, v___x_1362_);
v___x_1364_ = l_Lean_Syntax_node1(v_a_1326_, v___x_1340_, v___x_1363_);
v___x_1365_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__23));
v___x_1366_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1366_, 0, v_a_1326_);
lean_ctor_set(v___x_1366_, 1, v___x_1365_);
lean_inc_ref(v___x_1366_);
v___x_1367_ = l_Lean_Syntax_node5(v_a_1326_, v___x_1336_, v___x_1339_, v___x_1364_, v___x_1360_, v___x_1366_, v_elseAlt_1292_);
v___x_1368_ = l_Lean_Syntax_node1(v_a_1326_, v___x_1335_, v___x_1367_);
v___x_1369_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__31));
v___x_1370_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1370_, 0, v_a_1326_);
lean_ctor_set(v___x_1370_, 1, v___x_1369_);
v___x_1371_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__13));
v___x_1372_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__14));
v___x_1373_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1373_, 0, v_a_1326_);
lean_ctor_set(v___x_1373_, 1, v___x_1371_);
v___x_1374_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__16));
v___x_1375_ = l_Lean_Syntax_node1(v_a_1326_, v___x_1374_, v___x_1360_);
v___x_1376_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1376_, 0, v_a_1326_);
lean_ctor_set(v___x_1376_, 1, v___x_1314_);
lean_ctor_set(v___x_1376_, 2, v___x_1316_);
lean_ctor_set(v___x_1376_, 3, v___x_1295_);
v___x_1377_ = l_Lean_Syntax_node1(v_a_1326_, v___x_1337_, v___x_1376_);
v___x_1378_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2));
v___x_1379_ = lean_obj_once(&l_Lean_Elab_Term_MatchExpr_generate___closed__4, &l_Lean_Elab_Term_MatchExpr_generate___closed__4_once, _init_l_Lean_Elab_Term_MatchExpr_generate___closed__4);
v___x_1380_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_generate___closed__6));
v___x_1381_ = l_Lean_addMacroScope(v_quotContext_1299_, v___x_1380_, v_currMacroScope_1300_);
v___x_1382_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_generate___closed__9));
v___x_1383_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1383_, 0, v_a_1326_);
lean_ctor_set(v___x_1383_, 1, v___x_1379_);
lean_ctor_set(v___x_1383_, 2, v___x_1381_);
lean_ctor_set(v___x_1383_, 3, v___x_1382_);
v___x_1384_ = l_Lean_Syntax_node1(v_a_1326_, v___x_1340_, v_discr_1290_);
v___x_1385_ = l_Lean_Syntax_node2(v_a_1326_, v___x_1378_, v___x_1383_, v___x_1384_);
v___x_1386_ = l_Lean_Syntax_node5(v_a_1326_, v___x_1336_, v___x_1377_, v___x_1360_, v___x_1360_, v___x_1366_, v___x_1385_);
v___x_1387_ = l_Lean_Syntax_node1(v_a_1326_, v___x_1335_, v___x_1386_);
lean_inc_ref(v___x_1370_);
v___x_1388_ = l_Lean_Syntax_node5(v_a_1326_, v___x_1372_, v___x_1373_, v___x_1375_, v___x_1387_, v___x_1370_, v_a_1323_);
v___x_1389_ = l_Lean_Syntax_node4(v_a_1326_, v___x_1332_, v___x_1334_, v___x_1368_, v___x_1370_, v___x_1388_);
v___x_1390_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg(v_a_1297_, v___x_1389_, v_a_1293_, v_a_1327_);
lean_dec(v_a_1297_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v_a_1391_; lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1399_; 
v_a_1391_ = lean_ctor_get(v___x_1390_, 0);
v_a_1392_ = lean_ctor_get(v___x_1390_, 1);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1394_ = v___x_1390_;
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_inc(v_a_1391_);
lean_dec(v___x_1390_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1397_; 
if (v_isShared_1395_ == 0)
{
v___x_1397_ = v___x_1394_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_a_1391_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v_a_1392_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
else
{
lean_object* v_a_1400_; lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1408_; 
v_a_1400_ = lean_ctor_get(v___x_1390_, 0);
v_a_1401_ = lean_ctor_get(v___x_1390_, 1);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1403_ = v___x_1390_;
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_inc(v_a_1400_);
lean_dec(v___x_1390_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1406_; 
if (v_isShared_1404_ == 0)
{
v___x_1406_ = v___x_1403_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_a_1400_);
lean_ctor_set(v_reuseFailAlloc_1407_, 1, v_a_1401_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_1413_; lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
lean_dec(v___x_1320_);
lean_dec(v___x_1316_);
lean_del_object(v___x_1312_);
lean_del_object(v___x_1306_);
lean_dec(v_a_1297_);
lean_dec(v_elseAlt_1292_);
lean_dec(v_discr_1290_);
v_a_1413_ = lean_ctor_get(v___x_1322_, 0);
v_a_1414_ = lean_ctor_get(v___x_1322_, 1);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1416_ = v___x_1322_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_inc(v_a_1413_);
lean_dec(v___x_1322_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1413_);
lean_ctor_set(v_reuseFailAlloc_1420_, 1, v_a_1414_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
}
}
else
{
lean_object* v_a_1424_; lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
lean_dec(v_elseAlt_1292_);
lean_dec(v_discr_1290_);
v_a_1424_ = lean_ctor_get(v___x_1296_, 0);
v_a_1425_ = lean_ctor_get(v___x_1296_, 1);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1296_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_inc(v_a_1424_);
lean_dec(v___x_1296_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1428_ == 0)
{
v___x_1430_ = v___x_1427_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_a_1424_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v_a_1425_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_generate___boxed(lean_object* v_discr_1433_, lean_object* v_alts_1434_, lean_object* v_elseAlt_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l_Lean_Elab_Term_MatchExpr_generate(v_discr_1433_, v_alts_1434_, v_elseAlt_1435_, v_a_1436_, v_a_1437_);
lean_dec_ref(v_a_1436_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1(lean_object* v_as_1439_, lean_object* v_as_x27_1440_, lean_object* v_b_1441_, lean_object* v_a_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg(v_as_x27_1440_, v_b_1441_, v___y_1443_, v___y_1444_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___boxed(lean_object* v_as_1446_, lean_object* v_as_x27_1447_, lean_object* v_b_1448_, lean_object* v_a_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1(v_as_1446_, v_as_x27_1447_, v_b_1448_, v_a_1449_, v___y_1450_, v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec(v_as_x27_1447_);
lean_dec(v_as_1446_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_main_spec__0(lean_object* v_x_1454_, lean_object* v_x_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
if (lean_obj_tag(v_x_1454_) == 0)
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1458_ = l_List_reverse___redArg(v_x_1455_);
v___x_1459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1458_);
lean_ctor_set(v___x_1459_, 1, v___y_1457_);
return v___x_1459_;
}
else
{
lean_object* v_head_1460_; lean_object* v_tail_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1487_; 
v_head_1460_ = lean_ctor_get(v_x_1454_, 0);
v_tail_1461_ = lean_ctor_get(v_x_1454_, 1);
v_isSharedCheck_1487_ = !lean_is_exclusive(v_x_1454_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1463_ = v_x_1454_;
v_isShared_1464_ = v_isSharedCheck_1487_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_tail_1461_);
lean_inc(v_head_1460_);
lean_dec(v_x_1454_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1487_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v_a_1466_; lean_object* v_a_1467_; lean_object* v___x_1472_; 
lean_inc(v_head_1460_);
v___x_1472_ = l_Lean_Elab_Term_MatchExpr_toAlt_x3f(v_head_1460_);
if (lean_obj_tag(v___x_1472_) == 1)
{
lean_object* v_val_1473_; 
lean_dec(v_head_1460_);
v_val_1473_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_val_1473_);
lean_dec_ref_known(v___x_1472_, 1);
v_a_1466_ = v_val_1473_;
v_a_1467_ = v___y_1457_;
goto v___jp_1465_;
}
else
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
lean_dec(v___x_1472_);
v___x_1474_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_main_spec__0___closed__0));
v___x_1475_ = l_Lean_Macro_throwErrorAt___redArg(v_head_1460_, v___x_1474_, v___y_1456_, v___y_1457_);
lean_dec(v_head_1460_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v_a_1477_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_a_1476_);
v_a_1477_ = lean_ctor_get(v___x_1475_, 1);
lean_inc(v_a_1477_);
lean_dec_ref_known(v___x_1475_, 2);
v_a_1466_ = v_a_1476_;
v_a_1467_ = v_a_1477_;
goto v___jp_1465_;
}
else
{
lean_object* v_a_1478_; lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1486_; 
lean_del_object(v___x_1463_);
lean_dec(v_tail_1461_);
lean_dec(v_x_1455_);
v_a_1478_ = lean_ctor_get(v___x_1475_, 0);
v_a_1479_ = lean_ctor_get(v___x_1475_, 1);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1481_ = v___x_1475_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_inc(v_a_1478_);
lean_dec(v___x_1475_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_a_1478_);
lean_ctor_set(v_reuseFailAlloc_1485_, 1, v_a_1479_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
v___jp_1465_:
{
lean_object* v___x_1469_; 
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 1, v_x_1455_);
lean_ctor_set(v___x_1463_, 0, v_a_1466_);
v___x_1469_ = v___x_1463_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_a_1466_);
lean_ctor_set(v_reuseFailAlloc_1471_, 1, v_x_1455_);
v___x_1469_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
v_x_1454_ = v_tail_1461_;
v_x_1455_ = v___x_1469_;
v___y_1457_ = v_a_1467_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_main_spec__0___boxed(lean_object* v_x_1488_, lean_object* v_x_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_main_spec__0(v_x_1488_, v_x_1489_, v___y_1490_, v___y_1491_);
lean_dec_ref(v___y_1490_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_main(lean_object* v_discr_1494_, lean_object* v_alts_1495_, lean_object* v_elseAlt_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_){
_start:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1499_ = lean_array_to_list(v_alts_1495_);
v___x_1500_ = lean_box(0);
v___x_1501_ = l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_main_spec__0(v___x_1499_, v___x_1500_, v_a_1497_, v_a_1498_);
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_object* v_a_1502_; lean_object* v_a_1503_; lean_object* v___x_1504_; 
v_a_1502_ = lean_ctor_get(v___x_1501_, 0);
lean_inc(v_a_1502_);
v_a_1503_ = lean_ctor_get(v___x_1501_, 1);
lean_inc(v_a_1503_);
lean_dec_ref_known(v___x_1501_, 2);
lean_inc(v_elseAlt_1496_);
v___x_1504_ = l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f(v_elseAlt_1496_);
if (lean_obj_tag(v___x_1504_) == 1)
{
lean_object* v_val_1505_; lean_object* v___x_1506_; 
lean_dec(v_elseAlt_1496_);
v_val_1505_ = lean_ctor_get(v___x_1504_, 0);
lean_inc(v_val_1505_);
lean_dec_ref_known(v___x_1504_, 1);
v___x_1506_ = l_Lean_Elab_Term_MatchExpr_generate(v_discr_1494_, v_a_1502_, v_val_1505_, v_a_1497_, v_a_1503_);
return v___x_1506_;
}
else
{
lean_object* v___x_1507_; lean_object* v___x_1508_; 
lean_dec(v___x_1504_);
lean_dec(v_a_1502_);
lean_dec(v_discr_1494_);
v___x_1507_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_main___closed__0));
v___x_1508_ = l_Lean_Macro_throwErrorAt___redArg(v_elseAlt_1496_, v___x_1507_, v_a_1497_, v_a_1503_);
lean_dec(v_elseAlt_1496_);
return v___x_1508_;
}
}
else
{
lean_object* v_a_1509_; lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1517_; 
lean_dec(v_elseAlt_1496_);
lean_dec(v_discr_1494_);
v_a_1509_ = lean_ctor_get(v___x_1501_, 0);
v_a_1510_ = lean_ctor_get(v___x_1501_, 1);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1512_ = v___x_1501_;
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_inc(v_a_1509_);
lean_dec(v___x_1501_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1513_ == 0)
{
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1509_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v_a_1510_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_main___boxed(lean_object* v_discr_1518_, lean_object* v_alts_1519_, lean_object* v_elseAlt_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_Lean_Elab_Term_MatchExpr_main(v_discr_1518_, v_alts_1519_, v_elseAlt_1520_, v_a_1521_, v_a_1522_);
lean_dec_ref(v_a_1521_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchExpr(lean_object* v_stx_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_){
_start:
{
lean_object* v___x_1533_; uint8_t v___x_1534_; 
v___x_1533_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchExpr___closed__1));
lean_inc(v_stx_1530_);
v___x_1534_ = l_Lean_Syntax_isOfKind(v_stx_1530_, v___x_1533_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; 
lean_dec(v_stx_1530_);
v___x_1535_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1532_);
return v___x_1535_;
}
else
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v_discr_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1536_ = lean_unsigned_to_nat(0u);
v___x_1537_ = lean_unsigned_to_nat(1u);
v_discr_1538_ = l_Lean_Syntax_getArg(v_stx_1530_, v___x_1537_);
v___x_1539_ = lean_unsigned_to_nat(3u);
v___x_1540_ = l_Lean_Syntax_getArg(v_stx_1530_, v___x_1539_);
lean_dec(v_stx_1530_);
v___x_1541_ = l_Lean_Syntax_getArg(v___x_1540_, v___x_1536_);
v___x_1542_ = l_Lean_Syntax_getArgs(v___x_1541_);
lean_dec(v___x_1541_);
v___x_1543_ = l_Lean_Syntax_getArg(v___x_1540_, v___x_1537_);
lean_dec(v___x_1540_);
v___x_1544_ = l_Lean_Elab_Term_MatchExpr_main(v_discr_1538_, v___x_1542_, v___x_1543_, v_a_1531_, v_a_1532_);
return v___x_1544_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchExpr___boxed(lean_object* v_stx_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_){
_start:
{
lean_object* v_res_1548_; 
v_res_1548_ = l_Lean_Elab_Term_expandMatchExpr(v_stx_1545_, v_a_1546_, v_a_1547_);
lean_dec_ref(v_a_1546_);
return v_res_1548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1(){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1556_ = l_Lean_Elab_macroAttribute;
v___x_1557_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchExpr___closed__1));
v___x_1558_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1));
v___x_1559_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandMatchExpr___boxed), 3, 0);
v___x_1560_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1556_, v___x_1557_, v___x_1558_, v___x_1559_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___boxed(lean_object* v_a_1561_){
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1();
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3(){
_start:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1589_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1));
v___x_1590_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__6));
v___x_1591_ = l_Lean_addBuiltinDeclarationRanges(v___x_1589_, v___x_1590_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___boxed(lean_object* v_a_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3();
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandLetExpr(lean_object* v_stx_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_){
_start:
{
lean_object* v___x_1613_; uint8_t v___x_1614_; 
v___x_1613_ = ((lean_object*)(l_Lean_Elab_Term_expandLetExpr___closed__1));
lean_inc(v_stx_1610_);
v___x_1614_ = l_Lean_Syntax_isOfKind(v_stx_1610_, v___x_1613_);
if (v___x_1614_ == 0)
{
lean_object* v___x_1615_; 
lean_dec(v_stx_1610_);
v___x_1615_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1612_);
return v___x_1615_;
}
else
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; uint8_t v___x_1619_; 
v___x_1616_ = lean_unsigned_to_nat(1u);
v___x_1617_ = l_Lean_Syntax_getArg(v_stx_1610_, v___x_1616_);
v___x_1618_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__5));
lean_inc(v___x_1617_);
v___x_1619_ = l_Lean_Syntax_isOfKind(v___x_1617_, v___x_1618_);
if (v___x_1619_ == 0)
{
lean_object* v___x_1620_; 
lean_dec(v___x_1617_);
lean_dec(v_stx_1610_);
v___x_1620_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1612_);
return v___x_1620_;
}
else
{
lean_object* v_ref_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; uint8_t v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v_ref_1621_ = lean_ctor_get(v_a_1611_, 5);
v___x_1622_ = lean_unsigned_to_nat(3u);
v___x_1623_ = l_Lean_Syntax_getArg(v_stx_1610_, v___x_1622_);
v___x_1624_ = lean_unsigned_to_nat(5u);
v___x_1625_ = l_Lean_Syntax_getArg(v_stx_1610_, v___x_1624_);
v___x_1626_ = lean_unsigned_to_nat(7u);
v___x_1627_ = l_Lean_Syntax_getArg(v_stx_1610_, v___x_1626_);
lean_dec(v_stx_1610_);
v___x_1628_ = 0;
v___x_1629_ = l_Lean_SourceInfo_fromRef(v_ref_1621_, v___x_1628_);
v___x_1630_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchExpr___closed__1));
v___x_1631_ = ((lean_object*)(l_Lean_Elab_Term_expandLetExpr___closed__2));
lean_inc_n(v___x_1629_, 10);
v___x_1632_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1629_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
v___x_1633_ = ((lean_object*)(l_Lean_Elab_Term_expandLetExpr___closed__3));
v___x_1634_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1629_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
v___x_1635_ = ((lean_object*)(l_Lean_Elab_Term_expandLetExpr___closed__5));
v___x_1636_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4));
v___x_1637_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__1));
v___x_1638_ = ((lean_object*)(l_Lean_Elab_Term_expandLetExpr___closed__6));
v___x_1639_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1629_);
lean_ctor_set(v___x_1639_, 1, v___x_1638_);
v___x_1640_ = ((lean_object*)(l_Lean_Elab_Term_expandLetExpr___closed__7));
v___x_1641_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1629_);
lean_ctor_set(v___x_1641_, 1, v___x_1640_);
lean_inc_ref(v___x_1641_);
lean_inc_ref(v___x_1639_);
v___x_1642_ = l_Lean_Syntax_node4(v___x_1629_, v___x_1637_, v___x_1639_, v___x_1617_, v___x_1641_, v___x_1627_);
v___x_1643_ = l_Lean_Syntax_node1(v___x_1629_, v___x_1636_, v___x_1642_);
v___x_1644_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__4));
v___x_1645_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1));
v___x_1646_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getParams___closed__0));
v___x_1647_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1629_);
lean_ctor_set(v___x_1647_, 1, v___x_1646_);
v___x_1648_ = l_Lean_Syntax_node1(v___x_1629_, v___x_1645_, v___x_1647_);
v___x_1649_ = l_Lean_Syntax_node4(v___x_1629_, v___x_1644_, v___x_1639_, v___x_1648_, v___x_1641_, v___x_1625_);
v___x_1650_ = l_Lean_Syntax_node2(v___x_1629_, v___x_1635_, v___x_1643_, v___x_1649_);
v___x_1651_ = l_Lean_Syntax_node4(v___x_1629_, v___x_1630_, v___x_1632_, v___x_1623_, v___x_1634_, v___x_1650_);
v___x_1652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1651_);
lean_ctor_set(v___x_1652_, 1, v_a_1612_);
return v___x_1652_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandLetExpr___boxed(lean_object* v_stx_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l_Lean_Elab_Term_expandLetExpr(v_stx_1653_, v_a_1654_, v_a_1655_);
lean_dec_ref(v_a_1654_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1(){
_start:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1664_ = l_Lean_Elab_macroAttribute;
v___x_1665_ = ((lean_object*)(l_Lean_Elab_Term_expandLetExpr___closed__1));
v___x_1666_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1));
v___x_1667_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandLetExpr___boxed), 3, 0);
v___x_1668_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1664_, v___x_1665_, v___x_1666_, v___x_1667_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___boxed(lean_object* v_a_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1();
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3(){
_start:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1697_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1));
v___x_1698_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__6));
v___x_1699_ = l_Lean_addBuiltinDeclarationRanges(v___x_1697_, v___x_1698_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___boxed(lean_object* v_a_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3();
return v_res_1701_;
}
}
lean_object* runtime_initialize_Lean_Elab_Term(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_MatchExpr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_MatchExpr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Term(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_MatchExpr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_MatchExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_MatchExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_MatchExpr(builtin);
}
#ifdef __cplusplus
}
#endif
