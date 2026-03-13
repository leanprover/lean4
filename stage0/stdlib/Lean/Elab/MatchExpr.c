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
lean_object* l_List_find_x3f___redArg(lean_object*, lean_object*);
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
uint8_t l_List_any___redArg(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_array_to_list(lean_object*);
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
static const lean_array_object l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch___closed__0 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Term_MatchExpr_shouldSaveActual___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_shouldSaveActual___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Elab_Term_MatchExpr_shouldSaveActual___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_MatchExpr_shouldSaveActual___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Term_MatchExpr_shouldSaveActual___closed__0 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_shouldSaveActual___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Elab_Term_MatchExpr_shouldSaveActual(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_shouldSaveActual___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Term_MatchExpr_getAltFor_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getAltFor_x3f___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getAltFor_x3f(lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__40_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__41 = (const lean_object*)&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__41_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_main_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "unexpected `match_expr` alternative"};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_main_spec__0___closed__0 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_main_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_main_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_MatchExpr_main___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "unexpected `match_expr` else-alternative"};
static const lean_object* l_Lean_Elab_Term_MatchExpr_main___closed__0 = (const lean_object*)&l_Lean_Elab_Term_MatchExpr_main___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_expandMatchExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchExpr"};
static const lean_object* l_Lean_Elab_Term_expandMatchExpr___closed__0 = (const lean_object*)&l_Lean_Elab_Term_expandMatchExpr___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_expandMatchExpr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_expandMatchExpr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandMatchExpr___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_expandMatchExpr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandMatchExpr___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_expandMatchExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandMatchExpr___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_expandMatchExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(72, 125, 75, 13, 242, 250, 162, 88)}};
static const lean_object* l_Lean_Elab_Term_expandMatchExpr___closed__1 = (const lean_object*)&l_Lean_Elab_Term_expandMatchExpr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchExpr(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "expandMatchExpr"};
static const lean_object* l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__0 = (const lean_object*)&l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__8_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(36, 0, 221, 127, 140, 97, 148, 247)}};
static const lean_object* l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1 = (const lean_object*)&l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(203) << 1) | 1)),((lean_object*)(((size_t)(44) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(207) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__0_value),((lean_object*)(((size_t)(44) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(203) << 1) | 1)),((lean_object*)(((size_t)(48) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(203) << 1) | 1)),((lean_object*)(((size_t)(63) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__3_value),((lean_object*)(((size_t)(48) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__4_value),((lean_object*)(((size_t)(63) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___boxed(lean_object*);
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
static const lean_string_object l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expandLetExpr"};
static const lean_object* l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__0 = (const lean_object*)&l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_MatchExpr_getActuals___closed__8_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(146, 223, 197, 206, 64, 44, 35, 96)}};
static const lean_object* l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1 = (const lean_object*)&l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(209) << 1) | 1)),((lean_object*)(((size_t)(42) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(215) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__0_value),((lean_object*)(((size_t)(42) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(209) << 1) | 1)),((lean_object*)(((size_t)(46) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(209) << 1) | 1)),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__3_value),((lean_object*)(((size_t)(46) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__4_value),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f(lean_object* v_stx_10_){
_start:
{
lean_object* v___x_11_; uint8_t v___x_12_; 
v___x_11_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__4));
lean_inc(v_stx_10_);
v___x_12_ = l_Lean_Syntax_isOfKind(v_stx_10_, v___x_11_);
if (v___x_12_ == 0)
{
lean_object* v___x_13_; 
lean_dec(v_stx_10_);
v___x_13_ = lean_box(0);
return v___x_13_;
}
else
{
lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_14_ = lean_unsigned_to_nat(3u);
v___x_15_ = l_Lean_Syntax_getArg(v_stx_10_, v___x_14_);
lean_dec(v_stx_10_);
v___x_16_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0(lean_object* v_a_23_, lean_object* v_a_24_){
_start:
{
if (lean_obj_tag(v_a_23_) == 0)
{
lean_object* v___x_25_; 
v___x_25_ = l_List_reverse___redArg(v_a_24_);
return v___x_25_;
}
else
{
lean_object* v_head_26_; lean_object* v_tail_27_; lean_object* v___x_29_; uint8_t v_isShared_30_; uint8_t v_isSharedCheck_41_; 
v_head_26_ = lean_ctor_get(v_a_23_, 0);
v_tail_27_ = lean_ctor_get(v_a_23_, 1);
v_isSharedCheck_41_ = !lean_is_exclusive(v_a_23_);
if (v_isSharedCheck_41_ == 0)
{
v___x_29_ = v_a_23_;
v_isShared_30_ = v_isSharedCheck_41_;
goto v_resetjp_28_;
}
else
{
lean_inc(v_tail_27_);
lean_inc(v_head_26_);
lean_dec(v_a_23_);
v___x_29_ = lean_box(0);
v_isShared_30_ = v_isSharedCheck_41_;
goto v_resetjp_28_;
}
v_resetjp_28_:
{
lean_object* v___y_32_; lean_object* v___x_37_; uint8_t v___x_38_; 
v___x_37_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1));
lean_inc(v_head_26_);
v___x_38_ = l_Lean_Syntax_isOfKind(v_head_26_, v___x_37_);
if (v___x_38_ == 0)
{
lean_object* v___x_39_; 
v___x_39_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_39_, 0, v_head_26_);
v___y_32_ = v___x_39_;
goto v___jp_31_;
}
else
{
lean_object* v___x_40_; 
lean_dec(v_head_26_);
v___x_40_ = lean_box(0);
v___y_32_ = v___x_40_;
goto v___jp_31_;
}
v___jp_31_:
{
lean_object* v___x_34_; 
if (v_isShared_30_ == 0)
{
lean_ctor_set(v___x_29_, 1, v_a_24_);
lean_ctor_set(v___x_29_, 0, v___y_32_);
v___x_34_ = v___x_29_;
goto v_reusejp_33_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v___y_32_);
lean_ctor_set(v_reuseFailAlloc_36_, 1, v_a_24_);
v___x_34_ = v_reuseFailAlloc_36_;
goto v_reusejp_33_;
}
v_reusejp_33_:
{
v_a_23_ = v_tail_27_;
v_a_24_ = v___x_34_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_toAlt_x3f(lean_object* v_stx_57_){
_start:
{
lean_object* v___x_58_; uint8_t v___x_59_; 
v___x_58_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__1));
lean_inc(v_stx_57_);
v___x_59_ = l_Lean_Syntax_isOfKind(v_stx_57_, v___x_58_);
if (v___x_59_ == 0)
{
lean_object* v___x_60_; 
lean_dec(v_stx_57_);
v___x_60_ = lean_box(0);
return v___x_60_;
}
else
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v_var_x3f_64_; lean_object* v___x_81_; uint8_t v___x_82_; 
v___x_61_ = lean_unsigned_to_nat(1u);
v___x_62_ = l_Lean_Syntax_getArg(v_stx_57_, v___x_61_);
v___x_81_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__5));
lean_inc(v___x_62_);
v___x_82_ = l_Lean_Syntax_isOfKind(v___x_62_, v___x_81_);
if (v___x_82_ == 0)
{
lean_object* v___x_83_; 
lean_dec(v___x_62_);
lean_dec(v_stx_57_);
v___x_83_ = lean_box(0);
return v___x_83_;
}
else
{
lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_84_ = lean_unsigned_to_nat(0u);
v___x_85_ = l_Lean_Syntax_getArg(v___x_62_, v___x_84_);
v___x_86_ = l_Lean_Syntax_isNone(v___x_85_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; uint8_t v___x_88_; 
v___x_87_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_85_);
v___x_88_ = l_Lean_Syntax_matchesNull(v___x_85_, v___x_87_);
if (v___x_88_ == 0)
{
lean_object* v___x_89_; 
lean_dec(v___x_85_);
lean_dec(v___x_62_);
lean_dec(v_stx_57_);
v___x_89_ = lean_box(0);
return v___x_89_;
}
else
{
lean_object* v_var_x3f_90_; lean_object* v___x_91_; 
v_var_x3f_90_ = l_Lean_Syntax_getArg(v___x_85_, v___x_84_);
lean_dec(v___x_85_);
v___x_91_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_91_, 0, v_var_x3f_90_);
v_var_x3f_64_ = v___x_91_;
goto v___jp_63_;
}
}
else
{
lean_object* v___x_92_; 
lean_dec(v___x_85_);
v___x_92_ = lean_box(0);
v_var_x3f_64_ = v___x_92_;
goto v___jp_63_;
}
}
v___jp_63_:
{
lean_object* v_funName_65_; lean_object* v___x_66_; uint8_t v___x_67_; 
v_funName_65_ = l_Lean_Syntax_getArg(v___x_62_, v___x_61_);
v___x_66_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__3));
lean_inc(v_funName_65_);
v___x_67_ = l_Lean_Syntax_isOfKind(v_funName_65_, v___x_66_);
if (v___x_67_ == 0)
{
lean_object* v___x_68_; 
lean_dec(v_funName_65_);
lean_dec(v_var_x3f_64_);
lean_dec(v___x_62_);
lean_dec(v_stx_57_);
v___x_68_ = lean_box(0);
return v___x_68_;
}
else
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v_pvars_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v_pvars_75_; lean_object* v___x_76_; lean_object* v_rhs_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_69_ = lean_unsigned_to_nat(2u);
v___x_70_ = l_Lean_Syntax_getArg(v___x_62_, v___x_69_);
lean_dec(v___x_62_);
v_pvars_71_ = l_Lean_Syntax_getArgs(v___x_70_);
lean_dec(v___x_70_);
v___x_72_ = lean_array_to_list(v_pvars_71_);
v___x_73_ = l_List_reverse___redArg(v___x_72_);
v___x_74_ = lean_box(0);
v_pvars_75_ = l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0(v___x_73_, v___x_74_);
v___x_76_ = lean_unsigned_to_nat(3u);
v_rhs_77_ = l_Lean_Syntax_getArg(v_stx_57_, v___x_76_);
lean_dec(v_stx_57_);
v___x_78_ = lean_box(0);
v___x_79_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_79_, 0, v_var_x3f_64_);
lean_ctor_set(v___x_79_, 1, v_funName_65_);
lean_ctor_set(v___x_79_, 2, v_pvars_75_);
lean_ctor_set(v___x_79_, 3, v_rhs_77_);
lean_ctor_set(v___x_79_, 4, v___x_78_);
lean_ctor_set(v___x_79_, 5, v___x_74_);
v___x_80_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
return v___x_80_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0(lean_object* v_a_96_, lean_object* v_as_97_, size_t v_sz_98_, size_t v_i_99_, lean_object* v_b_100_){
_start:
{
uint8_t v___x_101_; 
v___x_101_ = lean_usize_dec_lt(v_i_99_, v_sz_98_);
if (v___x_101_ == 0)
{
return v_b_100_;
}
else
{
lean_object* v_funName_102_; lean_object* v___x_103_; lean_object* v_a_104_; lean_object* v___x_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
lean_dec_ref(v_b_100_);
v_funName_102_ = lean_ctor_get(v_a_96_, 1);
v___x_103_ = lean_box(0);
v_a_104_ = lean_array_uget_borrowed(v_as_97_, v_i_99_);
v___x_105_ = l_Lean_TSyntax_getId(v_a_104_);
v___x_106_ = l_Lean_TSyntax_getId(v_funName_102_);
v___x_107_ = lean_name_eq(v___x_105_, v___x_106_);
lean_dec(v___x_106_);
lean_dec(v___x_105_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; size_t v___x_109_; size_t v___x_110_; 
v___x_108_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0___closed__0));
v___x_109_ = ((size_t)1ULL);
v___x_110_ = lean_usize_add(v_i_99_, v___x_109_);
v_i_99_ = v___x_110_;
v_b_100_ = v___x_108_;
goto _start;
}
else
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
lean_inc(v_a_104_);
v___x_112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_112_, 0, v_a_104_);
v___x_113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
v___x_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v___x_103_);
return v___x_114_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0___boxed(lean_object* v_a_115_, lean_object* v_as_116_, lean_object* v_sz_117_, lean_object* v_i_118_, lean_object* v_b_119_){
_start:
{
size_t v_sz_boxed_120_; size_t v_i_boxed_121_; lean_object* v_res_122_; 
v_sz_boxed_120_ = lean_unbox_usize(v_sz_117_);
lean_dec(v_sz_117_);
v_i_boxed_121_ = lean_unbox_usize(v_i_118_);
lean_dec(v_i_118_);
v_res_122_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0(v_a_115_, v_as_116_, v_sz_boxed_120_, v_i_boxed_121_, v_b_119_);
lean_dec_ref(v_as_116_);
lean_dec_ref(v_a_115_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1___redArg(lean_object* v_as_x27_123_, lean_object* v_b_124_){
_start:
{
if (lean_obj_tag(v_as_x27_123_) == 0)
{
return v_b_124_;
}
else
{
lean_object* v_head_125_; lean_object* v_tail_126_; lean_object* v_funName_127_; lean_object* v_pvars_128_; uint8_t v___x_129_; 
v_head_125_ = lean_ctor_get(v_as_x27_123_, 0);
lean_inc(v_head_125_);
v_tail_126_ = lean_ctor_get(v_as_x27_123_, 1);
lean_inc(v_tail_126_);
lean_dec_ref(v_as_x27_123_);
v_funName_127_ = lean_ctor_get(v_head_125_, 1);
lean_inc(v_funName_127_);
v_pvars_128_ = lean_ctor_get(v_head_125_, 2);
v___x_129_ = l_List_isEmpty___redArg(v_pvars_128_);
if (v___x_129_ == 0)
{
lean_dec(v_funName_127_);
lean_dec(v_head_125_);
v_as_x27_123_ = v_tail_126_;
goto _start;
}
else
{
lean_object* v___x_135_; size_t v_sz_136_; size_t v___x_137_; lean_object* v___x_138_; lean_object* v_fst_139_; 
v___x_135_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0___closed__0));
v_sz_136_ = lean_array_size(v_b_124_);
v___x_137_ = ((size_t)0ULL);
v___x_138_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0(v_head_125_, v_b_124_, v_sz_136_, v___x_137_, v___x_135_);
lean_dec(v_head_125_);
v_fst_139_ = lean_ctor_get(v___x_138_, 0);
lean_inc(v_fst_139_);
lean_dec_ref(v___x_138_);
if (lean_obj_tag(v_fst_139_) == 0)
{
goto v___jp_130_;
}
else
{
lean_object* v_val_140_; 
v_val_140_ = lean_ctor_get(v_fst_139_, 0);
lean_inc(v_val_140_);
lean_dec_ref(v_fst_139_);
if (lean_obj_tag(v_val_140_) == 0)
{
goto v___jp_130_;
}
else
{
lean_dec_ref(v_val_140_);
lean_dec(v_funName_127_);
v_as_x27_123_ = v_tail_126_;
goto _start;
}
}
}
v___jp_130_:
{
if (v___x_129_ == 0)
{
lean_dec(v_funName_127_);
v_as_x27_123_ = v_tail_126_;
goto _start;
}
else
{
lean_object* v___x_132_; 
v___x_132_ = lean_array_push(v_b_124_, v_funName_127_);
v_as_x27_123_ = v_tail_126_;
v_b_124_ = v___x_132_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch(lean_object* v_alts_144_){
_start:
{
lean_object* v_funNames_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v_funNames_145_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch___closed__0));
v___x_146_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1___redArg(v_alts_144_, v_funNames_145_);
v___x_147_ = lean_array_to_list(v___x_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1(lean_object* v_as_148_, lean_object* v_as_x27_149_, lean_object* v_b_150_, lean_object* v_a_151_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1___redArg(v_as_x27_149_, v_b_150_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1___boxed(lean_object* v_as_153_, lean_object* v_as_x27_154_, lean_object* v_b_155_, lean_object* v_a_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1(v_as_153_, v_as_x27_154_, v_b_155_, v_a_156_);
lean_dec(v_as_153_);
return v_res_157_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_MatchExpr_shouldSaveActual___lam__0(lean_object* v_alt_158_){
_start:
{
lean_object* v_pvars_159_; 
v_pvars_159_ = lean_ctor_get(v_alt_158_, 2);
if (lean_obj_tag(v_pvars_159_) == 1)
{
lean_object* v_head_160_; 
v_head_160_ = lean_ctor_get(v_pvars_159_, 0);
if (lean_obj_tag(v_head_160_) == 1)
{
uint8_t v___x_161_; 
v___x_161_ = 1;
return v___x_161_;
}
else
{
uint8_t v___x_162_; 
v___x_162_ = 0;
return v___x_162_;
}
}
else
{
uint8_t v___x_163_; 
v___x_163_ = 0;
return v___x_163_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_shouldSaveActual___lam__0___boxed(lean_object* v_alt_164_){
_start:
{
uint8_t v_res_165_; lean_object* v_r_166_; 
v_res_165_ = l_Lean_Elab_Term_MatchExpr_shouldSaveActual___lam__0(v_alt_164_);
lean_dec_ref(v_alt_164_);
v_r_166_ = lean_box(v_res_165_);
return v_r_166_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_MatchExpr_shouldSaveActual(lean_object* v_alts_168_){
_start:
{
lean_object* v___f_169_; uint8_t v___x_170_; 
v___f_169_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_shouldSaveActual___closed__0));
v___x_170_ = l_List_any___redArg(v_alts_168_, v___f_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_shouldSaveActual___boxed(lean_object* v_alts_171_){
_start:
{
uint8_t v_res_172_; lean_object* v_r_173_; 
v_res_172_ = l_Lean_Elab_Term_MatchExpr_shouldSaveActual(v_alts_171_);
v_r_173_ = lean_box(v_res_172_);
return v_r_173_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_MatchExpr_getAltFor_x3f___lam__0(lean_object* v_funName_174_, lean_object* v_alt_175_){
_start:
{
lean_object* v_funName_176_; lean_object* v_pvars_177_; lean_object* v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; 
v_funName_176_ = lean_ctor_get(v_alt_175_, 1);
v_pvars_177_ = lean_ctor_get(v_alt_175_, 2);
v___x_178_ = l_Lean_TSyntax_getId(v_funName_176_);
v___x_179_ = l_Lean_TSyntax_getId(v_funName_174_);
v___x_180_ = lean_name_eq(v___x_178_, v___x_179_);
lean_dec(v___x_179_);
lean_dec(v___x_178_);
if (v___x_180_ == 0)
{
return v___x_180_;
}
else
{
uint8_t v___x_181_; 
v___x_181_ = l_List_isEmpty___redArg(v_pvars_177_);
return v___x_181_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getAltFor_x3f___lam__0___boxed(lean_object* v_funName_182_, lean_object* v_alt_183_){
_start:
{
uint8_t v_res_184_; lean_object* v_r_185_; 
v_res_184_ = l_Lean_Elab_Term_MatchExpr_getAltFor_x3f___lam__0(v_funName_182_, v_alt_183_);
lean_dec_ref(v_alt_183_);
lean_dec(v_funName_182_);
v_r_185_ = lean_box(v_res_184_);
return v_r_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getAltFor_x3f(lean_object* v_alts_186_, lean_object* v_funName_187_){
_start:
{
lean_object* v___f_188_; lean_object* v___x_189_; 
v___f_188_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_MatchExpr_getAltFor_x3f___lam__0___boxed), 2, 1);
lean_closure_set(v___f_188_, 0, v_funName_187_);
v___x_189_ = l_List_find_x3f___redArg(v___f_188_, v_alts_186_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Elab_Term_MatchExpr_next_spec__0(lean_object* v_actual_190_, lean_object* v_a_191_, lean_object* v_a_192_){
_start:
{
if (lean_obj_tag(v_a_191_) == 0)
{
lean_object* v___x_193_; 
lean_dec(v_actual_190_);
v___x_193_ = lean_array_to_list(v_a_192_);
return v___x_193_;
}
else
{
lean_object* v_head_194_; lean_object* v_tail_195_; lean_object* v_val_197_; lean_object* v_var_x3f_200_; lean_object* v_funName_201_; lean_object* v_pvars_202_; lean_object* v_rhs_203_; lean_object* v_k_204_; lean_object* v_actuals_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_228_; 
v_head_194_ = lean_ctor_get(v_a_191_, 0);
lean_inc(v_head_194_);
v_tail_195_ = lean_ctor_get(v_a_191_, 1);
lean_inc(v_tail_195_);
lean_dec_ref(v_a_191_);
v_var_x3f_200_ = lean_ctor_get(v_head_194_, 0);
v_funName_201_ = lean_ctor_get(v_head_194_, 1);
v_pvars_202_ = lean_ctor_get(v_head_194_, 2);
v_rhs_203_ = lean_ctor_get(v_head_194_, 3);
v_k_204_ = lean_ctor_get(v_head_194_, 4);
v_actuals_205_ = lean_ctor_get(v_head_194_, 5);
v_isSharedCheck_228_ = !lean_is_exclusive(v_head_194_);
if (v_isSharedCheck_228_ == 0)
{
v___x_207_ = v_head_194_;
v_isShared_208_ = v_isSharedCheck_228_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_actuals_205_);
lean_inc(v_k_204_);
lean_inc(v_rhs_203_);
lean_inc(v_pvars_202_);
lean_inc(v_funName_201_);
lean_inc(v_var_x3f_200_);
lean_dec(v_head_194_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_228_;
goto v_resetjp_206_;
}
v___jp_196_:
{
lean_object* v___x_198_; 
v___x_198_ = lean_array_push(v_a_192_, v_val_197_);
v_a_191_ = v_tail_195_;
v_a_192_ = v___x_198_;
goto _start;
}
v_resetjp_206_:
{
if (lean_obj_tag(v_pvars_202_) == 1)
{
lean_object* v_head_217_; 
v_head_217_ = lean_ctor_get(v_pvars_202_, 0);
if (lean_obj_tag(v_head_217_) == 1)
{
lean_object* v_tail_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_226_; 
lean_del_object(v___x_207_);
v_tail_218_ = lean_ctor_get(v_pvars_202_, 1);
v_isSharedCheck_226_ = !lean_is_exclusive(v_pvars_202_);
if (v_isSharedCheck_226_ == 0)
{
lean_object* v_unused_227_; 
v_unused_227_ = lean_ctor_get(v_pvars_202_, 0);
lean_dec(v_unused_227_);
v___x_220_ = v_pvars_202_;
v_isShared_221_ = v_isSharedCheck_226_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_tail_218_);
lean_dec(v_pvars_202_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_226_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_223_; 
lean_inc(v_actual_190_);
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 1, v_actuals_205_);
lean_ctor_set(v___x_220_, 0, v_actual_190_);
v___x_223_ = v___x_220_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_actual_190_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v_actuals_205_);
v___x_223_ = v_reuseFailAlloc_225_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
lean_object* v___x_224_; 
v___x_224_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_224_, 0, v_var_x3f_200_);
lean_ctor_set(v___x_224_, 1, v_funName_201_);
lean_ctor_set(v___x_224_, 2, v_tail_218_);
lean_ctor_set(v___x_224_, 3, v_rhs_203_);
lean_ctor_set(v___x_224_, 4, v_k_204_);
lean_ctor_set(v___x_224_, 5, v___x_223_);
v_val_197_ = v___x_224_;
goto v___jp_196_;
}
}
}
else
{
goto v___jp_209_;
}
}
else
{
goto v___jp_209_;
}
v___jp_209_:
{
if (lean_obj_tag(v_pvars_202_) == 1)
{
lean_object* v_head_210_; 
v_head_210_ = lean_ctor_get(v_pvars_202_, 0);
if (lean_obj_tag(v_head_210_) == 0)
{
lean_object* v_tail_211_; lean_object* v___x_213_; 
v_tail_211_ = lean_ctor_get(v_pvars_202_, 1);
lean_inc(v_tail_211_);
lean_dec_ref(v_pvars_202_);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 2, v_tail_211_);
v___x_213_ = v___x_207_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_var_x3f_200_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v_funName_201_);
lean_ctor_set(v_reuseFailAlloc_214_, 2, v_tail_211_);
lean_ctor_set(v_reuseFailAlloc_214_, 3, v_rhs_203_);
lean_ctor_set(v_reuseFailAlloc_214_, 4, v_k_204_);
lean_ctor_set(v_reuseFailAlloc_214_, 5, v_actuals_205_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
v_val_197_ = v___x_213_;
goto v___jp_196_;
}
}
else
{
lean_dec_ref(v_pvars_202_);
lean_del_object(v___x_207_);
lean_dec(v_actuals_205_);
lean_dec(v_k_204_);
lean_dec(v_rhs_203_);
lean_dec(v_funName_201_);
lean_dec(v_var_x3f_200_);
v_a_191_ = v_tail_195_;
goto _start;
}
}
else
{
lean_del_object(v___x_207_);
lean_dec(v_actuals_205_);
lean_dec(v_k_204_);
lean_dec(v_rhs_203_);
lean_dec(v_pvars_202_);
lean_dec(v_funName_201_);
lean_dec(v_var_x3f_200_);
v_a_191_ = v_tail_195_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_next(lean_object* v_alts_231_, lean_object* v_actual_232_){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_next___closed__0));
v___x_234_ = l_List_filterMapTR_go___at___00Lean_Elab_Term_MatchExpr_next_spec__0(v_actual_232_, v_alts_231_, v___x_233_);
return v___x_234_;
}
}
static lean_object* _init_l_Lean_Elab_Term_MatchExpr_initK___closed__1(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_initK___closed__0));
v___x_237_ = l_String_toRawSubstring_x27(v___x_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_initK(lean_object* v_alt_240_, lean_object* v_a_241_, lean_object* v_a_242_){
_start:
{
lean_object* v_macroScope_243_; lean_object* v_traceMsgs_244_; lean_object* v_expandedMacroDecls_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_277_; 
v_macroScope_243_ = lean_ctor_get(v_a_242_, 0);
v_traceMsgs_244_ = lean_ctor_get(v_a_242_, 1);
v_expandedMacroDecls_245_ = lean_ctor_get(v_a_242_, 2);
v_isSharedCheck_277_ = !lean_is_exclusive(v_a_242_);
if (v_isSharedCheck_277_ == 0)
{
v___x_247_ = v_a_242_;
v_isShared_248_ = v_isSharedCheck_277_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_expandedMacroDecls_245_);
lean_inc(v_traceMsgs_244_);
lean_inc(v_macroScope_243_);
lean_dec(v_a_242_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_277_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v_quotContext_249_; lean_object* v_ref_250_; lean_object* v_var_x3f_251_; lean_object* v_funName_252_; lean_object* v_pvars_253_; lean_object* v_rhs_254_; lean_object* v_actuals_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_275_; 
v_quotContext_249_ = lean_ctor_get(v_a_241_, 1);
lean_inc(v_quotContext_249_);
v_ref_250_ = lean_ctor_get(v_a_241_, 5);
lean_inc(v_ref_250_);
lean_dec_ref(v_a_241_);
v_var_x3f_251_ = lean_ctor_get(v_alt_240_, 0);
v_funName_252_ = lean_ctor_get(v_alt_240_, 1);
v_pvars_253_ = lean_ctor_get(v_alt_240_, 2);
v_rhs_254_ = lean_ctor_get(v_alt_240_, 3);
v_actuals_255_ = lean_ctor_get(v_alt_240_, 5);
v_isSharedCheck_275_ = !lean_is_exclusive(v_alt_240_);
if (v_isSharedCheck_275_ == 0)
{
lean_object* v_unused_276_; 
v_unused_276_ = lean_ctor_get(v_alt_240_, 4);
lean_dec(v_unused_276_);
v___x_257_ = v_alt_240_;
v_isShared_258_ = v_isSharedCheck_275_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_actuals_255_);
lean_inc(v_rhs_254_);
lean_inc(v_pvars_253_);
lean_inc(v_funName_252_);
lean_inc(v_var_x3f_251_);
lean_dec(v_alt_240_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_275_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_263_; 
v___x_259_ = lean_unsigned_to_nat(1u);
v___x_260_ = lean_nat_add(v_macroScope_243_, v___x_259_);
v___x_261_ = lean_obj_once(&l_Lean_Elab_Term_MatchExpr_initK___closed__1, &l_Lean_Elab_Term_MatchExpr_initK___closed__1_once, _init_l_Lean_Elab_Term_MatchExpr_initK___closed__1);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v___x_260_);
v___x_263_ = v___x_247_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_260_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v_traceMsgs_244_);
lean_ctor_set(v_reuseFailAlloc_274_, 2, v_expandedMacroDecls_245_);
v___x_263_ = v_reuseFailAlloc_274_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
uint8_t v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_271_; 
v___x_264_ = 0;
v___x_265_ = l_Lean_SourceInfo_fromRef(v_ref_250_, v___x_264_);
lean_dec(v_ref_250_);
v___x_266_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_initK___closed__2));
v___x_267_ = l_Lean_addMacroScope(v_quotContext_249_, v___x_266_, v_macroScope_243_);
v___x_268_ = lean_box(0);
v___x_269_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_269_, 0, v___x_265_);
lean_ctor_set(v___x_269_, 1, v___x_261_);
lean_ctor_set(v___x_269_, 2, v___x_267_);
lean_ctor_set(v___x_269_, 3, v___x_268_);
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 4, v___x_269_);
v___x_271_ = v___x_257_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_var_x3f_251_);
lean_ctor_set(v_reuseFailAlloc_273_, 1, v_funName_252_);
lean_ctor_set(v_reuseFailAlloc_273_, 2, v_pvars_253_);
lean_ctor_set(v_reuseFailAlloc_273_, 3, v_rhs_254_);
lean_ctor_set(v_reuseFailAlloc_273_, 4, v___x_269_);
lean_ctor_set(v_reuseFailAlloc_273_, 5, v_actuals_255_);
v___x_271_ = v_reuseFailAlloc_273_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
lean_object* v___x_272_; 
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
lean_ctor_set(v___x_272_, 1, v___x_263_);
return v___x_272_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_MatchExpr_getParams_spec__1(size_t v_sz_278_, size_t v_i_279_, lean_object* v_bs_280_){
_start:
{
uint8_t v___x_281_; 
v___x_281_ = lean_usize_dec_lt(v_i_279_, v_sz_278_);
if (v___x_281_ == 0)
{
return v_bs_280_;
}
else
{
lean_object* v_v_282_; lean_object* v___x_283_; lean_object* v_bs_x27_284_; size_t v___x_285_; size_t v___x_286_; lean_object* v___x_287_; 
v_v_282_ = lean_array_uget(v_bs_280_, v_i_279_);
v___x_283_ = lean_unsigned_to_nat(0u);
v_bs_x27_284_ = lean_array_uset(v_bs_280_, v_i_279_, v___x_283_);
v___x_285_ = ((size_t)1ULL);
v___x_286_ = lean_usize_add(v_i_279_, v___x_285_);
v___x_287_ = lean_array_uset(v_bs_x27_284_, v_i_279_, v_v_282_);
v_i_279_ = v___x_286_;
v_bs_280_ = v___x_287_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_MatchExpr_getParams_spec__1___boxed(lean_object* v_sz_289_, lean_object* v_i_290_, lean_object* v_bs_291_){
_start:
{
size_t v_sz_boxed_292_; size_t v_i_boxed_293_; lean_object* v_res_294_; 
v_sz_boxed_292_ = lean_unbox_usize(v_sz_289_);
lean_dec(v_sz_289_);
v_i_boxed_293_ = lean_unbox_usize(v_i_290_);
lean_dec(v_i_290_);
v_res_294_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_MatchExpr_getParams_spec__1(v_sz_boxed_292_, v_i_boxed_293_, v_bs_291_);
return v_res_294_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__7(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__6));
v___x_308_ = l_String_toRawSubstring_x27(v___x_307_);
return v___x_308_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14(void){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l_Array_mkArray0(lean_box(0));
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0(lean_object* v_as_327_, size_t v_i_328_, size_t v_stop_329_, lean_object* v_b_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v_a_334_; lean_object* v_a_335_; uint8_t v___x_339_; 
v___x_339_ = lean_usize_dec_eq(v_i_328_, v_stop_329_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; 
v___x_340_ = lean_array_uget_borrowed(v_as_327_, v_i_328_);
if (lean_obj_tag(v___x_340_) == 0)
{
v_a_334_ = v_b_330_;
v_a_335_ = v___y_332_;
goto v___jp_333_;
}
else
{
lean_object* v_val_341_; lean_object* v_quotContext_342_; lean_object* v_currMacroScope_343_; lean_object* v_ref_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v_val_341_ = lean_ctor_get(v___x_340_, 0);
v_quotContext_342_ = lean_ctor_get(v___y_331_, 1);
v_currMacroScope_343_ = lean_ctor_get(v___y_331_, 2);
v_ref_344_ = lean_ctor_get(v___y_331_, 5);
v___x_345_ = l_Lean_SourceInfo_fromRef(v_ref_344_, v___x_339_);
v___x_346_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1));
v___x_347_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2));
lean_inc(v___x_345_);
v___x_348_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_345_);
lean_ctor_set(v___x_348_, 1, v___x_347_);
v___x_349_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4));
lean_inc(v_val_341_);
lean_inc(v___x_345_);
v___x_350_ = l_Lean_Syntax_node1(v___x_345_, v___x_349_, v_val_341_);
v___x_351_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__5));
lean_inc(v___x_345_);
v___x_352_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_345_);
lean_ctor_set(v___x_352_, 1, v___x_351_);
v___x_353_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__7);
v___x_354_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__8));
lean_inc(v_currMacroScope_343_);
lean_inc(v_quotContext_342_);
v___x_355_ = l_Lean_addMacroScope(v_quotContext_342_, v___x_354_, v_currMacroScope_343_);
v___x_356_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__13));
lean_inc(v___x_345_);
v___x_357_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_357_, 0, v___x_345_);
lean_ctor_set(v___x_357_, 1, v___x_353_);
lean_ctor_set(v___x_357_, 2, v___x_355_);
lean_ctor_set(v___x_357_, 3, v___x_356_);
lean_inc(v___x_345_);
v___x_358_ = l_Lean_Syntax_node2(v___x_345_, v___x_349_, v___x_352_, v___x_357_);
v___x_359_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
lean_inc(v___x_345_);
v___x_360_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_360_, 0, v___x_345_);
lean_ctor_set(v___x_360_, 1, v___x_349_);
lean_ctor_set(v___x_360_, 2, v___x_359_);
v___x_361_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15));
lean_inc(v___x_345_);
v___x_362_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_345_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
v___x_363_ = l_Lean_Syntax_node5(v___x_345_, v___x_346_, v___x_348_, v___x_350_, v___x_358_, v___x_360_, v___x_362_);
v___x_364_ = lean_array_push(v_b_330_, v___x_363_);
v_a_334_ = v___x_364_;
v_a_335_ = v___y_332_;
goto v___jp_333_;
}
}
else
{
lean_object* v___x_365_; 
lean_dec_ref(v___y_331_);
v___x_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_365_, 0, v_b_330_);
lean_ctor_set(v___x_365_, 1, v___y_332_);
return v___x_365_;
}
v___jp_333_:
{
size_t v___x_336_; size_t v___x_337_; 
v___x_336_ = ((size_t)1ULL);
v___x_337_ = lean_usize_add(v_i_328_, v___x_336_);
v_i_328_ = v___x_337_;
v_b_330_ = v_a_334_;
v___y_332_ = v_a_335_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___boxed(lean_object* v_as_366_, lean_object* v_i_367_, lean_object* v_stop_368_, lean_object* v_b_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
size_t v_i_boxed_372_; size_t v_stop_boxed_373_; lean_object* v_res_374_; 
v_i_boxed_372_ = lean_unbox_usize(v_i_367_);
lean_dec(v_i_367_);
v_stop_boxed_373_ = lean_unbox_usize(v_stop_368_);
lean_dec(v_stop_368_);
v_res_374_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0(v_as_366_, v_i_boxed_372_, v_stop_boxed_373_, v_b_369_, v___y_370_, v___y_371_);
lean_dec_ref(v_as_366_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0(lean_object* v_as_375_, lean_object* v_start_376_, lean_object* v_stop_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v___x_380_; uint8_t v___x_381_; 
v___x_380_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch___closed__0));
v___x_381_ = lean_nat_dec_lt(v_start_376_, v_stop_377_);
if (v___x_381_ == 0)
{
lean_object* v___x_382_; 
lean_dec_ref(v___y_378_);
v___x_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_380_);
lean_ctor_set(v___x_382_, 1, v___y_379_);
return v___x_382_;
}
else
{
lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_383_ = lean_array_get_size(v_as_375_);
v___x_384_ = lean_nat_dec_le(v_stop_377_, v___x_383_);
if (v___x_384_ == 0)
{
uint8_t v___x_385_; 
v___x_385_ = lean_nat_dec_lt(v_start_376_, v___x_383_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; 
lean_dec_ref(v___y_378_);
v___x_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_380_);
lean_ctor_set(v___x_386_, 1, v___y_379_);
return v___x_386_;
}
else
{
size_t v___x_387_; size_t v___x_388_; lean_object* v___x_389_; 
v___x_387_ = lean_usize_of_nat(v_start_376_);
v___x_388_ = lean_usize_of_nat(v___x_383_);
v___x_389_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0(v_as_375_, v___x_387_, v___x_388_, v___x_380_, v___y_378_, v___y_379_);
return v___x_389_;
}
}
else
{
size_t v___x_390_; size_t v___x_391_; lean_object* v___x_392_; 
v___x_390_ = lean_usize_of_nat(v_start_376_);
v___x_391_ = lean_usize_of_nat(v_stop_377_);
v___x_392_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0(v_as_375_, v___x_390_, v___x_391_, v___x_380_, v___y_378_, v___y_379_);
return v___x_392_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0___boxed(lean_object* v_as_393_, lean_object* v_start_394_, lean_object* v_stop_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0(v_as_393_, v_start_394_, v_stop_395_, v___y_396_, v___y_397_);
lean_dec(v_stop_395_);
lean_dec(v_start_394_);
lean_dec_ref(v_as_393_);
return v_res_398_;
}
}
static lean_object* _init_l_Lean_Elab_Term_MatchExpr_getParams___closed__2(void){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getParams___closed__1));
v___x_402_ = l_String_toRawSubstring_x27(v___x_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getParams(lean_object* v_alt_416_, lean_object* v_a_417_, lean_object* v_a_418_){
_start:
{
lean_object* v_var_x3f_419_; lean_object* v_pvars_420_; lean_object* v_params_422_; lean_object* v___y_423_; lean_object* v___y_424_; lean_object* v_params_478_; 
v_var_x3f_419_ = lean_ctor_get(v_alt_416_, 0);
lean_inc(v_var_x3f_419_);
v_pvars_420_ = lean_ctor_get(v_alt_416_, 2);
lean_inc(v_pvars_420_);
lean_dec_ref(v_alt_416_);
v_params_478_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch___closed__0));
if (lean_obj_tag(v_var_x3f_419_) == 1)
{
lean_object* v_val_479_; lean_object* v_quotContext_480_; lean_object* v_currMacroScope_481_; lean_object* v_ref_482_; uint8_t v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v_val_479_ = lean_ctor_get(v_var_x3f_419_, 0);
lean_inc(v_val_479_);
lean_dec_ref(v_var_x3f_419_);
v_quotContext_480_ = lean_ctor_get(v_a_417_, 1);
v_currMacroScope_481_ = lean_ctor_get(v_a_417_, 2);
v_ref_482_ = lean_ctor_get(v_a_417_, 5);
v___x_483_ = 0;
v___x_484_ = l_Lean_SourceInfo_fromRef(v_ref_482_, v___x_483_);
v___x_485_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1));
v___x_486_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2));
lean_inc(v___x_484_);
v___x_487_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_484_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
v___x_488_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4));
lean_inc(v___x_484_);
v___x_489_ = l_Lean_Syntax_node1(v___x_484_, v___x_488_, v_val_479_);
v___x_490_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__5));
lean_inc(v___x_484_);
v___x_491_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_491_, 0, v___x_484_);
lean_ctor_set(v___x_491_, 1, v___x_490_);
v___x_492_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__7);
v___x_493_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__8));
lean_inc(v_currMacroScope_481_);
lean_inc(v_quotContext_480_);
v___x_494_ = l_Lean_addMacroScope(v_quotContext_480_, v___x_493_, v_currMacroScope_481_);
v___x_495_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__13));
lean_inc(v___x_484_);
v___x_496_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_496_, 0, v___x_484_);
lean_ctor_set(v___x_496_, 1, v___x_492_);
lean_ctor_set(v___x_496_, 2, v___x_494_);
lean_ctor_set(v___x_496_, 3, v___x_495_);
lean_inc(v___x_484_);
v___x_497_ = l_Lean_Syntax_node2(v___x_484_, v___x_488_, v___x_491_, v___x_496_);
v___x_498_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
lean_inc(v___x_484_);
v___x_499_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_499_, 0, v___x_484_);
lean_ctor_set(v___x_499_, 1, v___x_488_);
lean_ctor_set(v___x_499_, 2, v___x_498_);
v___x_500_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15));
lean_inc(v___x_484_);
v___x_501_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_501_, 0, v___x_484_);
lean_ctor_set(v___x_501_, 1, v___x_500_);
v___x_502_ = l_Lean_Syntax_node5(v___x_484_, v___x_485_, v___x_487_, v___x_489_, v___x_497_, v___x_499_, v___x_501_);
v___x_503_ = lean_array_push(v_params_478_, v___x_502_);
v_params_422_ = v___x_503_;
v___y_423_ = v_a_417_;
v___y_424_ = v_a_418_;
goto v___jp_421_;
}
else
{
lean_dec(v_var_x3f_419_);
v_params_422_ = v_params_478_;
v___y_423_ = v_a_417_;
v___y_424_ = v_a_418_;
goto v___jp_421_;
}
v___jp_421_:
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_425_ = lean_array_mk(v_pvars_420_);
v___x_426_ = l_Array_reverse___redArg(v___x_425_);
v___x_427_ = lean_unsigned_to_nat(0u);
v___x_428_ = lean_array_get_size(v___x_426_);
lean_inc_ref(v___y_423_);
v___x_429_ = l_Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0(v___x_426_, v___x_427_, v___x_428_, v___y_423_, v___y_424_);
lean_dec_ref(v___x_426_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_a_430_; lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_477_; 
v_a_430_ = lean_ctor_get(v___x_429_, 0);
v_a_431_ = lean_ctor_get(v___x_429_, 1);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_477_ == 0)
{
v___x_433_ = v___x_429_;
v_isShared_434_ = v_isSharedCheck_477_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_inc(v_a_430_);
lean_dec(v___x_429_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_477_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_435_; lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_435_ = l_Array_append___redArg(v_params_422_, v_a_430_);
lean_dec(v_a_430_);
v___x_436_ = lean_array_get_size(v___x_435_);
v___x_437_ = lean_nat_dec_eq(v___x_436_, v___x_427_);
if (v___x_437_ == 0)
{
size_t v_sz_438_; size_t v___x_439_; lean_object* v___x_440_; lean_object* v___x_442_; 
lean_dec_ref(v___y_423_);
v_sz_438_ = lean_array_size(v___x_435_);
v___x_439_ = ((size_t)0ULL);
v___x_440_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_MatchExpr_getParams_spec__1(v_sz_438_, v___x_439_, v___x_435_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 0, v___x_440_);
v___x_442_ = v___x_433_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v___x_440_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v_a_431_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
else
{
lean_object* v_quotContext_444_; lean_object* v_currMacroScope_445_; lean_object* v_ref_446_; uint8_t v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_475_; 
lean_dec_ref(v___x_435_);
v_quotContext_444_ = lean_ctor_get(v___y_423_, 1);
lean_inc(v_quotContext_444_);
v_currMacroScope_445_ = lean_ctor_get(v___y_423_, 2);
lean_inc(v_currMacroScope_445_);
v_ref_446_ = lean_ctor_get(v___y_423_, 5);
lean_inc(v_ref_446_);
lean_dec_ref(v___y_423_);
v___x_447_ = 0;
v___x_448_ = l_Lean_SourceInfo_fromRef(v_ref_446_, v___x_447_);
lean_dec(v_ref_446_);
v___x_449_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1));
v___x_450_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2));
lean_inc(v___x_448_);
v___x_451_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_451_, 0, v___x_448_);
lean_ctor_set(v___x_451_, 1, v___x_450_);
v___x_452_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4));
v___x_453_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1));
v___x_454_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getParams___closed__0));
lean_inc(v___x_448_);
v___x_455_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_455_, 0, v___x_448_);
lean_ctor_set(v___x_455_, 1, v___x_454_);
lean_inc(v___x_448_);
v___x_456_ = l_Lean_Syntax_node1(v___x_448_, v___x_453_, v___x_455_);
lean_inc(v___x_448_);
v___x_457_ = l_Lean_Syntax_node1(v___x_448_, v___x_452_, v___x_456_);
v___x_458_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__5));
lean_inc(v___x_448_);
v___x_459_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_448_);
lean_ctor_set(v___x_459_, 1, v___x_458_);
v___x_460_ = lean_obj_once(&l_Lean_Elab_Term_MatchExpr_getParams___closed__2, &l_Lean_Elab_Term_MatchExpr_getParams___closed__2_once, _init_l_Lean_Elab_Term_MatchExpr_getParams___closed__2);
v___x_461_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getParams___closed__3));
v___x_462_ = l_Lean_addMacroScope(v_quotContext_444_, v___x_461_, v_currMacroScope_445_);
v___x_463_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getParams___closed__7));
lean_inc(v___x_448_);
v___x_464_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_464_, 0, v___x_448_);
lean_ctor_set(v___x_464_, 1, v___x_460_);
lean_ctor_set(v___x_464_, 2, v___x_462_);
lean_ctor_set(v___x_464_, 3, v___x_463_);
lean_inc(v___x_448_);
v___x_465_ = l_Lean_Syntax_node2(v___x_448_, v___x_452_, v___x_459_, v___x_464_);
v___x_466_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
lean_inc(v___x_448_);
v___x_467_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_467_, 0, v___x_448_);
lean_ctor_set(v___x_467_, 1, v___x_452_);
lean_ctor_set(v___x_467_, 2, v___x_466_);
v___x_468_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15));
lean_inc(v___x_448_);
v___x_469_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_469_, 0, v___x_448_);
lean_ctor_set(v___x_469_, 1, v___x_468_);
v___x_470_ = l_Lean_Syntax_node5(v___x_448_, v___x_449_, v___x_451_, v___x_457_, v___x_465_, v___x_467_, v___x_469_);
v___x_471_ = lean_unsigned_to_nat(1u);
v___x_472_ = lean_mk_empty_array_with_capacity(v___x_471_);
v___x_473_ = lean_array_push(v___x_472_, v___x_470_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 0, v___x_473_);
v___x_475_ = v___x_433_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v___x_473_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v_a_431_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
else
{
lean_dec_ref(v___y_423_);
lean_dec_ref(v_params_422_);
return v___x_429_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_MatchExpr_getActuals___closed__7(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__6));
v___x_521_ = l_String_toRawSubstring_x27(v___x_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getActuals(lean_object* v_discr_560_, lean_object* v_alt_561_, lean_object* v_a_562_, lean_object* v_a_563_){
_start:
{
lean_object* v_var_x3f_564_; lean_object* v_actuals_565_; lean_object* v_actuals_567_; lean_object* v___y_568_; lean_object* v___y_569_; lean_object* v_actuals_603_; 
v_var_x3f_564_ = lean_ctor_get(v_alt_561_, 0);
lean_inc(v_var_x3f_564_);
v_actuals_565_ = lean_ctor_get(v_alt_561_, 5);
lean_inc(v_actuals_565_);
lean_dec_ref(v_alt_561_);
v_actuals_603_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch___closed__0));
if (lean_obj_tag(v_var_x3f_564_) == 0)
{
lean_dec(v_discr_560_);
v_actuals_567_ = v_actuals_603_;
v___y_568_ = v_a_562_;
v___y_569_ = v_a_563_;
goto v___jp_566_;
}
else
{
lean_object* v_actuals_604_; 
lean_dec_ref(v_var_x3f_564_);
v_actuals_604_ = lean_array_push(v_actuals_603_, v_discr_560_);
v_actuals_567_ = v_actuals_604_;
v___y_568_ = v_a_562_;
v___y_569_ = v_a_563_;
goto v___jp_566_;
}
v___jp_566_:
{
lean_object* v___x_570_; lean_object* v_actuals_571_; lean_object* v___x_572_; lean_object* v___x_573_; uint8_t v___x_574_; 
v___x_570_ = lean_array_mk(v_actuals_565_);
v_actuals_571_ = l_Array_append___redArg(v_actuals_567_, v___x_570_);
lean_dec_ref(v___x_570_);
v___x_572_ = lean_array_get_size(v_actuals_571_);
v___x_573_ = lean_unsigned_to_nat(0u);
v___x_574_ = lean_nat_dec_eq(v___x_572_, v___x_573_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; 
lean_dec_ref(v___y_568_);
v___x_575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_575_, 0, v_actuals_571_);
lean_ctor_set(v___x_575_, 1, v___y_569_);
return v___x_575_;
}
else
{
lean_object* v_quotContext_576_; lean_object* v_currMacroScope_577_; lean_object* v_ref_578_; uint8_t v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
lean_dec_ref(v_actuals_571_);
v_quotContext_576_ = lean_ctor_get(v___y_568_, 1);
lean_inc(v_quotContext_576_);
v_currMacroScope_577_ = lean_ctor_get(v___y_568_, 2);
lean_inc(v_currMacroScope_577_);
v_ref_578_ = lean_ctor_get(v___y_568_, 5);
lean_inc(v_ref_578_);
lean_dec_ref(v___y_568_);
v___x_579_ = 0;
v___x_580_ = l_Lean_SourceInfo_fromRef(v_ref_578_, v___x_579_);
lean_dec(v_ref_578_);
v___x_581_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__1));
v___x_582_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__3));
v___x_583_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2));
lean_inc(v___x_580_);
v___x_584_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_580_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
v___x_585_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__5));
v___x_586_ = lean_obj_once(&l_Lean_Elab_Term_MatchExpr_getActuals___closed__7, &l_Lean_Elab_Term_MatchExpr_getActuals___closed__7_once, _init_l_Lean_Elab_Term_MatchExpr_getActuals___closed__7);
v___x_587_ = lean_box(0);
v___x_588_ = l_Lean_addMacroScope(v_quotContext_576_, v___x_587_, v_currMacroScope_577_);
v___x_589_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__21));
lean_inc(v___x_580_);
v___x_590_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_590_, 0, v___x_580_);
lean_ctor_set(v___x_590_, 1, v___x_586_);
lean_ctor_set(v___x_590_, 2, v___x_588_);
lean_ctor_set(v___x_590_, 3, v___x_589_);
lean_inc(v___x_580_);
v___x_591_ = l_Lean_Syntax_node1(v___x_580_, v___x_585_, v___x_590_);
lean_inc(v___x_580_);
v___x_592_ = l_Lean_Syntax_node2(v___x_580_, v___x_582_, v___x_584_, v___x_591_);
v___x_593_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4));
v___x_594_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
lean_inc(v___x_580_);
v___x_595_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_595_, 0, v___x_580_);
lean_ctor_set(v___x_595_, 1, v___x_593_);
lean_ctor_set(v___x_595_, 2, v___x_594_);
v___x_596_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15));
lean_inc(v___x_580_);
v___x_597_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_580_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
v___x_598_ = l_Lean_Syntax_node3(v___x_580_, v___x_581_, v___x_592_, v___x_595_, v___x_597_);
v___x_599_ = lean_unsigned_to_nat(1u);
v___x_600_ = lean_mk_empty_array_with_capacity(v___x_599_);
v___x_601_ = lean_array_push(v___x_600_, v___x_598_);
v___x_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
lean_ctor_set(v___x_602_, 1, v___y_569_);
return v___x_602_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__3(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__2));
v___x_613_ = l_Lean_mkAtom(v___x_612_);
return v___x_613_;
}
}
static lean_object* _init_l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__4(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_614_ = lean_obj_once(&l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__3, &l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__3_once, _init_l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__3);
v___x_615_ = lean_unsigned_to_nat(3u);
v___x_616_ = lean_mk_empty_array_with_capacity(v___x_615_);
v___x_617_ = lean_array_push(v___x_616_, v___x_614_);
return v___x_617_;
}
}
static lean_object* _init_l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__5(void){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_618_ = lean_obj_once(&l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__3, &l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__3_once, _init_l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__3);
v___x_619_ = lean_obj_once(&l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__4, &l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__4_once, _init_l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__4);
v___x_620_ = lean_array_push(v___x_619_, v___x_618_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName(lean_object* v_ident_621_){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_622_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__1));
v___x_623_ = lean_obj_once(&l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__5, &l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__5_once, _init_l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__5);
v___x_624_ = lean_array_push(v___x_623_, v_ident_621_);
v___x_625_ = lean_box(2);
v___x_626_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
lean_ctor_set(v___x_626_, 1, v___x_622_);
lean_ctor_set(v___x_626_, 2, v___x_624_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___lam__0(uint8_t v___x_627_, lean_object* v_____do__lift_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = l_Lean_SourceInfo_fromRef(v_____do__lift_628_, v___x_627_);
v___x_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_631_);
lean_ctor_set(v___x_632_, 1, v___y_630_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___lam__0___boxed(lean_object* v___x_633_, lean_object* v_____do__lift_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
uint8_t v___x_20975__boxed_637_; lean_object* v_res_638_; 
v___x_20975__boxed_637_ = lean_unbox(v___x_633_);
v_res_638_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___lam__0(v___x_20975__boxed_637_, v_____do__lift_634_, v___y_635_, v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec(v_____do__lift_634_);
return v_res_638_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__9(void){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_660_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__8));
v___x_661_ = l_String_toRawSubstring_x27(v___x_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg(lean_object* v_alts_669_, lean_object* v_discr_670_, lean_object* v_as_x27_671_, lean_object* v_b_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
if (lean_obj_tag(v_as_x27_671_) == 0)
{
lean_object* v___x_675_; 
lean_dec_ref(v___y_673_);
lean_dec(v_discr_670_);
lean_dec(v_alts_669_);
v___x_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_675_, 0, v_b_672_);
lean_ctor_set(v___x_675_, 1, v___y_674_);
return v___x_675_;
}
else
{
lean_object* v_head_676_; lean_object* v_tail_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_743_; 
v_head_676_ = lean_ctor_get(v_as_x27_671_, 0);
v_tail_677_ = lean_ctor_get(v_as_x27_671_, 1);
v_isSharedCheck_743_ = !lean_is_exclusive(v_as_x27_671_);
if (v_isSharedCheck_743_ == 0)
{
v___x_679_ = v_as_x27_671_;
v_isShared_680_ = v_isSharedCheck_743_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_tail_677_);
lean_inc(v_head_676_);
lean_dec(v_as_x27_671_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_743_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_681_; 
lean_inc(v_head_676_);
lean_inc(v_alts_669_);
v___x_681_ = l_Lean_Elab_Term_MatchExpr_getAltFor_x3f(v_alts_669_, v_head_676_);
if (lean_obj_tag(v___x_681_) == 1)
{
lean_object* v_val_682_; lean_object* v___x_683_; lean_object* v_a_684_; lean_object* v_a_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_741_; 
v_val_682_ = lean_ctor_get(v___x_681_, 0);
lean_inc(v_val_682_);
lean_dec_ref(v___x_681_);
lean_inc_ref(v___y_673_);
lean_inc(v_val_682_);
lean_inc(v_discr_670_);
v___x_683_ = l_Lean_Elab_Term_MatchExpr_getActuals(v_discr_670_, v_val_682_, v___y_673_, v___y_674_);
v_a_684_ = lean_ctor_get(v___x_683_, 0);
v_a_685_ = lean_ctor_get(v___x_683_, 1);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_741_ == 0)
{
v___x_687_ = v___x_683_;
v_isShared_688_ = v_isSharedCheck_741_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_a_685_);
lean_inc(v_a_684_);
lean_dec(v___x_683_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_741_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v_quotContext_689_; lean_object* v_currMacroScope_690_; lean_object* v_ref_691_; uint8_t v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_696_; 
v_quotContext_689_ = lean_ctor_get(v___y_673_, 1);
v_currMacroScope_690_ = lean_ctor_get(v___y_673_, 2);
v_ref_691_ = lean_ctor_get(v___y_673_, 5);
v___x_692_ = 0;
v___x_693_ = l_Lean_SourceInfo_fromRef(v_ref_691_, v___x_692_);
v___x_694_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__0));
lean_inc(v___x_693_);
if (v_isShared_688_ == 0)
{
lean_ctor_set_tag(v___x_687_, 2);
lean_ctor_set(v___x_687_, 1, v___x_694_);
lean_ctor_set(v___x_687_, 0, v___x_693_);
v___x_696_ = v___x_687_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_693_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v___x_694_);
v___x_696_ = v_reuseFailAlloc_740_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_703_; 
v___x_697_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2));
v___x_698_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__4));
v___x_699_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__6));
v___x_700_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__3));
v___x_701_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2));
lean_inc(v___x_693_);
if (v_isShared_680_ == 0)
{
lean_ctor_set_tag(v___x_679_, 2);
lean_ctor_set(v___x_679_, 1, v___x_701_);
lean_ctor_set(v___x_679_, 0, v___x_693_);
v___x_703_ = v___x_679_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_693_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v___x_701_);
v___x_703_ = v_reuseFailAlloc_739_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v_k_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_704_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__5));
v___x_705_ = lean_obj_once(&l_Lean_Elab_Term_MatchExpr_getActuals___closed__7, &l_Lean_Elab_Term_MatchExpr_getActuals___closed__7_once, _init_l_Lean_Elab_Term_MatchExpr_getActuals___closed__7);
v___x_706_ = lean_box(0);
lean_inc(v_currMacroScope_690_);
lean_inc(v_quotContext_689_);
v___x_707_ = l_Lean_addMacroScope(v_quotContext_689_, v___x_706_, v_currMacroScope_690_);
v___x_708_ = lean_box(0);
v___x_709_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__21));
lean_inc(v___x_693_);
v___x_710_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_710_, 0, v___x_693_);
lean_ctor_set(v___x_710_, 1, v___x_705_);
lean_ctor_set(v___x_710_, 2, v___x_707_);
lean_ctor_set(v___x_710_, 3, v___x_709_);
lean_inc(v___x_693_);
v___x_711_ = l_Lean_Syntax_node1(v___x_693_, v___x_704_, v___x_710_);
lean_inc(v___x_693_);
v___x_712_ = l_Lean_Syntax_node2(v___x_693_, v___x_700_, v___x_703_, v___x_711_);
v___x_713_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15));
lean_inc(v___x_693_);
v___x_714_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_693_);
lean_ctor_set(v___x_714_, 1, v___x_713_);
lean_inc(v_discr_670_);
lean_inc(v___x_693_);
v___x_715_ = l_Lean_Syntax_node3(v___x_693_, v___x_699_, v___x_712_, v_discr_670_, v___x_714_);
v___x_716_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__7));
lean_inc(v___x_693_);
v___x_717_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_717_, 0, v___x_693_);
lean_ctor_set(v___x_717_, 1, v___x_716_);
v___x_718_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__9, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__9_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__9);
v___x_719_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__10));
lean_inc(v_currMacroScope_690_);
lean_inc(v_quotContext_689_);
v___x_720_ = l_Lean_addMacroScope(v_quotContext_689_, v___x_719_, v_currMacroScope_690_);
lean_inc(v___x_693_);
v___x_721_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_721_, 0, v___x_693_);
lean_ctor_set(v___x_721_, 1, v___x_718_);
lean_ctor_set(v___x_721_, 2, v___x_720_);
lean_ctor_set(v___x_721_, 3, v___x_708_);
lean_inc(v___x_693_);
v___x_722_ = l_Lean_Syntax_node3(v___x_693_, v___x_698_, v___x_715_, v___x_717_, v___x_721_);
v___x_723_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4));
v___x_724_ = l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName(v_head_676_);
lean_inc(v___x_693_);
v___x_725_ = l_Lean_Syntax_node1(v___x_693_, v___x_723_, v___x_724_);
v_k_726_ = lean_ctor_get(v_val_682_, 4);
lean_inc(v_k_726_);
lean_dec(v_val_682_);
lean_inc(v___x_693_);
v___x_727_ = l_Lean_Syntax_node2(v___x_693_, v___x_697_, v___x_722_, v___x_725_);
v___x_728_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__12));
v___x_729_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__13));
lean_inc(v___x_693_);
v___x_730_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_693_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
v___x_731_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
v___x_732_ = l_Array_append___redArg(v___x_731_, v_a_684_);
lean_dec(v_a_684_);
lean_inc(v___x_693_);
v___x_733_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_733_, 0, v___x_693_);
lean_ctor_set(v___x_733_, 1, v___x_723_);
lean_ctor_set(v___x_733_, 2, v___x_732_);
lean_inc(v___x_693_);
v___x_734_ = l_Lean_Syntax_node2(v___x_693_, v___x_697_, v_k_726_, v___x_733_);
v___x_735_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__14));
lean_inc(v___x_693_);
v___x_736_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_693_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
v___x_737_ = l_Lean_Syntax_node6(v___x_693_, v___x_728_, v___x_696_, v___x_727_, v___x_730_, v___x_734_, v___x_736_, v_b_672_);
v_as_x27_671_ = v_tail_677_;
v_b_672_ = v___x_737_;
v___y_674_ = v_a_685_;
goto _start;
}
}
}
}
else
{
lean_dec(v___x_681_);
lean_del_object(v___x_679_);
lean_dec(v_head_676_);
v_as_x27_671_ = v_tail_677_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__1(void){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__0));
v___x_746_ = l_String_toRawSubstring_x27(v___x_745_);
return v___x_746_;
}
}
static lean_object* _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__8(void){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_757_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__7));
v___x_758_ = l_String_toRawSubstring_x27(v___x_757_);
return v___x_758_;
}
}
static lean_object* _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__11(void){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__10));
v___x_763_ = l_String_toRawSubstring_x27(v___x_762_);
return v___x_763_;
}
}
static lean_object* _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__25(void){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_798_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__24));
v___x_799_ = l_String_toRawSubstring_x27(v___x_798_);
return v___x_799_;
}
}
static lean_object* _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__33(void){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_816_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__32));
v___x_817_ = l_String_toRawSubstring_x27(v___x_816_);
return v___x_817_;
}
}
static lean_object* _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__36(void){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_821_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__35));
v___x_822_ = l_String_toRawSubstring_x27(v___x_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop(lean_object* v_kElse_837_, lean_object* v_discr_838_, lean_object* v_alts_839_, lean_object* v_a_840_, lean_object* v_a_841_){
_start:
{
lean_object* v_macroScope_842_; lean_object* v_traceMsgs_843_; lean_object* v_expandedMacroDecls_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_1121_; 
v_macroScope_842_ = lean_ctor_get(v_a_841_, 0);
v_traceMsgs_843_ = lean_ctor_get(v_a_841_, 1);
v_expandedMacroDecls_844_ = lean_ctor_get(v_a_841_, 2);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_a_841_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_846_ = v_a_841_;
v_isShared_847_ = v_isSharedCheck_1121_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_expandedMacroDecls_844_);
lean_inc(v_traceMsgs_843_);
lean_inc(v_macroScope_842_);
lean_dec(v_a_841_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_1121_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v_methods_848_; lean_object* v_quotContext_849_; lean_object* v_currRecDepth_850_; lean_object* v_maxRecDepth_851_; lean_object* v_ref_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_1119_; 
v_methods_848_ = lean_ctor_get(v_a_840_, 0);
v_quotContext_849_ = lean_ctor_get(v_a_840_, 1);
v_currRecDepth_850_ = lean_ctor_get(v_a_840_, 3);
v_maxRecDepth_851_ = lean_ctor_get(v_a_840_, 4);
v_ref_852_ = lean_ctor_get(v_a_840_, 5);
v_isSharedCheck_1119_ = !lean_is_exclusive(v_a_840_);
if (v_isSharedCheck_1119_ == 0)
{
lean_object* v_unused_1120_; 
v_unused_1120_ = lean_ctor_get(v_a_840_, 2);
lean_dec(v_unused_1120_);
v___x_854_ = v_a_840_;
v_isShared_855_ = v_isSharedCheck_1119_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_ref_852_);
lean_inc(v_maxRecDepth_851_);
lean_inc(v_currRecDepth_850_);
lean_inc(v_quotContext_849_);
lean_inc(v_methods_848_);
lean_dec(v_a_840_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_1119_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v_funNamesToMatch_856_; uint8_t v_saveActual_857_; lean_object* v_actual_859_; lean_object* v___y_860_; lean_object* v___y_861_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1102_; 
lean_inc(v_alts_839_);
v_funNamesToMatch_856_ = l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch(v_alts_839_);
lean_inc(v_alts_839_);
v_saveActual_857_ = l_Lean_Elab_Term_MatchExpr_shouldSaveActual(v_alts_839_);
v___x_1099_ = lean_unsigned_to_nat(1u);
v___x_1100_ = lean_nat_add(v_macroScope_842_, v___x_1099_);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 0, v___x_1100_);
v___x_1102_ = v___x_846_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v___x_1100_);
lean_ctor_set(v_reuseFailAlloc_1118_, 1, v_traceMsgs_843_);
lean_ctor_set(v_reuseFailAlloc_1118_, 2, v_expandedMacroDecls_844_);
v___x_1102_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1101_;
}
v___jp_858_:
{
lean_object* v_altsNext_862_; uint8_t v___x_863_; 
lean_inc(v_alts_839_);
v_altsNext_862_ = l_Lean_Elab_Term_MatchExpr_next(v_alts_839_, v_actual_859_);
v___x_863_ = l_List_isEmpty___redArg(v_altsNext_862_);
if (v___x_863_ == 0)
{
lean_object* v_quotContext_864_; lean_object* v_currMacroScope_865_; lean_object* v_ref_866_; lean_object* v___x_867_; 
v_quotContext_864_ = lean_ctor_get(v___y_860_, 1);
v_currMacroScope_865_ = lean_ctor_get(v___y_860_, 2);
v_ref_866_ = lean_ctor_get(v___y_860_, 5);
v___x_867_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___lam__0(v___x_863_, v_ref_866_, v___y_860_, v___y_861_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v_a_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_a_868_);
v_a_869_ = lean_ctor_get(v___x_867_, 1);
lean_inc(v_a_869_);
lean_dec_ref(v___x_867_);
v___x_870_ = lean_obj_once(&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__1, &l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__1_once, _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__1);
v___x_871_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__2));
lean_inc(v_currMacroScope_865_);
lean_inc(v_quotContext_864_);
v___x_872_ = l_Lean_addMacroScope(v_quotContext_864_, v___x_871_, v_currMacroScope_865_);
v___x_873_ = lean_box(0);
lean_inc(v___x_872_);
v___x_874_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_874_, 0, v_a_868_);
lean_ctor_set(v___x_874_, 1, v___x_870_);
lean_ctor_set(v___x_874_, 2, v___x_872_);
lean_ctor_set(v___x_874_, 3, v___x_873_);
lean_inc_ref(v___y_860_);
lean_inc(v_kElse_837_);
v___x_875_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop(v_kElse_837_, v___x_874_, v_altsNext_862_, v___y_860_, v_a_869_);
if (lean_obj_tag(v___x_875_) == 0)
{
if (v_saveActual_857_ == 0)
{
lean_object* v_a_876_; lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_956_; 
v_a_876_ = lean_ctor_get(v___x_875_, 0);
v_a_877_ = lean_ctor_get(v___x_875_, 1);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_956_ == 0)
{
v___x_879_ = v___x_875_;
v_isShared_880_ = v_isSharedCheck_956_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_inc(v_a_876_);
lean_dec(v___x_875_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_956_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_885_; 
v___x_881_ = l_Lean_SourceInfo_fromRef(v_ref_866_, v_saveActual_857_);
v___x_882_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__4));
v___x_883_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__0));
lean_inc(v___x_881_);
if (v_isShared_880_ == 0)
{
lean_ctor_set_tag(v___x_879_, 2);
lean_ctor_set(v___x_879_, 1, v___x_883_);
lean_ctor_set(v___x_879_, 0, v___x_881_);
v___x_885_ = v___x_879_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_881_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v___x_883_);
v___x_885_ = v_reuseFailAlloc_955_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_886_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__6));
v___x_887_ = lean_obj_once(&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__8, &l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__8_once, _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__8);
v___x_888_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__9));
lean_inc(v_currMacroScope_865_);
lean_inc(v_quotContext_864_);
v___x_889_ = l_Lean_addMacroScope(v_quotContext_864_, v___x_888_, v_currMacroScope_865_);
lean_inc(v___x_881_);
v___x_890_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_890_, 0, v___x_881_);
lean_ctor_set(v___x_890_, 1, v___x_887_);
lean_ctor_set(v___x_890_, 2, v___x_889_);
lean_ctor_set(v___x_890_, 3, v___x_873_);
lean_inc_ref(v___x_890_);
lean_inc(v___x_881_);
v___x_891_ = l_Lean_Syntax_node1(v___x_881_, v___x_886_, v___x_890_);
v___x_892_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__5));
lean_inc(v___x_881_);
v___x_893_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_881_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
v___x_894_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__4));
v___x_895_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__6));
v___x_896_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__3));
v___x_897_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2));
lean_inc(v___x_881_);
v___x_898_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_881_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v___x_899_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__5));
v___x_900_ = lean_obj_once(&l_Lean_Elab_Term_MatchExpr_getActuals___closed__7, &l_Lean_Elab_Term_MatchExpr_getActuals___closed__7_once, _init_l_Lean_Elab_Term_MatchExpr_getActuals___closed__7);
v___x_901_ = lean_box(0);
lean_inc(v_currMacroScope_865_);
lean_inc(v_quotContext_864_);
v___x_902_ = l_Lean_addMacroScope(v_quotContext_864_, v___x_901_, v_currMacroScope_865_);
v___x_903_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__21));
lean_inc(v___x_881_);
v___x_904_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_904_, 0, v___x_881_);
lean_ctor_set(v___x_904_, 1, v___x_900_);
lean_ctor_set(v___x_904_, 2, v___x_902_);
lean_ctor_set(v___x_904_, 3, v___x_903_);
lean_inc(v___x_881_);
v___x_905_ = l_Lean_Syntax_node1(v___x_881_, v___x_899_, v___x_904_);
lean_inc(v___x_881_);
v___x_906_ = l_Lean_Syntax_node2(v___x_881_, v___x_896_, v___x_898_, v___x_905_);
v___x_907_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15));
lean_inc(v___x_881_);
v___x_908_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_881_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
lean_inc_ref(v___x_908_);
lean_inc(v_discr_838_);
lean_inc(v___x_906_);
lean_inc(v___x_881_);
v___x_909_ = l_Lean_Syntax_node3(v___x_881_, v___x_895_, v___x_906_, v_discr_838_, v___x_908_);
v___x_910_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__7));
lean_inc(v___x_881_);
v___x_911_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_881_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = lean_obj_once(&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__11, &l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__11_once, _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__11);
v___x_913_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__12));
lean_inc(v_currMacroScope_865_);
lean_inc(v_quotContext_864_);
v___x_914_ = l_Lean_addMacroScope(v_quotContext_864_, v___x_913_, v_currMacroScope_865_);
lean_inc(v___x_881_);
v___x_915_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_915_, 0, v___x_881_);
lean_ctor_set(v___x_915_, 1, v___x_912_);
lean_ctor_set(v___x_915_, 2, v___x_914_);
lean_ctor_set(v___x_915_, 3, v___x_873_);
lean_inc(v___x_881_);
v___x_916_ = l_Lean_Syntax_node3(v___x_881_, v___x_894_, v___x_909_, v___x_911_, v___x_915_);
v___x_917_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__13));
lean_inc(v___x_881_);
v___x_918_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_881_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__13));
v___x_920_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__14));
lean_inc(v___x_881_);
v___x_921_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_881_);
lean_ctor_set(v___x_921_, 1, v___x_919_);
v___x_922_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__16));
v___x_923_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4));
v___x_924_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
lean_inc(v___x_881_);
v___x_925_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_925_, 0, v___x_881_);
lean_ctor_set(v___x_925_, 1, v___x_923_);
lean_ctor_set(v___x_925_, 2, v___x_924_);
lean_inc_ref(v___x_925_);
lean_inc(v___x_881_);
v___x_926_ = l_Lean_Syntax_node1(v___x_881_, v___x_922_, v___x_925_);
v___x_927_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18));
v___x_928_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20));
v___x_929_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22));
lean_inc(v___x_881_);
v___x_930_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_930_, 0, v___x_881_);
lean_ctor_set(v___x_930_, 1, v___x_870_);
lean_ctor_set(v___x_930_, 2, v___x_872_);
lean_ctor_set(v___x_930_, 3, v___x_873_);
lean_inc(v___x_881_);
v___x_931_ = l_Lean_Syntax_node1(v___x_881_, v___x_929_, v___x_930_);
v___x_932_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__23));
lean_inc(v___x_881_);
v___x_933_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_881_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
v___x_934_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2));
v___x_935_ = lean_obj_once(&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__25, &l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__25_once, _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__25);
v___x_936_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__27));
lean_inc(v_currMacroScope_865_);
lean_inc(v_quotContext_864_);
v___x_937_ = l_Lean_addMacroScope(v_quotContext_864_, v___x_936_, v_currMacroScope_865_);
v___x_938_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__30));
lean_inc(v___x_881_);
v___x_939_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_939_, 0, v___x_881_);
lean_ctor_set(v___x_939_, 1, v___x_935_);
lean_ctor_set(v___x_939_, 2, v___x_937_);
lean_ctor_set(v___x_939_, 3, v___x_938_);
lean_inc(v_discr_838_);
lean_inc(v___x_881_);
v___x_940_ = l_Lean_Syntax_node2(v___x_881_, v___x_923_, v_discr_838_, v___x_890_);
lean_inc(v___x_881_);
v___x_941_ = l_Lean_Syntax_node2(v___x_881_, v___x_934_, v___x_939_, v___x_940_);
lean_inc_ref_n(v___x_925_, 2);
lean_inc(v___x_881_);
v___x_942_ = l_Lean_Syntax_node5(v___x_881_, v___x_928_, v___x_931_, v___x_925_, v___x_925_, v___x_933_, v___x_941_);
lean_inc(v___x_881_);
v___x_943_ = l_Lean_Syntax_node1(v___x_881_, v___x_927_, v___x_942_);
v___x_944_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__31));
lean_inc(v___x_881_);
v___x_945_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_881_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
lean_inc(v___x_881_);
v___x_946_ = l_Lean_Syntax_node5(v___x_881_, v___x_920_, v___x_921_, v___x_926_, v___x_943_, v___x_945_, v_a_876_);
v___x_947_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__14));
lean_inc(v___x_881_);
v___x_948_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_881_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__1));
lean_inc(v___x_881_);
v___x_950_ = l_Lean_Syntax_node3(v___x_881_, v___x_949_, v___x_906_, v___x_925_, v___x_908_);
lean_inc(v___x_881_);
v___x_951_ = l_Lean_Syntax_node1(v___x_881_, v___x_923_, v___x_950_);
lean_inc(v___x_881_);
v___x_952_ = l_Lean_Syntax_node2(v___x_881_, v___x_934_, v_kElse_837_, v___x_951_);
v___x_953_ = l_Lean_Syntax_node8(v___x_881_, v___x_882_, v___x_885_, v___x_891_, v___x_893_, v___x_916_, v___x_918_, v___x_946_, v___x_948_, v___x_952_);
v___x_954_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg(v_alts_839_, v_discr_838_, v_funNamesToMatch_856_, v___x_953_, v___y_860_, v_a_877_);
return v___x_954_;
}
}
}
else
{
lean_object* v_a_957_; lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_1062_; 
v_a_957_ = lean_ctor_get(v___x_875_, 0);
v_a_958_ = lean_ctor_get(v___x_875_, 1);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_960_ = v___x_875_;
v_isShared_961_ = v_isSharedCheck_1062_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_inc(v_a_957_);
lean_dec(v___x_875_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_1062_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_962_; 
v___x_962_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___lam__0(v___x_863_, v_ref_866_, v___y_860_, v_a_958_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v_a_963_; lean_object* v_a_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_968_; 
v_a_963_ = lean_ctor_get(v___x_962_, 0);
lean_inc(v_a_963_);
v_a_964_ = lean_ctor_get(v___x_962_, 1);
lean_inc(v_a_964_);
lean_dec_ref(v___x_962_);
v___x_965_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__4));
v___x_966_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__0));
lean_inc(v_a_963_);
if (v_isShared_961_ == 0)
{
lean_ctor_set_tag(v___x_960_, 2);
lean_ctor_set(v___x_960_, 1, v___x_966_);
lean_ctor_set(v___x_960_, 0, v_a_963_);
v___x_968_ = v___x_960_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_a_963_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v___x_966_);
v___x_968_ = v_reuseFailAlloc_1052_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_969_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__6));
v___x_970_ = lean_obj_once(&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__8, &l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__8_once, _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__8);
v___x_971_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__9));
lean_inc(v_currMacroScope_865_);
lean_inc(v_quotContext_864_);
v___x_972_ = l_Lean_addMacroScope(v_quotContext_864_, v___x_971_, v_currMacroScope_865_);
lean_inc(v_a_963_);
v___x_973_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_973_, 0, v_a_963_);
lean_ctor_set(v___x_973_, 1, v___x_970_);
lean_ctor_set(v___x_973_, 2, v___x_972_);
lean_ctor_set(v___x_973_, 3, v___x_873_);
lean_inc_ref(v___x_973_);
lean_inc(v_a_963_);
v___x_974_ = l_Lean_Syntax_node1(v_a_963_, v___x_969_, v___x_973_);
v___x_975_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__5));
lean_inc(v_a_963_);
v___x_976_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_976_, 0, v_a_963_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
v___x_977_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__4));
v___x_978_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__6));
v___x_979_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__3));
v___x_980_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2));
lean_inc(v_a_963_);
v___x_981_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_981_, 0, v_a_963_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
v___x_982_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__5));
v___x_983_ = lean_obj_once(&l_Lean_Elab_Term_MatchExpr_getActuals___closed__7, &l_Lean_Elab_Term_MatchExpr_getActuals___closed__7_once, _init_l_Lean_Elab_Term_MatchExpr_getActuals___closed__7);
v___x_984_ = lean_box(0);
lean_inc(v_currMacroScope_865_);
lean_inc(v_quotContext_864_);
v___x_985_ = l_Lean_addMacroScope(v_quotContext_864_, v___x_984_, v_currMacroScope_865_);
v___x_986_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__21));
lean_inc(v_a_963_);
v___x_987_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_987_, 0, v_a_963_);
lean_ctor_set(v___x_987_, 1, v___x_983_);
lean_ctor_set(v___x_987_, 2, v___x_985_);
lean_ctor_set(v___x_987_, 3, v___x_986_);
lean_inc(v_a_963_);
v___x_988_ = l_Lean_Syntax_node1(v_a_963_, v___x_982_, v___x_987_);
lean_inc(v_a_963_);
v___x_989_ = l_Lean_Syntax_node2(v_a_963_, v___x_979_, v___x_981_, v___x_988_);
v___x_990_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15));
lean_inc(v_a_963_);
v___x_991_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_991_, 0, v_a_963_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
lean_inc_ref(v___x_991_);
lean_inc(v_discr_838_);
lean_inc(v___x_989_);
lean_inc(v_a_963_);
v___x_992_ = l_Lean_Syntax_node3(v_a_963_, v___x_978_, v___x_989_, v_discr_838_, v___x_991_);
v___x_993_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__7));
lean_inc(v_a_963_);
v___x_994_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_994_, 0, v_a_963_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
v___x_995_ = lean_obj_once(&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__11, &l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__11_once, _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__11);
v___x_996_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__12));
lean_inc(v_currMacroScope_865_);
lean_inc(v_quotContext_864_);
v___x_997_ = l_Lean_addMacroScope(v_quotContext_864_, v___x_996_, v_currMacroScope_865_);
lean_inc(v_a_963_);
v___x_998_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_998_, 0, v_a_963_);
lean_ctor_set(v___x_998_, 1, v___x_995_);
lean_ctor_set(v___x_998_, 2, v___x_997_);
lean_ctor_set(v___x_998_, 3, v___x_873_);
lean_inc(v_a_963_);
v___x_999_ = l_Lean_Syntax_node3(v_a_963_, v___x_977_, v___x_992_, v___x_994_, v___x_998_);
v___x_1000_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__13));
lean_inc(v_a_963_);
v___x_1001_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1001_, 0, v_a_963_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__13));
v___x_1003_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__14));
lean_inc(v_a_963_);
v___x_1004_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1004_, 0, v_a_963_);
lean_ctor_set(v___x_1004_, 1, v___x_1002_);
v___x_1005_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__16));
v___x_1006_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4));
v___x_1007_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
lean_inc(v_a_963_);
v___x_1008_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1008_, 0, v_a_963_);
lean_ctor_set(v___x_1008_, 1, v___x_1006_);
lean_ctor_set(v___x_1008_, 2, v___x_1007_);
lean_inc_ref(v___x_1008_);
lean_inc(v_a_963_);
v___x_1009_ = l_Lean_Syntax_node1(v_a_963_, v___x_1005_, v___x_1008_);
v___x_1010_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18));
v___x_1011_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20));
v___x_1012_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22));
v___x_1013_ = lean_obj_once(&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__33, &l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__33_once, _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__33);
v___x_1014_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__34));
lean_inc(v_currMacroScope_865_);
lean_inc(v_quotContext_864_);
v___x_1015_ = l_Lean_addMacroScope(v_quotContext_864_, v___x_1014_, v_currMacroScope_865_);
lean_inc(v_a_963_);
v___x_1016_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1016_, 0, v_a_963_);
lean_ctor_set(v___x_1016_, 1, v___x_1013_);
lean_ctor_set(v___x_1016_, 2, v___x_1015_);
lean_ctor_set(v___x_1016_, 3, v___x_873_);
lean_inc(v_a_963_);
v___x_1017_ = l_Lean_Syntax_node1(v_a_963_, v___x_1012_, v___x_1016_);
v___x_1018_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__23));
lean_inc(v_a_963_);
v___x_1019_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1019_, 0, v_a_963_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
v___x_1020_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2));
v___x_1021_ = lean_obj_once(&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__36, &l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__36_once, _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__36);
v___x_1022_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__38));
lean_inc(v_currMacroScope_865_);
lean_inc(v_quotContext_864_);
v___x_1023_ = l_Lean_addMacroScope(v_quotContext_864_, v___x_1022_, v_currMacroScope_865_);
v___x_1024_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__41));
lean_inc(v_a_963_);
v___x_1025_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1025_, 0, v_a_963_);
lean_ctor_set(v___x_1025_, 1, v___x_1021_);
lean_ctor_set(v___x_1025_, 2, v___x_1023_);
lean_ctor_set(v___x_1025_, 3, v___x_1024_);
lean_inc(v_discr_838_);
lean_inc(v_a_963_);
v___x_1026_ = l_Lean_Syntax_node2(v_a_963_, v___x_1006_, v_discr_838_, v___x_973_);
lean_inc(v___x_1026_);
lean_inc(v_a_963_);
v___x_1027_ = l_Lean_Syntax_node2(v_a_963_, v___x_1020_, v___x_1025_, v___x_1026_);
lean_inc_ref(v___x_1019_);
lean_inc_ref_n(v___x_1008_, 2);
lean_inc(v_a_963_);
v___x_1028_ = l_Lean_Syntax_node5(v_a_963_, v___x_1011_, v___x_1017_, v___x_1008_, v___x_1008_, v___x_1019_, v___x_1027_);
lean_inc(v_a_963_);
v___x_1029_ = l_Lean_Syntax_node1(v_a_963_, v___x_1010_, v___x_1028_);
v___x_1030_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__31));
lean_inc(v_a_963_);
v___x_1031_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1031_, 0, v_a_963_);
lean_ctor_set(v___x_1031_, 1, v___x_1030_);
lean_inc(v_a_963_);
v___x_1032_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1032_, 0, v_a_963_);
lean_ctor_set(v___x_1032_, 1, v___x_870_);
lean_ctor_set(v___x_1032_, 2, v___x_872_);
lean_ctor_set(v___x_1032_, 3, v___x_873_);
lean_inc(v_a_963_);
v___x_1033_ = l_Lean_Syntax_node1(v_a_963_, v___x_1012_, v___x_1032_);
v___x_1034_ = lean_obj_once(&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__25, &l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__25_once, _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__25);
v___x_1035_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__27));
lean_inc(v_currMacroScope_865_);
lean_inc(v_quotContext_864_);
v___x_1036_ = l_Lean_addMacroScope(v_quotContext_864_, v___x_1035_, v_currMacroScope_865_);
v___x_1037_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__30));
lean_inc(v_a_963_);
v___x_1038_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1038_, 0, v_a_963_);
lean_ctor_set(v___x_1038_, 1, v___x_1034_);
lean_ctor_set(v___x_1038_, 2, v___x_1036_);
lean_ctor_set(v___x_1038_, 3, v___x_1037_);
lean_inc(v_a_963_);
v___x_1039_ = l_Lean_Syntax_node2(v_a_963_, v___x_1020_, v___x_1038_, v___x_1026_);
lean_inc_ref_n(v___x_1008_, 2);
lean_inc(v_a_963_);
v___x_1040_ = l_Lean_Syntax_node5(v_a_963_, v___x_1011_, v___x_1033_, v___x_1008_, v___x_1008_, v___x_1019_, v___x_1039_);
lean_inc(v_a_963_);
v___x_1041_ = l_Lean_Syntax_node1(v_a_963_, v___x_1010_, v___x_1040_);
lean_inc_ref(v___x_1031_);
lean_inc(v___x_1009_);
lean_inc_ref(v___x_1004_);
lean_inc(v_a_963_);
v___x_1042_ = l_Lean_Syntax_node5(v_a_963_, v___x_1003_, v___x_1004_, v___x_1009_, v___x_1041_, v___x_1031_, v_a_957_);
lean_inc(v_a_963_);
v___x_1043_ = l_Lean_Syntax_node5(v_a_963_, v___x_1003_, v___x_1004_, v___x_1009_, v___x_1029_, v___x_1031_, v___x_1042_);
v___x_1044_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__14));
lean_inc(v_a_963_);
v___x_1045_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1045_, 0, v_a_963_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
v___x_1046_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__1));
lean_inc(v_a_963_);
v___x_1047_ = l_Lean_Syntax_node3(v_a_963_, v___x_1046_, v___x_989_, v___x_1008_, v___x_991_);
lean_inc(v_a_963_);
v___x_1048_ = l_Lean_Syntax_node1(v_a_963_, v___x_1006_, v___x_1047_);
lean_inc(v_a_963_);
v___x_1049_ = l_Lean_Syntax_node2(v_a_963_, v___x_1020_, v_kElse_837_, v___x_1048_);
v___x_1050_ = l_Lean_Syntax_node8(v_a_963_, v___x_965_, v___x_968_, v___x_974_, v___x_976_, v___x_999_, v___x_1001_, v___x_1043_, v___x_1045_, v___x_1049_);
v___x_1051_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg(v_alts_839_, v_discr_838_, v_funNamesToMatch_856_, v___x_1050_, v___y_860_, v_a_964_);
return v___x_1051_;
}
}
else
{
lean_object* v_a_1053_; lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1061_; 
lean_del_object(v___x_960_);
lean_dec(v_a_957_);
lean_dec(v___x_872_);
lean_dec_ref(v___y_860_);
lean_dec(v_funNamesToMatch_856_);
lean_dec(v_alts_839_);
lean_dec(v_discr_838_);
lean_dec(v_kElse_837_);
v_a_1053_ = lean_ctor_get(v___x_962_, 0);
v_a_1054_ = lean_ctor_get(v___x_962_, 1);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1056_ = v___x_962_;
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_inc(v_a_1053_);
lean_dec(v___x_962_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1059_; 
if (v_isShared_1057_ == 0)
{
v___x_1059_ = v___x_1056_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1053_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v_a_1054_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
}
}
else
{
lean_dec(v___x_872_);
lean_dec_ref(v___y_860_);
lean_dec(v_funNamesToMatch_856_);
lean_dec(v_alts_839_);
lean_dec(v_discr_838_);
lean_dec(v_kElse_837_);
return v___x_875_;
}
}
else
{
lean_object* v_a_1063_; lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
lean_dec(v_altsNext_862_);
lean_dec_ref(v___y_860_);
lean_dec(v_funNamesToMatch_856_);
lean_dec(v_alts_839_);
lean_dec(v_discr_838_);
lean_dec(v_kElse_837_);
v_a_1063_ = lean_ctor_get(v___x_867_, 0);
v_a_1064_ = lean_ctor_get(v___x_867_, 1);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_867_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_inc(v_a_1063_);
lean_dec(v___x_867_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1063_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v_a_1064_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
else
{
lean_object* v_quotContext_1072_; lean_object* v_currMacroScope_1073_; lean_object* v_ref_1074_; uint8_t v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
lean_dec(v_altsNext_862_);
v_quotContext_1072_ = lean_ctor_get(v___y_860_, 1);
v_currMacroScope_1073_ = lean_ctor_get(v___y_860_, 2);
v_ref_1074_ = lean_ctor_get(v___y_860_, 5);
v___x_1075_ = 0;
v___x_1076_ = l_Lean_SourceInfo_fromRef(v_ref_1074_, v___x_1075_);
v___x_1077_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2));
v___x_1078_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4));
v___x_1079_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__1));
v___x_1080_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__3));
v___x_1081_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2));
lean_inc(v___x_1076_);
v___x_1082_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1076_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
v___x_1083_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__5));
v___x_1084_ = lean_obj_once(&l_Lean_Elab_Term_MatchExpr_getActuals___closed__7, &l_Lean_Elab_Term_MatchExpr_getActuals___closed__7_once, _init_l_Lean_Elab_Term_MatchExpr_getActuals___closed__7);
v___x_1085_ = lean_box(0);
lean_inc(v_currMacroScope_1073_);
lean_inc(v_quotContext_1072_);
v___x_1086_ = l_Lean_addMacroScope(v_quotContext_1072_, v___x_1085_, v_currMacroScope_1073_);
v___x_1087_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__21));
lean_inc(v___x_1076_);
v___x_1088_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1076_);
lean_ctor_set(v___x_1088_, 1, v___x_1084_);
lean_ctor_set(v___x_1088_, 2, v___x_1086_);
lean_ctor_set(v___x_1088_, 3, v___x_1087_);
lean_inc(v___x_1076_);
v___x_1089_ = l_Lean_Syntax_node1(v___x_1076_, v___x_1083_, v___x_1088_);
lean_inc(v___x_1076_);
v___x_1090_ = l_Lean_Syntax_node2(v___x_1076_, v___x_1080_, v___x_1082_, v___x_1089_);
v___x_1091_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
lean_inc(v___x_1076_);
v___x_1092_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1076_);
lean_ctor_set(v___x_1092_, 1, v___x_1078_);
lean_ctor_set(v___x_1092_, 2, v___x_1091_);
v___x_1093_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15));
lean_inc(v___x_1076_);
v___x_1094_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1076_);
lean_ctor_set(v___x_1094_, 1, v___x_1093_);
lean_inc(v___x_1076_);
v___x_1095_ = l_Lean_Syntax_node3(v___x_1076_, v___x_1079_, v___x_1090_, v___x_1092_, v___x_1094_);
lean_inc(v___x_1076_);
v___x_1096_ = l_Lean_Syntax_node1(v___x_1076_, v___x_1078_, v___x_1095_);
v___x_1097_ = l_Lean_Syntax_node2(v___x_1076_, v___x_1077_, v_kElse_837_, v___x_1096_);
v___x_1098_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg(v_alts_839_, v_discr_838_, v_funNamesToMatch_856_, v___x_1097_, v___y_860_, v___y_861_);
return v___x_1098_;
}
}
v_reusejp_1101_:
{
lean_object* v___x_1104_; 
lean_inc(v_ref_852_);
lean_inc(v_macroScope_842_);
lean_inc(v_quotContext_849_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 2, v_macroScope_842_);
v___x_1104_ = v___x_854_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_methods_848_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v_quotContext_849_);
lean_ctor_set(v_reuseFailAlloc_1117_, 2, v_macroScope_842_);
lean_ctor_set(v_reuseFailAlloc_1117_, 3, v_currRecDepth_850_);
lean_ctor_set(v_reuseFailAlloc_1117_, 4, v_maxRecDepth_851_);
lean_ctor_set(v_reuseFailAlloc_1117_, 5, v_ref_852_);
v___x_1104_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
if (v_saveActual_857_ == 0)
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
lean_dec(v_quotContext_849_);
lean_dec(v_macroScope_842_);
v___x_1105_ = l_Lean_SourceInfo_fromRef(v_ref_852_, v_saveActual_857_);
lean_dec(v_ref_852_);
v___x_1106_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1));
v___x_1107_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getParams___closed__0));
lean_inc(v___x_1105_);
v___x_1108_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1105_);
lean_ctor_set(v___x_1108_, 1, v___x_1107_);
v___x_1109_ = l_Lean_Syntax_node1(v___x_1105_, v___x_1106_, v___x_1108_);
v_actual_859_ = v___x_1109_;
v___y_860_ = v___x_1104_;
v___y_861_ = v___x_1102_;
goto v___jp_858_;
}
else
{
uint8_t v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1110_ = 0;
v___x_1111_ = l_Lean_SourceInfo_fromRef(v_ref_852_, v___x_1110_);
lean_dec(v_ref_852_);
v___x_1112_ = lean_obj_once(&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__33, &l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__33_once, _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__33);
v___x_1113_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__34));
v___x_1114_ = l_Lean_addMacroScope(v_quotContext_849_, v___x_1113_, v_macroScope_842_);
v___x_1115_ = lean_box(0);
v___x_1116_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1111_);
lean_ctor_set(v___x_1116_, 1, v___x_1112_);
lean_ctor_set(v___x_1116_, 2, v___x_1114_);
lean_ctor_set(v___x_1116_, 3, v___x_1115_);
v_actual_859_ = v___x_1116_;
v___y_860_ = v___x_1104_;
v___y_861_ = v___x_1102_;
goto v___jp_858_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0(lean_object* v_alts_1122_, lean_object* v_discr_1123_, lean_object* v_as_1124_, lean_object* v_as_x27_1125_, lean_object* v_b_1126_, lean_object* v_a_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v___x_1130_; 
v___x_1130_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg(v_alts_1122_, v_discr_1123_, v_as_x27_1125_, v_b_1126_, v___y_1128_, v___y_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___boxed(lean_object* v_alts_1131_, lean_object* v_discr_1132_, lean_object* v_as_1133_, lean_object* v_as_x27_1134_, lean_object* v_b_1135_, lean_object* v_a_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0(v_alts_1131_, v_discr_1132_, v_as_1133_, v_as_x27_1134_, v_b_1135_, v_a_1136_, v___y_1137_, v___y_1138_);
lean_dec(v_as_1133_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_generate___lam__0(lean_object* v_____do__lift_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
uint8_t v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1143_ = 0;
v___x_1144_ = l_Lean_SourceInfo_fromRef(v_____do__lift_1140_, v___x_1143_);
v___x_1145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
lean_ctor_set(v___x_1145_, 1, v___y_1142_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_generate___lam__0___boxed(lean_object* v_____do__lift_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_Elab_Term_MatchExpr_generate___lam__0(v_____do__lift_1146_, v___y_1147_, v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec(v_____do__lift_1146_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg(lean_object* v_as_x27_1156_, lean_object* v_b_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
if (lean_obj_tag(v_as_x27_1156_) == 0)
{
lean_object* v___x_1160_; 
lean_dec_ref(v___y_1158_);
v___x_1160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1160_, 0, v_b_1157_);
lean_ctor_set(v___x_1160_, 1, v___y_1159_);
return v___x_1160_;
}
else
{
lean_object* v_head_1161_; lean_object* v_tail_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1205_; 
v_head_1161_ = lean_ctor_get(v_as_x27_1156_, 0);
v_tail_1162_ = lean_ctor_get(v_as_x27_1156_, 1);
v_isSharedCheck_1205_ = !lean_is_exclusive(v_as_x27_1156_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1164_ = v_as_x27_1156_;
v_isShared_1165_ = v_isSharedCheck_1205_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_tail_1162_);
lean_inc(v_head_1161_);
lean_dec(v_as_x27_1156_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1205_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1166_; 
lean_inc_ref(v___y_1158_);
lean_inc(v_head_1161_);
v___x_1166_ = l_Lean_Elab_Term_MatchExpr_getParams(v_head_1161_, v___y_1158_, v___y_1159_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v_a_1167_; lean_object* v_a_1168_; lean_object* v_ref_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v_rhs_1173_; lean_object* v_k_1174_; lean_object* v___x_1175_; uint8_t v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1179_; 
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
lean_inc(v_a_1167_);
v_a_1168_ = lean_ctor_get(v___x_1166_, 1);
lean_inc(v_a_1168_);
lean_dec_ref(v___x_1166_);
v_ref_1169_ = lean_ctor_get(v___y_1158_, 5);
v___x_1170_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__0));
v___x_1171_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__1));
v___x_1172_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18));
v_rhs_1173_ = lean_ctor_get(v_head_1161_, 3);
lean_inc(v_rhs_1173_);
v_k_1174_ = lean_ctor_get(v_head_1161_, 4);
lean_inc(v_k_1174_);
lean_dec(v_head_1161_);
v___x_1175_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20));
v___x_1176_ = 0;
v___x_1177_ = l_Lean_SourceInfo_fromRef(v_ref_1169_, v___x_1176_);
lean_inc(v___x_1177_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set_tag(v___x_1164_, 2);
lean_ctor_set(v___x_1164_, 1, v___x_1170_);
lean_ctor_set(v___x_1164_, 0, v___x_1177_);
v___x_1179_ = v___x_1164_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1177_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v___x_1170_);
v___x_1179_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1180_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22));
lean_inc(v___x_1177_);
v___x_1181_ = l_Lean_Syntax_node1(v___x_1177_, v___x_1180_, v_k_1174_);
v___x_1182_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4));
v___x_1183_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
v___x_1184_ = l_Array_append___redArg(v___x_1183_, v_a_1167_);
lean_dec(v_a_1167_);
lean_inc(v___x_1177_);
v___x_1185_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1177_);
lean_ctor_set(v___x_1185_, 1, v___x_1182_);
lean_ctor_set(v___x_1185_, 2, v___x_1184_);
lean_inc(v___x_1177_);
v___x_1186_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1177_);
lean_ctor_set(v___x_1186_, 1, v___x_1182_);
lean_ctor_set(v___x_1186_, 2, v___x_1183_);
v___x_1187_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__23));
lean_inc(v___x_1177_);
v___x_1188_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1177_);
lean_ctor_set(v___x_1188_, 1, v___x_1187_);
lean_inc(v___x_1177_);
v___x_1189_ = l_Lean_Syntax_node5(v___x_1177_, v___x_1175_, v___x_1181_, v___x_1185_, v___x_1186_, v___x_1188_, v_rhs_1173_);
lean_inc(v___x_1177_);
v___x_1190_ = l_Lean_Syntax_node1(v___x_1177_, v___x_1172_, v___x_1189_);
v___x_1191_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__31));
lean_inc(v___x_1177_);
v___x_1192_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1177_);
lean_ctor_set(v___x_1192_, 1, v___x_1191_);
v___x_1193_ = l_Lean_Syntax_node4(v___x_1177_, v___x_1171_, v___x_1179_, v___x_1190_, v___x_1192_, v_b_1157_);
v_as_x27_1156_ = v_tail_1162_;
v_b_1157_ = v___x_1193_;
v___y_1159_ = v_a_1168_;
goto _start;
}
}
else
{
lean_object* v_a_1196_; lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1204_; 
lean_del_object(v___x_1164_);
lean_dec(v_tail_1162_);
lean_dec(v_head_1161_);
lean_dec_ref(v___y_1158_);
lean_dec(v_b_1157_);
v_a_1196_ = lean_ctor_get(v___x_1166_, 0);
v_a_1197_ = lean_ctor_get(v___x_1166_, 1);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1199_ = v___x_1166_;
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_inc(v_a_1196_);
lean_dec(v___x_1166_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1200_ == 0)
{
v___x_1202_ = v___x_1199_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_a_1196_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v_a_1197_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__0(lean_object* v_x_1206_, lean_object* v_x_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
if (lean_obj_tag(v_x_1206_) == 0)
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
lean_dec_ref(v___y_1208_);
v___x_1210_ = l_List_reverse___redArg(v_x_1207_);
v___x_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
lean_ctor_set(v___x_1211_, 1, v___y_1209_);
return v___x_1211_;
}
else
{
lean_object* v_head_1212_; lean_object* v_tail_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1224_; 
v_head_1212_ = lean_ctor_get(v_x_1206_, 0);
v_tail_1213_ = lean_ctor_get(v_x_1206_, 1);
v_isSharedCheck_1224_ = !lean_is_exclusive(v_x_1206_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1215_ = v_x_1206_;
v_isShared_1216_ = v_isSharedCheck_1224_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_tail_1213_);
lean_inc(v_head_1212_);
lean_dec(v_x_1206_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1224_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1217_; lean_object* v_a_1218_; lean_object* v_a_1219_; lean_object* v___x_1221_; 
lean_inc_ref(v___y_1208_);
v___x_1217_ = l_Lean_Elab_Term_MatchExpr_initK(v_head_1212_, v___y_1208_, v___y_1209_);
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc(v_a_1218_);
v_a_1219_ = lean_ctor_get(v___x_1217_, 1);
lean_inc(v_a_1219_);
lean_dec_ref(v___x_1217_);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 1, v_x_1207_);
lean_ctor_set(v___x_1215_, 0, v_a_1218_);
v___x_1221_ = v___x_1215_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1218_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v_x_1207_);
v___x_1221_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
v_x_1206_ = v_tail_1213_;
v_x_1207_ = v___x_1221_;
v___y_1209_ = v_a_1219_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_MatchExpr_generate___closed__4(void){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1235_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_generate___closed__3));
v___x_1236_ = l_String_toRawSubstring_x27(v___x_1235_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_generate(lean_object* v_discr_1251_, lean_object* v_alts_1252_, lean_object* v_elseAlt_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1256_ = lean_box(0);
lean_inc_ref(v_a_1254_);
v___x_1257_ = l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__0(v_alts_1252_, v___x_1256_, v_a_1254_, v_a_1255_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v_a_1258_; lean_object* v_a_1259_; lean_object* v_quotContext_1260_; lean_object* v_currMacroScope_1261_; lean_object* v_ref_1262_; lean_object* v___x_1263_; lean_object* v_a_1264_; lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1384_; 
v_a_1258_ = lean_ctor_get(v___x_1257_, 0);
lean_inc(v_a_1258_);
v_a_1259_ = lean_ctor_get(v___x_1257_, 1);
lean_inc(v_a_1259_);
lean_dec_ref(v___x_1257_);
v_quotContext_1260_ = lean_ctor_get(v_a_1254_, 1);
v_currMacroScope_1261_ = lean_ctor_get(v_a_1254_, 2);
v_ref_1262_ = lean_ctor_get(v_a_1254_, 5);
v___x_1263_ = l_Lean_Elab_Term_MatchExpr_generate___lam__0(v_ref_1262_, v_a_1254_, v_a_1259_);
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
v_a_1265_ = lean_ctor_get(v___x_1263_, 1);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1267_ = v___x_1263_;
v_isShared_1268_ = v_isSharedCheck_1384_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_inc(v_a_1264_);
lean_dec(v___x_1263_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1384_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1269_; lean_object* v_a_1270_; lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1383_; 
v___x_1269_ = l_Lean_Elab_Term_MatchExpr_generate___lam__0(v_ref_1262_, v_a_1254_, v_a_1265_);
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
v_a_1271_ = lean_ctor_get(v___x_1269_, 1);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1273_ = v___x_1269_;
v_isShared_1274_ = v_isSharedCheck_1383_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_inc(v_a_1270_);
lean_dec(v___x_1269_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1383_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1275_ = lean_obj_once(&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__1, &l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__1_once, _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__1);
v___x_1276_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__2));
lean_inc(v_currMacroScope_1261_);
lean_inc(v_quotContext_1260_);
v___x_1277_ = l_Lean_addMacroScope(v_quotContext_1260_, v___x_1276_, v_currMacroScope_1261_);
lean_inc(v___x_1277_);
v___x_1278_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1278_, 0, v_a_1264_);
lean_ctor_set(v___x_1278_, 1, v___x_1275_);
lean_ctor_set(v___x_1278_, 2, v___x_1277_);
lean_ctor_set(v___x_1278_, 3, v___x_1256_);
v___x_1279_ = lean_obj_once(&l_Lean_Elab_Term_MatchExpr_initK___closed__1, &l_Lean_Elab_Term_MatchExpr_initK___closed__1_once, _init_l_Lean_Elab_Term_MatchExpr_initK___closed__1);
v___x_1280_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_initK___closed__2));
lean_inc(v_currMacroScope_1261_);
lean_inc(v_quotContext_1260_);
v___x_1281_ = l_Lean_addMacroScope(v_quotContext_1260_, v___x_1280_, v_currMacroScope_1261_);
lean_inc(v___x_1281_);
v___x_1282_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1282_, 0, v_a_1270_);
lean_ctor_set(v___x_1282_, 1, v___x_1279_);
lean_ctor_set(v___x_1282_, 2, v___x_1281_);
lean_ctor_set(v___x_1282_, 3, v___x_1256_);
lean_inc_ref(v_a_1254_);
lean_inc(v_a_1258_);
v___x_1283_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop(v___x_1282_, v___x_1278_, v_a_1258_, v_a_1254_, v_a_1271_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; lean_object* v_a_1285_; lean_object* v___x_1286_; lean_object* v_a_1287_; lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1373_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_a_1284_);
v_a_1285_ = lean_ctor_get(v___x_1283_, 1);
lean_inc(v_a_1285_);
lean_dec_ref(v___x_1283_);
v___x_1286_ = l_Lean_Elab_Term_MatchExpr_generate___lam__0(v_ref_1262_, v_a_1254_, v_a_1285_);
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
v_a_1288_ = lean_ctor_get(v___x_1286_, 1);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1290_ = v___x_1286_;
v_isShared_1291_ = v_isSharedCheck_1373_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_inc(v_a_1287_);
lean_dec(v___x_1286_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1373_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1295_; 
v___x_1292_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__0));
v___x_1293_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__1));
lean_inc(v_a_1287_);
if (v_isShared_1291_ == 0)
{
lean_ctor_set_tag(v___x_1290_, 2);
lean_ctor_set(v___x_1290_, 1, v___x_1292_);
v___x_1295_ = v___x_1290_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_a_1287_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v___x_1292_);
v___x_1295_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1305_; 
v___x_1296_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18));
v___x_1297_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20));
v___x_1298_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22));
lean_inc(v_a_1287_);
v___x_1299_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1299_, 0, v_a_1287_);
lean_ctor_set(v___x_1299_, 1, v___x_1279_);
lean_ctor_set(v___x_1299_, 2, v___x_1281_);
lean_ctor_set(v___x_1299_, 3, v___x_1256_);
lean_inc(v_a_1287_);
v___x_1300_ = l_Lean_Syntax_node1(v_a_1287_, v___x_1298_, v___x_1299_);
v___x_1301_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4));
v___x_1302_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1));
v___x_1303_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2));
lean_inc(v_a_1287_);
if (v_isShared_1274_ == 0)
{
lean_ctor_set_tag(v___x_1273_, 2);
lean_ctor_set(v___x_1273_, 1, v___x_1303_);
lean_ctor_set(v___x_1273_, 0, v_a_1287_);
v___x_1305_ = v___x_1273_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1287_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v___x_1303_);
v___x_1305_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1309_; 
v___x_1306_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1));
v___x_1307_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getParams___closed__0));
lean_inc(v_a_1287_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set_tag(v___x_1267_, 2);
lean_ctor_set(v___x_1267_, 1, v___x_1307_);
lean_ctor_set(v___x_1267_, 0, v_a_1287_);
v___x_1309_ = v___x_1267_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1287_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v___x_1307_);
v___x_1309_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
lean_inc(v_a_1287_);
v___x_1310_ = l_Lean_Syntax_node1(v_a_1287_, v___x_1306_, v___x_1309_);
lean_inc(v_a_1287_);
v___x_1311_ = l_Lean_Syntax_node1(v_a_1287_, v___x_1301_, v___x_1310_);
v___x_1312_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__5));
lean_inc(v_a_1287_);
v___x_1313_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1313_, 0, v_a_1287_);
lean_ctor_set(v___x_1313_, 1, v___x_1312_);
v___x_1314_ = lean_obj_once(&l_Lean_Elab_Term_MatchExpr_getParams___closed__2, &l_Lean_Elab_Term_MatchExpr_getParams___closed__2_once, _init_l_Lean_Elab_Term_MatchExpr_getParams___closed__2);
v___x_1315_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getParams___closed__3));
lean_inc(v_currMacroScope_1261_);
lean_inc(v_quotContext_1260_);
v___x_1316_ = l_Lean_addMacroScope(v_quotContext_1260_, v___x_1315_, v_currMacroScope_1261_);
v___x_1317_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_generate___closed__2));
lean_inc(v_a_1287_);
v___x_1318_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1318_, 0, v_a_1287_);
lean_ctor_set(v___x_1318_, 1, v___x_1314_);
lean_ctor_set(v___x_1318_, 2, v___x_1316_);
lean_ctor_set(v___x_1318_, 3, v___x_1317_);
lean_inc(v_a_1287_);
v___x_1319_ = l_Lean_Syntax_node2(v_a_1287_, v___x_1301_, v___x_1313_, v___x_1318_);
v___x_1320_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
lean_inc(v_a_1287_);
v___x_1321_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1321_, 0, v_a_1287_);
lean_ctor_set(v___x_1321_, 1, v___x_1301_);
lean_ctor_set(v___x_1321_, 2, v___x_1320_);
v___x_1322_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15));
lean_inc(v_a_1287_);
v___x_1323_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1323_, 0, v_a_1287_);
lean_ctor_set(v___x_1323_, 1, v___x_1322_);
lean_inc_ref(v___x_1321_);
lean_inc(v_a_1287_);
v___x_1324_ = l_Lean_Syntax_node5(v_a_1287_, v___x_1302_, v___x_1305_, v___x_1311_, v___x_1319_, v___x_1321_, v___x_1323_);
lean_inc(v_a_1287_);
v___x_1325_ = l_Lean_Syntax_node1(v_a_1287_, v___x_1301_, v___x_1324_);
v___x_1326_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__23));
lean_inc(v_a_1287_);
v___x_1327_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1327_, 0, v_a_1287_);
lean_ctor_set(v___x_1327_, 1, v___x_1326_);
lean_inc_ref(v___x_1327_);
lean_inc_ref(v___x_1321_);
lean_inc(v_a_1287_);
v___x_1328_ = l_Lean_Syntax_node5(v_a_1287_, v___x_1297_, v___x_1300_, v___x_1325_, v___x_1321_, v___x_1327_, v_elseAlt_1253_);
lean_inc(v_a_1287_);
v___x_1329_ = l_Lean_Syntax_node1(v_a_1287_, v___x_1296_, v___x_1328_);
v___x_1330_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__31));
lean_inc(v_a_1287_);
v___x_1331_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1331_, 0, v_a_1287_);
lean_ctor_set(v___x_1331_, 1, v___x_1330_);
v___x_1332_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__13));
v___x_1333_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__14));
lean_inc(v_a_1287_);
v___x_1334_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1334_, 0, v_a_1287_);
lean_ctor_set(v___x_1334_, 1, v___x_1332_);
v___x_1335_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__16));
lean_inc_ref(v___x_1321_);
lean_inc(v_a_1287_);
v___x_1336_ = l_Lean_Syntax_node1(v_a_1287_, v___x_1335_, v___x_1321_);
lean_inc(v_a_1287_);
v___x_1337_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1337_, 0, v_a_1287_);
lean_ctor_set(v___x_1337_, 1, v___x_1275_);
lean_ctor_set(v___x_1337_, 2, v___x_1277_);
lean_ctor_set(v___x_1337_, 3, v___x_1256_);
lean_inc(v_a_1287_);
v___x_1338_ = l_Lean_Syntax_node1(v_a_1287_, v___x_1298_, v___x_1337_);
v___x_1339_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2));
v___x_1340_ = lean_obj_once(&l_Lean_Elab_Term_MatchExpr_generate___closed__4, &l_Lean_Elab_Term_MatchExpr_generate___closed__4_once, _init_l_Lean_Elab_Term_MatchExpr_generate___closed__4);
v___x_1341_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_generate___closed__6));
lean_inc(v_currMacroScope_1261_);
lean_inc(v_quotContext_1260_);
v___x_1342_ = l_Lean_addMacroScope(v_quotContext_1260_, v___x_1341_, v_currMacroScope_1261_);
v___x_1343_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_generate___closed__9));
lean_inc(v_a_1287_);
v___x_1344_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1344_, 0, v_a_1287_);
lean_ctor_set(v___x_1344_, 1, v___x_1340_);
lean_ctor_set(v___x_1344_, 2, v___x_1342_);
lean_ctor_set(v___x_1344_, 3, v___x_1343_);
lean_inc(v_a_1287_);
v___x_1345_ = l_Lean_Syntax_node1(v_a_1287_, v___x_1301_, v_discr_1251_);
lean_inc(v_a_1287_);
v___x_1346_ = l_Lean_Syntax_node2(v_a_1287_, v___x_1339_, v___x_1344_, v___x_1345_);
lean_inc_ref(v___x_1321_);
lean_inc(v_a_1287_);
v___x_1347_ = l_Lean_Syntax_node5(v_a_1287_, v___x_1297_, v___x_1338_, v___x_1321_, v___x_1321_, v___x_1327_, v___x_1346_);
lean_inc(v_a_1287_);
v___x_1348_ = l_Lean_Syntax_node1(v_a_1287_, v___x_1296_, v___x_1347_);
lean_inc_ref(v___x_1331_);
lean_inc(v_a_1287_);
v___x_1349_ = l_Lean_Syntax_node5(v_a_1287_, v___x_1333_, v___x_1334_, v___x_1336_, v___x_1348_, v___x_1331_, v_a_1284_);
v___x_1350_ = l_Lean_Syntax_node4(v_a_1287_, v___x_1293_, v___x_1295_, v___x_1329_, v___x_1331_, v___x_1349_);
v___x_1351_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg(v_a_1258_, v___x_1350_, v_a_1254_, v_a_1288_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_a_1352_; lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
v_a_1353_ = lean_ctor_get(v___x_1351_, 1);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1355_ = v___x_1351_;
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_inc(v_a_1352_);
lean_dec(v___x_1351_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1358_; 
if (v_isShared_1356_ == 0)
{
v___x_1358_ = v___x_1355_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_a_1352_);
lean_ctor_set(v_reuseFailAlloc_1359_, 1, v_a_1353_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
else
{
lean_object* v_a_1361_; lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
v_a_1361_ = lean_ctor_get(v___x_1351_, 0);
v_a_1362_ = lean_ctor_get(v___x_1351_, 1);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1351_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_inc(v_a_1361_);
lean_dec(v___x_1351_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1361_);
lean_ctor_set(v_reuseFailAlloc_1368_, 1, v_a_1362_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
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
lean_object* v_a_1374_; lean_object* v_a_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1382_; 
lean_dec(v___x_1281_);
lean_dec(v___x_1277_);
lean_del_object(v___x_1273_);
lean_del_object(v___x_1267_);
lean_dec(v_a_1258_);
lean_dec_ref(v_a_1254_);
lean_dec(v_elseAlt_1253_);
lean_dec(v_discr_1251_);
v_a_1374_ = lean_ctor_get(v___x_1283_, 0);
v_a_1375_ = lean_ctor_get(v___x_1283_, 1);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1377_ = v___x_1283_;
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_a_1375_);
lean_inc(v_a_1374_);
lean_dec(v___x_1283_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1380_; 
if (v_isShared_1378_ == 0)
{
v___x_1380_ = v___x_1377_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_a_1374_);
lean_ctor_set(v_reuseFailAlloc_1381_, 1, v_a_1375_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
}
}
}
else
{
lean_object* v_a_1385_; lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1393_; 
lean_dec_ref(v_a_1254_);
lean_dec(v_elseAlt_1253_);
lean_dec(v_discr_1251_);
v_a_1385_ = lean_ctor_get(v___x_1257_, 0);
v_a_1386_ = lean_ctor_get(v___x_1257_, 1);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1388_ = v___x_1257_;
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_inc(v_a_1385_);
lean_dec(v___x_1257_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1391_; 
if (v_isShared_1389_ == 0)
{
v___x_1391_ = v___x_1388_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_a_1385_);
lean_ctor_set(v_reuseFailAlloc_1392_, 1, v_a_1386_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1(lean_object* v_as_1394_, lean_object* v_as_x27_1395_, lean_object* v_b_1396_, lean_object* v_a_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v___x_1400_; 
v___x_1400_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg(v_as_x27_1395_, v_b_1396_, v___y_1398_, v___y_1399_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___boxed(lean_object* v_as_1401_, lean_object* v_as_x27_1402_, lean_object* v_b_1403_, lean_object* v_a_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1(v_as_1401_, v_as_x27_1402_, v_b_1403_, v_a_1404_, v___y_1405_, v___y_1406_);
lean_dec(v_as_1401_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_main_spec__0(lean_object* v_x_1409_, lean_object* v_x_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
if (lean_obj_tag(v_x_1409_) == 0)
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
lean_dec_ref(v___y_1411_);
v___x_1413_ = l_List_reverse___redArg(v_x_1410_);
v___x_1414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1413_);
lean_ctor_set(v___x_1414_, 1, v___y_1412_);
return v___x_1414_;
}
else
{
lean_object* v_head_1415_; lean_object* v_tail_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1442_; 
v_head_1415_ = lean_ctor_get(v_x_1409_, 0);
v_tail_1416_ = lean_ctor_get(v_x_1409_, 1);
v_isSharedCheck_1442_ = !lean_is_exclusive(v_x_1409_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1418_ = v_x_1409_;
v_isShared_1419_ = v_isSharedCheck_1442_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_tail_1416_);
lean_inc(v_head_1415_);
lean_dec(v_x_1409_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1442_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v_a_1421_; lean_object* v_a_1422_; lean_object* v___x_1427_; 
lean_inc(v_head_1415_);
v___x_1427_ = l_Lean_Elab_Term_MatchExpr_toAlt_x3f(v_head_1415_);
if (lean_obj_tag(v___x_1427_) == 1)
{
lean_object* v_val_1428_; 
lean_dec(v_head_1415_);
v_val_1428_ = lean_ctor_get(v___x_1427_, 0);
lean_inc(v_val_1428_);
lean_dec_ref(v___x_1427_);
v_a_1421_ = v_val_1428_;
v_a_1422_ = v___y_1412_;
goto v___jp_1420_;
}
else
{
lean_object* v___x_1429_; lean_object* v___x_1430_; 
lean_dec(v___x_1427_);
v___x_1429_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_main_spec__0___closed__0));
lean_inc_ref(v___y_1411_);
v___x_1430_ = l_Lean_Macro_throwErrorAt___redArg(v_head_1415_, v___x_1429_, v___y_1411_, v___y_1412_);
lean_dec(v_head_1415_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; lean_object* v_a_1432_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1431_);
v_a_1432_ = lean_ctor_get(v___x_1430_, 1);
lean_inc(v_a_1432_);
lean_dec_ref(v___x_1430_);
v_a_1421_ = v_a_1431_;
v_a_1422_ = v_a_1432_;
goto v___jp_1420_;
}
else
{
lean_object* v_a_1433_; lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1441_; 
lean_del_object(v___x_1418_);
lean_dec(v_tail_1416_);
lean_dec_ref(v___y_1411_);
lean_dec(v_x_1410_);
v_a_1433_ = lean_ctor_get(v___x_1430_, 0);
v_a_1434_ = lean_ctor_get(v___x_1430_, 1);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1436_ = v___x_1430_;
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_inc(v_a_1433_);
lean_dec(v___x_1430_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1439_; 
if (v_isShared_1437_ == 0)
{
v___x_1439_ = v___x_1436_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_a_1433_);
lean_ctor_set(v_reuseFailAlloc_1440_, 1, v_a_1434_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
v___jp_1420_:
{
lean_object* v___x_1424_; 
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 1, v_x_1410_);
lean_ctor_set(v___x_1418_, 0, v_a_1421_);
v___x_1424_ = v___x_1418_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_a_1421_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v_x_1410_);
v___x_1424_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
v_x_1409_ = v_tail_1416_;
v_x_1410_ = v___x_1424_;
v___y_1412_ = v_a_1422_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_main(lean_object* v_discr_1444_, lean_object* v_alts_1445_, lean_object* v_elseAlt_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1449_ = lean_array_to_list(v_alts_1445_);
v___x_1450_ = lean_box(0);
lean_inc_ref(v_a_1447_);
v___x_1451_ = l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_main_spec__0(v___x_1449_, v___x_1450_, v_a_1447_, v_a_1448_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v_a_1452_; lean_object* v_a_1453_; lean_object* v___x_1454_; 
v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_a_1452_);
v_a_1453_ = lean_ctor_get(v___x_1451_, 1);
lean_inc(v_a_1453_);
lean_dec_ref(v___x_1451_);
lean_inc(v_elseAlt_1446_);
v___x_1454_ = l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f(v_elseAlt_1446_);
if (lean_obj_tag(v___x_1454_) == 1)
{
lean_object* v_val_1455_; lean_object* v___x_1456_; 
lean_dec(v_elseAlt_1446_);
v_val_1455_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_val_1455_);
lean_dec_ref(v___x_1454_);
v___x_1456_ = l_Lean_Elab_Term_MatchExpr_generate(v_discr_1444_, v_a_1452_, v_val_1455_, v_a_1447_, v_a_1453_);
return v___x_1456_;
}
else
{
lean_object* v___x_1457_; lean_object* v___x_1458_; 
lean_dec(v___x_1454_);
lean_dec(v_a_1452_);
lean_dec(v_discr_1444_);
v___x_1457_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_main___closed__0));
v___x_1458_ = l_Lean_Macro_throwErrorAt___redArg(v_elseAlt_1446_, v___x_1457_, v_a_1447_, v_a_1453_);
lean_dec(v_elseAlt_1446_);
return v___x_1458_;
}
}
else
{
lean_object* v_a_1459_; lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
lean_dec_ref(v_a_1447_);
lean_dec(v_elseAlt_1446_);
lean_dec(v_discr_1444_);
v_a_1459_ = lean_ctor_get(v___x_1451_, 0);
v_a_1460_ = lean_ctor_get(v___x_1451_, 1);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1462_ = v___x_1451_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_inc(v_a_1459_);
lean_dec(v___x_1451_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1459_);
lean_ctor_set(v_reuseFailAlloc_1466_, 1, v_a_1460_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchExpr(lean_object* v_stx_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_){
_start:
{
lean_object* v___x_1477_; uint8_t v___x_1478_; 
v___x_1477_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchExpr___closed__1));
lean_inc(v_stx_1474_);
v___x_1478_ = l_Lean_Syntax_isOfKind(v_stx_1474_, v___x_1477_);
if (v___x_1478_ == 0)
{
lean_object* v___x_1479_; 
lean_dec_ref(v_a_1475_);
lean_dec(v_stx_1474_);
v___x_1479_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1476_);
return v___x_1479_;
}
else
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v_discr_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1480_ = lean_unsigned_to_nat(0u);
v___x_1481_ = lean_unsigned_to_nat(1u);
v_discr_1482_ = l_Lean_Syntax_getArg(v_stx_1474_, v___x_1481_);
v___x_1483_ = lean_unsigned_to_nat(3u);
v___x_1484_ = l_Lean_Syntax_getArg(v_stx_1474_, v___x_1483_);
lean_dec(v_stx_1474_);
v___x_1485_ = l_Lean_Syntax_getArg(v___x_1484_, v___x_1480_);
v___x_1486_ = l_Lean_Syntax_getArgs(v___x_1485_);
lean_dec(v___x_1485_);
v___x_1487_ = l_Lean_Syntax_getArg(v___x_1484_, v___x_1481_);
lean_dec(v___x_1484_);
v___x_1488_ = l_Lean_Elab_Term_MatchExpr_main(v_discr_1482_, v___x_1486_, v___x_1487_, v_a_1475_, v_a_1476_);
return v___x_1488_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1(){
_start:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1496_ = l_Lean_Elab_macroAttribute;
v___x_1497_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchExpr___closed__1));
v___x_1498_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1));
v___x_1499_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandMatchExpr), 3, 0);
v___x_1500_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1496_, v___x_1497_, v___x_1498_, v___x_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___boxed(lean_object* v_a_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1();
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3(){
_start:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1529_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1));
v___x_1530_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__6));
v___x_1531_ = l_Lean_addBuiltinDeclarationRanges(v___x_1529_, v___x_1530_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___boxed(lean_object* v_a_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3();
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandLetExpr(lean_object* v_stx_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_){
_start:
{
lean_object* v___x_1553_; uint8_t v___x_1554_; 
v___x_1553_ = ((lean_object*)(l_Lean_Elab_Term_expandLetExpr___closed__1));
lean_inc(v_stx_1550_);
v___x_1554_ = l_Lean_Syntax_isOfKind(v_stx_1550_, v___x_1553_);
if (v___x_1554_ == 0)
{
lean_object* v___x_1555_; 
lean_dec(v_stx_1550_);
v___x_1555_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1552_);
return v___x_1555_;
}
else
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; uint8_t v___x_1559_; 
v___x_1556_ = lean_unsigned_to_nat(1u);
v___x_1557_ = l_Lean_Syntax_getArg(v_stx_1550_, v___x_1556_);
v___x_1558_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__5));
lean_inc(v___x_1557_);
v___x_1559_ = l_Lean_Syntax_isOfKind(v___x_1557_, v___x_1558_);
if (v___x_1559_ == 0)
{
lean_object* v___x_1560_; 
lean_dec(v___x_1557_);
lean_dec(v_stx_1550_);
v___x_1560_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1552_);
return v___x_1560_;
}
else
{
lean_object* v_ref_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; uint8_t v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v_ref_1561_ = lean_ctor_get(v_a_1551_, 5);
v___x_1562_ = lean_unsigned_to_nat(3u);
v___x_1563_ = l_Lean_Syntax_getArg(v_stx_1550_, v___x_1562_);
v___x_1564_ = lean_unsigned_to_nat(5u);
v___x_1565_ = l_Lean_Syntax_getArg(v_stx_1550_, v___x_1564_);
v___x_1566_ = lean_unsigned_to_nat(7u);
v___x_1567_ = l_Lean_Syntax_getArg(v_stx_1550_, v___x_1566_);
lean_dec(v_stx_1550_);
v___x_1568_ = 0;
v___x_1569_ = l_Lean_SourceInfo_fromRef(v_ref_1561_, v___x_1568_);
v___x_1570_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchExpr___closed__1));
v___x_1571_ = ((lean_object*)(l_Lean_Elab_Term_expandLetExpr___closed__2));
lean_inc(v___x_1569_);
v___x_1572_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1569_);
lean_ctor_set(v___x_1572_, 1, v___x_1571_);
v___x_1573_ = ((lean_object*)(l_Lean_Elab_Term_expandLetExpr___closed__3));
lean_inc(v___x_1569_);
v___x_1574_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1569_);
lean_ctor_set(v___x_1574_, 1, v___x_1573_);
v___x_1575_ = ((lean_object*)(l_Lean_Elab_Term_expandLetExpr___closed__5));
v___x_1576_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4));
v___x_1577_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__1));
v___x_1578_ = ((lean_object*)(l_Lean_Elab_Term_expandLetExpr___closed__6));
lean_inc(v___x_1569_);
v___x_1579_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1569_);
lean_ctor_set(v___x_1579_, 1, v___x_1578_);
v___x_1580_ = ((lean_object*)(l_Lean_Elab_Term_expandLetExpr___closed__7));
lean_inc(v___x_1569_);
v___x_1581_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1569_);
lean_ctor_set(v___x_1581_, 1, v___x_1580_);
lean_inc_ref(v___x_1581_);
lean_inc_ref(v___x_1579_);
lean_inc(v___x_1569_);
v___x_1582_ = l_Lean_Syntax_node4(v___x_1569_, v___x_1577_, v___x_1579_, v___x_1557_, v___x_1581_, v___x_1567_);
lean_inc(v___x_1569_);
v___x_1583_ = l_Lean_Syntax_node1(v___x_1569_, v___x_1576_, v___x_1582_);
v___x_1584_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__4));
v___x_1585_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1));
v___x_1586_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getParams___closed__0));
lean_inc(v___x_1569_);
v___x_1587_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1569_);
lean_ctor_set(v___x_1587_, 1, v___x_1586_);
lean_inc(v___x_1569_);
v___x_1588_ = l_Lean_Syntax_node1(v___x_1569_, v___x_1585_, v___x_1587_);
lean_inc(v___x_1569_);
v___x_1589_ = l_Lean_Syntax_node4(v___x_1569_, v___x_1584_, v___x_1579_, v___x_1588_, v___x_1581_, v___x_1565_);
lean_inc(v___x_1569_);
v___x_1590_ = l_Lean_Syntax_node2(v___x_1569_, v___x_1575_, v___x_1583_, v___x_1589_);
v___x_1591_ = l_Lean_Syntax_node4(v___x_1569_, v___x_1570_, v___x_1572_, v___x_1563_, v___x_1574_, v___x_1590_);
v___x_1592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1591_);
lean_ctor_set(v___x_1592_, 1, v_a_1552_);
return v___x_1592_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandLetExpr___boxed(lean_object* v_stx_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l_Lean_Elab_Term_expandLetExpr(v_stx_1593_, v_a_1594_, v_a_1595_);
lean_dec_ref(v_a_1594_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1(){
_start:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1604_ = l_Lean_Elab_macroAttribute;
v___x_1605_ = ((lean_object*)(l_Lean_Elab_Term_expandLetExpr___closed__1));
v___x_1606_ = ((lean_object*)(l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1));
v___x_1607_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandLetExpr___boxed), 3, 0);
v___x_1608_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1604_, v___x_1605_, v___x_1606_, v___x_1607_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___boxed(lean_object* v_a_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1();
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3(){
_start:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1637_ = ((lean_object*)(l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1));
v___x_1638_ = ((lean_object*)(l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__6));
v___x_1639_ = l_Lean_addBuiltinDeclarationRanges(v___x_1637_, v___x_1638_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___boxed(lean_object* v_a_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3();
return v_res_1641_;
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
res = l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3();
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
