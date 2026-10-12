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
lean_object* l_Array_mkArray0___redArg();
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0(lean_object* v_a_96_, lean_object* v_as_97_, size_t v_sz_98_, size_t v_i_99_, lean_object* v_b_100_){
_start:
{
uint8_t v___x_101_; 
v___x_101_ = lean_usize_dec_lt(v_i_99_, v_sz_98_);
if (v___x_101_ == 0)
{
lean_inc_ref(v_b_100_);
return v_b_100_;
}
else
{
lean_object* v_funName_102_; lean_object* v___x_103_; lean_object* v_a_104_; lean_object* v___x_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_96_ = stack[0].m_obj;
lean_object* v_as_97_ = stack[1].m_obj;
size_t v_sz_98_ = stack[2].m_num;
size_t v_i_99_ = stack[3].m_num;
lean_object* v_b_100_ = stack[4].m_obj;
lean_object* v_res_115_;
v_res_115_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0(v_a_96_, v_as_97_, v_sz_98_, v_i_99_, v_b_100_);
stack->m_obj
 = v_res_115_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0___boxed(lean_object* v_a_116_, lean_object* v_as_117_, lean_object* v_sz_118_, lean_object* v_i_119_, lean_object* v_b_120_){
_start:
{
size_t v_sz_boxed_121_; size_t v_i_boxed_122_; lean_object* v_res_123_; 
v_sz_boxed_121_ = lean_unbox_usize(v_sz_118_);
lean_dec(v_sz_118_);
v_i_boxed_122_ = lean_unbox_usize(v_i_119_);
lean_dec(v_i_119_);
v_res_123_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0(v_a_116_, v_as_117_, v_sz_boxed_121_, v_i_boxed_122_, v_b_120_);
lean_dec_ref(v_b_120_);
lean_dec_ref(v_as_117_);
lean_dec_ref(v_a_116_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1___redArg(lean_object* v_as_x27_124_, lean_object* v_b_125_){
_start:
{
if (lean_obj_tag(v_as_x27_124_) == 0)
{
return v_b_125_;
}
else
{
lean_object* v_head_126_; lean_object* v_tail_127_; lean_object* v_funName_128_; lean_object* v_pvars_129_; uint8_t v___x_130_; 
v_head_126_ = lean_ctor_get(v_as_x27_124_, 0);
v_tail_127_ = lean_ctor_get(v_as_x27_124_, 1);
v_funName_128_ = lean_ctor_get(v_head_126_, 1);
v_pvars_129_ = lean_ctor_get(v_head_126_, 2);
v___x_130_ = l_List_isEmpty___redArg(v_pvars_129_);
if (v___x_130_ == 0)
{
v_as_x27_124_ = v_tail_127_;
goto _start;
}
else
{
lean_object* v___x_136_; size_t v_sz_137_; size_t v___x_138_; lean_object* v___x_139_; lean_object* v_fst_140_; 
v___x_136_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0___closed__0));
v_sz_137_ = lean_array_size(v_b_125_);
v___x_138_ = ((size_t)0ULL);
v___x_139_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0(v_head_126_, v_b_125_, v_sz_137_, v___x_138_, v___x_136_);
v_fst_140_ = lean_ctor_get(v___x_139_, 0);
lean_inc(v_fst_140_);
lean_dec_ref(v___x_139_);
if (lean_obj_tag(v_fst_140_) == 0)
{
goto v___jp_131_;
}
else
{
lean_object* v_val_141_; 
v_val_141_ = lean_ctor_get(v_fst_140_, 0);
lean_inc(v_val_141_);
lean_dec_ref_known(v_fst_140_, 1);
if (lean_obj_tag(v_val_141_) == 0)
{
goto v___jp_131_;
}
else
{
lean_dec_ref_known(v_val_141_, 1);
v_as_x27_124_ = v_tail_127_;
goto _start;
}
}
}
v___jp_131_:
{
if (v___x_130_ == 0)
{
v_as_x27_124_ = v_tail_127_;
goto _start;
}
else
{
lean_object* v___x_133_; 
lean_inc(v_funName_128_);
v___x_133_ = lean_array_push(v_b_125_, v_funName_128_);
v_as_x27_124_ = v_tail_127_;
v_b_125_ = v___x_133_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1___redArg___boxed(lean_object* v_as_x27_143_, lean_object* v_b_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1___redArg(v_as_x27_143_, v_b_144_);
lean_dec(v_as_x27_143_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch(lean_object* v_alts_148_){
_start:
{
lean_object* v_funNames_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v_funNames_149_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch___closed__0));
v___x_150_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1___redArg(v_alts_148_, v_funNames_149_);
v___x_151_ = lean_array_to_list(v___x_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch___boxed(lean_object* v_alts_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch(v_alts_152_);
lean_dec(v_alts_152_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1(lean_object* v_as_154_, lean_object* v_as_x27_155_, lean_object* v_b_156_, lean_object* v_a_157_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1___redArg(v_as_x27_155_, v_b_156_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1___boxed(lean_object* v_as_159_, lean_object* v_as_x27_160_, lean_object* v_b_161_, lean_object* v_a_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1(v_as_159_, v_as_x27_160_, v_b_161_, v_a_162_);
lean_dec(v_as_x27_160_);
lean_dec(v_as_159_);
return v_res_163_;
}
}
uint8_t l_List_any___at___00Lean_Elab_Term_MatchExpr_shouldSaveActual_spec__0(lean_object* v_x_164_){
_start:
{
if (lean_obj_tag(v_x_164_) == 0)
{
uint8_t v___x_165_; 
v___x_165_ = 0;
return v___x_165_;
}
else
{
lean_object* v_head_166_; lean_object* v_pvars_167_; 
v_head_166_ = lean_ctor_get(v_x_164_, 0);
v_pvars_167_ = lean_ctor_get(v_head_166_, 2);
if (lean_obj_tag(v_pvars_167_) == 1)
{
lean_object* v_head_168_; 
v_head_168_ = lean_ctor_get(v_pvars_167_, 0);
if (lean_obj_tag(v_head_168_) == 1)
{
uint8_t v___x_169_; 
v___x_169_ = 1;
return v___x_169_;
}
else
{
lean_object* v_tail_170_; 
v_tail_170_ = lean_ctor_get(v_x_164_, 1);
v_x_164_ = v_tail_170_;
goto _start;
}
}
else
{
lean_object* v_tail_172_; 
v_tail_172_ = lean_ctor_get(v_x_164_, 1);
v_x_164_ = v_tail_172_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_List_any___at___00Lean_Elab_Term_MatchExpr_shouldSaveActual_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_164_ = stack[0].m_obj;
uint8_t v_res_174_;
v_res_174_ = l_List_any___at___00Lean_Elab_Term_MatchExpr_shouldSaveActual_spec__0(v_x_164_);
stack->m_num = v_res_174_;
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
uint8_t l_Lean_Elab_Term_MatchExpr_shouldSaveActual(lean_object* v_alts_178_){
_start:
{
uint8_t v___x_179_; 
v___x_179_ = l_List_any___at___00Lean_Elab_Term_MatchExpr_shouldSaveActual_spec__0(v_alts_178_);
return v___x_179_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_MatchExpr_shouldSaveActual_0interp(lean_interpreter_value* stack)
{
lean_object* v_alts_178_ = stack[0].m_obj;
uint8_t v_res_180_;
v_res_180_ = l_Lean_Elab_Term_MatchExpr_shouldSaveActual(v_alts_178_);
stack->m_num = v_res_180_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_shouldSaveActual___boxed(lean_object* v_alts_181_){
_start:
{
uint8_t v_res_182_; lean_object* v_r_183_; 
v_res_182_ = l_Lean_Elab_Term_MatchExpr_shouldSaveActual(v_alts_181_);
lean_dec(v_alts_181_);
v_r_183_ = lean_box(v_res_182_);
return v_r_183_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Elab_Term_MatchExpr_getAltFor_x3f_spec__0(lean_object* v_funName_184_, lean_object* v_x_185_){
_start:
{
if (lean_obj_tag(v_x_185_) == 0)
{
lean_object* v___x_186_; 
v___x_186_ = lean_box(0);
return v___x_186_;
}
else
{
lean_object* v_head_187_; lean_object* v_tail_188_; uint8_t v___y_190_; lean_object* v_funName_193_; lean_object* v_pvars_194_; lean_object* v___x_195_; lean_object* v___x_196_; uint8_t v___x_197_; 
v_head_187_ = lean_ctor_get(v_x_185_, 0);
v_tail_188_ = lean_ctor_get(v_x_185_, 1);
v_funName_193_ = lean_ctor_get(v_head_187_, 1);
v_pvars_194_ = lean_ctor_get(v_head_187_, 2);
v___x_195_ = l_Lean_TSyntax_getId(v_funName_193_);
v___x_196_ = l_Lean_TSyntax_getId(v_funName_184_);
v___x_197_ = lean_name_eq(v___x_195_, v___x_196_);
lean_dec(v___x_196_);
lean_dec(v___x_195_);
if (v___x_197_ == 0)
{
v___y_190_ = v___x_197_;
goto v___jp_189_;
}
else
{
uint8_t v___x_198_; 
v___x_198_ = l_List_isEmpty___redArg(v_pvars_194_);
v___y_190_ = v___x_198_;
goto v___jp_189_;
}
v___jp_189_:
{
if (v___y_190_ == 0)
{
v_x_185_ = v_tail_188_;
goto _start;
}
else
{
lean_object* v___x_192_; 
lean_inc(v_head_187_);
v___x_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_192_, 0, v_head_187_);
return v___x_192_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Elab_Term_MatchExpr_getAltFor_x3f_spec__0___boxed(lean_object* v_funName_199_, lean_object* v_x_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_List_find_x3f___at___00Lean_Elab_Term_MatchExpr_getAltFor_x3f_spec__0(v_funName_199_, v_x_200_);
lean_dec(v_x_200_);
lean_dec(v_funName_199_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getAltFor_x3f(lean_object* v_alts_202_, lean_object* v_funName_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_List_find_x3f___at___00Lean_Elab_Term_MatchExpr_getAltFor_x3f_spec__0(v_funName_203_, v_alts_202_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getAltFor_x3f___boxed(lean_object* v_alts_205_, lean_object* v_funName_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Lean_Elab_Term_MatchExpr_getAltFor_x3f(v_alts_205_, v_funName_206_);
lean_dec(v_funName_206_);
lean_dec(v_alts_205_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Elab_Term_MatchExpr_next_spec__0(lean_object* v_actual_208_, lean_object* v_a_209_, lean_object* v_a_210_){
_start:
{
if (lean_obj_tag(v_a_209_) == 0)
{
lean_object* v___x_211_; 
lean_dec(v_actual_208_);
v___x_211_ = lean_array_to_list(v_a_210_);
return v___x_211_;
}
else
{
lean_object* v_head_212_; lean_object* v_tail_213_; lean_object* v_val_215_; lean_object* v_var_x3f_218_; lean_object* v_funName_219_; lean_object* v_pvars_220_; lean_object* v_rhs_221_; lean_object* v_k_222_; lean_object* v_actuals_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_246_; 
v_head_212_ = lean_ctor_get(v_a_209_, 0);
lean_inc(v_head_212_);
v_tail_213_ = lean_ctor_get(v_a_209_, 1);
lean_inc(v_tail_213_);
lean_dec_ref_known(v_a_209_, 2);
v_var_x3f_218_ = lean_ctor_get(v_head_212_, 0);
v_funName_219_ = lean_ctor_get(v_head_212_, 1);
v_pvars_220_ = lean_ctor_get(v_head_212_, 2);
v_rhs_221_ = lean_ctor_get(v_head_212_, 3);
v_k_222_ = lean_ctor_get(v_head_212_, 4);
v_actuals_223_ = lean_ctor_get(v_head_212_, 5);
v_isSharedCheck_246_ = !lean_is_exclusive(v_head_212_);
if (v_isSharedCheck_246_ == 0)
{
v___x_225_ = v_head_212_;
v_isShared_226_ = v_isSharedCheck_246_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_actuals_223_);
lean_inc(v_k_222_);
lean_inc(v_rhs_221_);
lean_inc(v_pvars_220_);
lean_inc(v_funName_219_);
lean_inc(v_var_x3f_218_);
lean_dec(v_head_212_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_246_;
goto v_resetjp_224_;
}
v___jp_214_:
{
lean_object* v___x_216_; 
v___x_216_ = lean_array_push(v_a_210_, v_val_215_);
v_a_209_ = v_tail_213_;
v_a_210_ = v___x_216_;
goto _start;
}
v_resetjp_224_:
{
if (lean_obj_tag(v_pvars_220_) == 1)
{
lean_object* v_head_235_; 
v_head_235_ = lean_ctor_get(v_pvars_220_, 0);
if (lean_obj_tag(v_head_235_) == 1)
{
lean_object* v_tail_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_244_; 
lean_del_object(v___x_225_);
v_tail_236_ = lean_ctor_get(v_pvars_220_, 1);
v_isSharedCheck_244_ = !lean_is_exclusive(v_pvars_220_);
if (v_isSharedCheck_244_ == 0)
{
lean_object* v_unused_245_; 
v_unused_245_ = lean_ctor_get(v_pvars_220_, 0);
lean_dec(v_unused_245_);
v___x_238_ = v_pvars_220_;
v_isShared_239_ = v_isSharedCheck_244_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_tail_236_);
lean_dec(v_pvars_220_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_244_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_241_; 
lean_inc(v_actual_208_);
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 1, v_actuals_223_);
lean_ctor_set(v___x_238_, 0, v_actual_208_);
v___x_241_ = v___x_238_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_actual_208_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v_actuals_223_);
v___x_241_ = v_reuseFailAlloc_243_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v___x_242_; 
v___x_242_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_242_, 0, v_var_x3f_218_);
lean_ctor_set(v___x_242_, 1, v_funName_219_);
lean_ctor_set(v___x_242_, 2, v_tail_236_);
lean_ctor_set(v___x_242_, 3, v_rhs_221_);
lean_ctor_set(v___x_242_, 4, v_k_222_);
lean_ctor_set(v___x_242_, 5, v___x_241_);
v_val_215_ = v___x_242_;
goto v___jp_214_;
}
}
}
else
{
goto v___jp_227_;
}
}
else
{
goto v___jp_227_;
}
v___jp_227_:
{
if (lean_obj_tag(v_pvars_220_) == 1)
{
lean_object* v_head_228_; 
v_head_228_ = lean_ctor_get(v_pvars_220_, 0);
if (lean_obj_tag(v_head_228_) == 0)
{
lean_object* v_tail_229_; lean_object* v___x_231_; 
v_tail_229_ = lean_ctor_get(v_pvars_220_, 1);
lean_inc(v_tail_229_);
lean_dec_ref_known(v_pvars_220_, 2);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 2, v_tail_229_);
v___x_231_ = v___x_225_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_var_x3f_218_);
lean_ctor_set(v_reuseFailAlloc_232_, 1, v_funName_219_);
lean_ctor_set(v_reuseFailAlloc_232_, 2, v_tail_229_);
lean_ctor_set(v_reuseFailAlloc_232_, 3, v_rhs_221_);
lean_ctor_set(v_reuseFailAlloc_232_, 4, v_k_222_);
lean_ctor_set(v_reuseFailAlloc_232_, 5, v_actuals_223_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
v_val_215_ = v___x_231_;
goto v___jp_214_;
}
}
else
{
lean_dec_ref_known(v_pvars_220_, 2);
lean_del_object(v___x_225_);
lean_dec(v_actuals_223_);
lean_dec(v_k_222_);
lean_dec(v_rhs_221_);
lean_dec(v_funName_219_);
lean_dec(v_var_x3f_218_);
v_a_209_ = v_tail_213_;
goto _start;
}
}
else
{
lean_del_object(v___x_225_);
lean_dec(v_actuals_223_);
lean_dec(v_k_222_);
lean_dec(v_rhs_221_);
lean_dec(v_pvars_220_);
lean_dec(v_funName_219_);
lean_dec(v_var_x3f_218_);
v_a_209_ = v_tail_213_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_next(lean_object* v_alts_249_, lean_object* v_actual_250_){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_next___closed__0));
v___x_252_ = l_List_filterMapTR_go___at___00Lean_Elab_Term_MatchExpr_next_spec__0(v_actual_250_, v_alts_249_, v___x_251_);
return v___x_252_;
}
}
static lean_object* _init_l_Lean_Elab_Term_MatchExpr_initK___closed__1(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_initK___closed__0));
v___x_255_ = l_String_toRawSubstring_x27(v___x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_initK(lean_object* v_alt_258_, lean_object* v_a_259_, lean_object* v_a_260_){
_start:
{
lean_object* v_macroScope_261_; lean_object* v_traceMsgs_262_; lean_object* v_expandedMacroDecls_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_295_; 
v_macroScope_261_ = lean_ctor_get(v_a_260_, 0);
v_traceMsgs_262_ = lean_ctor_get(v_a_260_, 1);
v_expandedMacroDecls_263_ = lean_ctor_get(v_a_260_, 2);
v_isSharedCheck_295_ = !lean_is_exclusive(v_a_260_);
if (v_isSharedCheck_295_ == 0)
{
v___x_265_ = v_a_260_;
v_isShared_266_ = v_isSharedCheck_295_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_expandedMacroDecls_263_);
lean_inc(v_traceMsgs_262_);
lean_inc(v_macroScope_261_);
lean_dec(v_a_260_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_295_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v_quotContext_267_; lean_object* v_ref_268_; lean_object* v_var_x3f_269_; lean_object* v_funName_270_; lean_object* v_pvars_271_; lean_object* v_rhs_272_; lean_object* v_actuals_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_293_; 
v_quotContext_267_ = lean_ctor_get(v_a_259_, 1);
v_ref_268_ = lean_ctor_get(v_a_259_, 5);
v_var_x3f_269_ = lean_ctor_get(v_alt_258_, 0);
v_funName_270_ = lean_ctor_get(v_alt_258_, 1);
v_pvars_271_ = lean_ctor_get(v_alt_258_, 2);
v_rhs_272_ = lean_ctor_get(v_alt_258_, 3);
v_actuals_273_ = lean_ctor_get(v_alt_258_, 5);
v_isSharedCheck_293_ = !lean_is_exclusive(v_alt_258_);
if (v_isSharedCheck_293_ == 0)
{
lean_object* v_unused_294_; 
v_unused_294_ = lean_ctor_get(v_alt_258_, 4);
lean_dec(v_unused_294_);
v___x_275_ = v_alt_258_;
v_isShared_276_ = v_isSharedCheck_293_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_actuals_273_);
lean_inc(v_rhs_272_);
lean_inc(v_pvars_271_);
lean_inc(v_funName_270_);
lean_inc(v_var_x3f_269_);
lean_dec(v_alt_258_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_293_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_281_; 
v___x_277_ = lean_unsigned_to_nat(1u);
v___x_278_ = lean_nat_add(v_macroScope_261_, v___x_277_);
v___x_279_ = lean_obj_once(&l_Lean_Elab_Term_MatchExpr_initK___closed__1, &l_Lean_Elab_Term_MatchExpr_initK___closed__1_once, _init_l_Lean_Elab_Term_MatchExpr_initK___closed__1);
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 0, v___x_278_);
v___x_281_ = v___x_265_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_278_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v_traceMsgs_262_);
lean_ctor_set(v_reuseFailAlloc_292_, 2, v_expandedMacroDecls_263_);
v___x_281_ = v_reuseFailAlloc_292_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
uint8_t v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_289_; 
v___x_282_ = 0;
v___x_283_ = l_Lean_SourceInfo_fromRef(v_ref_268_, v___x_282_);
v___x_284_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_initK___closed__2));
lean_inc(v_quotContext_267_);
v___x_285_ = l_Lean_addMacroScope(v_quotContext_267_, v___x_284_, v_macroScope_261_);
v___x_286_ = lean_box(0);
v___x_287_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_287_, 0, v___x_283_);
lean_ctor_set(v___x_287_, 1, v___x_279_);
lean_ctor_set(v___x_287_, 2, v___x_285_);
lean_ctor_set(v___x_287_, 3, v___x_286_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 4, v___x_287_);
v___x_289_ = v___x_275_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_var_x3f_269_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v_funName_270_);
lean_ctor_set(v_reuseFailAlloc_291_, 2, v_pvars_271_);
lean_ctor_set(v_reuseFailAlloc_291_, 3, v_rhs_272_);
lean_ctor_set(v_reuseFailAlloc_291_, 4, v___x_287_);
lean_ctor_set(v_reuseFailAlloc_291_, 5, v_actuals_273_);
v___x_289_ = v_reuseFailAlloc_291_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
lean_object* v___x_290_; 
v___x_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
lean_ctor_set(v___x_290_, 1, v___x_281_);
return v___x_290_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_initK___boxed(lean_object* v_alt_296_, lean_object* v_a_297_, lean_object* v_a_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_Elab_Term_MatchExpr_initK(v_alt_296_, v_a_297_, v_a_298_);
lean_dec_ref(v_a_297_);
return v_res_299_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_MatchExpr_getParams_spec__1(size_t v_sz_300_, size_t v_i_301_, lean_object* v_bs_302_){
_start:
{
uint8_t v___x_303_; 
v___x_303_ = lean_usize_dec_lt(v_i_301_, v_sz_300_);
if (v___x_303_ == 0)
{
return v_bs_302_;
}
else
{
lean_object* v_v_304_; lean_object* v___x_305_; lean_object* v_bs_x27_306_; size_t v___x_307_; size_t v___x_308_; lean_object* v___x_309_; 
v_v_304_ = lean_array_uget(v_bs_302_, v_i_301_);
v___x_305_ = lean_unsigned_to_nat(0u);
v_bs_x27_306_ = lean_array_uset(v_bs_302_, v_i_301_, v___x_305_);
v___x_307_ = ((size_t)1ULL);
v___x_308_ = lean_usize_add(v_i_301_, v___x_307_);
v___x_309_ = lean_array_uset(v_bs_x27_306_, v_i_301_, v_v_304_);
v_i_301_ = v___x_308_;
v_bs_302_ = v___x_309_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_MatchExpr_getParams_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_300_ = stack[0].m_num;
size_t v_i_301_ = stack[1].m_num;
lean_object* v_bs_302_ = stack[2].m_obj;
lean_object* v_res_311_;
v_res_311_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_MatchExpr_getParams_spec__1(v_sz_300_, v_i_301_, v_bs_302_);
stack->m_obj
 = v_res_311_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_MatchExpr_getParams_spec__1___boxed(lean_object* v_sz_312_, lean_object* v_i_313_, lean_object* v_bs_314_){
_start:
{
size_t v_sz_boxed_315_; size_t v_i_boxed_316_; lean_object* v_res_317_; 
v_sz_boxed_315_ = lean_unbox_usize(v_sz_312_);
lean_dec(v_sz_312_);
v_i_boxed_316_ = lean_unbox_usize(v_i_313_);
lean_dec(v_i_313_);
v_res_317_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_MatchExpr_getParams_spec__1(v_sz_boxed_315_, v_i_boxed_316_, v_bs_314_);
return v_res_317_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__7(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__6));
v___x_331_ = l_String_toRawSubstring_x27(v___x_330_);
return v___x_331_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14(void){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_Array_mkArray0___redArg();
return v___x_348_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0(lean_object* v_as_350_, size_t v_i_351_, size_t v_stop_352_, lean_object* v_b_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v_a_357_; lean_object* v_a_358_; uint8_t v___x_362_; 
v___x_362_ = lean_usize_dec_eq(v_i_351_, v_stop_352_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; 
v___x_363_ = lean_array_uget_borrowed(v_as_350_, v_i_351_);
if (lean_obj_tag(v___x_363_) == 0)
{
v_a_357_ = v_b_353_;
v_a_358_ = v___y_355_;
goto v___jp_356_;
}
else
{
lean_object* v_val_364_; lean_object* v_quotContext_365_; lean_object* v_currMacroScope_366_; lean_object* v_ref_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v_val_364_ = lean_ctor_get(v___x_363_, 0);
v_quotContext_365_ = lean_ctor_get(v___y_354_, 1);
v_currMacroScope_366_ = lean_ctor_get(v___y_354_, 2);
v_ref_367_ = lean_ctor_get(v___y_354_, 5);
v___x_368_ = l_Lean_SourceInfo_fromRef(v_ref_367_, v___x_362_);
v___x_369_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1));
v___x_370_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2));
lean_inc_n(v___x_368_, 7);
v___x_371_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_371_, 0, v___x_368_);
lean_ctor_set(v___x_371_, 1, v___x_370_);
v___x_372_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4));
lean_inc(v_val_364_);
v___x_373_ = l_Lean_Syntax_node1(v___x_368_, v___x_372_, v_val_364_);
v___x_374_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__5));
v___x_375_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_368_);
lean_ctor_set(v___x_375_, 1, v___x_374_);
v___x_376_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__7);
v___x_377_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__8));
lean_inc(v_currMacroScope_366_);
lean_inc(v_quotContext_365_);
v___x_378_ = l_Lean_addMacroScope(v_quotContext_365_, v___x_377_, v_currMacroScope_366_);
v___x_379_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__13));
v___x_380_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_380_, 0, v___x_368_);
lean_ctor_set(v___x_380_, 1, v___x_376_);
lean_ctor_set(v___x_380_, 2, v___x_378_);
lean_ctor_set(v___x_380_, 3, v___x_379_);
v___x_381_ = l_Lean_Syntax_node2(v___x_368_, v___x_372_, v___x_375_, v___x_380_);
v___x_382_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
v___x_383_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_383_, 0, v___x_368_);
lean_ctor_set(v___x_383_, 1, v___x_372_);
lean_ctor_set(v___x_383_, 2, v___x_382_);
v___x_384_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15));
v___x_385_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_385_, 0, v___x_368_);
lean_ctor_set(v___x_385_, 1, v___x_384_);
v___x_386_ = l_Lean_Syntax_node5(v___x_368_, v___x_369_, v___x_371_, v___x_373_, v___x_381_, v___x_383_, v___x_385_);
v___x_387_ = lean_array_push(v_b_353_, v___x_386_);
v_a_357_ = v___x_387_;
v_a_358_ = v___y_355_;
goto v___jp_356_;
}
}
else
{
lean_object* v___x_388_; 
v___x_388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_388_, 0, v_b_353_);
lean_ctor_set(v___x_388_, 1, v___y_355_);
return v___x_388_;
}
v___jp_356_:
{
size_t v___x_359_; size_t v___x_360_; 
v___x_359_ = ((size_t)1ULL);
v___x_360_ = lean_usize_add(v_i_351_, v___x_359_);
v_i_351_ = v___x_360_;
v_b_353_ = v_a_357_;
v___y_355_ = v_a_358_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_350_ = stack[0].m_obj;
size_t v_i_351_ = stack[1].m_num;
size_t v_stop_352_ = stack[2].m_num;
lean_object* v_b_353_ = stack[3].m_obj;
lean_object* v___y_354_ = stack[4].m_obj;
lean_object* v___y_355_ = stack[5].m_obj;
lean_object* v_res_389_;
v_res_389_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0(v_as_350_, v_i_351_, v_stop_352_, v_b_353_, v___y_354_, v___y_355_);
stack->m_obj
 = v_res_389_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___boxed(lean_object* v_as_390_, lean_object* v_i_391_, lean_object* v_stop_392_, lean_object* v_b_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
size_t v_i_boxed_396_; size_t v_stop_boxed_397_; lean_object* v_res_398_; 
v_i_boxed_396_ = lean_unbox_usize(v_i_391_);
lean_dec(v_i_391_);
v_stop_boxed_397_ = lean_unbox_usize(v_stop_392_);
lean_dec(v_stop_392_);
v_res_398_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0(v_as_390_, v_i_boxed_396_, v_stop_boxed_397_, v_b_393_, v___y_394_, v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec_ref(v_as_390_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0(lean_object* v_as_399_, lean_object* v_start_400_, lean_object* v_stop_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v___x_404_; uint8_t v___x_405_; 
v___x_404_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch___closed__0));
v___x_405_ = lean_nat_dec_lt(v_start_400_, v_stop_401_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; 
v___x_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_404_);
lean_ctor_set(v___x_406_, 1, v___y_403_);
return v___x_406_;
}
else
{
lean_object* v___x_407_; uint8_t v___x_408_; 
v___x_407_ = lean_array_get_size(v_as_399_);
v___x_408_ = lean_nat_dec_le(v_stop_401_, v___x_407_);
if (v___x_408_ == 0)
{
uint8_t v___x_409_; 
v___x_409_ = lean_nat_dec_lt(v_start_400_, v___x_407_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; 
v___x_410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_410_, 0, v___x_404_);
lean_ctor_set(v___x_410_, 1, v___y_403_);
return v___x_410_;
}
else
{
size_t v___x_411_; size_t v___x_412_; lean_object* v___x_413_; 
v___x_411_ = lean_usize_of_nat(v_start_400_);
v___x_412_ = lean_usize_of_nat(v___x_407_);
v___x_413_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0(v_as_399_, v___x_411_, v___x_412_, v___x_404_, v___y_402_, v___y_403_);
return v___x_413_;
}
}
else
{
size_t v___x_414_; size_t v___x_415_; lean_object* v___x_416_; 
v___x_414_ = lean_usize_of_nat(v_start_400_);
v___x_415_ = lean_usize_of_nat(v_stop_401_);
v___x_416_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0(v_as_399_, v___x_414_, v___x_415_, v___x_404_, v___y_402_, v___y_403_);
return v___x_416_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0___boxed(lean_object* v_as_417_, lean_object* v_start_418_, lean_object* v_stop_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0(v_as_417_, v_start_418_, v_stop_419_, v___y_420_, v___y_421_);
lean_dec_ref(v___y_420_);
lean_dec(v_stop_419_);
lean_dec(v_start_418_);
lean_dec_ref(v_as_417_);
return v_res_422_;
}
}
static lean_object* _init_l_Lean_Elab_Term_MatchExpr_getParams___closed__2(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getParams___closed__1));
v___x_426_ = l_String_toRawSubstring_x27(v___x_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getParams(lean_object* v_alt_440_, lean_object* v_a_441_, lean_object* v_a_442_){
_start:
{
lean_object* v_var_x3f_443_; lean_object* v_pvars_444_; lean_object* v_params_446_; lean_object* v___y_447_; lean_object* v___y_448_; lean_object* v_params_502_; 
v_var_x3f_443_ = lean_ctor_get(v_alt_440_, 0);
lean_inc(v_var_x3f_443_);
v_pvars_444_ = lean_ctor_get(v_alt_440_, 2);
lean_inc(v_pvars_444_);
lean_dec_ref(v_alt_440_);
v_params_502_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch___closed__0));
if (lean_obj_tag(v_var_x3f_443_) == 1)
{
lean_object* v_val_503_; lean_object* v_quotContext_504_; lean_object* v_currMacroScope_505_; lean_object* v_ref_506_; uint8_t v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v_val_503_ = lean_ctor_get(v_var_x3f_443_, 0);
lean_inc(v_val_503_);
lean_dec_ref_known(v_var_x3f_443_, 1);
v_quotContext_504_ = lean_ctor_get(v_a_441_, 1);
v_currMacroScope_505_ = lean_ctor_get(v_a_441_, 2);
v_ref_506_ = lean_ctor_get(v_a_441_, 5);
v___x_507_ = 0;
v___x_508_ = l_Lean_SourceInfo_fromRef(v_ref_506_, v___x_507_);
v___x_509_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1));
v___x_510_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2));
lean_inc_n(v___x_508_, 7);
v___x_511_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_511_, 0, v___x_508_);
lean_ctor_set(v___x_511_, 1, v___x_510_);
v___x_512_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4));
v___x_513_ = l_Lean_Syntax_node1(v___x_508_, v___x_512_, v_val_503_);
v___x_514_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__5));
v___x_515_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_515_, 0, v___x_508_);
lean_ctor_set(v___x_515_, 1, v___x_514_);
v___x_516_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__7);
v___x_517_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__8));
lean_inc(v_currMacroScope_505_);
lean_inc(v_quotContext_504_);
v___x_518_ = l_Lean_addMacroScope(v_quotContext_504_, v___x_517_, v_currMacroScope_505_);
v___x_519_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__13));
v___x_520_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_520_, 0, v___x_508_);
lean_ctor_set(v___x_520_, 1, v___x_516_);
lean_ctor_set(v___x_520_, 2, v___x_518_);
lean_ctor_set(v___x_520_, 3, v___x_519_);
v___x_521_ = l_Lean_Syntax_node2(v___x_508_, v___x_512_, v___x_515_, v___x_520_);
v___x_522_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
v___x_523_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_523_, 0, v___x_508_);
lean_ctor_set(v___x_523_, 1, v___x_512_);
lean_ctor_set(v___x_523_, 2, v___x_522_);
v___x_524_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15));
v___x_525_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_508_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
v___x_526_ = l_Lean_Syntax_node5(v___x_508_, v___x_509_, v___x_511_, v___x_513_, v___x_521_, v___x_523_, v___x_525_);
v___x_527_ = lean_array_push(v_params_502_, v___x_526_);
v_params_446_ = v___x_527_;
v___y_447_ = v_a_441_;
v___y_448_ = v_a_442_;
goto v___jp_445_;
}
else
{
lean_dec(v_var_x3f_443_);
v_params_446_ = v_params_502_;
v___y_447_ = v_a_441_;
v___y_448_ = v_a_442_;
goto v___jp_445_;
}
v___jp_445_:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_449_ = lean_array_mk(v_pvars_444_);
v___x_450_ = l_Array_reverse___redArg(v___x_449_);
v___x_451_ = lean_unsigned_to_nat(0u);
v___x_452_ = lean_array_get_size(v___x_450_);
v___x_453_ = l_Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0(v___x_450_, v___x_451_, v___x_452_, v___y_447_, v___y_448_);
lean_dec_ref(v___x_450_);
if (lean_obj_tag(v___x_453_) == 0)
{
lean_object* v_a_454_; lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_501_; 
v_a_454_ = lean_ctor_get(v___x_453_, 0);
v_a_455_ = lean_ctor_get(v___x_453_, 1);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_501_ == 0)
{
v___x_457_ = v___x_453_;
v_isShared_458_ = v_isSharedCheck_501_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_inc(v_a_454_);
lean_dec(v___x_453_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_501_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_459_; lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_459_ = l_Array_append___redArg(v_params_446_, v_a_454_);
lean_dec(v_a_454_);
v___x_460_ = lean_array_get_size(v___x_459_);
v___x_461_ = lean_nat_dec_eq(v___x_460_, v___x_451_);
if (v___x_461_ == 0)
{
size_t v_sz_462_; size_t v___x_463_; lean_object* v___x_464_; lean_object* v___x_466_; 
v_sz_462_ = lean_array_size(v___x_459_);
v___x_463_ = ((size_t)0ULL);
v___x_464_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_MatchExpr_getParams_spec__1(v_sz_462_, v___x_463_, v___x_459_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 0, v___x_464_);
v___x_466_ = v___x_457_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_464_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v_a_455_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
else
{
lean_object* v_quotContext_468_; lean_object* v_currMacroScope_469_; lean_object* v_ref_470_; uint8_t v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_499_; 
lean_dec_ref(v___x_459_);
v_quotContext_468_ = lean_ctor_get(v___y_447_, 1);
v_currMacroScope_469_ = lean_ctor_get(v___y_447_, 2);
v_ref_470_ = lean_ctor_get(v___y_447_, 5);
v___x_471_ = 0;
v___x_472_ = l_Lean_SourceInfo_fromRef(v_ref_470_, v___x_471_);
v___x_473_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1));
v___x_474_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2));
lean_inc_n(v___x_472_, 9);
v___x_475_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_475_, 0, v___x_472_);
lean_ctor_set(v___x_475_, 1, v___x_474_);
v___x_476_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4));
v___x_477_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1));
v___x_478_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getParams___closed__0));
v___x_479_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_479_, 0, v___x_472_);
lean_ctor_set(v___x_479_, 1, v___x_478_);
v___x_480_ = l_Lean_Syntax_node1(v___x_472_, v___x_477_, v___x_479_);
v___x_481_ = l_Lean_Syntax_node1(v___x_472_, v___x_476_, v___x_480_);
v___x_482_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__5));
v___x_483_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_472_);
lean_ctor_set(v___x_483_, 1, v___x_482_);
v___x_484_ = lean_obj_once(&l_Lean_Elab_Term_MatchExpr_getParams___closed__2, &l_Lean_Elab_Term_MatchExpr_getParams___closed__2_once, _init_l_Lean_Elab_Term_MatchExpr_getParams___closed__2);
v___x_485_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getParams___closed__3));
lean_inc(v_currMacroScope_469_);
lean_inc(v_quotContext_468_);
v___x_486_ = l_Lean_addMacroScope(v_quotContext_468_, v___x_485_, v_currMacroScope_469_);
v___x_487_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getParams___closed__7));
v___x_488_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_488_, 0, v___x_472_);
lean_ctor_set(v___x_488_, 1, v___x_484_);
lean_ctor_set(v___x_488_, 2, v___x_486_);
lean_ctor_set(v___x_488_, 3, v___x_487_);
v___x_489_ = l_Lean_Syntax_node2(v___x_472_, v___x_476_, v___x_483_, v___x_488_);
v___x_490_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
v___x_491_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_491_, 0, v___x_472_);
lean_ctor_set(v___x_491_, 1, v___x_476_);
lean_ctor_set(v___x_491_, 2, v___x_490_);
v___x_492_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15));
v___x_493_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_472_);
lean_ctor_set(v___x_493_, 1, v___x_492_);
v___x_494_ = l_Lean_Syntax_node5(v___x_472_, v___x_473_, v___x_475_, v___x_481_, v___x_489_, v___x_491_, v___x_493_);
v___x_495_ = lean_unsigned_to_nat(1u);
v___x_496_ = lean_mk_empty_array_with_capacity(v___x_495_);
v___x_497_ = lean_array_push(v___x_496_, v___x_494_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 0, v___x_497_);
v___x_499_ = v___x_457_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v_a_455_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
else
{
lean_dec_ref(v_params_446_);
return v___x_453_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getParams___boxed(lean_object* v_alt_528_, lean_object* v_a_529_, lean_object* v_a_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Lean_Elab_Term_MatchExpr_getParams(v_alt_528_, v_a_529_, v_a_530_);
lean_dec_ref(v_a_529_);
return v_res_531_;
}
}
static lean_object* _init_l_Lean_Elab_Term_MatchExpr_getActuals___closed__7(void){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__6));
v___x_549_ = l_String_toRawSubstring_x27(v___x_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getActuals(lean_object* v_discr_588_, lean_object* v_alt_589_, lean_object* v_a_590_, lean_object* v_a_591_){
_start:
{
lean_object* v_var_x3f_592_; lean_object* v_actuals_593_; lean_object* v_actuals_595_; lean_object* v___y_596_; lean_object* v___y_597_; lean_object* v_actuals_631_; 
v_var_x3f_592_ = lean_ctor_get(v_alt_589_, 0);
lean_inc(v_var_x3f_592_);
v_actuals_593_ = lean_ctor_get(v_alt_589_, 5);
lean_inc(v_actuals_593_);
lean_dec_ref(v_alt_589_);
v_actuals_631_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch___closed__0));
if (lean_obj_tag(v_var_x3f_592_) == 0)
{
lean_dec(v_discr_588_);
v_actuals_595_ = v_actuals_631_;
v___y_596_ = v_a_590_;
v___y_597_ = v_a_591_;
goto v___jp_594_;
}
else
{
lean_object* v_actuals_632_; 
lean_dec_ref_known(v_var_x3f_592_, 1);
v_actuals_632_ = lean_array_push(v_actuals_631_, v_discr_588_);
v_actuals_595_ = v_actuals_632_;
v___y_596_ = v_a_590_;
v___y_597_ = v_a_591_;
goto v___jp_594_;
}
v___jp_594_:
{
lean_object* v___x_598_; lean_object* v_actuals_599_; lean_object* v___x_600_; lean_object* v___x_601_; uint8_t v___x_602_; 
v___x_598_ = lean_array_mk(v_actuals_593_);
v_actuals_599_ = l_Array_append___redArg(v_actuals_595_, v___x_598_);
lean_dec_ref(v___x_598_);
v___x_600_ = lean_array_get_size(v_actuals_599_);
v___x_601_ = lean_unsigned_to_nat(0u);
v___x_602_ = lean_nat_dec_eq(v___x_600_, v___x_601_);
if (v___x_602_ == 0)
{
lean_object* v___x_603_; 
v___x_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_603_, 0, v_actuals_599_);
lean_ctor_set(v___x_603_, 1, v___y_597_);
return v___x_603_;
}
else
{
lean_object* v_quotContext_604_; lean_object* v_currMacroScope_605_; lean_object* v_ref_606_; uint8_t v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
lean_dec_ref(v_actuals_599_);
v_quotContext_604_ = lean_ctor_get(v___y_596_, 1);
v_currMacroScope_605_ = lean_ctor_get(v___y_596_, 2);
v_ref_606_ = lean_ctor_get(v___y_596_, 5);
v___x_607_ = 0;
v___x_608_ = l_Lean_SourceInfo_fromRef(v_ref_606_, v___x_607_);
v___x_609_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__1));
v___x_610_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__3));
v___x_611_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2));
lean_inc_n(v___x_608_, 6);
v___x_612_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_608_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
v___x_613_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__5));
v___x_614_ = lean_obj_once(&l_Lean_Elab_Term_MatchExpr_getActuals___closed__7, &l_Lean_Elab_Term_MatchExpr_getActuals___closed__7_once, _init_l_Lean_Elab_Term_MatchExpr_getActuals___closed__7);
v___x_615_ = lean_box(0);
lean_inc(v_currMacroScope_605_);
lean_inc(v_quotContext_604_);
v___x_616_ = l_Lean_addMacroScope(v_quotContext_604_, v___x_615_, v_currMacroScope_605_);
v___x_617_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__21));
v___x_618_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_618_, 0, v___x_608_);
lean_ctor_set(v___x_618_, 1, v___x_614_);
lean_ctor_set(v___x_618_, 2, v___x_616_);
lean_ctor_set(v___x_618_, 3, v___x_617_);
v___x_619_ = l_Lean_Syntax_node1(v___x_608_, v___x_613_, v___x_618_);
v___x_620_ = l_Lean_Syntax_node2(v___x_608_, v___x_610_, v___x_612_, v___x_619_);
v___x_621_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4));
v___x_622_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
v___x_623_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_623_, 0, v___x_608_);
lean_ctor_set(v___x_623_, 1, v___x_621_);
lean_ctor_set(v___x_623_, 2, v___x_622_);
v___x_624_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15));
v___x_625_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_608_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
v___x_626_ = l_Lean_Syntax_node3(v___x_608_, v___x_609_, v___x_620_, v___x_623_, v___x_625_);
v___x_627_ = lean_unsigned_to_nat(1u);
v___x_628_ = lean_mk_empty_array_with_capacity(v___x_627_);
v___x_629_ = lean_array_push(v___x_628_, v___x_626_);
v___x_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
lean_ctor_set(v___x_630_, 1, v___y_597_);
return v___x_630_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getActuals___boxed(lean_object* v_discr_633_, lean_object* v_alt_634_, lean_object* v_a_635_, lean_object* v_a_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Lean_Elab_Term_MatchExpr_getActuals(v_discr_633_, v_alt_634_, v_a_635_, v_a_636_);
lean_dec_ref(v_a_635_);
return v_res_637_;
}
}
static lean_object* _init_l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__3(void){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__2));
v___x_646_ = l_Lean_mkAtom(v___x_645_);
return v___x_646_;
}
}
static lean_object* _init_l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__4(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_647_ = lean_obj_once(&l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__3, &l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__3_once, _init_l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__3);
v___x_648_ = lean_unsigned_to_nat(3u);
v___x_649_ = lean_mk_empty_array_with_capacity(v___x_648_);
v___x_650_ = lean_array_push(v___x_649_, v___x_647_);
return v___x_650_;
}
}
static lean_object* _init_l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__5(void){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_651_ = lean_obj_once(&l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__3, &l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__3_once, _init_l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__3);
v___x_652_ = lean_obj_once(&l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__4, &l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__4_once, _init_l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__4);
v___x_653_ = lean_array_push(v___x_652_, v___x_651_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName(lean_object* v_ident_654_){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_655_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__1));
v___x_656_ = lean_obj_once(&l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__5, &l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__5_once, _init_l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__5);
v___x_657_ = lean_array_push(v___x_656_, v_ident_654_);
v___x_658_ = lean_box(2);
v___x_659_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
lean_ctor_set(v___x_659_, 1, v___x_655_);
lean_ctor_set(v___x_659_, 2, v___x_657_);
return v___x_659_;
}
}
lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___lam__0(uint8_t v___x_660_, lean_object* v_____do__lift_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_664_ = l_Lean_SourceInfo_fromRef(v_____do__lift_661_, v___x_660_);
v___x_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
lean_ctor_set(v___x_665_, 1, v___y_663_);
return v___x_665_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_660_ = stack[0].m_num;
lean_object* v_____do__lift_661_ = stack[1].m_obj;
lean_object* v___y_662_ = stack[2].m_obj;
lean_object* v___y_663_ = stack[3].m_obj;
lean_object* v_res_666_;
v_res_666_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___lam__0(v___x_660_, v_____do__lift_661_, v___y_662_, v___y_663_);
stack->m_obj
 = v_res_666_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___lam__0___boxed(lean_object* v___x_667_, lean_object* v_____do__lift_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
uint8_t v___x_18785__boxed_671_; lean_object* v_res_672_; 
v___x_18785__boxed_671_ = lean_unbox(v___x_667_);
v_res_672_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___lam__0(v___x_18785__boxed_671_, v_____do__lift_668_, v___y_669_, v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v_____do__lift_668_);
return v_res_672_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__9(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__8));
v___x_695_ = l_String_toRawSubstring_x27(v___x_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg(lean_object* v_alts_703_, lean_object* v_discr_704_, lean_object* v_as_x27_705_, lean_object* v_b_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
if (lean_obj_tag(v_as_x27_705_) == 0)
{
lean_object* v___x_709_; 
lean_dec(v_discr_704_);
v___x_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_709_, 0, v_b_706_);
lean_ctor_set(v___x_709_, 1, v___y_708_);
return v___x_709_;
}
else
{
lean_object* v_head_710_; lean_object* v_tail_711_; lean_object* v___x_712_; 
v_head_710_ = lean_ctor_get(v_as_x27_705_, 0);
v_tail_711_ = lean_ctor_get(v_as_x27_705_, 1);
v___x_712_ = l_List_find_x3f___at___00Lean_Elab_Term_MatchExpr_getAltFor_x3f_spec__0(v_head_710_, v_alts_703_);
if (lean_obj_tag(v___x_712_) == 1)
{
lean_object* v_val_713_; lean_object* v___x_714_; lean_object* v_a_715_; lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_770_; 
v_val_713_ = lean_ctor_get(v___x_712_, 0);
lean_inc_n(v_val_713_, 2);
lean_dec_ref_known(v___x_712_, 1);
lean_inc(v_discr_704_);
v___x_714_ = l_Lean_Elab_Term_MatchExpr_getActuals(v_discr_704_, v_val_713_, v___y_707_, v___y_708_);
v_a_715_ = lean_ctor_get(v___x_714_, 0);
v_a_716_ = lean_ctor_get(v___x_714_, 1);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_770_ == 0)
{
v___x_718_ = v___x_714_;
v_isShared_719_ = v_isSharedCheck_770_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_inc(v_a_715_);
lean_dec(v___x_714_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_770_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v_quotContext_720_; lean_object* v_currMacroScope_721_; lean_object* v_ref_722_; uint8_t v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_727_; 
v_quotContext_720_ = lean_ctor_get(v___y_707_, 1);
v_currMacroScope_721_ = lean_ctor_get(v___y_707_, 2);
v_ref_722_ = lean_ctor_get(v___y_707_, 5);
v___x_723_ = 0;
v___x_724_ = l_Lean_SourceInfo_fromRef(v_ref_722_, v___x_723_);
v___x_725_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__0));
lean_inc(v___x_724_);
if (v_isShared_719_ == 0)
{
lean_ctor_set_tag(v___x_718_, 2);
lean_ctor_set(v___x_718_, 1, v___x_725_);
lean_ctor_set(v___x_718_, 0, v___x_724_);
v___x_727_ = v___x_718_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_724_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v___x_725_);
v___x_727_ = v_reuseFailAlloc_769_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v_k_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_728_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2));
v___x_729_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__4));
v___x_730_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__6));
v___x_731_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__3));
v___x_732_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2));
lean_inc_n(v___x_724_, 15);
v___x_733_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_724_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
v___x_734_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__5));
v___x_735_ = lean_obj_once(&l_Lean_Elab_Term_MatchExpr_getActuals___closed__7, &l_Lean_Elab_Term_MatchExpr_getActuals___closed__7_once, _init_l_Lean_Elab_Term_MatchExpr_getActuals___closed__7);
v___x_736_ = lean_box(0);
lean_inc_n(v_currMacroScope_721_, 2);
lean_inc_n(v_quotContext_720_, 2);
v___x_737_ = l_Lean_addMacroScope(v_quotContext_720_, v___x_736_, v_currMacroScope_721_);
v___x_738_ = lean_box(0);
v___x_739_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__21));
v___x_740_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_740_, 0, v___x_724_);
lean_ctor_set(v___x_740_, 1, v___x_735_);
lean_ctor_set(v___x_740_, 2, v___x_737_);
lean_ctor_set(v___x_740_, 3, v___x_739_);
v___x_741_ = l_Lean_Syntax_node1(v___x_724_, v___x_734_, v___x_740_);
v___x_742_ = l_Lean_Syntax_node2(v___x_724_, v___x_731_, v___x_733_, v___x_741_);
v___x_743_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15));
v___x_744_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_724_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
lean_inc(v_discr_704_);
v___x_745_ = l_Lean_Syntax_node3(v___x_724_, v___x_730_, v___x_742_, v_discr_704_, v___x_744_);
v___x_746_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__7));
v___x_747_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_724_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
v___x_748_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__9, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__9_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__9);
v___x_749_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__10));
v___x_750_ = l_Lean_addMacroScope(v_quotContext_720_, v___x_749_, v_currMacroScope_721_);
v___x_751_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_751_, 0, v___x_724_);
lean_ctor_set(v___x_751_, 1, v___x_748_);
lean_ctor_set(v___x_751_, 2, v___x_750_);
lean_ctor_set(v___x_751_, 3, v___x_738_);
v___x_752_ = l_Lean_Syntax_node3(v___x_724_, v___x_729_, v___x_745_, v___x_747_, v___x_751_);
v___x_753_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4));
lean_inc(v_head_710_);
v___x_754_ = l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName(v_head_710_);
v___x_755_ = l_Lean_Syntax_node1(v___x_724_, v___x_753_, v___x_754_);
v_k_756_ = lean_ctor_get(v_val_713_, 4);
lean_inc(v_k_756_);
lean_dec(v_val_713_);
v___x_757_ = l_Lean_Syntax_node2(v___x_724_, v___x_728_, v___x_752_, v___x_755_);
v___x_758_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__12));
v___x_759_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__13));
v___x_760_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_760_, 0, v___x_724_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
v___x_761_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
v___x_762_ = l_Array_append___redArg(v___x_761_, v_a_715_);
lean_dec(v_a_715_);
v___x_763_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_763_, 0, v___x_724_);
lean_ctor_set(v___x_763_, 1, v___x_753_);
lean_ctor_set(v___x_763_, 2, v___x_762_);
v___x_764_ = l_Lean_Syntax_node2(v___x_724_, v___x_728_, v_k_756_, v___x_763_);
v___x_765_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__14));
v___x_766_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_766_, 0, v___x_724_);
lean_ctor_set(v___x_766_, 1, v___x_765_);
v___x_767_ = l_Lean_Syntax_node6(v___x_724_, v___x_758_, v___x_727_, v___x_757_, v___x_760_, v___x_764_, v___x_766_, v_b_706_);
v_as_x27_705_ = v_tail_711_;
v_b_706_ = v___x_767_;
v___y_708_ = v_a_716_;
goto _start;
}
}
}
else
{
lean_dec(v___x_712_);
v_as_x27_705_ = v_tail_711_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___boxed(lean_object* v_alts_772_, lean_object* v_discr_773_, lean_object* v_as_x27_774_, lean_object* v_b_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg(v_alts_772_, v_discr_773_, v_as_x27_774_, v_b_775_, v___y_776_, v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec(v_as_x27_774_);
lean_dec(v_alts_772_);
return v_res_778_;
}
}
static lean_object* _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__1(void){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__0));
v___x_781_ = l_String_toRawSubstring_x27(v___x_780_);
return v___x_781_;
}
}
static lean_object* _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__8(void){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__7));
v___x_793_ = l_String_toRawSubstring_x27(v___x_792_);
return v___x_793_;
}
}
static lean_object* _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__11(void){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__10));
v___x_798_ = l_String_toRawSubstring_x27(v___x_797_);
return v___x_798_;
}
}
static lean_object* _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__25(void){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_833_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__24));
v___x_834_ = l_String_toRawSubstring_x27(v___x_833_);
return v___x_834_;
}
}
static lean_object* _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__33(void){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__32));
v___x_852_ = l_String_toRawSubstring_x27(v___x_851_);
return v___x_852_;
}
}
static lean_object* _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__36(void){
_start:
{
lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_856_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__35));
v___x_857_ = l_String_toRawSubstring_x27(v___x_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop(lean_object* v_kElse_877_, lean_object* v_discr_878_, lean_object* v_alts_879_, lean_object* v_a_880_, lean_object* v_a_881_){
_start:
{
lean_object* v_macroScope_882_; lean_object* v_traceMsgs_883_; lean_object* v_expandedMacroDecls_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_1154_; 
v_macroScope_882_ = lean_ctor_get(v_a_881_, 0);
v_traceMsgs_883_ = lean_ctor_get(v_a_881_, 1);
v_expandedMacroDecls_884_ = lean_ctor_get(v_a_881_, 2);
v_isSharedCheck_1154_ = !lean_is_exclusive(v_a_881_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_886_ = v_a_881_;
v_isShared_887_ = v_isSharedCheck_1154_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_expandedMacroDecls_884_);
lean_inc(v_traceMsgs_883_);
lean_inc(v_macroScope_882_);
lean_dec(v_a_881_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_1154_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v_methods_888_; lean_object* v_quotContext_889_; lean_object* v_currRecDepth_890_; lean_object* v_maxRecDepth_891_; lean_object* v_ref_892_; lean_object* v_funNamesToMatch_893_; uint8_t v_saveActual_894_; lean_object* v_actual_896_; lean_object* v___y_897_; lean_object* v___y_898_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1139_; 
v_methods_888_ = lean_ctor_get(v_a_880_, 0);
v_quotContext_889_ = lean_ctor_get(v_a_880_, 1);
v_currRecDepth_890_ = lean_ctor_get(v_a_880_, 3);
v_maxRecDepth_891_ = lean_ctor_get(v_a_880_, 4);
v_ref_892_ = lean_ctor_get(v_a_880_, 5);
v_funNamesToMatch_893_ = l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch(v_alts_879_);
v_saveActual_894_ = l_List_any___at___00Lean_Elab_Term_MatchExpr_shouldSaveActual_spec__0(v_alts_879_);
v___x_1136_ = lean_unsigned_to_nat(1u);
v___x_1137_ = lean_nat_add(v_macroScope_882_, v___x_1136_);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 0, v___x_1137_);
v___x_1139_ = v___x_886_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1137_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v_traceMsgs_883_);
lean_ctor_set(v_reuseFailAlloc_1153_, 2, v_expandedMacroDecls_884_);
v___x_1139_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1138_;
}
v___jp_895_:
{
lean_object* v_altsNext_899_; uint8_t v___x_900_; 
lean_inc(v_alts_879_);
v_altsNext_899_ = l_Lean_Elab_Term_MatchExpr_next(v_alts_879_, v_actual_896_);
v___x_900_ = l_List_isEmpty___redArg(v_altsNext_899_);
if (v___x_900_ == 0)
{
lean_object* v_quotContext_901_; lean_object* v_currMacroScope_902_; lean_object* v_ref_903_; lean_object* v___x_904_; 
v_quotContext_901_ = lean_ctor_get(v___y_897_, 1);
v_currMacroScope_902_ = lean_ctor_get(v___y_897_, 2);
v_ref_903_ = lean_ctor_get(v___y_897_, 5);
v___x_904_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___lam__0(v___x_900_, v_ref_903_, v___y_897_, v___y_898_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v_a_905_; lean_object* v_a_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v_a_905_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_a_905_);
v_a_906_ = lean_ctor_get(v___x_904_, 1);
lean_inc(v_a_906_);
lean_dec_ref_known(v___x_904_, 2);
v___x_907_ = lean_obj_once(&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__1, &l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__1_once, _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__1);
v___x_908_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__2));
lean_inc(v_currMacroScope_902_);
lean_inc(v_quotContext_901_);
v___x_909_ = l_Lean_addMacroScope(v_quotContext_901_, v___x_908_, v_currMacroScope_902_);
v___x_910_ = lean_box(0);
lean_inc(v___x_909_);
v___x_911_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_911_, 0, v_a_905_);
lean_ctor_set(v___x_911_, 1, v___x_907_);
lean_ctor_set(v___x_911_, 2, v___x_909_);
lean_ctor_set(v___x_911_, 3, v___x_910_);
lean_inc(v_kElse_877_);
v___x_912_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop(v_kElse_877_, v___x_911_, v_altsNext_899_, v___y_897_, v_a_906_);
if (lean_obj_tag(v___x_912_) == 0)
{
if (v_saveActual_894_ == 0)
{
lean_object* v_a_913_; lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_993_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
v_a_914_ = lean_ctor_get(v___x_912_, 1);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_993_ == 0)
{
v___x_916_ = v___x_912_;
v_isShared_917_ = v_isSharedCheck_993_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_inc(v_a_913_);
lean_dec(v___x_912_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_993_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_922_; 
v___x_918_ = l_Lean_SourceInfo_fromRef(v_ref_903_, v___x_900_);
v___x_919_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__4));
v___x_920_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__0));
lean_inc(v___x_918_);
if (v_isShared_917_ == 0)
{
lean_ctor_set_tag(v___x_916_, 2);
lean_ctor_set(v___x_916_, 1, v___x_920_);
lean_ctor_set(v___x_916_, 0, v___x_918_);
v___x_922_ = v___x_916_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v___x_918_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v___x_920_);
v___x_922_ = v_reuseFailAlloc_992_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_923_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__6));
v___x_924_ = lean_obj_once(&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__8, &l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__8_once, _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__8);
v___x_925_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__9));
lean_inc_n(v_currMacroScope_902_, 4);
lean_inc_n(v_quotContext_901_, 4);
v___x_926_ = l_Lean_addMacroScope(v_quotContext_901_, v___x_925_, v_currMacroScope_902_);
lean_inc_n(v___x_918_, 30);
v___x_927_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_927_, 0, v___x_918_);
lean_ctor_set(v___x_927_, 1, v___x_924_);
lean_ctor_set(v___x_927_, 2, v___x_926_);
lean_ctor_set(v___x_927_, 3, v___x_910_);
lean_inc_ref(v___x_927_);
v___x_928_ = l_Lean_Syntax_node1(v___x_918_, v___x_923_, v___x_927_);
v___x_929_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__5));
v___x_930_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_918_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
v___x_931_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__4));
v___x_932_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__6));
v___x_933_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__3));
v___x_934_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2));
v___x_935_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_918_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
v___x_936_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__5));
v___x_937_ = lean_obj_once(&l_Lean_Elab_Term_MatchExpr_getActuals___closed__7, &l_Lean_Elab_Term_MatchExpr_getActuals___closed__7_once, _init_l_Lean_Elab_Term_MatchExpr_getActuals___closed__7);
v___x_938_ = lean_box(0);
v___x_939_ = l_Lean_addMacroScope(v_quotContext_901_, v___x_938_, v_currMacroScope_902_);
v___x_940_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__21));
v___x_941_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_941_, 0, v___x_918_);
lean_ctor_set(v___x_941_, 1, v___x_937_);
lean_ctor_set(v___x_941_, 2, v___x_939_);
lean_ctor_set(v___x_941_, 3, v___x_940_);
v___x_942_ = l_Lean_Syntax_node1(v___x_918_, v___x_936_, v___x_941_);
v___x_943_ = l_Lean_Syntax_node2(v___x_918_, v___x_933_, v___x_935_, v___x_942_);
v___x_944_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15));
v___x_945_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_918_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
lean_inc_ref(v___x_945_);
lean_inc_n(v_discr_878_, 2);
lean_inc(v___x_943_);
v___x_946_ = l_Lean_Syntax_node3(v___x_918_, v___x_932_, v___x_943_, v_discr_878_, v___x_945_);
v___x_947_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__7));
v___x_948_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_918_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = lean_obj_once(&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__11, &l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__11_once, _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__11);
v___x_950_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__12));
v___x_951_ = l_Lean_addMacroScope(v_quotContext_901_, v___x_950_, v_currMacroScope_902_);
v___x_952_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_952_, 0, v___x_918_);
lean_ctor_set(v___x_952_, 1, v___x_949_);
lean_ctor_set(v___x_952_, 2, v___x_951_);
lean_ctor_set(v___x_952_, 3, v___x_910_);
v___x_953_ = l_Lean_Syntax_node3(v___x_918_, v___x_931_, v___x_946_, v___x_948_, v___x_952_);
v___x_954_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__13));
v___x_955_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_918_);
lean_ctor_set(v___x_955_, 1, v___x_954_);
v___x_956_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__13));
v___x_957_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__14));
v___x_958_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_918_);
lean_ctor_set(v___x_958_, 1, v___x_956_);
v___x_959_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__16));
v___x_960_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4));
v___x_961_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
v___x_962_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_962_, 0, v___x_918_);
lean_ctor_set(v___x_962_, 1, v___x_960_);
lean_ctor_set(v___x_962_, 2, v___x_961_);
lean_inc_ref_n(v___x_962_, 3);
v___x_963_ = l_Lean_Syntax_node1(v___x_918_, v___x_959_, v___x_962_);
v___x_964_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18));
v___x_965_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20));
v___x_966_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22));
v___x_967_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_967_, 0, v___x_918_);
lean_ctor_set(v___x_967_, 1, v___x_907_);
lean_ctor_set(v___x_967_, 2, v___x_909_);
lean_ctor_set(v___x_967_, 3, v___x_910_);
v___x_968_ = l_Lean_Syntax_node1(v___x_918_, v___x_966_, v___x_967_);
v___x_969_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__23));
v___x_970_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_918_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
v___x_971_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2));
v___x_972_ = lean_obj_once(&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__25, &l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__25_once, _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__25);
v___x_973_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__27));
v___x_974_ = l_Lean_addMacroScope(v_quotContext_901_, v___x_973_, v_currMacroScope_902_);
v___x_975_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__30));
v___x_976_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_976_, 0, v___x_918_);
lean_ctor_set(v___x_976_, 1, v___x_972_);
lean_ctor_set(v___x_976_, 2, v___x_974_);
lean_ctor_set(v___x_976_, 3, v___x_975_);
v___x_977_ = l_Lean_Syntax_node2(v___x_918_, v___x_960_, v_discr_878_, v___x_927_);
v___x_978_ = l_Lean_Syntax_node2(v___x_918_, v___x_971_, v___x_976_, v___x_977_);
v___x_979_ = l_Lean_Syntax_node5(v___x_918_, v___x_965_, v___x_968_, v___x_962_, v___x_962_, v___x_970_, v___x_978_);
v___x_980_ = l_Lean_Syntax_node1(v___x_918_, v___x_964_, v___x_979_);
v___x_981_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__31));
v___x_982_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_918_);
lean_ctor_set(v___x_982_, 1, v___x_981_);
v___x_983_ = l_Lean_Syntax_node5(v___x_918_, v___x_957_, v___x_958_, v___x_963_, v___x_980_, v___x_982_, v_a_913_);
v___x_984_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__14));
v___x_985_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_918_);
lean_ctor_set(v___x_985_, 1, v___x_984_);
v___x_986_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__1));
v___x_987_ = l_Lean_Syntax_node3(v___x_918_, v___x_986_, v___x_943_, v___x_962_, v___x_945_);
v___x_988_ = l_Lean_Syntax_node1(v___x_918_, v___x_960_, v___x_987_);
v___x_989_ = l_Lean_Syntax_node2(v___x_918_, v___x_971_, v_kElse_877_, v___x_988_);
v___x_990_ = l_Lean_Syntax_node8(v___x_918_, v___x_919_, v___x_922_, v___x_928_, v___x_930_, v___x_953_, v___x_955_, v___x_983_, v___x_985_, v___x_989_);
v___x_991_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg(v_alts_879_, v_discr_878_, v_funNamesToMatch_893_, v___x_990_, v___y_897_, v_a_914_);
lean_dec_ref(v___y_897_);
lean_dec(v_funNamesToMatch_893_);
lean_dec(v_alts_879_);
return v___x_991_;
}
}
}
else
{
lean_object* v_a_994_; lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1099_; 
v_a_994_ = lean_ctor_get(v___x_912_, 0);
v_a_995_ = lean_ctor_get(v___x_912_, 1);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_997_ = v___x_912_;
v_isShared_998_ = v_isSharedCheck_1099_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_inc(v_a_994_);
lean_dec(v___x_912_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1099_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_999_; 
v___x_999_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___lam__0(v___x_900_, v_ref_903_, v___y_897_, v_a_995_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v_a_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1005_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc_n(v_a_1000_, 2);
v_a_1001_ = lean_ctor_get(v___x_999_, 1);
lean_inc(v_a_1001_);
lean_dec_ref_known(v___x_999_, 2);
v___x_1002_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__4));
v___x_1003_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__0));
if (v_isShared_998_ == 0)
{
lean_ctor_set_tag(v___x_997_, 2);
lean_ctor_set(v___x_997_, 1, v___x_1003_);
lean_ctor_set(v___x_997_, 0, v_a_1000_);
v___x_1005_ = v___x_997_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1000_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v___x_1003_);
v___x_1005_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1006_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__6));
v___x_1007_ = lean_obj_once(&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__8, &l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__8_once, _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__8);
v___x_1008_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__9));
lean_inc_n(v_currMacroScope_902_, 6);
lean_inc_n(v_quotContext_901_, 6);
v___x_1009_ = l_Lean_addMacroScope(v_quotContext_901_, v___x_1008_, v_currMacroScope_902_);
lean_inc_n(v_a_1000_, 37);
v___x_1010_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1010_, 0, v_a_1000_);
lean_ctor_set(v___x_1010_, 1, v___x_1007_);
lean_ctor_set(v___x_1010_, 2, v___x_1009_);
lean_ctor_set(v___x_1010_, 3, v___x_910_);
lean_inc_ref(v___x_1010_);
v___x_1011_ = l_Lean_Syntax_node1(v_a_1000_, v___x_1006_, v___x_1010_);
v___x_1012_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__5));
v___x_1013_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1013_, 0, v_a_1000_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
v___x_1014_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__4));
v___x_1015_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__6));
v___x_1016_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__3));
v___x_1017_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2));
v___x_1018_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1018_, 0, v_a_1000_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
v___x_1019_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__5));
v___x_1020_ = lean_obj_once(&l_Lean_Elab_Term_MatchExpr_getActuals___closed__7, &l_Lean_Elab_Term_MatchExpr_getActuals___closed__7_once, _init_l_Lean_Elab_Term_MatchExpr_getActuals___closed__7);
v___x_1021_ = lean_box(0);
v___x_1022_ = l_Lean_addMacroScope(v_quotContext_901_, v___x_1021_, v_currMacroScope_902_);
v___x_1023_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__21));
v___x_1024_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1024_, 0, v_a_1000_);
lean_ctor_set(v___x_1024_, 1, v___x_1020_);
lean_ctor_set(v___x_1024_, 2, v___x_1022_);
lean_ctor_set(v___x_1024_, 3, v___x_1023_);
v___x_1025_ = l_Lean_Syntax_node1(v_a_1000_, v___x_1019_, v___x_1024_);
v___x_1026_ = l_Lean_Syntax_node2(v_a_1000_, v___x_1016_, v___x_1018_, v___x_1025_);
v___x_1027_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15));
v___x_1028_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1028_, 0, v_a_1000_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
lean_inc_ref(v___x_1028_);
lean_inc_n(v_discr_878_, 2);
lean_inc(v___x_1026_);
v___x_1029_ = l_Lean_Syntax_node3(v_a_1000_, v___x_1015_, v___x_1026_, v_discr_878_, v___x_1028_);
v___x_1030_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__7));
v___x_1031_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1031_, 0, v_a_1000_);
lean_ctor_set(v___x_1031_, 1, v___x_1030_);
v___x_1032_ = lean_obj_once(&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__11, &l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__11_once, _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__11);
v___x_1033_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__12));
v___x_1034_ = l_Lean_addMacroScope(v_quotContext_901_, v___x_1033_, v_currMacroScope_902_);
v___x_1035_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1035_, 0, v_a_1000_);
lean_ctor_set(v___x_1035_, 1, v___x_1032_);
lean_ctor_set(v___x_1035_, 2, v___x_1034_);
lean_ctor_set(v___x_1035_, 3, v___x_910_);
v___x_1036_ = l_Lean_Syntax_node3(v_a_1000_, v___x_1014_, v___x_1029_, v___x_1031_, v___x_1035_);
v___x_1037_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__13));
v___x_1038_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1038_, 0, v_a_1000_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
v___x_1039_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__13));
v___x_1040_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__14));
v___x_1041_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1041_, 0, v_a_1000_);
lean_ctor_set(v___x_1041_, 1, v___x_1039_);
v___x_1042_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__16));
v___x_1043_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4));
v___x_1044_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
v___x_1045_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1045_, 0, v_a_1000_);
lean_ctor_set(v___x_1045_, 1, v___x_1043_);
lean_ctor_set(v___x_1045_, 2, v___x_1044_);
lean_inc_ref_n(v___x_1045_, 5);
v___x_1046_ = l_Lean_Syntax_node1(v_a_1000_, v___x_1042_, v___x_1045_);
v___x_1047_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18));
v___x_1048_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20));
v___x_1049_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22));
v___x_1050_ = lean_obj_once(&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__33, &l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__33_once, _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__33);
v___x_1051_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__34));
v___x_1052_ = l_Lean_addMacroScope(v_quotContext_901_, v___x_1051_, v_currMacroScope_902_);
v___x_1053_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1053_, 0, v_a_1000_);
lean_ctor_set(v___x_1053_, 1, v___x_1050_);
lean_ctor_set(v___x_1053_, 2, v___x_1052_);
lean_ctor_set(v___x_1053_, 3, v___x_910_);
v___x_1054_ = l_Lean_Syntax_node1(v_a_1000_, v___x_1049_, v___x_1053_);
v___x_1055_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__23));
v___x_1056_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1056_, 0, v_a_1000_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
v___x_1057_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2));
v___x_1058_ = lean_obj_once(&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__36, &l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__36_once, _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__36);
v___x_1059_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__38));
v___x_1060_ = l_Lean_addMacroScope(v_quotContext_901_, v___x_1059_, v_currMacroScope_902_);
v___x_1061_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__43));
v___x_1062_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1062_, 0, v_a_1000_);
lean_ctor_set(v___x_1062_, 1, v___x_1058_);
lean_ctor_set(v___x_1062_, 2, v___x_1060_);
lean_ctor_set(v___x_1062_, 3, v___x_1061_);
v___x_1063_ = l_Lean_Syntax_node2(v_a_1000_, v___x_1043_, v_discr_878_, v___x_1010_);
lean_inc(v___x_1063_);
v___x_1064_ = l_Lean_Syntax_node2(v_a_1000_, v___x_1057_, v___x_1062_, v___x_1063_);
lean_inc_ref(v___x_1056_);
v___x_1065_ = l_Lean_Syntax_node5(v_a_1000_, v___x_1048_, v___x_1054_, v___x_1045_, v___x_1045_, v___x_1056_, v___x_1064_);
v___x_1066_ = l_Lean_Syntax_node1(v_a_1000_, v___x_1047_, v___x_1065_);
v___x_1067_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__31));
v___x_1068_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1068_, 0, v_a_1000_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
v___x_1069_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1069_, 0, v_a_1000_);
lean_ctor_set(v___x_1069_, 1, v___x_907_);
lean_ctor_set(v___x_1069_, 2, v___x_909_);
lean_ctor_set(v___x_1069_, 3, v___x_910_);
v___x_1070_ = l_Lean_Syntax_node1(v_a_1000_, v___x_1049_, v___x_1069_);
v___x_1071_ = lean_obj_once(&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__25, &l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__25_once, _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__25);
v___x_1072_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__27));
v___x_1073_ = l_Lean_addMacroScope(v_quotContext_901_, v___x_1072_, v_currMacroScope_902_);
v___x_1074_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__30));
v___x_1075_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1075_, 0, v_a_1000_);
lean_ctor_set(v___x_1075_, 1, v___x_1071_);
lean_ctor_set(v___x_1075_, 2, v___x_1073_);
lean_ctor_set(v___x_1075_, 3, v___x_1074_);
v___x_1076_ = l_Lean_Syntax_node2(v_a_1000_, v___x_1057_, v___x_1075_, v___x_1063_);
v___x_1077_ = l_Lean_Syntax_node5(v_a_1000_, v___x_1048_, v___x_1070_, v___x_1045_, v___x_1045_, v___x_1056_, v___x_1076_);
v___x_1078_ = l_Lean_Syntax_node1(v_a_1000_, v___x_1047_, v___x_1077_);
lean_inc_ref(v___x_1068_);
lean_inc(v___x_1046_);
lean_inc_ref(v___x_1041_);
v___x_1079_ = l_Lean_Syntax_node5(v_a_1000_, v___x_1040_, v___x_1041_, v___x_1046_, v___x_1078_, v___x_1068_, v_a_994_);
v___x_1080_ = l_Lean_Syntax_node5(v_a_1000_, v___x_1040_, v___x_1041_, v___x_1046_, v___x_1066_, v___x_1068_, v___x_1079_);
v___x_1081_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__14));
v___x_1082_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1082_, 0, v_a_1000_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
v___x_1083_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__1));
v___x_1084_ = l_Lean_Syntax_node3(v_a_1000_, v___x_1083_, v___x_1026_, v___x_1045_, v___x_1028_);
v___x_1085_ = l_Lean_Syntax_node1(v_a_1000_, v___x_1043_, v___x_1084_);
v___x_1086_ = l_Lean_Syntax_node2(v_a_1000_, v___x_1057_, v_kElse_877_, v___x_1085_);
v___x_1087_ = l_Lean_Syntax_node8(v_a_1000_, v___x_1002_, v___x_1005_, v___x_1011_, v___x_1013_, v___x_1036_, v___x_1038_, v___x_1080_, v___x_1082_, v___x_1086_);
v___x_1088_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg(v_alts_879_, v_discr_878_, v_funNamesToMatch_893_, v___x_1087_, v___y_897_, v_a_1001_);
lean_dec_ref(v___y_897_);
lean_dec(v_funNamesToMatch_893_);
lean_dec(v_alts_879_);
return v___x_1088_;
}
}
else
{
lean_object* v_a_1090_; lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
lean_del_object(v___x_997_);
lean_dec(v_a_994_);
lean_dec(v___x_909_);
lean_dec_ref(v___y_897_);
lean_dec(v_funNamesToMatch_893_);
lean_dec(v_alts_879_);
lean_dec(v_discr_878_);
lean_dec(v_kElse_877_);
v_a_1090_ = lean_ctor_get(v___x_999_, 0);
v_a_1091_ = lean_ctor_get(v___x_999_, 1);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1093_ = v___x_999_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_inc(v_a_1090_);
lean_dec(v___x_999_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1090_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v_a_1091_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
}
}
else
{
lean_dec(v___x_909_);
lean_dec_ref(v___y_897_);
lean_dec(v_funNamesToMatch_893_);
lean_dec(v_alts_879_);
lean_dec(v_discr_878_);
lean_dec(v_kElse_877_);
return v___x_912_;
}
}
else
{
lean_object* v_a_1100_; lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
lean_dec(v_altsNext_899_);
lean_dec_ref(v___y_897_);
lean_dec(v_funNamesToMatch_893_);
lean_dec(v_alts_879_);
lean_dec(v_discr_878_);
lean_dec(v_kElse_877_);
v_a_1100_ = lean_ctor_get(v___x_904_, 0);
v_a_1101_ = lean_ctor_get(v___x_904_, 1);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v___x_904_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_inc(v_a_1100_);
lean_dec(v___x_904_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1100_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v_a_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
else
{
lean_object* v_quotContext_1109_; lean_object* v_currMacroScope_1110_; lean_object* v_ref_1111_; uint8_t v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
lean_dec(v_altsNext_899_);
v_quotContext_1109_ = lean_ctor_get(v___y_897_, 1);
v_currMacroScope_1110_ = lean_ctor_get(v___y_897_, 2);
v_ref_1111_ = lean_ctor_get(v___y_897_, 5);
v___x_1112_ = 0;
v___x_1113_ = l_Lean_SourceInfo_fromRef(v_ref_1111_, v___x_1112_);
v___x_1114_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2));
v___x_1115_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4));
v___x_1116_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__1));
v___x_1117_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__3));
v___x_1118_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2));
lean_inc_n(v___x_1113_, 8);
v___x_1119_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1113_);
lean_ctor_set(v___x_1119_, 1, v___x_1118_);
v___x_1120_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__5));
v___x_1121_ = lean_obj_once(&l_Lean_Elab_Term_MatchExpr_getActuals___closed__7, &l_Lean_Elab_Term_MatchExpr_getActuals___closed__7_once, _init_l_Lean_Elab_Term_MatchExpr_getActuals___closed__7);
v___x_1122_ = lean_box(0);
lean_inc(v_currMacroScope_1110_);
lean_inc(v_quotContext_1109_);
v___x_1123_ = l_Lean_addMacroScope(v_quotContext_1109_, v___x_1122_, v_currMacroScope_1110_);
v___x_1124_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getActuals___closed__21));
v___x_1125_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1113_);
lean_ctor_set(v___x_1125_, 1, v___x_1121_);
lean_ctor_set(v___x_1125_, 2, v___x_1123_);
lean_ctor_set(v___x_1125_, 3, v___x_1124_);
v___x_1126_ = l_Lean_Syntax_node1(v___x_1113_, v___x_1120_, v___x_1125_);
v___x_1127_ = l_Lean_Syntax_node2(v___x_1113_, v___x_1117_, v___x_1119_, v___x_1126_);
v___x_1128_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
v___x_1129_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1113_);
lean_ctor_set(v___x_1129_, 1, v___x_1115_);
lean_ctor_set(v___x_1129_, 2, v___x_1128_);
v___x_1130_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15));
v___x_1131_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1113_);
lean_ctor_set(v___x_1131_, 1, v___x_1130_);
v___x_1132_ = l_Lean_Syntax_node3(v___x_1113_, v___x_1116_, v___x_1127_, v___x_1129_, v___x_1131_);
v___x_1133_ = l_Lean_Syntax_node1(v___x_1113_, v___x_1115_, v___x_1132_);
v___x_1134_ = l_Lean_Syntax_node2(v___x_1113_, v___x_1114_, v_kElse_877_, v___x_1133_);
v___x_1135_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg(v_alts_879_, v_discr_878_, v_funNamesToMatch_893_, v___x_1134_, v___y_897_, v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v_funNamesToMatch_893_);
lean_dec(v_alts_879_);
return v___x_1135_;
}
}
v_reusejp_1138_:
{
lean_object* v___x_1140_; 
lean_inc(v_ref_892_);
lean_inc(v_maxRecDepth_891_);
lean_inc(v_currRecDepth_890_);
lean_inc(v_macroScope_882_);
lean_inc(v_quotContext_889_);
lean_inc(v_methods_888_);
v___x_1140_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1140_, 0, v_methods_888_);
lean_ctor_set(v___x_1140_, 1, v_quotContext_889_);
lean_ctor_set(v___x_1140_, 2, v_macroScope_882_);
lean_ctor_set(v___x_1140_, 3, v_currRecDepth_890_);
lean_ctor_set(v___x_1140_, 4, v_maxRecDepth_891_);
lean_ctor_set(v___x_1140_, 5, v_ref_892_);
if (v_saveActual_894_ == 0)
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
lean_dec(v_macroScope_882_);
v___x_1141_ = l_Lean_SourceInfo_fromRef(v_ref_892_, v_saveActual_894_);
v___x_1142_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1));
v___x_1143_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getParams___closed__0));
lean_inc(v___x_1141_);
v___x_1144_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1141_);
lean_ctor_set(v___x_1144_, 1, v___x_1143_);
v___x_1145_ = l_Lean_Syntax_node1(v___x_1141_, v___x_1142_, v___x_1144_);
v_actual_896_ = v___x_1145_;
v___y_897_ = v___x_1140_;
v___y_898_ = v___x_1139_;
goto v___jp_895_;
}
else
{
uint8_t v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1146_ = 0;
v___x_1147_ = l_Lean_SourceInfo_fromRef(v_ref_892_, v___x_1146_);
v___x_1148_ = lean_obj_once(&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__33, &l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__33_once, _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__33);
v___x_1149_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__34));
lean_inc(v_quotContext_889_);
v___x_1150_ = l_Lean_addMacroScope(v_quotContext_889_, v___x_1149_, v_macroScope_882_);
v___x_1151_ = lean_box(0);
v___x_1152_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1147_);
lean_ctor_set(v___x_1152_, 1, v___x_1148_);
lean_ctor_set(v___x_1152_, 2, v___x_1150_);
lean_ctor_set(v___x_1152_, 3, v___x_1151_);
v_actual_896_ = v___x_1152_;
v___y_897_ = v___x_1140_;
v___y_898_ = v___x_1139_;
goto v___jp_895_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___boxed(lean_object* v_kElse_1155_, lean_object* v_discr_1156_, lean_object* v_alts_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop(v_kElse_1155_, v_discr_1156_, v_alts_1157_, v_a_1158_, v_a_1159_);
lean_dec_ref(v_a_1158_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0(lean_object* v_alts_1161_, lean_object* v_discr_1162_, lean_object* v_as_1163_, lean_object* v_as_x27_1164_, lean_object* v_b_1165_, lean_object* v_a_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v___x_1169_; 
v___x_1169_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg(v_alts_1161_, v_discr_1162_, v_as_x27_1164_, v_b_1165_, v___y_1167_, v___y_1168_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___boxed(lean_object* v_alts_1170_, lean_object* v_discr_1171_, lean_object* v_as_1172_, lean_object* v_as_x27_1173_, lean_object* v_b_1174_, lean_object* v_a_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0(v_alts_1170_, v_discr_1171_, v_as_1172_, v_as_x27_1173_, v_b_1174_, v_a_1175_, v___y_1176_, v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v_as_x27_1173_);
lean_dec(v_as_1172_);
lean_dec(v_alts_1170_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_generate___lam__0(lean_object* v_____do__lift_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
uint8_t v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1182_ = 0;
v___x_1183_ = l_Lean_SourceInfo_fromRef(v_____do__lift_1179_, v___x_1182_);
v___x_1184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1183_);
lean_ctor_set(v___x_1184_, 1, v___y_1181_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_generate___lam__0___boxed(lean_object* v_____do__lift_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Lean_Elab_Term_MatchExpr_generate___lam__0(v_____do__lift_1185_, v___y_1186_, v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec(v_____do__lift_1185_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg(lean_object* v_as_x27_1195_, lean_object* v_b_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
if (lean_obj_tag(v_as_x27_1195_) == 0)
{
lean_object* v___x_1199_; 
v___x_1199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1199_, 0, v_b_1196_);
lean_ctor_set(v___x_1199_, 1, v___y_1198_);
return v___x_1199_;
}
else
{
lean_object* v_head_1200_; lean_object* v_tail_1201_; lean_object* v___x_1202_; 
v_head_1200_ = lean_ctor_get(v_as_x27_1195_, 0);
v_tail_1201_ = lean_ctor_get(v_as_x27_1195_, 1);
lean_inc(v_head_1200_);
v___x_1202_ = l_Lean_Elab_Term_MatchExpr_getParams(v_head_1200_, v___y_1197_, v___y_1198_);
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v_a_1203_; lean_object* v_a_1204_; lean_object* v_ref_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v_rhs_1209_; lean_object* v_k_1210_; lean_object* v___x_1211_; uint8_t v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
lean_inc(v_a_1203_);
v_a_1204_ = lean_ctor_get(v___x_1202_, 1);
lean_inc(v_a_1204_);
lean_dec_ref_known(v___x_1202_, 2);
v_ref_1205_ = lean_ctor_get(v___y_1197_, 5);
v___x_1206_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__0));
v___x_1207_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__1));
v___x_1208_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18));
v_rhs_1209_ = lean_ctor_get(v_head_1200_, 3);
v_k_1210_ = lean_ctor_get(v_head_1200_, 4);
v___x_1211_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20));
v___x_1212_ = 0;
v___x_1213_ = l_Lean_SourceInfo_fromRef(v_ref_1205_, v___x_1212_);
lean_inc_n(v___x_1213_, 8);
v___x_1214_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
lean_ctor_set(v___x_1214_, 1, v___x_1206_);
v___x_1215_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22));
lean_inc(v_k_1210_);
v___x_1216_ = l_Lean_Syntax_node1(v___x_1213_, v___x_1215_, v_k_1210_);
v___x_1217_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4));
v___x_1218_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
v___x_1219_ = l_Array_append___redArg(v___x_1218_, v_a_1203_);
lean_dec(v_a_1203_);
v___x_1220_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1213_);
lean_ctor_set(v___x_1220_, 1, v___x_1217_);
lean_ctor_set(v___x_1220_, 2, v___x_1219_);
v___x_1221_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1213_);
lean_ctor_set(v___x_1221_, 1, v___x_1217_);
lean_ctor_set(v___x_1221_, 2, v___x_1218_);
v___x_1222_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__23));
v___x_1223_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1213_);
lean_ctor_set(v___x_1223_, 1, v___x_1222_);
lean_inc(v_rhs_1209_);
v___x_1224_ = l_Lean_Syntax_node5(v___x_1213_, v___x_1211_, v___x_1216_, v___x_1220_, v___x_1221_, v___x_1223_, v_rhs_1209_);
v___x_1225_ = l_Lean_Syntax_node1(v___x_1213_, v___x_1208_, v___x_1224_);
v___x_1226_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__31));
v___x_1227_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1213_);
lean_ctor_set(v___x_1227_, 1, v___x_1226_);
v___x_1228_ = l_Lean_Syntax_node4(v___x_1213_, v___x_1207_, v___x_1214_, v___x_1225_, v___x_1227_, v_b_1196_);
v_as_x27_1195_ = v_tail_1201_;
v_b_1196_ = v___x_1228_;
v___y_1198_ = v_a_1204_;
goto _start;
}
else
{
lean_object* v_a_1230_; lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1238_; 
lean_dec(v_b_1196_);
v_a_1230_ = lean_ctor_get(v___x_1202_, 0);
v_a_1231_ = lean_ctor_get(v___x_1202_, 1);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1233_ = v___x_1202_;
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_inc(v_a_1230_);
lean_dec(v___x_1202_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1236_; 
if (v_isShared_1234_ == 0)
{
v___x_1236_ = v___x_1233_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_a_1230_);
lean_ctor_set(v_reuseFailAlloc_1237_, 1, v_a_1231_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___boxed(lean_object* v_as_x27_1239_, lean_object* v_b_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg(v_as_x27_1239_, v_b_1240_, v___y_1241_, v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v_as_x27_1239_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__0(lean_object* v_x_1244_, lean_object* v_x_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
if (lean_obj_tag(v_x_1244_) == 0)
{
lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1248_ = l_List_reverse___redArg(v_x_1245_);
v___x_1249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1248_);
lean_ctor_set(v___x_1249_, 1, v___y_1247_);
return v___x_1249_;
}
else
{
lean_object* v_head_1250_; lean_object* v_tail_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1262_; 
v_head_1250_ = lean_ctor_get(v_x_1244_, 0);
v_tail_1251_ = lean_ctor_get(v_x_1244_, 1);
v_isSharedCheck_1262_ = !lean_is_exclusive(v_x_1244_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1253_ = v_x_1244_;
v_isShared_1254_ = v_isSharedCheck_1262_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_tail_1251_);
lean_inc(v_head_1250_);
lean_dec(v_x_1244_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1262_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1255_; lean_object* v_a_1256_; lean_object* v_a_1257_; lean_object* v___x_1259_; 
v___x_1255_ = l_Lean_Elab_Term_MatchExpr_initK(v_head_1250_, v___y_1246_, v___y_1247_);
v_a_1256_ = lean_ctor_get(v___x_1255_, 0);
lean_inc(v_a_1256_);
v_a_1257_ = lean_ctor_get(v___x_1255_, 1);
lean_inc(v_a_1257_);
lean_dec_ref(v___x_1255_);
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 1, v_x_1245_);
lean_ctor_set(v___x_1253_, 0, v_a_1256_);
v___x_1259_ = v___x_1253_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_a_1256_);
lean_ctor_set(v_reuseFailAlloc_1261_, 1, v_x_1245_);
v___x_1259_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
v_x_1244_ = v_tail_1251_;
v_x_1245_ = v___x_1259_;
v___y_1247_ = v_a_1257_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__0___boxed(lean_object* v_x_1263_, lean_object* v_x_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__0(v_x_1263_, v_x_1264_, v___y_1265_, v___y_1266_);
lean_dec_ref(v___y_1265_);
return v_res_1267_;
}
}
static lean_object* _init_l_Lean_Elab_Term_MatchExpr_generate___closed__4(void){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_generate___closed__3));
v___x_1279_ = l_String_toRawSubstring_x27(v___x_1278_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_generate(lean_object* v_discr_1294_, lean_object* v_alts_1295_, lean_object* v_elseAlt_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = lean_box(0);
v___x_1300_ = l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__0(v_alts_1295_, v___x_1299_, v_a_1297_, v_a_1298_);
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v_a_1301_; lean_object* v_a_1302_; lean_object* v_quotContext_1303_; lean_object* v_currMacroScope_1304_; lean_object* v_ref_1305_; lean_object* v___x_1306_; lean_object* v_a_1307_; lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1427_; 
v_a_1301_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_a_1301_);
v_a_1302_ = lean_ctor_get(v___x_1300_, 1);
lean_inc(v_a_1302_);
lean_dec_ref_known(v___x_1300_, 2);
v_quotContext_1303_ = lean_ctor_get(v_a_1297_, 1);
v_currMacroScope_1304_ = lean_ctor_get(v_a_1297_, 2);
v_ref_1305_ = lean_ctor_get(v_a_1297_, 5);
v___x_1306_ = l_Lean_Elab_Term_MatchExpr_generate___lam__0(v_ref_1305_, v_a_1297_, v_a_1302_);
v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
v_a_1308_ = lean_ctor_get(v___x_1306_, 1);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1310_ = v___x_1306_;
v_isShared_1311_ = v_isSharedCheck_1427_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_inc(v_a_1307_);
lean_dec(v___x_1306_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1427_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1312_; lean_object* v_a_1313_; lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1426_; 
v___x_1312_ = l_Lean_Elab_Term_MatchExpr_generate___lam__0(v_ref_1305_, v_a_1297_, v_a_1308_);
v_a_1313_ = lean_ctor_get(v___x_1312_, 0);
v_a_1314_ = lean_ctor_get(v___x_1312_, 1);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1316_ = v___x_1312_;
v_isShared_1317_ = v_isSharedCheck_1426_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_inc(v_a_1313_);
lean_dec(v___x_1312_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1426_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1318_ = lean_obj_once(&l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__1, &l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__1_once, _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__1);
v___x_1319_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__2));
lean_inc_n(v_currMacroScope_1304_, 2);
lean_inc_n(v_quotContext_1303_, 2);
v___x_1320_ = l_Lean_addMacroScope(v_quotContext_1303_, v___x_1319_, v_currMacroScope_1304_);
lean_inc(v___x_1320_);
v___x_1321_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1321_, 0, v_a_1307_);
lean_ctor_set(v___x_1321_, 1, v___x_1318_);
lean_ctor_set(v___x_1321_, 2, v___x_1320_);
lean_ctor_set(v___x_1321_, 3, v___x_1299_);
v___x_1322_ = lean_obj_once(&l_Lean_Elab_Term_MatchExpr_initK___closed__1, &l_Lean_Elab_Term_MatchExpr_initK___closed__1_once, _init_l_Lean_Elab_Term_MatchExpr_initK___closed__1);
v___x_1323_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_initK___closed__2));
v___x_1324_ = l_Lean_addMacroScope(v_quotContext_1303_, v___x_1323_, v_currMacroScope_1304_);
lean_inc(v___x_1324_);
v___x_1325_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1325_, 0, v_a_1313_);
lean_ctor_set(v___x_1325_, 1, v___x_1322_);
lean_ctor_set(v___x_1325_, 2, v___x_1324_);
lean_ctor_set(v___x_1325_, 3, v___x_1299_);
lean_inc(v_a_1301_);
v___x_1326_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop(v___x_1325_, v___x_1321_, v_a_1301_, v_a_1297_, v_a_1314_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v_a_1327_; lean_object* v_a_1328_; lean_object* v___x_1329_; lean_object* v_a_1330_; lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1416_; 
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
lean_inc(v_a_1327_);
v_a_1328_ = lean_ctor_get(v___x_1326_, 1);
lean_inc(v_a_1328_);
lean_dec_ref_known(v___x_1326_, 2);
v___x_1329_ = l_Lean_Elab_Term_MatchExpr_generate___lam__0(v_ref_1305_, v_a_1297_, v_a_1328_);
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
v_a_1331_ = lean_ctor_get(v___x_1329_, 1);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1333_ = v___x_1329_;
v_isShared_1334_ = v_isSharedCheck_1416_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_inc(v_a_1330_);
lean_dec(v___x_1329_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1416_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1338_; 
v___x_1335_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__0));
v___x_1336_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__1));
lean_inc(v_a_1330_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set_tag(v___x_1333_, 2);
lean_ctor_set(v___x_1333_, 1, v___x_1335_);
v___x_1338_ = v___x_1333_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_a_1330_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v___x_1335_);
v___x_1338_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1348_; 
v___x_1339_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18));
v___x_1340_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20));
v___x_1341_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22));
lean_inc_n(v_a_1330_, 3);
v___x_1342_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1342_, 0, v_a_1330_);
lean_ctor_set(v___x_1342_, 1, v___x_1322_);
lean_ctor_set(v___x_1342_, 2, v___x_1324_);
lean_ctor_set(v___x_1342_, 3, v___x_1299_);
v___x_1343_ = l_Lean_Syntax_node1(v_a_1330_, v___x_1341_, v___x_1342_);
v___x_1344_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4));
v___x_1345_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1));
v___x_1346_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2));
if (v_isShared_1317_ == 0)
{
lean_ctor_set_tag(v___x_1316_, 2);
lean_ctor_set(v___x_1316_, 1, v___x_1346_);
lean_ctor_set(v___x_1316_, 0, v_a_1330_);
v___x_1348_ = v___x_1316_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1330_);
lean_ctor_set(v_reuseFailAlloc_1414_, 1, v___x_1346_);
v___x_1348_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1352_; 
v___x_1349_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1));
v___x_1350_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getParams___closed__0));
lean_inc(v_a_1330_);
if (v_isShared_1311_ == 0)
{
lean_ctor_set_tag(v___x_1310_, 2);
lean_ctor_set(v___x_1310_, 1, v___x_1350_);
lean_ctor_set(v___x_1310_, 0, v_a_1330_);
v___x_1352_ = v___x_1310_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1330_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v___x_1350_);
v___x_1352_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
lean_inc_n(v_a_1330_, 23);
v___x_1353_ = l_Lean_Syntax_node1(v_a_1330_, v___x_1349_, v___x_1352_);
v___x_1354_ = l_Lean_Syntax_node1(v_a_1330_, v___x_1344_, v___x_1353_);
v___x_1355_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__5));
v___x_1356_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1356_, 0, v_a_1330_);
lean_ctor_set(v___x_1356_, 1, v___x_1355_);
v___x_1357_ = lean_obj_once(&l_Lean_Elab_Term_MatchExpr_getParams___closed__2, &l_Lean_Elab_Term_MatchExpr_getParams___closed__2_once, _init_l_Lean_Elab_Term_MatchExpr_getParams___closed__2);
v___x_1358_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getParams___closed__3));
lean_inc_n(v_currMacroScope_1304_, 2);
lean_inc_n(v_quotContext_1303_, 2);
v___x_1359_ = l_Lean_addMacroScope(v_quotContext_1303_, v___x_1358_, v_currMacroScope_1304_);
v___x_1360_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_generate___closed__2));
v___x_1361_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1361_, 0, v_a_1330_);
lean_ctor_set(v___x_1361_, 1, v___x_1357_);
lean_ctor_set(v___x_1361_, 2, v___x_1359_);
lean_ctor_set(v___x_1361_, 3, v___x_1360_);
v___x_1362_ = l_Lean_Syntax_node2(v_a_1330_, v___x_1344_, v___x_1356_, v___x_1361_);
v___x_1363_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
v___x_1364_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1364_, 0, v_a_1330_);
lean_ctor_set(v___x_1364_, 1, v___x_1344_);
lean_ctor_set(v___x_1364_, 2, v___x_1363_);
v___x_1365_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15));
v___x_1366_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1366_, 0, v_a_1330_);
lean_ctor_set(v___x_1366_, 1, v___x_1365_);
lean_inc_ref_n(v___x_1364_, 4);
v___x_1367_ = l_Lean_Syntax_node5(v_a_1330_, v___x_1345_, v___x_1348_, v___x_1354_, v___x_1362_, v___x_1364_, v___x_1366_);
v___x_1368_ = l_Lean_Syntax_node1(v_a_1330_, v___x_1344_, v___x_1367_);
v___x_1369_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__23));
v___x_1370_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1370_, 0, v_a_1330_);
lean_ctor_set(v___x_1370_, 1, v___x_1369_);
lean_inc_ref(v___x_1370_);
v___x_1371_ = l_Lean_Syntax_node5(v_a_1330_, v___x_1340_, v___x_1343_, v___x_1368_, v___x_1364_, v___x_1370_, v_elseAlt_1296_);
v___x_1372_ = l_Lean_Syntax_node1(v_a_1330_, v___x_1339_, v___x_1371_);
v___x_1373_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__31));
v___x_1374_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1374_, 0, v_a_1330_);
lean_ctor_set(v___x_1374_, 1, v___x_1373_);
v___x_1375_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__13));
v___x_1376_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__14));
v___x_1377_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1377_, 0, v_a_1330_);
lean_ctor_set(v___x_1377_, 1, v___x_1375_);
v___x_1378_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__16));
v___x_1379_ = l_Lean_Syntax_node1(v_a_1330_, v___x_1378_, v___x_1364_);
v___x_1380_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1380_, 0, v_a_1330_);
lean_ctor_set(v___x_1380_, 1, v___x_1318_);
lean_ctor_set(v___x_1380_, 2, v___x_1320_);
lean_ctor_set(v___x_1380_, 3, v___x_1299_);
v___x_1381_ = l_Lean_Syntax_node1(v_a_1330_, v___x_1341_, v___x_1380_);
v___x_1382_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2));
v___x_1383_ = lean_obj_once(&l_Lean_Elab_Term_MatchExpr_generate___closed__4, &l_Lean_Elab_Term_MatchExpr_generate___closed__4_once, _init_l_Lean_Elab_Term_MatchExpr_generate___closed__4);
v___x_1384_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_generate___closed__6));
v___x_1385_ = l_Lean_addMacroScope(v_quotContext_1303_, v___x_1384_, v_currMacroScope_1304_);
v___x_1386_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_generate___closed__9));
v___x_1387_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1387_, 0, v_a_1330_);
lean_ctor_set(v___x_1387_, 1, v___x_1383_);
lean_ctor_set(v___x_1387_, 2, v___x_1385_);
lean_ctor_set(v___x_1387_, 3, v___x_1386_);
v___x_1388_ = l_Lean_Syntax_node1(v_a_1330_, v___x_1344_, v_discr_1294_);
v___x_1389_ = l_Lean_Syntax_node2(v_a_1330_, v___x_1382_, v___x_1387_, v___x_1388_);
v___x_1390_ = l_Lean_Syntax_node5(v_a_1330_, v___x_1340_, v___x_1381_, v___x_1364_, v___x_1364_, v___x_1370_, v___x_1389_);
v___x_1391_ = l_Lean_Syntax_node1(v_a_1330_, v___x_1339_, v___x_1390_);
lean_inc_ref(v___x_1374_);
v___x_1392_ = l_Lean_Syntax_node5(v_a_1330_, v___x_1376_, v___x_1377_, v___x_1379_, v___x_1391_, v___x_1374_, v_a_1327_);
v___x_1393_ = l_Lean_Syntax_node4(v_a_1330_, v___x_1336_, v___x_1338_, v___x_1372_, v___x_1374_, v___x_1392_);
v___x_1394_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg(v_a_1301_, v___x_1393_, v_a_1297_, v_a_1331_);
lean_dec(v_a_1301_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v_a_1395_; lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1403_; 
v_a_1395_ = lean_ctor_get(v___x_1394_, 0);
v_a_1396_ = lean_ctor_get(v___x_1394_, 1);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1398_ = v___x_1394_;
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_inc(v_a_1395_);
lean_dec(v___x_1394_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1401_; 
if (v_isShared_1399_ == 0)
{
v___x_1401_ = v___x_1398_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_a_1395_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v_a_1396_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
else
{
lean_object* v_a_1404_; lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
v_a_1404_ = lean_ctor_get(v___x_1394_, 0);
v_a_1405_ = lean_ctor_get(v___x_1394_, 1);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1394_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_inc(v_a_1404_);
lean_dec(v___x_1394_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1404_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v_a_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
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
lean_object* v_a_1417_; lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1425_; 
lean_dec(v___x_1324_);
lean_dec(v___x_1320_);
lean_del_object(v___x_1316_);
lean_del_object(v___x_1310_);
lean_dec(v_a_1301_);
lean_dec(v_elseAlt_1296_);
lean_dec(v_discr_1294_);
v_a_1417_ = lean_ctor_get(v___x_1326_, 0);
v_a_1418_ = lean_ctor_get(v___x_1326_, 1);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1420_ = v___x_1326_;
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_inc(v_a_1417_);
lean_dec(v___x_1326_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1423_; 
if (v_isShared_1421_ == 0)
{
v___x_1423_ = v___x_1420_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_a_1417_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v_a_1418_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
}
}
else
{
lean_object* v_a_1428_; lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1436_; 
lean_dec(v_elseAlt_1296_);
lean_dec(v_discr_1294_);
v_a_1428_ = lean_ctor_get(v___x_1300_, 0);
v_a_1429_ = lean_ctor_get(v___x_1300_, 1);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1431_ = v___x_1300_;
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_inc(v_a_1428_);
lean_dec(v___x_1300_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1434_; 
if (v_isShared_1432_ == 0)
{
v___x_1434_ = v___x_1431_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_a_1428_);
lean_ctor_set(v_reuseFailAlloc_1435_, 1, v_a_1429_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_generate___boxed(lean_object* v_discr_1437_, lean_object* v_alts_1438_, lean_object* v_elseAlt_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Lean_Elab_Term_MatchExpr_generate(v_discr_1437_, v_alts_1438_, v_elseAlt_1439_, v_a_1440_, v_a_1441_);
lean_dec_ref(v_a_1440_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1(lean_object* v_as_1443_, lean_object* v_as_x27_1444_, lean_object* v_b_1445_, lean_object* v_a_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v___x_1449_; 
v___x_1449_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg(v_as_x27_1444_, v_b_1445_, v___y_1447_, v___y_1448_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___boxed(lean_object* v_as_1450_, lean_object* v_as_x27_1451_, lean_object* v_b_1452_, lean_object* v_a_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1(v_as_1450_, v_as_x27_1451_, v_b_1452_, v_a_1453_, v___y_1454_, v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v_as_x27_1451_);
lean_dec(v_as_1450_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_main_spec__0(lean_object* v_x_1458_, lean_object* v_x_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
if (lean_obj_tag(v_x_1458_) == 0)
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1462_ = l_List_reverse___redArg(v_x_1459_);
v___x_1463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1462_);
lean_ctor_set(v___x_1463_, 1, v___y_1461_);
return v___x_1463_;
}
else
{
lean_object* v_head_1464_; lean_object* v_tail_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1491_; 
v_head_1464_ = lean_ctor_get(v_x_1458_, 0);
v_tail_1465_ = lean_ctor_get(v_x_1458_, 1);
v_isSharedCheck_1491_ = !lean_is_exclusive(v_x_1458_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1467_ = v_x_1458_;
v_isShared_1468_ = v_isSharedCheck_1491_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_tail_1465_);
lean_inc(v_head_1464_);
lean_dec(v_x_1458_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1491_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v_a_1470_; lean_object* v_a_1471_; lean_object* v___x_1476_; 
lean_inc(v_head_1464_);
v___x_1476_ = l_Lean_Elab_Term_MatchExpr_toAlt_x3f(v_head_1464_);
if (lean_obj_tag(v___x_1476_) == 1)
{
lean_object* v_val_1477_; 
lean_dec(v_head_1464_);
v_val_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_val_1477_);
lean_dec_ref_known(v___x_1476_, 1);
v_a_1470_ = v_val_1477_;
v_a_1471_ = v___y_1461_;
goto v___jp_1469_;
}
else
{
lean_object* v___x_1478_; lean_object* v___x_1479_; 
lean_dec(v___x_1476_);
v___x_1478_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_main_spec__0___closed__0));
v___x_1479_ = l_Lean_Macro_throwErrorAt___redArg(v_head_1464_, v___x_1478_, v___y_1460_, v___y_1461_);
lean_dec(v_head_1464_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v_a_1480_; lean_object* v_a_1481_; 
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_a_1480_);
v_a_1481_ = lean_ctor_get(v___x_1479_, 1);
lean_inc(v_a_1481_);
lean_dec_ref_known(v___x_1479_, 2);
v_a_1470_ = v_a_1480_;
v_a_1471_ = v_a_1481_;
goto v___jp_1469_;
}
else
{
lean_object* v_a_1482_; lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1490_; 
lean_del_object(v___x_1467_);
lean_dec(v_tail_1465_);
lean_dec(v_x_1459_);
v_a_1482_ = lean_ctor_get(v___x_1479_, 0);
v_a_1483_ = lean_ctor_get(v___x_1479_, 1);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1485_ = v___x_1479_;
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_inc(v_a_1482_);
lean_dec(v___x_1479_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1488_; 
if (v_isShared_1486_ == 0)
{
v___x_1488_ = v___x_1485_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_a_1482_);
lean_ctor_set(v_reuseFailAlloc_1489_, 1, v_a_1483_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
}
v___jp_1469_:
{
lean_object* v___x_1473_; 
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 1, v_x_1459_);
lean_ctor_set(v___x_1467_, 0, v_a_1470_);
v___x_1473_ = v___x_1467_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1470_);
lean_ctor_set(v_reuseFailAlloc_1475_, 1, v_x_1459_);
v___x_1473_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
v_x_1458_ = v_tail_1465_;
v_x_1459_ = v___x_1473_;
v___y_1461_ = v_a_1471_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_main_spec__0___boxed(lean_object* v_x_1492_, lean_object* v_x_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_main_spec__0(v_x_1492_, v_x_1493_, v___y_1494_, v___y_1495_);
lean_dec_ref(v___y_1494_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_main(lean_object* v_discr_1498_, lean_object* v_alts_1499_, lean_object* v_elseAlt_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1503_ = lean_array_to_list(v_alts_1499_);
v___x_1504_ = lean_box(0);
v___x_1505_ = l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_main_spec__0(v___x_1503_, v___x_1504_, v_a_1501_, v_a_1502_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v_a_1506_; lean_object* v_a_1507_; lean_object* v___x_1508_; 
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
lean_inc(v_a_1506_);
v_a_1507_ = lean_ctor_get(v___x_1505_, 1);
lean_inc(v_a_1507_);
lean_dec_ref_known(v___x_1505_, 2);
lean_inc(v_elseAlt_1500_);
v___x_1508_ = l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f(v_elseAlt_1500_);
if (lean_obj_tag(v___x_1508_) == 1)
{
lean_object* v_val_1509_; lean_object* v___x_1510_; 
lean_dec(v_elseAlt_1500_);
v_val_1509_ = lean_ctor_get(v___x_1508_, 0);
lean_inc(v_val_1509_);
lean_dec_ref_known(v___x_1508_, 1);
v___x_1510_ = l_Lean_Elab_Term_MatchExpr_generate(v_discr_1498_, v_a_1506_, v_val_1509_, v_a_1501_, v_a_1507_);
return v___x_1510_;
}
else
{
lean_object* v___x_1511_; lean_object* v___x_1512_; 
lean_dec(v___x_1508_);
lean_dec(v_a_1506_);
lean_dec(v_discr_1498_);
v___x_1511_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_main___closed__0));
v___x_1512_ = l_Lean_Macro_throwErrorAt___redArg(v_elseAlt_1500_, v___x_1511_, v_a_1501_, v_a_1507_);
lean_dec(v_elseAlt_1500_);
return v___x_1512_;
}
}
else
{
lean_object* v_a_1513_; lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1521_; 
lean_dec(v_elseAlt_1500_);
lean_dec(v_discr_1498_);
v_a_1513_ = lean_ctor_get(v___x_1505_, 0);
v_a_1514_ = lean_ctor_get(v___x_1505_, 1);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1516_ = v___x_1505_;
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_inc(v_a_1513_);
lean_dec(v___x_1505_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1519_; 
if (v_isShared_1517_ == 0)
{
v___x_1519_ = v___x_1516_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1513_);
lean_ctor_set(v_reuseFailAlloc_1520_, 1, v_a_1514_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_main___boxed(lean_object* v_discr_1522_, lean_object* v_alts_1523_, lean_object* v_elseAlt_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l_Lean_Elab_Term_MatchExpr_main(v_discr_1522_, v_alts_1523_, v_elseAlt_1524_, v_a_1525_, v_a_1526_);
lean_dec_ref(v_a_1525_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchExpr(lean_object* v_stx_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_){
_start:
{
lean_object* v___x_1537_; uint8_t v___x_1538_; 
v___x_1537_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchExpr___closed__1));
lean_inc(v_stx_1534_);
v___x_1538_ = l_Lean_Syntax_isOfKind(v_stx_1534_, v___x_1537_);
if (v___x_1538_ == 0)
{
lean_object* v___x_1539_; 
lean_dec(v_stx_1534_);
v___x_1539_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1536_);
return v___x_1539_;
}
else
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v_discr_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1540_ = lean_unsigned_to_nat(0u);
v___x_1541_ = lean_unsigned_to_nat(1u);
v_discr_1542_ = l_Lean_Syntax_getArg(v_stx_1534_, v___x_1541_);
v___x_1543_ = lean_unsigned_to_nat(3u);
v___x_1544_ = l_Lean_Syntax_getArg(v_stx_1534_, v___x_1543_);
lean_dec(v_stx_1534_);
v___x_1545_ = l_Lean_Syntax_getArg(v___x_1544_, v___x_1540_);
v___x_1546_ = l_Lean_Syntax_getArgs(v___x_1545_);
lean_dec(v___x_1545_);
v___x_1547_ = l_Lean_Syntax_getArg(v___x_1544_, v___x_1541_);
lean_dec(v___x_1544_);
v___x_1548_ = l_Lean_Elab_Term_MatchExpr_main(v_discr_1542_, v___x_1546_, v___x_1547_, v_a_1535_, v_a_1536_);
return v___x_1548_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchExpr___boxed(lean_object* v_stx_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_Lean_Elab_Term_expandMatchExpr(v_stx_1549_, v_a_1550_, v_a_1551_);
lean_dec_ref(v_a_1550_);
return v_res_1552_;
}
}
lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1(){
_start:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1560_ = l_Lean_Elab_macroAttribute;
v___x_1561_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchExpr___closed__1));
v___x_1562_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1));
v___x_1563_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandMatchExpr___boxed), 3, 0);
v___x_1564_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1560_, v___x_1561_, v___x_1562_, v___x_1563_);
return v___x_1564_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1565_;
v_res_1565_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1();
stack->m_obj
 = v_res_1565_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___boxed(lean_object* v_a_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1();
return v_res_1567_;
}
}
lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3(){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1594_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1));
v___x_1595_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__6));
v___x_1596_ = l_Lean_addBuiltinDeclarationRanges(v___x_1594_, v___x_1595_);
return v___x_1596_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1597_;
v_res_1597_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3();
stack->m_obj
 = v_res_1597_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___boxed(lean_object* v_a_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3();
return v_res_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandLetExpr(lean_object* v_stx_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_){
_start:
{
lean_object* v___x_1619_; uint8_t v___x_1620_; 
v___x_1619_ = ((lean_object*)(l_Lean_Elab_Term_expandLetExpr___closed__1));
lean_inc(v_stx_1616_);
v___x_1620_ = l_Lean_Syntax_isOfKind(v_stx_1616_, v___x_1619_);
if (v___x_1620_ == 0)
{
lean_object* v___x_1621_; 
lean_dec(v_stx_1616_);
v___x_1621_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1618_);
return v___x_1621_;
}
else
{
lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; uint8_t v___x_1625_; 
v___x_1622_ = lean_unsigned_to_nat(1u);
v___x_1623_ = l_Lean_Syntax_getArg(v_stx_1616_, v___x_1622_);
v___x_1624_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__5));
lean_inc(v___x_1623_);
v___x_1625_ = l_Lean_Syntax_isOfKind(v___x_1623_, v___x_1624_);
if (v___x_1625_ == 0)
{
lean_object* v___x_1626_; 
lean_dec(v___x_1623_);
lean_dec(v_stx_1616_);
v___x_1626_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1618_);
return v___x_1626_;
}
else
{
lean_object* v_ref_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; uint8_t v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
v_ref_1627_ = lean_ctor_get(v_a_1617_, 5);
v___x_1628_ = lean_unsigned_to_nat(3u);
v___x_1629_ = l_Lean_Syntax_getArg(v_stx_1616_, v___x_1628_);
v___x_1630_ = lean_unsigned_to_nat(5u);
v___x_1631_ = l_Lean_Syntax_getArg(v_stx_1616_, v___x_1630_);
v___x_1632_ = lean_unsigned_to_nat(7u);
v___x_1633_ = l_Lean_Syntax_getArg(v_stx_1616_, v___x_1632_);
lean_dec(v_stx_1616_);
v___x_1634_ = 0;
v___x_1635_ = l_Lean_SourceInfo_fromRef(v_ref_1627_, v___x_1634_);
v___x_1636_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchExpr___closed__1));
v___x_1637_ = ((lean_object*)(l_Lean_Elab_Term_expandLetExpr___closed__2));
lean_inc_n(v___x_1635_, 10);
v___x_1638_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1635_);
lean_ctor_set(v___x_1638_, 1, v___x_1637_);
v___x_1639_ = ((lean_object*)(l_Lean_Elab_Term_expandLetExpr___closed__3));
v___x_1640_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1635_);
lean_ctor_set(v___x_1640_, 1, v___x_1639_);
v___x_1641_ = ((lean_object*)(l_Lean_Elab_Term_expandLetExpr___closed__5));
v___x_1642_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4));
v___x_1643_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__1));
v___x_1644_ = ((lean_object*)(l_Lean_Elab_Term_expandLetExpr___closed__6));
v___x_1645_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1635_);
lean_ctor_set(v___x_1645_, 1, v___x_1644_);
v___x_1646_ = ((lean_object*)(l_Lean_Elab_Term_expandLetExpr___closed__7));
v___x_1647_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1635_);
lean_ctor_set(v___x_1647_, 1, v___x_1646_);
lean_inc_ref(v___x_1647_);
lean_inc_ref(v___x_1645_);
v___x_1648_ = l_Lean_Syntax_node4(v___x_1635_, v___x_1643_, v___x_1645_, v___x_1623_, v___x_1647_, v___x_1633_);
v___x_1649_ = l_Lean_Syntax_node1(v___x_1635_, v___x_1642_, v___x_1648_);
v___x_1650_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__4));
v___x_1651_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1));
v___x_1652_ = ((lean_object*)(l_Lean_Elab_Term_MatchExpr_getParams___closed__0));
v___x_1653_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1635_);
lean_ctor_set(v___x_1653_, 1, v___x_1652_);
v___x_1654_ = l_Lean_Syntax_node1(v___x_1635_, v___x_1651_, v___x_1653_);
v___x_1655_ = l_Lean_Syntax_node4(v___x_1635_, v___x_1650_, v___x_1645_, v___x_1654_, v___x_1647_, v___x_1631_);
v___x_1656_ = l_Lean_Syntax_node2(v___x_1635_, v___x_1641_, v___x_1649_, v___x_1655_);
v___x_1657_ = l_Lean_Syntax_node4(v___x_1635_, v___x_1636_, v___x_1638_, v___x_1629_, v___x_1640_, v___x_1656_);
v___x_1658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1657_);
lean_ctor_set(v___x_1658_, 1, v_a_1618_);
return v___x_1658_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandLetExpr___boxed(lean_object* v_stx_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_Lean_Elab_Term_expandLetExpr(v_stx_1659_, v_a_1660_, v_a_1661_);
lean_dec_ref(v_a_1660_);
return v_res_1662_;
}
}
lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1(){
_start:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1670_ = l_Lean_Elab_macroAttribute;
v___x_1671_ = ((lean_object*)(l_Lean_Elab_Term_expandLetExpr___closed__1));
v___x_1672_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1));
v___x_1673_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandLetExpr___boxed), 3, 0);
v___x_1674_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1670_, v___x_1671_, v___x_1672_, v___x_1673_);
return v___x_1674_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1675_;
v_res_1675_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1();
stack->m_obj
 = v_res_1675_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___boxed(lean_object* v_a_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1();
return v_res_1677_;
}
}
lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3(){
_start:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1704_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1));
v___x_1705_ = ((lean_object*)(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__6));
v___x_1706_ = l_Lean_addBuiltinDeclarationRanges(v___x_1704_, v___x_1705_);
return v___x_1706_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1707_;
v_res_1707_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3();
stack->m_obj
 = v_res_1707_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___boxed(lean_object* v_a_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3();
return v_res_1709_;
}
}
lean_object* runtime_initialize_Lean_Elab_Term(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_MatchExpr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
