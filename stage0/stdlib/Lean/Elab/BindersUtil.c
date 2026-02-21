// Lean compiler output
// Module: Lean.Elab.BindersUtil
// Imports: public import Lean.Parser.Term meta import Lean.Parser.Term meta import Lean.Parser.Do import Init.Syntax
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
uint8_t l_Lean_Name_isImplementationDetail(lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalDeclKind_ofBinderName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ofBinderName___boxed(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_mkHole(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandOptType(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandOptType___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getMatchAltsNumPatterns(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getMatchAltsNumPatterns___boxed(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__0;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__1_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__2_value;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlt(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_shouldExpandMatchAlt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Term_shouldExpandMatchAlt___closed__0 = (const lean_object*)&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__0_value;
static const lean_string_object l_Lean_Elab_Term_shouldExpandMatchAlt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Term_shouldExpandMatchAlt___closed__1 = (const lean_object*)&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__1_value;
static const lean_string_object l_Lean_Elab_Term_shouldExpandMatchAlt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_Term_shouldExpandMatchAlt___closed__2 = (const lean_object*)&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__2_value;
static const lean_string_object l_Lean_Elab_Term_shouldExpandMatchAlt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l_Lean_Elab_Term_shouldExpandMatchAlt___closed__3 = (const lean_object*)&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Term_shouldExpandMatchAlt___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_shouldExpandMatchAlt___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_shouldExpandMatchAlt___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_shouldExpandMatchAlt___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__3_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l_Lean_Elab_Term_shouldExpandMatchAlt___closed__4 = (const lean_object*)&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__4_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Term_shouldExpandMatchAlt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_shouldExpandMatchAlt___boxed(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_expandMatchAlts_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "match"};
static const lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___closed__0 = (const lean_object*)&l_Lean_Elab_Term_expandMatchAlts_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_expandMatchAlts_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 208, 235, 82, 91, 230, 203, 159)}};
static const lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1 = (const lean_object*)&l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1_value;
static const lean_string_object l_Lean_Elab_Term_expandMatchAlts_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___closed__2 = (const lean_object*)&l_Lean_Elab_Term_expandMatchAlts_x3f___closed__2_value;
static const lean_string_object l_Lean_Elab_Term_expandMatchAlts_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doMatch"};
static const lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___closed__3 = (const lean_object*)&l_Lean_Elab_Term_expandMatchAlts_x3f___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Term_expandMatchAlts_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_expandMatchAlts_x3f___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandMatchAlts_x3f___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_expandMatchAlts_x3f___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandMatchAlts_x3f___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_expandMatchAlts_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandMatchAlts_x3f___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Term_expandMatchAlts_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(29, 50, 175, 23, 122, 111, 148, 60)}};
static const lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___closed__4 = (const lean_object*)&l_Lean_Elab_Term_expandMatchAlts_x3f___closed__4_value;
static const lean_string_object l_Lean_Elab_Term_expandMatchAlts_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___closed__5 = (const lean_object*)&l_Lean_Elab_Term_expandMatchAlts_x3f___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Term_expandMatchAlts_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6 = (const lean_object*)&l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6_value;
lean_object* l_Array_mkArray0(lean_object*);
static lean_once_cell_t l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7;
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "clear"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 189, 43, 31, 203, 133, 30, 26)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "clear%"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__3_value;
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
static lean_once_cell_t l_Lean_Elab_Term_clearInMatchAlt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_clearInMatchAlt___closed__0;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Term_clearInMatchAlt___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_clearInMatchAlt___closed__1;
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatchAlt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatchAlt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_clearInMatch_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_clearInMatch_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatch(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalDeclKind_ofBinderName(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Name_isImplementationDetail(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ofBinderName___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_LocalDeclKind_ofBinderName(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandOptType(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Syntax_isNone(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Syntax_getArg(x_2, x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_Syntax_getArg(x_5, x_6);
lean_dec(x_5);
return x_7;
}
else
{
uint8_t x_8; lean_object* x_9; 
x_8 = 0;
x_9 = l_Lean_mkHole(x_1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandOptType___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_expandOptType(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getMatchAltsNumPatterns(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getArg(x_3, x_2);
lean_dec(x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_4, x_5);
lean_dec(x_4);
x_7 = l_Lean_Syntax_getArg(x_6, x_2);
lean_dec(x_6);
x_8 = l_Lean_Syntax_getSepArgs(x_7);
lean_dec(x_7);
x_9 = lean_array_get_size(x_8);
lean_dec_ref(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getMatchAltsNumPatterns___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_getMatchAltsNumPatterns(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_array_uget(x_4, x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_4, x_3, x_8);
x_10 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__0);
x_11 = lean_array_push(x_10, x_7);
x_12 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__2));
x_13 = lean_box(2);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_11);
lean_inc(x_1);
x_15 = l_Lean_Syntax_setArg(x_1, x_6, x_14);
x_16 = 1;
x_17 = lean_usize_add(x_3, x_16);
x_18 = lean_array_uset(x_9, x_3, x_15);
x_3 = x_17;
x_4 = x_18;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlt(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getSepArgs(x_3);
lean_dec(x_3);
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_le(x_5, x_2);
if (x_6 == 0)
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_array_size(x_4);
x_8 = 0;
x_9 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0(x_1, x_7, x_8, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_4);
x_10 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__0);
x_11 = lean_array_push(x_10, x_1);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = l_Lean_Syntax_getArgs(x_6);
lean_dec(x_6);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_8, x_2, x_9);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__1(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_unbox(x_12);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_5, 0);
lean_dec(x_15);
x_16 = lean_box(x_1);
lean_ctor_set(x_5, 0, x_16);
x_6 = x_5;
goto block_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_dec(x_5);
x_18 = lean_box(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_6 = x_19;
goto block_10;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_5);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_5, 1);
x_22 = lean_ctor_get(x_5, 0);
lean_dec(x_22);
x_23 = lean_array_uget_borrowed(x_2, x_3);
lean_inc(x_23);
x_24 = lean_array_push(x_21, x_23);
x_25 = lean_box(x_11);
lean_ctor_set(x_5, 1, x_24);
lean_ctor_set(x_5, 0, x_25);
x_6 = x_5;
goto block_10;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
lean_dec(x_5);
x_27 = lean_array_uget_borrowed(x_2, x_3);
lean_inc(x_27);
x_28 = lean_array_push(x_26, x_27);
x_29 = lean_box(x_11);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_6 = x_30;
goto block_10;
}
}
}
else
{
return x_5;
}
block_10:
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_3, x_7);
x_3 = x_8;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_unbox(x_1);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__1(x_6, x_2, x_7, x_8, x_5);
lean_dec_ref(x_2);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_shouldExpandMatchAlt(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = ((lean_object*)(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__4));
lean_inc(x_1);
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
if (x_3 == 0)
{
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_4 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_4);
lean_dec(x_1);
x_15 = l_Lean_Syntax_getArgs(x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_obj_once(&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5, &l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5_once, _init_l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5);
x_18 = lean_array_get_size(x_15);
x_19 = lean_nat_dec_lt(x_16, x_18);
if (x_19 == 0)
{
lean_dec_ref(x_15);
x_5 = x_17;
goto block_13;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_box(x_3);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
x_22 = lean_nat_dec_le(x_18, x_18);
if (x_22 == 0)
{
if (x_19 == 0)
{
lean_dec_ref(x_21);
lean_dec_ref(x_15);
x_5 = x_17;
goto block_13;
}
else
{
size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
x_23 = 0;
x_24 = lean_usize_of_nat(x_18);
x_25 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__1(x_3, x_15, x_23, x_24, x_21);
lean_dec_ref(x_15);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec_ref(x_25);
x_5 = x_26;
goto block_13;
}
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; 
x_27 = 0;
x_28 = lean_usize_of_nat(x_18);
x_29 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__1(x_3, x_15, x_27, x_28, x_21);
lean_dec_ref(x_15);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec_ref(x_29);
x_5 = x_30;
goto block_13;
}
}
block_13:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_array_size(x_5);
x_7 = 0;
x_8 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__0(x_6, x_7, x_5);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_array_get_size(x_10);
lean_dec(x_10);
x_12 = lean_nat_dec_lt(x_4, x_11);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_shouldExpandMatchAlt___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_shouldExpandMatchAlt(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_7 = lean_array_uget_borrowed(x_1, x_2);
lean_inc(x_7);
x_8 = l_Lean_Elab_Term_expandMatchAlt(x_7);
x_9 = l_Array_append___redArg(x_4, x_8);
lean_dec_ref(x_8);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
x_4 = x_9;
goto _start;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___redArg(x_1, x_6, x_7, x_4, x_5);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__0(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget_borrowed(x_1, x_2);
lean_inc(x_5);
x_6 = l_Lean_Elab_Term_shouldExpandMatchAlt(x_5);
if (x_6 == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
x_2 = x_8;
goto _start;
}
else
{
return x_6;
}
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__0(x_1, x_4, x_5);
lean_dec_ref(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_12; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_array_get_size(x_1);
x_22 = lean_nat_dec_lt(x_20, x_21);
if (x_22 == 0)
{
goto block_6;
}
else
{
if (x_22 == 0)
{
goto block_6;
}
else
{
size_t x_23; size_t x_24; uint8_t x_25; 
x_23 = 0;
x_24 = lean_usize_of_nat(x_21);
x_25 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__0(x_1, x_23, x_24);
if (x_25 == 0)
{
goto block_6;
}
else
{
lean_object* x_26; 
x_26 = lean_obj_once(&l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand___closed__0, &l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand___closed__0_once, _init_l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand___closed__0);
if (x_22 == 0)
{
x_7 = x_26;
x_8 = x_3;
goto block_11;
}
else
{
uint8_t x_27; 
x_27 = lean_nat_dec_le(x_21, x_21);
if (x_27 == 0)
{
if (x_22 == 0)
{
x_7 = x_26;
x_8 = x_3;
goto block_11;
}
else
{
lean_object* x_28; 
x_28 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___redArg(x_1, x_23, x_24, x_26, x_3);
x_12 = x_28;
goto block_19;
}
}
else
{
lean_object* x_29; 
x_29 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___redArg(x_1, x_23, x_24, x_26, x_3);
x_12 = x_29;
goto block_19;
}
}
}
}
}
block_6:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
block_19:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_7 = x_13;
x_8 = x_14;
goto block_11;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Array_mkArray0(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_29; 
x_4 = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__0));
x_5 = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1));
lean_inc(x_1);
x_29 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_55; 
x_30 = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__4));
lean_inc(x_1);
x_55 = l_Lean_Syntax_isOfKind(x_1, x_30);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_1);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_3);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_160; uint8_t x_161; 
x_58 = lean_unsigned_to_nat(0u);
x_132 = lean_unsigned_to_nat(1u);
x_160 = l_Lean_Syntax_getArg(x_1, x_132);
x_161 = l_Lean_Syntax_isNone(x_160);
if (x_161 == 0)
{
uint8_t x_162; 
lean_inc(x_160);
x_162 = l_Lean_Syntax_matchesNull(x_160, x_132);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; 
lean_dec(x_160);
lean_dec(x_1);
x_163 = lean_box(0);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_3);
return x_164;
}
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = l_Lean_Syntax_getArg(x_160, x_58);
lean_dec(x_160);
x_166 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_166, 0, x_165);
x_147 = x_166;
x_148 = x_2;
x_149 = x_3;
goto block_159;
}
}
else
{
lean_object* x_167; 
lean_dec(x_160);
x_167 = lean_box(0);
x_147 = x_167;
x_148 = x_2;
x_149 = x_3;
goto block_159;
}
block_75:
{
lean_object* x_70; lean_object* x_71; 
lean_inc_ref(x_66);
x_70 = l_Array_append___redArg(x_66, x_69);
lean_dec_ref(x_69);
lean_inc(x_68);
lean_inc(x_65);
x_71 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_71, 0, x_65);
lean_ctor_set(x_71, 1, x_68);
lean_ctor_set(x_71, 2, x_70);
if (lean_obj_tag(x_67) == 1)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_67, 0);
lean_inc(x_72);
lean_dec_ref(x_67);
x_73 = l_Array_mkArray1___redArg(x_72);
x_31 = x_59;
x_32 = x_61;
x_33 = x_71;
x_34 = x_60;
x_35 = x_62;
x_36 = x_63;
x_37 = x_64;
x_38 = x_65;
x_39 = x_66;
x_40 = x_68;
x_41 = x_73;
goto block_54;
}
else
{
lean_object* x_74; 
lean_dec(x_67);
x_74 = lean_obj_once(&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5, &l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5_once, _init_l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5);
x_31 = x_59;
x_32 = x_61;
x_33 = x_71;
x_34 = x_60;
x_35 = x_62;
x_36 = x_63;
x_37 = x_64;
x_38 = x_65;
x_39 = x_66;
x_40 = x_68;
x_41 = x_74;
goto block_54;
}
}
block_92:
{
lean_object* x_87; lean_object* x_88; 
lean_inc_ref(x_83);
x_87 = l_Array_append___redArg(x_83, x_86);
lean_dec_ref(x_86);
lean_inc(x_85);
lean_inc(x_82);
x_88 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_88, 0, x_82);
lean_ctor_set(x_88, 1, x_85);
lean_ctor_set(x_88, 2, x_87);
if (lean_obj_tag(x_81) == 1)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_81, 0);
lean_inc(x_89);
lean_dec_ref(x_81);
x_90 = l_Array_mkArray1___redArg(x_89);
x_59 = x_76;
x_60 = x_88;
x_61 = x_77;
x_62 = x_78;
x_63 = x_79;
x_64 = x_80;
x_65 = x_82;
x_66 = x_83;
x_67 = x_84;
x_68 = x_85;
x_69 = x_90;
goto block_75;
}
else
{
lean_object* x_91; 
lean_dec(x_81);
x_91 = lean_obj_once(&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5, &l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5_once, _init_l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5);
x_59 = x_76;
x_60 = x_88;
x_61 = x_77;
x_62 = x_78;
x_63 = x_79;
x_64 = x_80;
x_65 = x_82;
x_66 = x_83;
x_67 = x_84;
x_68 = x_85;
x_69 = x_91;
goto block_75;
}
}
block_131:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_98 = lean_unsigned_to_nat(6u);
x_99 = l_Lean_Syntax_getArg(x_1, x_98);
x_100 = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6));
lean_inc(x_99);
x_101 = l_Lean_Syntax_isOfKind(x_99, x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_99);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_1);
x_102 = lean_box(0);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_97);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = l_Lean_Syntax_getArg(x_99, x_58);
lean_dec(x_99);
x_105 = l_Lean_Syntax_getArgs(x_104);
lean_dec(x_104);
x_106 = l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand(x_105, x_96, x_97);
lean_dec_ref(x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
if (lean_obj_tag(x_107) == 0)
{
uint8_t x_108; 
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_106);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_106, 0);
lean_dec(x_109);
x_110 = lean_box(0);
lean_ctor_set(x_106, 0, x_110);
return x_106;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_106, 1);
lean_inc(x_111);
lean_dec(x_106);
x_112 = lean_box(0);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_114 = lean_ctor_get(x_106, 1);
lean_inc(x_114);
lean_dec_ref(x_106);
x_115 = lean_ctor_get(x_107, 0);
lean_inc(x_115);
lean_dec_ref(x_107);
x_116 = lean_ctor_get(x_96, 5);
x_117 = lean_unsigned_to_nat(4u);
x_118 = l_Lean_Syntax_getArg(x_1, x_117);
lean_dec(x_1);
x_119 = l_Lean_Syntax_getArgs(x_118);
lean_dec(x_118);
x_120 = l_Lean_SourceInfo_fromRef(x_116, x_29);
lean_inc(x_120);
x_121 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_4);
x_122 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__2));
x_123 = lean_obj_once(&l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7, &l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7_once, _init_l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7);
if (lean_obj_tag(x_93) == 1)
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_93, 0);
lean_inc(x_124);
lean_dec_ref(x_93);
x_125 = l_Array_mkArray1___redArg(x_124);
x_76 = x_100;
x_77 = x_114;
x_78 = x_121;
x_79 = x_119;
x_80 = x_115;
x_81 = x_94;
x_82 = x_120;
x_83 = x_123;
x_84 = x_95;
x_85 = x_122;
x_86 = x_125;
goto block_92;
}
else
{
lean_object* x_126; 
lean_dec(x_93);
x_126 = lean_obj_once(&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5, &l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5_once, _init_l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5);
x_76 = x_100;
x_77 = x_114;
x_78 = x_121;
x_79 = x_119;
x_80 = x_115;
x_81 = x_94;
x_82 = x_120;
x_83 = x_123;
x_84 = x_95;
x_85 = x_122;
x_86 = x_126;
goto block_92;
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_1);
x_127 = !lean_is_exclusive(x_106);
if (x_127 == 0)
{
return x_106;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_106, 0);
x_129 = lean_ctor_get(x_106, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_106);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
}
block_146:
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_137 = lean_unsigned_to_nat(3u);
x_138 = l_Lean_Syntax_getArg(x_1, x_137);
x_139 = l_Lean_Syntax_isNone(x_138);
if (x_139 == 0)
{
uint8_t x_140; 
lean_inc(x_138);
x_140 = l_Lean_Syntax_matchesNull(x_138, x_132);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_138);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_1);
x_141 = lean_box(0);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_136);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = l_Lean_Syntax_getArg(x_138, x_58);
lean_dec(x_138);
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_143);
x_93 = x_133;
x_94 = x_134;
x_95 = x_144;
x_96 = x_135;
x_97 = x_136;
goto block_131;
}
}
else
{
lean_object* x_145; 
lean_dec(x_138);
x_145 = lean_box(0);
x_93 = x_133;
x_94 = x_134;
x_95 = x_145;
x_96 = x_135;
x_97 = x_136;
goto block_131;
}
}
block_159:
{
lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_150 = lean_unsigned_to_nat(2u);
x_151 = l_Lean_Syntax_getArg(x_1, x_150);
x_152 = l_Lean_Syntax_isNone(x_151);
if (x_152 == 0)
{
uint8_t x_153; 
lean_inc(x_151);
x_153 = l_Lean_Syntax_matchesNull(x_151, x_132);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_151);
lean_dec(x_147);
lean_dec(x_1);
x_154 = lean_box(0);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_149);
return x_155;
}
else
{
lean_object* x_156; lean_object* x_157; 
x_156 = l_Lean_Syntax_getArg(x_151, x_58);
lean_dec(x_151);
x_157 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_157, 0, x_156);
x_133 = x_147;
x_134 = x_157;
x_135 = x_148;
x_136 = x_149;
goto block_146;
}
}
else
{
lean_object* x_158; 
lean_dec(x_151);
x_158 = lean_box(0);
x_133 = x_147;
x_134 = x_158;
x_135 = x_148;
x_136 = x_149;
goto block_146;
}
}
}
block_54:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_inc_ref(x_39);
x_42 = l_Array_append___redArg(x_39, x_41);
lean_dec_ref(x_41);
lean_inc(x_40);
lean_inc(x_38);
x_43 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_40);
lean_ctor_set(x_43, 2, x_42);
lean_inc_ref(x_39);
x_44 = l_Array_append___redArg(x_39, x_36);
lean_dec_ref(x_36);
lean_inc(x_40);
lean_inc(x_38);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_40);
lean_ctor_set(x_45, 2, x_44);
x_46 = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__2));
lean_inc(x_38);
x_47 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_47, 0, x_38);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Array_append___redArg(x_39, x_37);
lean_dec_ref(x_37);
lean_inc(x_38);
x_49 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_49, 0, x_38);
lean_ctor_set(x_49, 1, x_40);
lean_ctor_set(x_49, 2, x_48);
lean_inc(x_38);
x_50 = l_Lean_Syntax_node1(x_38, x_31, x_49);
x_51 = l_Lean_Syntax_node7(x_38, x_30, x_35, x_34, x_33, x_43, x_45, x_47, x_50);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_32);
return x_53;
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_238; uint8_t x_239; 
x_168 = lean_unsigned_to_nat(0u);
x_224 = lean_unsigned_to_nat(1u);
x_238 = l_Lean_Syntax_getArg(x_1, x_224);
x_239 = l_Lean_Syntax_isNone(x_238);
if (x_239 == 0)
{
uint8_t x_240; 
lean_inc(x_238);
x_240 = l_Lean_Syntax_matchesNull(x_238, x_224);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; 
lean_dec(x_238);
lean_dec(x_1);
x_241 = lean_box(0);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_3);
return x_242;
}
else
{
lean_object* x_243; lean_object* x_244; 
x_243 = l_Lean_Syntax_getArg(x_238, x_168);
lean_dec(x_238);
x_244 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_244, 0, x_243);
x_225 = x_244;
x_226 = x_2;
x_227 = x_3;
goto block_237;
}
}
else
{
lean_object* x_245; 
lean_dec(x_238);
x_245 = lean_box(0);
x_225 = x_245;
x_226 = x_2;
x_227 = x_3;
goto block_237;
}
block_184:
{
lean_object* x_179; lean_object* x_180; 
lean_inc_ref(x_169);
x_179 = l_Array_append___redArg(x_169, x_178);
lean_dec_ref(x_178);
lean_inc(x_176);
lean_inc(x_173);
x_180 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_180, 0, x_173);
lean_ctor_set(x_180, 1, x_176);
lean_ctor_set(x_180, 2, x_179);
if (lean_obj_tag(x_171) == 1)
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_171, 0);
lean_inc(x_181);
lean_dec_ref(x_171);
x_182 = l_Array_mkArray1___redArg(x_181);
x_6 = x_169;
x_7 = x_170;
x_8 = x_172;
x_9 = x_173;
x_10 = x_174;
x_11 = x_175;
x_12 = x_180;
x_13 = x_176;
x_14 = x_177;
x_15 = x_182;
goto block_28;
}
else
{
lean_object* x_183; 
lean_dec(x_171);
x_183 = lean_obj_once(&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5, &l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5_once, _init_l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5);
x_6 = x_169;
x_7 = x_170;
x_8 = x_172;
x_9 = x_173;
x_10 = x_174;
x_11 = x_175;
x_12 = x_180;
x_13 = x_176;
x_14 = x_177;
x_15 = x_183;
goto block_28;
}
}
block_223:
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; 
x_189 = lean_unsigned_to_nat(5u);
x_190 = l_Lean_Syntax_getArg(x_1, x_189);
x_191 = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6));
lean_inc(x_190);
x_192 = l_Lean_Syntax_isOfKind(x_190, x_191);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; 
lean_dec(x_190);
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_1);
x_193 = lean_box(0);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_188);
return x_194;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = l_Lean_Syntax_getArg(x_190, x_168);
lean_dec(x_190);
x_196 = l_Lean_Syntax_getArgs(x_195);
lean_dec(x_195);
x_197 = l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand(x_196, x_187, x_188);
lean_dec_ref(x_196);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; 
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
if (lean_obj_tag(x_198) == 0)
{
uint8_t x_199; 
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_1);
x_199 = !lean_is_exclusive(x_197);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; 
x_200 = lean_ctor_get(x_197, 0);
lean_dec(x_200);
x_201 = lean_box(0);
lean_ctor_set(x_197, 0, x_201);
return x_197;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_197, 1);
lean_inc(x_202);
lean_dec(x_197);
x_203 = lean_box(0);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_202);
return x_204;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_205 = lean_ctor_get(x_197, 1);
lean_inc(x_205);
lean_dec_ref(x_197);
x_206 = lean_ctor_get(x_198, 0);
lean_inc(x_206);
lean_dec_ref(x_198);
x_207 = lean_ctor_get(x_187, 5);
x_208 = lean_unsigned_to_nat(3u);
x_209 = l_Lean_Syntax_getArg(x_1, x_208);
lean_dec(x_1);
x_210 = l_Lean_Syntax_getArgs(x_209);
lean_dec(x_209);
x_211 = 0;
x_212 = l_Lean_SourceInfo_fromRef(x_207, x_211);
lean_inc(x_212);
x_213 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_4);
x_214 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__2));
x_215 = lean_obj_once(&l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7, &l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7_once, _init_l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7);
if (lean_obj_tag(x_185) == 1)
{
lean_object* x_216; lean_object* x_217; 
x_216 = lean_ctor_get(x_185, 0);
lean_inc(x_216);
lean_dec_ref(x_185);
x_217 = l_Array_mkArray1___redArg(x_216);
x_169 = x_215;
x_170 = x_191;
x_171 = x_186;
x_172 = x_213;
x_173 = x_212;
x_174 = x_210;
x_175 = x_206;
x_176 = x_214;
x_177 = x_205;
x_178 = x_217;
goto block_184;
}
else
{
lean_object* x_218; 
lean_dec(x_185);
x_218 = lean_obj_once(&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5, &l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5_once, _init_l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5);
x_169 = x_215;
x_170 = x_191;
x_171 = x_186;
x_172 = x_213;
x_173 = x_212;
x_174 = x_210;
x_175 = x_206;
x_176 = x_214;
x_177 = x_205;
x_178 = x_218;
goto block_184;
}
}
}
else
{
uint8_t x_219; 
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_1);
x_219 = !lean_is_exclusive(x_197);
if (x_219 == 0)
{
return x_197;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_197, 0);
x_221 = lean_ctor_get(x_197, 1);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_197);
x_222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
return x_222;
}
}
}
}
block_237:
{
lean_object* x_228; lean_object* x_229; uint8_t x_230; 
x_228 = lean_unsigned_to_nat(2u);
x_229 = l_Lean_Syntax_getArg(x_1, x_228);
x_230 = l_Lean_Syntax_isNone(x_229);
if (x_230 == 0)
{
uint8_t x_231; 
lean_inc(x_229);
x_231 = l_Lean_Syntax_matchesNull(x_229, x_224);
if (x_231 == 0)
{
lean_object* x_232; lean_object* x_233; 
lean_dec(x_229);
lean_dec(x_225);
lean_dec(x_1);
x_232 = lean_box(0);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_227);
return x_233;
}
else
{
lean_object* x_234; lean_object* x_235; 
x_234 = l_Lean_Syntax_getArg(x_229, x_168);
lean_dec(x_229);
x_235 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_235, 0, x_234);
x_185 = x_225;
x_186 = x_235;
x_187 = x_226;
x_188 = x_227;
goto block_223;
}
}
else
{
lean_object* x_236; 
lean_dec(x_229);
x_236 = lean_box(0);
x_185 = x_225;
x_186 = x_236;
x_187 = x_226;
x_188 = x_227;
goto block_223;
}
}
}
block_28:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_inc_ref(x_6);
x_16 = l_Array_append___redArg(x_6, x_15);
lean_dec_ref(x_15);
lean_inc(x_13);
lean_inc(x_9);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_17, 2, x_16);
lean_inc_ref(x_6);
x_18 = l_Array_append___redArg(x_6, x_10);
lean_dec_ref(x_10);
lean_inc(x_13);
lean_inc(x_9);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__2));
lean_inc(x_9);
x_21 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_21, 0, x_9);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Array_append___redArg(x_6, x_11);
lean_dec_ref(x_11);
lean_inc(x_9);
x_23 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_23, 0, x_9);
lean_ctor_set(x_23, 1, x_13);
lean_ctor_set(x_23, 2, x_22);
lean_inc(x_9);
x_24 = l_Lean_Syntax_node1(x_9, x_7, x_23);
x_25 = l_Lean_Syntax_node6(x_9, x_5, x_8, x_12, x_17, x_19, x_21, x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_14);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandMatchAlts_x3f(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_3, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_array_uget_borrowed(x_1, x_3);
x_11 = 0;
x_12 = l_Lean_SourceInfo_fromRef(x_9, x_11);
x_13 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__1));
x_14 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__2));
lean_inc(x_12);
x_15 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__3));
lean_inc(x_12);
x_17 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_16);
lean_inc(x_10);
x_18 = l_Lean_Syntax_node4(x_12, x_13, x_15, x_10, x_17, x_4);
x_19 = 1;
x_20 = lean_usize_add(x_3, x_19);
x_3 = x_20;
x_4 = x_18;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_Term_clearInMatchAlt___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_firstFrontendMacroScope;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_clearInMatchAlt___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Lean_firstFrontendMacroScope;
x_3 = lean_nat_add(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatchAlt(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_unsigned_to_nat(3u);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_6, x_7);
if (x_8 == 0)
{
return x_1;
}
else
{
uint8_t x_9; 
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_10 = lean_ctor_get(x_1, 2);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_1, 0);
lean_dec(x_12);
x_13 = lean_array_fget_borrowed(x_5, x_6);
x_14 = lean_array_size(x_2);
x_15 = 0;
x_16 = lean_obj_once(&l_Lean_Elab_Term_clearInMatchAlt___closed__0, &l_Lean_Elab_Term_clearInMatchAlt___closed__0_once, _init_l_Lean_Elab_Term_clearInMatchAlt___closed__0);
x_17 = lean_obj_once(&l_Lean_Elab_Term_clearInMatchAlt___closed__1, &l_Lean_Elab_Term_clearInMatchAlt___closed__1_once, _init_l_Lean_Elab_Term_clearInMatchAlt___closed__1);
lean_inc(x_13);
x_18 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0(x_2, x_14, x_15, x_13, x_16, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_box(0);
x_21 = lean_array_fset(x_5, x_6, x_20);
x_22 = lean_array_fset(x_21, x_6, x_19);
lean_ctor_set(x_1, 2, x_22);
return x_1;
}
else
{
lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_1);
x_23 = lean_array_fget_borrowed(x_5, x_6);
x_24 = lean_array_size(x_2);
x_25 = 0;
x_26 = lean_obj_once(&l_Lean_Elab_Term_clearInMatchAlt___closed__0, &l_Lean_Elab_Term_clearInMatchAlt___closed__0_once, _init_l_Lean_Elab_Term_clearInMatchAlt___closed__0);
x_27 = lean_obj_once(&l_Lean_Elab_Term_clearInMatchAlt___closed__1, &l_Lean_Elab_Term_clearInMatchAlt___closed__1_once, _init_l_Lean_Elab_Term_clearInMatchAlt___closed__1);
lean_inc(x_23);
x_28 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0(x_2, x_24, x_25, x_23, x_26, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_box(0);
x_31 = lean_array_fset(x_5, x_6, x_30);
x_32 = lean_array_fset(x_31, x_6, x_29);
x_33 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_33, 0, x_3);
lean_ctor_set(x_33, 1, x_4);
lean_ctor_set(x_33, 2, x_32);
return x_33;
}
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatchAlt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_clearInMatchAlt(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_clearInMatch_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = l_Lean_Elab_Term_clearInMatchAlt(x_6, x_1);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_11;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_clearInMatch_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_clearInMatch_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Array_isEmpty___redArg(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_30; 
x_6 = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__0));
x_7 = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1));
lean_inc(x_1);
x_30 = l_Lean_Syntax_isOfKind(x_1, x_7);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_4);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_88; uint8_t x_89; 
x_32 = lean_unsigned_to_nat(0u);
x_75 = lean_unsigned_to_nat(1u);
x_88 = l_Lean_Syntax_getArg(x_1, x_75);
x_89 = l_Lean_Syntax_isNone(x_88);
if (x_89 == 0)
{
uint8_t x_90; 
lean_inc(x_88);
x_90 = l_Lean_Syntax_matchesNull(x_88, x_75);
if (x_90 == 0)
{
lean_object* x_91; 
lean_dec(x_88);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_1);
lean_ctor_set(x_91, 1, x_4);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = l_Lean_Syntax_getArg(x_88, x_32);
lean_dec(x_88);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
x_76 = x_93;
x_77 = x_3;
x_78 = x_4;
goto block_87;
}
}
else
{
lean_object* x_94; 
lean_dec(x_88);
x_94 = lean_box(0);
x_76 = x_94;
x_77 = x_3;
x_78 = x_4;
goto block_87;
}
block_48:
{
lean_object* x_43; lean_object* x_44; 
lean_inc_ref(x_40);
x_43 = l_Array_append___redArg(x_40, x_42);
lean_dec_ref(x_42);
lean_inc(x_33);
lean_inc(x_38);
x_44 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_33);
lean_ctor_set(x_44, 2, x_43);
if (lean_obj_tag(x_37) == 1)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_37, 0);
lean_inc(x_45);
lean_dec_ref(x_37);
x_46 = l_Array_mkArray1___redArg(x_45);
x_8 = x_44;
x_9 = x_33;
x_10 = x_34;
x_11 = x_35;
x_12 = x_36;
x_13 = x_38;
x_14 = x_39;
x_15 = x_40;
x_16 = x_41;
x_17 = x_46;
goto block_29;
}
else
{
lean_object* x_47; 
lean_dec(x_37);
x_47 = lean_obj_once(&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5, &l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5_once, _init_l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5);
x_8 = x_44;
x_9 = x_33;
x_10 = x_34;
x_11 = x_35;
x_12 = x_36;
x_13 = x_38;
x_14 = x_39;
x_15 = x_40;
x_16 = x_41;
x_17 = x_47;
goto block_29;
}
}
block_74:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_unsigned_to_nat(5u);
x_54 = l_Lean_Syntax_getArg(x_1, x_53);
x_55 = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6));
lean_inc(x_54);
x_56 = l_Lean_Syntax_isOfKind(x_54, x_55);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_54);
lean_dec(x_50);
lean_dec(x_49);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_52);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; size_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; size_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_58 = lean_ctor_get(x_51, 5);
x_59 = l_Lean_Syntax_getArg(x_54, x_32);
lean_dec(x_54);
x_60 = l_Lean_Syntax_getArgs(x_59);
lean_dec(x_59);
x_61 = lean_array_size(x_60);
x_62 = lean_unsigned_to_nat(3u);
x_63 = l_Lean_Syntax_getArg(x_1, x_62);
lean_dec(x_1);
x_64 = l_Lean_Syntax_getArgs(x_63);
lean_dec(x_63);
x_65 = 0;
x_66 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_clearInMatch_spec__0(x_2, x_61, x_65, x_60);
x_67 = l_Lean_SourceInfo_fromRef(x_58, x_5);
lean_inc(x_67);
x_68 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_6);
x_69 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__2));
x_70 = lean_obj_once(&l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7, &l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7_once, _init_l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7);
if (lean_obj_tag(x_49) == 1)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_49, 0);
lean_inc(x_71);
lean_dec_ref(x_49);
x_72 = l_Array_mkArray1___redArg(x_71);
x_33 = x_69;
x_34 = x_66;
x_35 = x_64;
x_36 = x_68;
x_37 = x_50;
x_38 = x_67;
x_39 = x_52;
x_40 = x_70;
x_41 = x_55;
x_42 = x_72;
goto block_48;
}
else
{
lean_object* x_73; 
lean_dec(x_49);
x_73 = lean_obj_once(&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5, &l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5_once, _init_l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5);
x_33 = x_69;
x_34 = x_66;
x_35 = x_64;
x_36 = x_68;
x_37 = x_50;
x_38 = x_67;
x_39 = x_52;
x_40 = x_70;
x_41 = x_55;
x_42 = x_73;
goto block_48;
}
}
}
block_87:
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = lean_unsigned_to_nat(2u);
x_80 = l_Lean_Syntax_getArg(x_1, x_79);
x_81 = l_Lean_Syntax_isNone(x_80);
if (x_81 == 0)
{
uint8_t x_82; 
lean_inc(x_80);
x_82 = l_Lean_Syntax_matchesNull(x_80, x_75);
if (x_82 == 0)
{
lean_object* x_83; 
lean_dec(x_80);
lean_dec(x_76);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_1);
lean_ctor_set(x_83, 1, x_78);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = l_Lean_Syntax_getArg(x_80, x_32);
lean_dec(x_80);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_49 = x_76;
x_50 = x_85;
x_51 = x_77;
x_52 = x_78;
goto block_74;
}
}
else
{
lean_object* x_86; 
lean_dec(x_80);
x_86 = lean_box(0);
x_49 = x_76;
x_50 = x_86;
x_51 = x_77;
x_52 = x_78;
goto block_74;
}
}
}
block_29:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_inc_ref(x_15);
x_18 = l_Array_append___redArg(x_15, x_17);
lean_dec_ref(x_17);
lean_inc(x_9);
lean_inc(x_13);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_9);
lean_ctor_set(x_19, 2, x_18);
lean_inc_ref(x_15);
x_20 = l_Array_append___redArg(x_15, x_11);
lean_dec_ref(x_11);
lean_inc(x_9);
lean_inc(x_13);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_9);
lean_ctor_set(x_21, 2, x_20);
x_22 = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__2));
lean_inc(x_13);
x_23 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_23, 0, x_13);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Array_append___redArg(x_15, x_10);
lean_dec_ref(x_10);
lean_inc(x_13);
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set(x_25, 1, x_9);
lean_ctor_set(x_25, 2, x_24);
lean_inc(x_13);
x_26 = l_Lean_Syntax_node1(x_13, x_16, x_25);
x_27 = l_Lean_Syntax_node6(x_13, x_7, x_12, x_8, x_19, x_21, x_23, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_14);
return x_28;
}
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_1);
lean_ctor_set(x_95, 1, x_4);
return x_95;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatch___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_clearInMatch(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
lean_object* initialize_Lean_Parser_Term(uint8_t builtin);
lean_object* initialize_Lean_Parser_Term(uint8_t builtin);
lean_object* initialize_Lean_Parser_Do(uint8_t builtin);
lean_object* initialize_Init_Syntax(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_BindersUtil(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
