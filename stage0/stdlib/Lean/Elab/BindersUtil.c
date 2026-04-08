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
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_mkHole(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray0(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalDeclKind_ofBinderName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ofBinderName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandOptType(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandOptType___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getMatchAltsNumPatterns(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getMatchAltsNumPatterns___boxed(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlt(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_shouldExpandMatchAlt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Term_shouldExpandMatchAlt___closed__0 = (const lean_object*)&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__0_value;
static const lean_string_object l_Lean_Elab_Term_shouldExpandMatchAlt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Term_shouldExpandMatchAlt___closed__1 = (const lean_object*)&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__1_value;
static const lean_string_object l_Lean_Elab_Term_shouldExpandMatchAlt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_Term_shouldExpandMatchAlt___closed__2 = (const lean_object*)&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__2_value;
static const lean_string_object l_Lean_Elab_Term_shouldExpandMatchAlt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l_Lean_Elab_Term_shouldExpandMatchAlt___closed__3 = (const lean_object*)&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Term_shouldExpandMatchAlt___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_shouldExpandMatchAlt___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_shouldExpandMatchAlt___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_shouldExpandMatchAlt___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__3_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l_Lean_Elab_Term_shouldExpandMatchAlt___closed__4 = (const lean_object*)&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__4_value;
static const lean_array_object l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5 = (const lean_object*)&l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5_value;
LEAN_EXPORT uint8_t l_Lean_Elab_Term_shouldExpandMatchAlt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_shouldExpandMatchAlt___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand___closed__0 = (const lean_object*)&l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand___closed__0_value;
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
static lean_once_cell_t l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Term_clearInMatchAlt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_clearInMatchAlt___closed__0;
static lean_once_cell_t l_Lean_Elab_Term_clearInMatchAlt___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_clearInMatchAlt___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatchAlt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatchAlt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_clearInMatch_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_clearInMatch_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatch(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalDeclKind_ofBinderName(lean_object* v_binderName_1_){
_start:
{
uint8_t v___x_2_; 
v___x_2_ = l_Lean_Name_isImplementationDetail(v_binderName_1_);
if (v___x_2_ == 0)
{
uint8_t v___x_3_; 
v___x_3_ = 0;
return v___x_3_;
}
else
{
uint8_t v___x_4_; 
v___x_4_ = 1;
return v___x_4_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ofBinderName___boxed(lean_object* v_binderName_5_){
_start:
{
uint8_t v_res_6_; lean_object* v_r_7_; 
v_res_6_ = l_Lean_LocalDeclKind_ofBinderName(v_binderName_5_);
lean_dec(v_binderName_5_);
v_r_7_ = lean_box(v_res_6_);
return v_r_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandOptType(lean_object* v_ref_8_, lean_object* v_optType_9_){
_start:
{
uint8_t v___x_10_; 
v___x_10_ = l_Lean_Syntax_isNone(v_optType_9_);
if (v___x_10_ == 0)
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_11_ = lean_unsigned_to_nat(0u);
v___x_12_ = l_Lean_Syntax_getArg(v_optType_9_, v___x_11_);
v___x_13_ = lean_unsigned_to_nat(1u);
v___x_14_ = l_Lean_Syntax_getArg(v___x_12_, v___x_13_);
lean_dec(v___x_12_);
return v___x_14_;
}
else
{
uint8_t v___x_15_; lean_object* v___x_16_; 
v___x_15_ = 0;
v___x_16_ = l_Lean_mkHole(v_ref_8_, v___x_15_);
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandOptType___boxed(lean_object* v_ref_17_, lean_object* v_optType_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Lean_Elab_Term_expandOptType(v_ref_17_, v_optType_18_);
lean_dec(v_optType_18_);
lean_dec(v_ref_17_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getMatchAltsNumPatterns(lean_object* v_matchAlts_20_){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v_alt0_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v_pats_27_; lean_object* v___x_28_; 
v___x_21_ = lean_unsigned_to_nat(0u);
v___x_22_ = l_Lean_Syntax_getArg(v_matchAlts_20_, v___x_21_);
v_alt0_23_ = l_Lean_Syntax_getArg(v___x_22_, v___x_21_);
lean_dec(v___x_22_);
v___x_24_ = lean_unsigned_to_nat(1u);
v___x_25_ = l_Lean_Syntax_getArg(v_alt0_23_, v___x_24_);
lean_dec(v_alt0_23_);
v___x_26_ = l_Lean_Syntax_getArg(v___x_25_, v___x_21_);
lean_dec(v___x_25_);
v_pats_27_ = l_Lean_Syntax_getSepArgs(v___x_26_);
lean_dec(v___x_26_);
v___x_28_ = lean_array_get_size(v_pats_27_);
lean_dec_ref(v_pats_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getMatchAltsNumPatterns___boxed(lean_object* v_matchAlts_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Elab_Term_getMatchAltsNumPatterns(v_matchAlts_29_);
lean_dec(v_matchAlts_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0(lean_object* v___x_34_, size_t v_sz_35_, size_t v_i_36_, lean_object* v_bs_37_){
_start:
{
uint8_t v___x_38_; 
v___x_38_ = lean_usize_dec_lt(v_i_36_, v_sz_35_);
if (v___x_38_ == 0)
{
lean_dec(v___x_34_);
return v_bs_37_;
}
else
{
lean_object* v___x_39_; lean_object* v_v_40_; lean_object* v___x_41_; lean_object* v_bs_x27_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; size_t v___x_49_; size_t v___x_50_; lean_object* v___x_51_; 
v___x_39_ = lean_unsigned_to_nat(1u);
v_v_40_ = lean_array_uget(v_bs_37_, v_i_36_);
v___x_41_ = lean_unsigned_to_nat(0u);
v_bs_x27_42_ = lean_array_uset(v_bs_37_, v_i_36_, v___x_41_);
v___x_43_ = lean_mk_empty_array_with_capacity(v___x_39_);
v___x_44_ = lean_array_push(v___x_43_, v_v_40_);
v___x_45_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__1));
v___x_46_ = lean_box(2);
v___x_47_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
lean_ctor_set(v___x_47_, 1, v___x_45_);
lean_ctor_set(v___x_47_, 2, v___x_44_);
lean_inc(v___x_34_);
v___x_48_ = l_Lean_Syntax_setArg(v___x_34_, v___x_39_, v___x_47_);
v___x_49_ = ((size_t)1ULL);
v___x_50_ = lean_usize_add(v_i_36_, v___x_49_);
v___x_51_ = lean_array_uset(v_bs_x27_42_, v_i_36_, v___x_48_);
v_i_36_ = v___x_50_;
v_bs_37_ = v___x_51_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___boxed(lean_object* v___x_53_, lean_object* v_sz_54_, lean_object* v_i_55_, lean_object* v_bs_56_){
_start:
{
size_t v_sz_boxed_57_; size_t v_i_boxed_58_; lean_object* v_res_59_; 
v_sz_boxed_57_ = lean_unbox_usize(v_sz_54_);
lean_dec(v_sz_54_);
v_i_boxed_58_ = lean_unbox_usize(v_i_55_);
lean_dec(v_i_55_);
v_res_59_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0(v___x_53_, v_sz_boxed_57_, v_i_boxed_58_, v_bs_56_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlt(lean_object* v_stx_60_){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v_patss_63_; lean_object* v___x_64_; uint8_t v___x_65_; 
v___x_61_ = lean_unsigned_to_nat(1u);
v___x_62_ = l_Lean_Syntax_getArg(v_stx_60_, v___x_61_);
v_patss_63_ = l_Lean_Syntax_getSepArgs(v___x_62_);
lean_dec(v___x_62_);
v___x_64_ = lean_array_get_size(v_patss_63_);
v___x_65_ = lean_nat_dec_le(v___x_64_, v___x_61_);
if (v___x_65_ == 0)
{
size_t v_sz_66_; size_t v___x_67_; lean_object* v___x_68_; 
v_sz_66_ = lean_array_size(v_patss_63_);
v___x_67_ = ((size_t)0ULL);
v___x_68_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0(v_stx_60_, v_sz_66_, v___x_67_, v_patss_63_);
return v___x_68_;
}
else
{
lean_object* v___x_69_; lean_object* v___x_70_; 
lean_dec_ref(v_patss_63_);
v___x_69_ = lean_mk_empty_array_with_capacity(v___x_61_);
v___x_70_ = lean_array_push(v___x_69_, v_stx_60_);
return v___x_70_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__0(size_t v_sz_71_, size_t v_i_72_, lean_object* v_bs_73_){
_start:
{
uint8_t v___x_74_; 
v___x_74_ = lean_usize_dec_lt(v_i_72_, v_sz_71_);
if (v___x_74_ == 0)
{
lean_object* v___x_75_; 
v___x_75_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_75_, 0, v_bs_73_);
return v___x_75_;
}
else
{
lean_object* v_v_76_; lean_object* v___x_77_; lean_object* v_bs_x27_78_; lean_object* v_patss_79_; size_t v___x_80_; size_t v___x_81_; lean_object* v___x_82_; 
v_v_76_ = lean_array_uget(v_bs_73_, v_i_72_);
v___x_77_ = lean_unsigned_to_nat(0u);
v_bs_x27_78_ = lean_array_uset(v_bs_73_, v_i_72_, v___x_77_);
v_patss_79_ = l_Lean_Syntax_getArgs(v_v_76_);
lean_dec(v_v_76_);
v___x_80_ = ((size_t)1ULL);
v___x_81_ = lean_usize_add(v_i_72_, v___x_80_);
v___x_82_ = lean_array_uset(v_bs_x27_78_, v_i_72_, v_patss_79_);
v_i_72_ = v___x_81_;
v_bs_73_ = v___x_82_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__0___boxed(lean_object* v_sz_84_, lean_object* v_i_85_, lean_object* v_bs_86_){
_start:
{
size_t v_sz_boxed_87_; size_t v_i_boxed_88_; lean_object* v_res_89_; 
v_sz_boxed_87_ = lean_unbox_usize(v_sz_84_);
lean_dec(v_sz_84_);
v_i_boxed_88_ = lean_unbox_usize(v_i_85_);
lean_dec(v_i_85_);
v_res_89_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__0(v_sz_boxed_87_, v_i_boxed_88_, v_bs_86_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__1(uint8_t v___x_90_, lean_object* v_as_91_, size_t v_i_92_, size_t v_stop_93_, lean_object* v_b_94_){
_start:
{
lean_object* v___y_96_; uint8_t v___x_100_; 
v___x_100_ = lean_usize_dec_eq(v_i_92_, v_stop_93_);
if (v___x_100_ == 0)
{
lean_object* v_fst_101_; uint8_t v___x_102_; 
v_fst_101_ = lean_ctor_get(v_b_94_, 0);
v___x_102_ = lean_unbox(v_fst_101_);
if (v___x_102_ == 0)
{
lean_object* v_snd_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_111_; 
v_snd_103_ = lean_ctor_get(v_b_94_, 1);
v_isSharedCheck_111_ = !lean_is_exclusive(v_b_94_);
if (v_isSharedCheck_111_ == 0)
{
lean_object* v_unused_112_; 
v_unused_112_ = lean_ctor_get(v_b_94_, 0);
lean_dec(v_unused_112_);
v___x_105_ = v_b_94_;
v_isShared_106_ = v_isSharedCheck_111_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_snd_103_);
lean_dec(v_b_94_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_111_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_107_; lean_object* v___x_109_; 
v___x_107_ = lean_box(v___x_90_);
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 0, v___x_107_);
v___x_109_ = v___x_105_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v___x_107_);
lean_ctor_set(v_reuseFailAlloc_110_, 1, v_snd_103_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
v___y_96_ = v___x_109_;
goto v___jp_95_;
}
}
}
else
{
lean_object* v_snd_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_123_; 
v_snd_113_ = lean_ctor_get(v_b_94_, 1);
v_isSharedCheck_123_ = !lean_is_exclusive(v_b_94_);
if (v_isSharedCheck_123_ == 0)
{
lean_object* v_unused_124_; 
v_unused_124_ = lean_ctor_get(v_b_94_, 0);
lean_dec(v_unused_124_);
v___x_115_ = v_b_94_;
v_isShared_116_ = v_isSharedCheck_123_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_snd_113_);
lean_dec(v_b_94_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_123_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_121_; 
v___x_117_ = lean_array_uget_borrowed(v_as_91_, v_i_92_);
lean_inc(v___x_117_);
v___x_118_ = lean_array_push(v_snd_113_, v___x_117_);
v___x_119_ = lean_box(v___x_100_);
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 1, v___x_118_);
lean_ctor_set(v___x_115_, 0, v___x_119_);
v___x_121_ = v___x_115_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v___x_119_);
lean_ctor_set(v_reuseFailAlloc_122_, 1, v___x_118_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
v___y_96_ = v___x_121_;
goto v___jp_95_;
}
}
}
}
else
{
return v_b_94_;
}
v___jp_95_:
{
size_t v___x_97_; size_t v___x_98_; 
v___x_97_ = ((size_t)1ULL);
v___x_98_ = lean_usize_add(v_i_92_, v___x_97_);
v_i_92_ = v___x_98_;
v_b_94_ = v___y_96_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__1___boxed(lean_object* v___x_125_, lean_object* v_as_126_, lean_object* v_i_127_, lean_object* v_stop_128_, lean_object* v_b_129_){
_start:
{
uint8_t v___x_530__boxed_130_; size_t v_i_boxed_131_; size_t v_stop_boxed_132_; lean_object* v_res_133_; 
v___x_530__boxed_130_ = lean_unbox(v___x_125_);
v_i_boxed_131_ = lean_unbox_usize(v_i_127_);
lean_dec(v_i_127_);
v_stop_boxed_132_ = lean_unbox_usize(v_stop_128_);
lean_dec(v_stop_128_);
v_res_133_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__1(v___x_530__boxed_130_, v_as_126_, v_i_boxed_131_, v_stop_boxed_132_, v_b_129_);
lean_dec_ref(v_as_126_);
return v_res_133_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_shouldExpandMatchAlt(lean_object* v_x_145_){
_start:
{
lean_object* v___x_146_; uint8_t v___x_147_; 
v___x_146_ = ((lean_object*)(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__4));
lean_inc(v_x_145_);
v___x_147_ = l_Lean_Syntax_isOfKind(v_x_145_, v___x_146_);
if (v___x_147_ == 0)
{
lean_dec(v_x_145_);
return v___x_147_;
}
else
{
lean_object* v___x_148_; lean_object* v___y_150_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_148_ = lean_unsigned_to_nat(1u);
v___x_158_ = l_Lean_Syntax_getArg(v_x_145_, v___x_148_);
lean_dec(v_x_145_);
v___x_159_ = l_Lean_Syntax_getArgs(v___x_158_);
lean_dec(v___x_158_);
v___x_160_ = lean_unsigned_to_nat(0u);
v___x_161_ = ((lean_object*)(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5));
v___x_162_ = lean_array_get_size(v___x_159_);
v___x_163_ = lean_nat_dec_lt(v___x_160_, v___x_162_);
if (v___x_163_ == 0)
{
lean_dec_ref(v___x_159_);
v___y_150_ = v___x_161_;
goto v___jp_149_;
}
else
{
lean_object* v___x_164_; lean_object* v___x_165_; uint8_t v___x_166_; 
v___x_164_ = lean_box(v___x_147_);
v___x_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
lean_ctor_set(v___x_165_, 1, v___x_161_);
v___x_166_ = lean_nat_dec_le(v___x_162_, v___x_162_);
if (v___x_166_ == 0)
{
if (v___x_163_ == 0)
{
lean_dec_ref(v___x_165_);
lean_dec_ref(v___x_159_);
v___y_150_ = v___x_161_;
goto v___jp_149_;
}
else
{
size_t v___x_167_; size_t v___x_168_; lean_object* v___x_169_; lean_object* v_snd_170_; 
v___x_167_ = ((size_t)0ULL);
v___x_168_ = lean_usize_of_nat(v___x_162_);
v___x_169_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__1(v___x_147_, v___x_159_, v___x_167_, v___x_168_, v___x_165_);
lean_dec_ref(v___x_159_);
v_snd_170_ = lean_ctor_get(v___x_169_, 1);
lean_inc(v_snd_170_);
lean_dec_ref(v___x_169_);
v___y_150_ = v_snd_170_;
goto v___jp_149_;
}
}
else
{
size_t v___x_171_; size_t v___x_172_; lean_object* v___x_173_; lean_object* v_snd_174_; 
v___x_171_ = ((size_t)0ULL);
v___x_172_ = lean_usize_of_nat(v___x_162_);
v___x_173_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__1(v___x_147_, v___x_159_, v___x_171_, v___x_172_, v___x_165_);
lean_dec_ref(v___x_159_);
v_snd_174_ = lean_ctor_get(v___x_173_, 1);
lean_inc(v_snd_174_);
lean_dec_ref(v___x_173_);
v___y_150_ = v_snd_174_;
goto v___jp_149_;
}
}
v___jp_149_:
{
size_t v_sz_151_; size_t v___x_152_; lean_object* v___x_153_; 
v_sz_151_ = lean_array_size(v___y_150_);
v___x_152_ = ((size_t)0ULL);
v___x_153_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__0(v_sz_151_, v___x_152_, v___y_150_);
if (lean_obj_tag(v___x_153_) == 0)
{
uint8_t v___x_154_; 
v___x_154_ = 0;
return v___x_154_;
}
else
{
lean_object* v_val_155_; lean_object* v___x_156_; uint8_t v___x_157_; 
v_val_155_ = lean_ctor_get(v___x_153_, 0);
lean_inc(v_val_155_);
lean_dec_ref(v___x_153_);
v___x_156_ = lean_array_get_size(v_val_155_);
lean_dec(v_val_155_);
v___x_157_ = lean_nat_dec_lt(v___x_148_, v___x_156_);
return v___x_157_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_shouldExpandMatchAlt___boxed(lean_object* v_x_175_){
_start:
{
uint8_t v_res_176_; lean_object* v_r_177_; 
v_res_176_ = l_Lean_Elab_Term_shouldExpandMatchAlt(v_x_175_);
v_r_177_ = lean_box(v_res_176_);
return v_r_177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___redArg(lean_object* v_as_178_, size_t v_i_179_, size_t v_stop_180_, lean_object* v_b_181_, lean_object* v___y_182_){
_start:
{
uint8_t v___x_183_; 
v___x_183_ = lean_usize_dec_eq(v_i_179_, v_stop_180_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; size_t v___x_187_; size_t v___x_188_; 
v___x_184_ = lean_array_uget_borrowed(v_as_178_, v_i_179_);
lean_inc(v___x_184_);
v___x_185_ = l_Lean_Elab_Term_expandMatchAlt(v___x_184_);
v___x_186_ = l_Array_append___redArg(v_b_181_, v___x_185_);
lean_dec_ref(v___x_185_);
v___x_187_ = ((size_t)1ULL);
v___x_188_ = lean_usize_add(v_i_179_, v___x_187_);
v_i_179_ = v___x_188_;
v_b_181_ = v___x_186_;
goto _start;
}
else
{
lean_object* v___x_190_; 
v___x_190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_190_, 0, v_b_181_);
lean_ctor_set(v___x_190_, 1, v___y_182_);
return v___x_190_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___redArg___boxed(lean_object* v_as_191_, lean_object* v_i_192_, lean_object* v_stop_193_, lean_object* v_b_194_, lean_object* v___y_195_){
_start:
{
size_t v_i_boxed_196_; size_t v_stop_boxed_197_; lean_object* v_res_198_; 
v_i_boxed_196_ = lean_unbox_usize(v_i_192_);
lean_dec(v_i_192_);
v_stop_boxed_197_ = lean_unbox_usize(v_stop_193_);
lean_dec(v_stop_193_);
v_res_198_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___redArg(v_as_191_, v_i_boxed_196_, v_stop_boxed_197_, v_b_194_, v___y_195_);
lean_dec_ref(v_as_191_);
return v_res_198_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__0(lean_object* v_as_199_, size_t v_i_200_, size_t v_stop_201_){
_start:
{
uint8_t v___x_202_; 
v___x_202_ = lean_usize_dec_eq(v_i_200_, v_stop_201_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; uint8_t v___x_204_; 
v___x_203_ = lean_array_uget_borrowed(v_as_199_, v_i_200_);
lean_inc(v___x_203_);
v___x_204_ = l_Lean_Elab_Term_shouldExpandMatchAlt(v___x_203_);
if (v___x_204_ == 0)
{
size_t v___x_205_; size_t v___x_206_; 
v___x_205_ = ((size_t)1ULL);
v___x_206_ = lean_usize_add(v_i_200_, v___x_205_);
v_i_200_ = v___x_206_;
goto _start;
}
else
{
return v___x_204_;
}
}
else
{
uint8_t v___x_208_; 
v___x_208_ = 0;
return v___x_208_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__0___boxed(lean_object* v_as_209_, lean_object* v_i_210_, lean_object* v_stop_211_){
_start:
{
size_t v_i_boxed_212_; size_t v_stop_boxed_213_; uint8_t v_res_214_; lean_object* v_r_215_; 
v_i_boxed_212_ = lean_unbox_usize(v_i_210_);
lean_dec(v_i_210_);
v_stop_boxed_213_ = lean_unbox_usize(v_stop_211_);
lean_dec(v_stop_211_);
v_res_214_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__0(v_as_209_, v_i_boxed_212_, v_stop_boxed_213_);
lean_dec_ref(v_as_209_);
v_r_215_ = lean_box(v_res_214_);
return v_r_215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand(lean_object* v_alts_218_, lean_object* v_a_219_, lean_object* v_a_220_){
_start:
{
lean_object* v_a_225_; lean_object* v_a_226_; lean_object* v___y_230_; lean_object* v___x_242_; lean_object* v___x_243_; uint8_t v___x_244_; 
v___x_242_ = lean_unsigned_to_nat(0u);
v___x_243_ = lean_array_get_size(v_alts_218_);
v___x_244_ = lean_nat_dec_lt(v___x_242_, v___x_243_);
if (v___x_244_ == 0)
{
goto v___jp_221_;
}
else
{
if (v___x_244_ == 0)
{
goto v___jp_221_;
}
else
{
size_t v___x_245_; size_t v___x_246_; uint8_t v___x_247_; 
v___x_245_ = ((size_t)0ULL);
v___x_246_ = lean_usize_of_nat(v___x_243_);
v___x_247_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__0(v_alts_218_, v___x_245_, v___x_246_);
if (v___x_247_ == 0)
{
goto v___jp_221_;
}
else
{
lean_object* v___x_248_; 
v___x_248_ = ((lean_object*)(l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand___closed__0));
if (v___x_244_ == 0)
{
v_a_225_ = v___x_248_;
v_a_226_ = v_a_220_;
goto v___jp_224_;
}
else
{
uint8_t v___x_249_; 
v___x_249_ = lean_nat_dec_le(v___x_243_, v___x_243_);
if (v___x_249_ == 0)
{
if (v___x_244_ == 0)
{
v_a_225_ = v___x_248_;
v_a_226_ = v_a_220_;
goto v___jp_224_;
}
else
{
lean_object* v___x_250_; 
v___x_250_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___redArg(v_alts_218_, v___x_245_, v___x_246_, v___x_248_, v_a_220_);
v___y_230_ = v___x_250_;
goto v___jp_229_;
}
}
else
{
lean_object* v___x_251_; 
v___x_251_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___redArg(v_alts_218_, v___x_245_, v___x_246_, v___x_248_, v_a_220_);
v___y_230_ = v___x_251_;
goto v___jp_229_;
}
}
}
}
}
v___jp_221_:
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = lean_box(0);
v___x_223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
lean_ctor_set(v___x_223_, 1, v_a_220_);
return v___x_223_;
}
v___jp_224_:
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_227_, 0, v_a_225_);
v___x_228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
lean_ctor_set(v___x_228_, 1, v_a_226_);
return v___x_228_;
}
v___jp_229_:
{
if (lean_obj_tag(v___y_230_) == 0)
{
lean_object* v_a_231_; lean_object* v_a_232_; 
v_a_231_ = lean_ctor_get(v___y_230_, 0);
lean_inc(v_a_231_);
v_a_232_ = lean_ctor_get(v___y_230_, 1);
lean_inc(v_a_232_);
lean_dec_ref(v___y_230_);
v_a_225_ = v_a_231_;
v_a_226_ = v_a_232_;
goto v___jp_224_;
}
else
{
lean_object* v_a_233_; lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_241_; 
v_a_233_ = lean_ctor_get(v___y_230_, 0);
v_a_234_ = lean_ctor_get(v___y_230_, 1);
v_isSharedCheck_241_ = !lean_is_exclusive(v___y_230_);
if (v_isSharedCheck_241_ == 0)
{
v___x_236_ = v___y_230_;
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_inc(v_a_233_);
lean_dec(v___y_230_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_239_; 
if (v_isShared_237_ == 0)
{
v___x_239_ = v___x_236_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_a_233_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v_a_234_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand___boxed(lean_object* v_alts_252_, lean_object* v_a_253_, lean_object* v_a_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand(v_alts_252_, v_a_253_, v_a_254_);
lean_dec_ref(v_a_253_);
lean_dec_ref(v_alts_252_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1(lean_object* v_as_256_, size_t v_i_257_, size_t v_stop_258_, lean_object* v_b_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___redArg(v_as_256_, v_i_257_, v_stop_258_, v_b_259_, v___y_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___boxed(lean_object* v_as_263_, lean_object* v_i_264_, lean_object* v_stop_265_, lean_object* v_b_266_, lean_object* v___y_267_, lean_object* v___y_268_){
_start:
{
size_t v_i_boxed_269_; size_t v_stop_boxed_270_; lean_object* v_res_271_; 
v_i_boxed_269_ = lean_unbox_usize(v_i_264_);
lean_dec(v_i_264_);
v_stop_boxed_270_ = lean_unbox_usize(v_stop_265_);
lean_dec(v_stop_265_);
v_res_271_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1(v_as_263_, v_i_boxed_269_, v_stop_boxed_270_, v_b_266_, v___y_267_, v___y_268_);
lean_dec_ref(v___y_267_);
lean_dec_ref(v_as_263_);
return v_res_271_;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7(void){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l_Array_mkArray0(lean_box(0));
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f(lean_object* v_stx_292_, lean_object* v_a_293_, lean_object* v_a_294_){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___y_298_; lean_object* v___y_299_; lean_object* v___y_300_; lean_object* v___y_301_; lean_object* v___y_302_; lean_object* v___y_303_; lean_object* v___y_304_; lean_object* v___y_305_; lean_object* v___y_306_; lean_object* v___y_307_; uint8_t v___x_320_; 
v___x_295_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__0));
v___x_296_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1));
lean_inc(v_stx_292_);
v___x_320_ = l_Lean_Syntax_isOfKind(v_stx_292_, v___x_296_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; lean_object* v___y_323_; lean_object* v___y_324_; lean_object* v___y_325_; lean_object* v___y_326_; lean_object* v___y_327_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v___y_331_; lean_object* v___y_332_; lean_object* v___y_333_; uint8_t v___x_346_; 
v___x_321_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__4));
lean_inc(v_stx_292_);
v___x_346_ = l_Lean_Syntax_isOfKind(v_stx_292_, v___x_321_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; lean_object* v___x_348_; 
lean_dec(v_stx_292_);
v___x_347_ = lean_box(0);
v___x_348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
lean_ctor_set(v___x_348_, 1, v_a_294_);
return v___x_348_;
}
else
{
lean_object* v___x_349_; lean_object* v___y_351_; lean_object* v___y_352_; lean_object* v___y_353_; lean_object* v___y_354_; lean_object* v___y_355_; lean_object* v___y_356_; lean_object* v___y_357_; lean_object* v___y_358_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___y_368_; lean_object* v___y_369_; lean_object* v___y_370_; lean_object* v___y_371_; lean_object* v___y_372_; lean_object* v___y_373_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v___y_376_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___y_385_; lean_object* v___y_386_; lean_object* v_motive_387_; lean_object* v___y_388_; lean_object* v___y_389_; lean_object* v___x_432_; lean_object* v___y_434_; lean_object* v_gen_435_; lean_object* v___y_436_; lean_object* v___y_437_; lean_object* v_dep_x3f_448_; lean_object* v___y_449_; lean_object* v___y_450_; lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_349_ = lean_unsigned_to_nat(0u);
v___x_432_ = lean_unsigned_to_nat(1u);
v___x_460_ = l_Lean_Syntax_getArg(v_stx_292_, v___x_432_);
v___x_461_ = l_Lean_Syntax_isNone(v___x_460_);
if (v___x_461_ == 0)
{
uint8_t v___x_462_; 
lean_inc(v___x_460_);
v___x_462_ = l_Lean_Syntax_matchesNull(v___x_460_, v___x_432_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; lean_object* v___x_464_; 
lean_dec(v___x_460_);
lean_dec(v_stx_292_);
v___x_463_ = lean_box(0);
v___x_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
lean_ctor_set(v___x_464_, 1, v_a_294_);
return v___x_464_;
}
else
{
lean_object* v_dep_x3f_465_; lean_object* v___x_466_; 
v_dep_x3f_465_ = l_Lean_Syntax_getArg(v___x_460_, v___x_349_);
lean_dec(v___x_460_);
v___x_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_466_, 0, v_dep_x3f_465_);
v_dep_x3f_448_ = v___x_466_;
v___y_449_ = v_a_293_;
v___y_450_ = v_a_294_;
goto v___jp_447_;
}
}
else
{
lean_object* v___x_467_; 
lean_dec(v___x_460_);
v___x_467_ = lean_box(0);
v_dep_x3f_448_ = v___x_467_;
v___y_449_ = v_a_293_;
v___y_450_ = v_a_294_;
goto v___jp_447_;
}
v___jp_350_:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
lean_inc_ref(v___y_353_);
v___x_362_ = l_Array_append___redArg(v___y_353_, v___y_361_);
lean_dec_ref(v___y_361_);
lean_inc(v___y_355_);
lean_inc(v___y_352_);
v___x_363_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_363_, 0, v___y_352_);
lean_ctor_set(v___x_363_, 1, v___y_355_);
lean_ctor_set(v___x_363_, 2, v___x_362_);
if (lean_obj_tag(v___y_358_) == 1)
{
lean_object* v_val_364_; lean_object* v___x_365_; 
v_val_364_ = lean_ctor_get(v___y_358_, 0);
lean_inc(v_val_364_);
lean_dec_ref(v___y_358_);
v___x_365_ = l_Array_mkArray1___redArg(v_val_364_);
v___y_323_ = v___y_351_;
v___y_324_ = v___y_352_;
v___y_325_ = v___y_353_;
v___y_326_ = v___y_354_;
v___y_327_ = v___y_355_;
v___y_328_ = v___y_357_;
v___y_329_ = v___y_356_;
v___y_330_ = v___x_363_;
v___y_331_ = v___y_359_;
v___y_332_ = v___y_360_;
v___y_333_ = v___x_365_;
goto v___jp_322_;
}
else
{
lean_object* v___x_366_; 
lean_dec(v___y_358_);
v___x_366_ = ((lean_object*)(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5));
v___y_323_ = v___y_351_;
v___y_324_ = v___y_352_;
v___y_325_ = v___y_353_;
v___y_326_ = v___y_354_;
v___y_327_ = v___y_355_;
v___y_328_ = v___y_357_;
v___y_329_ = v___y_356_;
v___y_330_ = v___x_363_;
v___y_331_ = v___y_359_;
v___y_332_ = v___y_360_;
v___y_333_ = v___x_366_;
goto v___jp_322_;
}
}
v___jp_367_:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
lean_inc_ref(v___y_370_);
v___x_379_ = l_Array_append___redArg(v___y_370_, v___y_378_);
lean_dec_ref(v___y_378_);
lean_inc(v___y_372_);
lean_inc(v___y_369_);
v___x_380_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_380_, 0, v___y_369_);
lean_ctor_set(v___x_380_, 1, v___y_372_);
lean_ctor_set(v___x_380_, 2, v___x_379_);
if (lean_obj_tag(v___y_368_) == 1)
{
lean_object* v_val_381_; lean_object* v___x_382_; 
v_val_381_ = lean_ctor_get(v___y_368_, 0);
lean_inc(v_val_381_);
lean_dec_ref(v___y_368_);
v___x_382_ = l_Array_mkArray1___redArg(v_val_381_);
v___y_351_ = v___x_380_;
v___y_352_ = v___y_369_;
v___y_353_ = v___y_370_;
v___y_354_ = v___y_371_;
v___y_355_ = v___y_372_;
v___y_356_ = v___y_374_;
v___y_357_ = v___y_373_;
v___y_358_ = v___y_375_;
v___y_359_ = v___y_376_;
v___y_360_ = v___y_377_;
v___y_361_ = v___x_382_;
goto v___jp_350_;
}
else
{
lean_object* v___x_383_; 
lean_dec(v___y_368_);
v___x_383_ = ((lean_object*)(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5));
v___y_351_ = v___x_380_;
v___y_352_ = v___y_369_;
v___y_353_ = v___y_370_;
v___y_354_ = v___y_371_;
v___y_355_ = v___y_372_;
v___y_356_ = v___y_374_;
v___y_357_ = v___y_373_;
v___y_358_ = v___y_375_;
v___y_359_ = v___y_376_;
v___y_360_ = v___y_377_;
v___y_361_ = v___x_383_;
goto v___jp_350_;
}
}
v___jp_384_:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_390_ = lean_unsigned_to_nat(6u);
v___x_391_ = l_Lean_Syntax_getArg(v_stx_292_, v___x_390_);
v___x_392_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6));
lean_inc(v___x_391_);
v___x_393_ = l_Lean_Syntax_isOfKind(v___x_391_, v___x_392_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; lean_object* v___x_395_; 
lean_dec(v___x_391_);
lean_dec(v_motive_387_);
lean_dec(v___y_386_);
lean_dec(v___y_385_);
lean_dec(v_stx_292_);
v___x_394_ = lean_box(0);
v___x_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
lean_ctor_set(v___x_395_, 1, v___y_389_);
return v___x_395_;
}
else
{
lean_object* v___x_396_; lean_object* v_alts_397_; lean_object* v___x_398_; 
v___x_396_ = l_Lean_Syntax_getArg(v___x_391_, v___x_349_);
lean_dec(v___x_391_);
v_alts_397_ = l_Lean_Syntax_getArgs(v___x_396_);
lean_dec(v___x_396_);
v___x_398_ = l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand(v_alts_397_, v___y_388_, v___y_389_);
lean_dec_ref(v_alts_397_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v_a_399_; 
v_a_399_ = lean_ctor_get(v___x_398_, 0);
lean_inc(v_a_399_);
if (lean_obj_tag(v_a_399_) == 0)
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_408_; 
lean_dec(v_motive_387_);
lean_dec(v___y_386_);
lean_dec(v___y_385_);
lean_dec(v_stx_292_);
v_a_400_ = lean_ctor_get(v___x_398_, 1);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_408_ == 0)
{
lean_object* v_unused_409_; 
v_unused_409_ = lean_ctor_get(v___x_398_, 0);
lean_dec(v_unused_409_);
v___x_402_ = v___x_398_;
v_isShared_403_ = v_isSharedCheck_408_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_398_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_408_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_404_ = lean_box(0);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v___x_404_);
v___x_406_ = v___x_402_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_404_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v_a_400_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
else
{
lean_object* v_a_410_; lean_object* v_val_411_; lean_object* v_ref_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v_a_410_ = lean_ctor_get(v___x_398_, 1);
lean_inc(v_a_410_);
lean_dec_ref(v___x_398_);
v_val_411_ = lean_ctor_get(v_a_399_, 0);
lean_inc(v_val_411_);
lean_dec_ref(v_a_399_);
v_ref_412_ = lean_ctor_get(v___y_388_, 5);
v___x_413_ = lean_unsigned_to_nat(4u);
v___x_414_ = l_Lean_Syntax_getArg(v_stx_292_, v___x_413_);
lean_dec(v_stx_292_);
v___x_415_ = l_Lean_Syntax_getArgs(v___x_414_);
lean_dec(v___x_414_);
v___x_416_ = l_Lean_SourceInfo_fromRef(v_ref_412_, v___x_320_);
lean_inc(v___x_416_);
v___x_417_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
lean_ctor_set(v___x_417_, 1, v___x_295_);
v___x_418_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__1));
v___x_419_ = lean_obj_once(&l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7, &l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7_once, _init_l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7);
if (lean_obj_tag(v___y_386_) == 1)
{
lean_object* v_val_420_; lean_object* v___x_421_; 
v_val_420_ = lean_ctor_get(v___y_386_, 0);
lean_inc(v_val_420_);
lean_dec_ref(v___y_386_);
v___x_421_ = l_Array_mkArray1___redArg(v_val_420_);
v___y_368_ = v___y_385_;
v___y_369_ = v___x_416_;
v___y_370_ = v___x_419_;
v___y_371_ = v___x_415_;
v___y_372_ = v___x_418_;
v___y_373_ = v___x_392_;
v___y_374_ = v_val_411_;
v___y_375_ = v_motive_387_;
v___y_376_ = v_a_410_;
v___y_377_ = v___x_417_;
v___y_378_ = v___x_421_;
goto v___jp_367_;
}
else
{
lean_object* v___x_422_; 
lean_dec(v___y_386_);
v___x_422_ = ((lean_object*)(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5));
v___y_368_ = v___y_385_;
v___y_369_ = v___x_416_;
v___y_370_ = v___x_419_;
v___y_371_ = v___x_415_;
v___y_372_ = v___x_418_;
v___y_373_ = v___x_392_;
v___y_374_ = v_val_411_;
v___y_375_ = v_motive_387_;
v___y_376_ = v_a_410_;
v___y_377_ = v___x_417_;
v___y_378_ = v___x_422_;
goto v___jp_367_;
}
}
}
else
{
lean_object* v_a_423_; lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
lean_dec(v_motive_387_);
lean_dec(v___y_386_);
lean_dec(v___y_385_);
lean_dec(v_stx_292_);
v_a_423_ = lean_ctor_get(v___x_398_, 0);
v_a_424_ = lean_ctor_get(v___x_398_, 1);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_431_ == 0)
{
v___x_426_ = v___x_398_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_inc(v_a_423_);
lean_dec(v___x_398_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_a_423_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v_a_424_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
}
v___jp_433_:
{
lean_object* v___x_438_; lean_object* v___x_439_; uint8_t v___x_440_; 
v___x_438_ = lean_unsigned_to_nat(3u);
v___x_439_ = l_Lean_Syntax_getArg(v_stx_292_, v___x_438_);
v___x_440_ = l_Lean_Syntax_isNone(v___x_439_);
if (v___x_440_ == 0)
{
uint8_t v___x_441_; 
lean_inc(v___x_439_);
v___x_441_ = l_Lean_Syntax_matchesNull(v___x_439_, v___x_432_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; lean_object* v___x_443_; 
lean_dec(v___x_439_);
lean_dec(v_gen_435_);
lean_dec(v___y_434_);
lean_dec(v_stx_292_);
v___x_442_ = lean_box(0);
v___x_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_443_, 0, v___x_442_);
lean_ctor_set(v___x_443_, 1, v___y_437_);
return v___x_443_;
}
else
{
lean_object* v_motive_444_; lean_object* v___x_445_; 
v_motive_444_ = l_Lean_Syntax_getArg(v___x_439_, v___x_349_);
lean_dec(v___x_439_);
v___x_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_445_, 0, v_motive_444_);
v___y_385_ = v_gen_435_;
v___y_386_ = v___y_434_;
v_motive_387_ = v___x_445_;
v___y_388_ = v___y_436_;
v___y_389_ = v___y_437_;
goto v___jp_384_;
}
}
else
{
lean_object* v___x_446_; 
lean_dec(v___x_439_);
v___x_446_ = lean_box(0);
v___y_385_ = v_gen_435_;
v___y_386_ = v___y_434_;
v_motive_387_ = v___x_446_;
v___y_388_ = v___y_436_;
v___y_389_ = v___y_437_;
goto v___jp_384_;
}
}
v___jp_447_:
{
lean_object* v___x_451_; lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_451_ = lean_unsigned_to_nat(2u);
v___x_452_ = l_Lean_Syntax_getArg(v_stx_292_, v___x_451_);
v___x_453_ = l_Lean_Syntax_isNone(v___x_452_);
if (v___x_453_ == 0)
{
uint8_t v___x_454_; 
lean_inc(v___x_452_);
v___x_454_ = l_Lean_Syntax_matchesNull(v___x_452_, v___x_432_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; lean_object* v___x_456_; 
lean_dec(v___x_452_);
lean_dec(v_dep_x3f_448_);
lean_dec(v_stx_292_);
v___x_455_ = lean_box(0);
v___x_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
lean_ctor_set(v___x_456_, 1, v___y_450_);
return v___x_456_;
}
else
{
lean_object* v_gen_457_; lean_object* v___x_458_; 
v_gen_457_ = l_Lean_Syntax_getArg(v___x_452_, v___x_349_);
lean_dec(v___x_452_);
v___x_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_458_, 0, v_gen_457_);
v___y_434_ = v_dep_x3f_448_;
v_gen_435_ = v___x_458_;
v___y_436_ = v___y_449_;
v___y_437_ = v___y_450_;
goto v___jp_433_;
}
}
else
{
lean_object* v___x_459_; 
lean_dec(v___x_452_);
v___x_459_ = lean_box(0);
v___y_434_ = v_dep_x3f_448_;
v_gen_435_ = v___x_459_;
v___y_436_ = v___y_449_;
v___y_437_ = v___y_450_;
goto v___jp_433_;
}
}
}
v___jp_322_:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
lean_inc_ref_n(v___y_325_, 3);
v___x_334_ = l_Array_append___redArg(v___y_325_, v___y_333_);
lean_dec_ref(v___y_333_);
lean_inc_n(v___y_327_, 3);
lean_inc_n(v___y_324_, 5);
v___x_335_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_335_, 0, v___y_324_);
lean_ctor_set(v___x_335_, 1, v___y_327_);
lean_ctor_set(v___x_335_, 2, v___x_334_);
v___x_336_ = l_Array_append___redArg(v___y_325_, v___y_326_);
lean_dec_ref(v___y_326_);
v___x_337_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_337_, 0, v___y_324_);
lean_ctor_set(v___x_337_, 1, v___y_327_);
lean_ctor_set(v___x_337_, 2, v___x_336_);
v___x_338_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__2));
v___x_339_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_339_, 0, v___y_324_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
v___x_340_ = l_Array_append___redArg(v___y_325_, v___y_329_);
lean_dec_ref(v___y_329_);
v___x_341_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_341_, 0, v___y_324_);
lean_ctor_set(v___x_341_, 1, v___y_327_);
lean_ctor_set(v___x_341_, 2, v___x_340_);
lean_inc(v___y_328_);
v___x_342_ = l_Lean_Syntax_node1(v___y_324_, v___y_328_, v___x_341_);
v___x_343_ = l_Lean_Syntax_node7(v___y_324_, v___x_321_, v___y_332_, v___y_323_, v___y_330_, v___x_335_, v___x_337_, v___x_339_, v___x_342_);
v___x_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
v___x_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
lean_ctor_set(v___x_345_, 1, v___y_331_);
return v___x_345_;
}
}
else
{
lean_object* v___x_468_; lean_object* v___y_470_; lean_object* v___y_471_; lean_object* v___y_472_; lean_object* v___y_473_; lean_object* v___y_474_; lean_object* v___y_475_; lean_object* v___y_476_; lean_object* v___y_477_; lean_object* v___y_478_; lean_object* v___y_479_; lean_object* v___y_486_; lean_object* v_motive_487_; lean_object* v___y_488_; lean_object* v___y_489_; lean_object* v___x_533_; lean_object* v_gen_535_; lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___x_547_; uint8_t v___x_548_; 
v___x_468_ = lean_unsigned_to_nat(0u);
v___x_533_ = lean_unsigned_to_nat(1u);
v___x_547_ = l_Lean_Syntax_getArg(v_stx_292_, v___x_533_);
v___x_548_ = l_Lean_Syntax_isNone(v___x_547_);
if (v___x_548_ == 0)
{
uint8_t v___x_549_; 
lean_inc(v___x_547_);
v___x_549_ = l_Lean_Syntax_matchesNull(v___x_547_, v___x_533_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; lean_object* v___x_551_; 
lean_dec(v___x_547_);
lean_dec(v_stx_292_);
v___x_550_ = lean_box(0);
v___x_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
lean_ctor_set(v___x_551_, 1, v_a_294_);
return v___x_551_;
}
else
{
lean_object* v_gen_552_; lean_object* v___x_553_; 
v_gen_552_ = l_Lean_Syntax_getArg(v___x_547_, v___x_468_);
lean_dec(v___x_547_);
v___x_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_553_, 0, v_gen_552_);
v_gen_535_ = v___x_553_;
v___y_536_ = v_a_293_;
v___y_537_ = v_a_294_;
goto v___jp_534_;
}
}
else
{
lean_object* v___x_554_; 
lean_dec(v___x_547_);
v___x_554_ = lean_box(0);
v_gen_535_ = v___x_554_;
v___y_536_ = v_a_293_;
v___y_537_ = v_a_294_;
goto v___jp_534_;
}
v___jp_469_:
{
lean_object* v___x_480_; lean_object* v___x_481_; 
lean_inc_ref(v___y_470_);
v___x_480_ = l_Array_append___redArg(v___y_470_, v___y_479_);
lean_dec_ref(v___y_479_);
lean_inc(v___y_475_);
lean_inc(v___y_472_);
v___x_481_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_481_, 0, v___y_472_);
lean_ctor_set(v___x_481_, 1, v___y_475_);
lean_ctor_set(v___x_481_, 2, v___x_480_);
if (lean_obj_tag(v___y_473_) == 1)
{
lean_object* v_val_482_; lean_object* v___x_483_; 
v_val_482_ = lean_ctor_get(v___y_473_, 0);
lean_inc(v_val_482_);
lean_dec_ref(v___y_473_);
v___x_483_ = l_Array_mkArray1___redArg(v_val_482_);
v___y_298_ = v___y_470_;
v___y_299_ = v___y_471_;
v___y_300_ = v___y_472_;
v___y_301_ = v___y_474_;
v___y_302_ = v___y_475_;
v___y_303_ = v___y_476_;
v___y_304_ = v___x_481_;
v___y_305_ = v___y_478_;
v___y_306_ = v___y_477_;
v___y_307_ = v___x_483_;
goto v___jp_297_;
}
else
{
lean_object* v___x_484_; 
lean_dec(v___y_473_);
v___x_484_ = ((lean_object*)(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5));
v___y_298_ = v___y_470_;
v___y_299_ = v___y_471_;
v___y_300_ = v___y_472_;
v___y_301_ = v___y_474_;
v___y_302_ = v___y_475_;
v___y_303_ = v___y_476_;
v___y_304_ = v___x_481_;
v___y_305_ = v___y_478_;
v___y_306_ = v___y_477_;
v___y_307_ = v___x_484_;
goto v___jp_297_;
}
}
v___jp_485_:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; uint8_t v___x_493_; 
v___x_490_ = lean_unsigned_to_nat(5u);
v___x_491_ = l_Lean_Syntax_getArg(v_stx_292_, v___x_490_);
v___x_492_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6));
lean_inc(v___x_491_);
v___x_493_ = l_Lean_Syntax_isOfKind(v___x_491_, v___x_492_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; lean_object* v___x_495_; 
lean_dec(v___x_491_);
lean_dec(v_motive_487_);
lean_dec(v___y_486_);
lean_dec(v_stx_292_);
v___x_494_ = lean_box(0);
v___x_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
lean_ctor_set(v___x_495_, 1, v___y_489_);
return v___x_495_;
}
else
{
lean_object* v___x_496_; lean_object* v_alts_497_; lean_object* v___x_498_; 
v___x_496_ = l_Lean_Syntax_getArg(v___x_491_, v___x_468_);
lean_dec(v___x_491_);
v_alts_497_ = l_Lean_Syntax_getArgs(v___x_496_);
lean_dec(v___x_496_);
v___x_498_ = l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand(v_alts_497_, v___y_488_, v___y_489_);
lean_dec_ref(v_alts_497_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc(v_a_499_);
if (lean_obj_tag(v_a_499_) == 0)
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_508_; 
lean_dec(v_motive_487_);
lean_dec(v___y_486_);
lean_dec(v_stx_292_);
v_a_500_ = lean_ctor_get(v___x_498_, 1);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_508_ == 0)
{
lean_object* v_unused_509_; 
v_unused_509_ = lean_ctor_get(v___x_498_, 0);
lean_dec(v_unused_509_);
v___x_502_ = v___x_498_;
v_isShared_503_ = v_isSharedCheck_508_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_498_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_508_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_504_; lean_object* v___x_506_; 
v___x_504_ = lean_box(0);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v___x_504_);
v___x_506_ = v___x_502_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_504_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v_a_500_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
else
{
lean_object* v_a_510_; lean_object* v_val_511_; lean_object* v_ref_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; uint8_t v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v_a_510_ = lean_ctor_get(v___x_498_, 1);
lean_inc(v_a_510_);
lean_dec_ref(v___x_498_);
v_val_511_ = lean_ctor_get(v_a_499_, 0);
lean_inc(v_val_511_);
lean_dec_ref(v_a_499_);
v_ref_512_ = lean_ctor_get(v___y_488_, 5);
v___x_513_ = lean_unsigned_to_nat(3u);
v___x_514_ = l_Lean_Syntax_getArg(v_stx_292_, v___x_513_);
lean_dec(v_stx_292_);
v___x_515_ = l_Lean_Syntax_getArgs(v___x_514_);
lean_dec(v___x_514_);
v___x_516_ = 0;
v___x_517_ = l_Lean_SourceInfo_fromRef(v_ref_512_, v___x_516_);
lean_inc(v___x_517_);
v___x_518_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
lean_ctor_set(v___x_518_, 1, v___x_295_);
v___x_519_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__1));
v___x_520_ = lean_obj_once(&l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7, &l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7_once, _init_l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7);
if (lean_obj_tag(v___y_486_) == 1)
{
lean_object* v_val_521_; lean_object* v___x_522_; 
v_val_521_ = lean_ctor_get(v___y_486_, 0);
lean_inc(v_val_521_);
lean_dec_ref(v___y_486_);
v___x_522_ = l_Array_mkArray1___redArg(v_val_521_);
v___y_470_ = v___x_520_;
v___y_471_ = v_a_510_;
v___y_472_ = v___x_517_;
v___y_473_ = v_motive_487_;
v___y_474_ = v_val_511_;
v___y_475_ = v___x_519_;
v___y_476_ = v___x_492_;
v___y_477_ = v___x_515_;
v___y_478_ = v___x_518_;
v___y_479_ = v___x_522_;
goto v___jp_469_;
}
else
{
lean_object* v___x_523_; 
lean_dec(v___y_486_);
v___x_523_ = ((lean_object*)(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5));
v___y_470_ = v___x_520_;
v___y_471_ = v_a_510_;
v___y_472_ = v___x_517_;
v___y_473_ = v_motive_487_;
v___y_474_ = v_val_511_;
v___y_475_ = v___x_519_;
v___y_476_ = v___x_492_;
v___y_477_ = v___x_515_;
v___y_478_ = v___x_518_;
v___y_479_ = v___x_523_;
goto v___jp_469_;
}
}
}
else
{
lean_object* v_a_524_; lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_532_; 
lean_dec(v_motive_487_);
lean_dec(v___y_486_);
lean_dec(v_stx_292_);
v_a_524_ = lean_ctor_get(v___x_498_, 0);
v_a_525_ = lean_ctor_get(v___x_498_, 1);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_532_ == 0)
{
v___x_527_ = v___x_498_;
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_inc(v_a_524_);
lean_dec(v___x_498_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_530_; 
if (v_isShared_528_ == 0)
{
v___x_530_ = v___x_527_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_a_524_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v_a_525_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
}
v___jp_534_:
{
lean_object* v___x_538_; lean_object* v___x_539_; uint8_t v___x_540_; 
v___x_538_ = lean_unsigned_to_nat(2u);
v___x_539_ = l_Lean_Syntax_getArg(v_stx_292_, v___x_538_);
v___x_540_ = l_Lean_Syntax_isNone(v___x_539_);
if (v___x_540_ == 0)
{
uint8_t v___x_541_; 
lean_inc(v___x_539_);
v___x_541_ = l_Lean_Syntax_matchesNull(v___x_539_, v___x_533_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; lean_object* v___x_543_; 
lean_dec(v___x_539_);
lean_dec(v_gen_535_);
lean_dec(v_stx_292_);
v___x_542_ = lean_box(0);
v___x_543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
lean_ctor_set(v___x_543_, 1, v___y_537_);
return v___x_543_;
}
else
{
lean_object* v_motive_544_; lean_object* v___x_545_; 
v_motive_544_ = l_Lean_Syntax_getArg(v___x_539_, v___x_468_);
lean_dec(v___x_539_);
v___x_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_545_, 0, v_motive_544_);
v___y_486_ = v_gen_535_;
v_motive_487_ = v___x_545_;
v___y_488_ = v___y_536_;
v___y_489_ = v___y_537_;
goto v___jp_485_;
}
}
else
{
lean_object* v___x_546_; 
lean_dec(v___x_539_);
v___x_546_ = lean_box(0);
v___y_486_ = v_gen_535_;
v_motive_487_ = v___x_546_;
v___y_488_ = v___y_536_;
v___y_489_ = v___y_537_;
goto v___jp_485_;
}
}
}
v___jp_297_:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
lean_inc_ref_n(v___y_298_, 3);
v___x_308_ = l_Array_append___redArg(v___y_298_, v___y_307_);
lean_dec_ref(v___y_307_);
lean_inc_n(v___y_302_, 3);
lean_inc_n(v___y_300_, 5);
v___x_309_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_309_, 0, v___y_300_);
lean_ctor_set(v___x_309_, 1, v___y_302_);
lean_ctor_set(v___x_309_, 2, v___x_308_);
v___x_310_ = l_Array_append___redArg(v___y_298_, v___y_306_);
lean_dec_ref(v___y_306_);
v___x_311_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_311_, 0, v___y_300_);
lean_ctor_set(v___x_311_, 1, v___y_302_);
lean_ctor_set(v___x_311_, 2, v___x_310_);
v___x_312_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__2));
v___x_313_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_313_, 0, v___y_300_);
lean_ctor_set(v___x_313_, 1, v___x_312_);
v___x_314_ = l_Array_append___redArg(v___y_298_, v___y_301_);
lean_dec_ref(v___y_301_);
v___x_315_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_315_, 0, v___y_300_);
lean_ctor_set(v___x_315_, 1, v___y_302_);
lean_ctor_set(v___x_315_, 2, v___x_314_);
lean_inc(v___y_303_);
v___x_316_ = l_Lean_Syntax_node1(v___y_300_, v___y_303_, v___x_315_);
v___x_317_ = l_Lean_Syntax_node6(v___y_300_, v___x_296_, v___y_305_, v___y_304_, v___x_309_, v___x_311_, v___x_313_, v___x_316_);
v___x_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
v___x_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
lean_ctor_set(v___x_319_, 1, v___y_299_);
return v___x_319_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___boxed(lean_object* v_stx_555_, lean_object* v_a_556_, lean_object* v_a_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Lean_Elab_Term_expandMatchAlts_x3f(v_stx_555_, v_a_556_, v_a_557_);
lean_dec_ref(v_a_556_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0(lean_object* v_as_567_, size_t v_sz_568_, size_t v_i_569_, lean_object* v_b_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
uint8_t v___x_573_; 
v___x_573_ = lean_usize_dec_lt(v_i_569_, v_sz_568_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; 
v___x_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_574_, 0, v_b_570_);
lean_ctor_set(v___x_574_, 1, v___y_572_);
return v___x_574_;
}
else
{
lean_object* v_ref_575_; lean_object* v_a_576_; uint8_t v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; size_t v___x_585_; size_t v___x_586_; 
v_ref_575_ = lean_ctor_get(v___y_571_, 0);
v_a_576_ = lean_array_uget_borrowed(v_as_567_, v_i_569_);
v___x_577_ = 0;
v___x_578_ = l_Lean_SourceInfo_fromRef(v_ref_575_, v___x_577_);
v___x_579_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__1));
v___x_580_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__2));
lean_inc_n(v___x_578_, 2);
v___x_581_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_578_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
v___x_582_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__3));
v___x_583_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_578_);
lean_ctor_set(v___x_583_, 1, v___x_582_);
lean_inc(v_a_576_);
v___x_584_ = l_Lean_Syntax_node4(v___x_578_, v___x_579_, v___x_581_, v_a_576_, v___x_583_, v_b_570_);
v___x_585_ = ((size_t)1ULL);
v___x_586_ = lean_usize_add(v_i_569_, v___x_585_);
v_i_569_ = v___x_586_;
v_b_570_ = v___x_584_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___boxed(lean_object* v_as_588_, lean_object* v_sz_589_, lean_object* v_i_590_, lean_object* v_b_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
size_t v_sz_boxed_594_; size_t v_i_boxed_595_; lean_object* v_res_596_; 
v_sz_boxed_594_ = lean_unbox_usize(v_sz_589_);
lean_dec(v_sz_589_);
v_i_boxed_595_ = lean_unbox_usize(v_i_590_);
lean_dec(v_i_590_);
v_res_596_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0(v_as_588_, v_sz_boxed_594_, v_i_boxed_595_, v_b_591_, v___y_592_, v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec_ref(v_as_588_);
return v_res_596_;
}
}
static lean_object* _init_l_Lean_Elab_Term_clearInMatchAlt___closed__0(void){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_597_ = l_Lean_firstFrontendMacroScope;
v___x_598_ = lean_box(0);
v___x_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
lean_ctor_set(v___x_599_, 1, v___x_597_);
return v___x_599_;
}
}
static lean_object* _init_l_Lean_Elab_Term_clearInMatchAlt___closed__1(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_600_ = lean_unsigned_to_nat(1u);
v___x_601_ = l_Lean_firstFrontendMacroScope;
v___x_602_ = lean_nat_add(v___x_601_, v___x_600_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatchAlt(lean_object* v_stx_603_, lean_object* v_vars_604_){
_start:
{
if (lean_obj_tag(v_stx_603_) == 1)
{
lean_object* v_info_605_; lean_object* v_kind_606_; lean_object* v_args_607_; lean_object* v___x_608_; lean_object* v___x_609_; uint8_t v___x_610_; 
v_info_605_ = lean_ctor_get(v_stx_603_, 0);
v_kind_606_ = lean_ctor_get(v_stx_603_, 1);
v_args_607_ = lean_ctor_get(v_stx_603_, 2);
v___x_608_ = lean_unsigned_to_nat(3u);
v___x_609_ = lean_array_get_size(v_args_607_);
v___x_610_ = lean_nat_dec_lt(v___x_608_, v___x_609_);
if (v___x_610_ == 0)
{
return v_stx_603_;
}
else
{
lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_627_; 
lean_inc_ref(v_args_607_);
lean_inc(v_kind_606_);
lean_inc(v_info_605_);
v_isSharedCheck_627_ = !lean_is_exclusive(v_stx_603_);
if (v_isSharedCheck_627_ == 0)
{
lean_object* v_unused_628_; lean_object* v_unused_629_; lean_object* v_unused_630_; 
v_unused_628_ = lean_ctor_get(v_stx_603_, 2);
lean_dec(v_unused_628_);
v_unused_629_ = lean_ctor_get(v_stx_603_, 1);
lean_dec(v_unused_629_);
v_unused_630_ = lean_ctor_get(v_stx_603_, 0);
lean_dec(v_unused_630_);
v___x_612_ = v_stx_603_;
v_isShared_613_ = v_isSharedCheck_627_;
goto v_resetjp_611_;
}
else
{
lean_dec(v_stx_603_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_627_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v_v_614_; size_t v_sz_615_; size_t v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v_fst_620_; lean_object* v___x_621_; lean_object* v_xs_x27_622_; lean_object* v___x_623_; lean_object* v___x_625_; 
v_v_614_ = lean_array_fget_borrowed(v_args_607_, v___x_608_);
v_sz_615_ = lean_array_size(v_vars_604_);
v___x_616_ = ((size_t)0ULL);
v___x_617_ = lean_obj_once(&l_Lean_Elab_Term_clearInMatchAlt___closed__0, &l_Lean_Elab_Term_clearInMatchAlt___closed__0_once, _init_l_Lean_Elab_Term_clearInMatchAlt___closed__0);
v___x_618_ = lean_obj_once(&l_Lean_Elab_Term_clearInMatchAlt___closed__1, &l_Lean_Elab_Term_clearInMatchAlt___closed__1_once, _init_l_Lean_Elab_Term_clearInMatchAlt___closed__1);
lean_inc(v_v_614_);
v___x_619_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0(v_vars_604_, v_sz_615_, v___x_616_, v_v_614_, v___x_617_, v___x_618_);
v_fst_620_ = lean_ctor_get(v___x_619_, 0);
lean_inc(v_fst_620_);
lean_dec_ref(v___x_619_);
v___x_621_ = lean_box(0);
v_xs_x27_622_ = lean_array_fset(v_args_607_, v___x_608_, v___x_621_);
v___x_623_ = lean_array_fset(v_xs_x27_622_, v___x_608_, v_fst_620_);
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 2, v___x_623_);
v___x_625_ = v___x_612_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_info_605_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_kind_606_);
lean_ctor_set(v_reuseFailAlloc_626_, 2, v___x_623_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
else
{
return v_stx_603_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatchAlt___boxed(lean_object* v_stx_631_, lean_object* v_vars_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Lean_Elab_Term_clearInMatchAlt(v_stx_631_, v_vars_632_);
lean_dec_ref(v_vars_632_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_clearInMatch_spec__0(lean_object* v_vars_634_, size_t v_sz_635_, size_t v_i_636_, lean_object* v_bs_637_){
_start:
{
uint8_t v___x_638_; 
v___x_638_ = lean_usize_dec_lt(v_i_636_, v_sz_635_);
if (v___x_638_ == 0)
{
return v_bs_637_;
}
else
{
lean_object* v_v_639_; lean_object* v___x_640_; lean_object* v_bs_x27_641_; lean_object* v___x_642_; size_t v___x_643_; size_t v___x_644_; lean_object* v___x_645_; 
v_v_639_ = lean_array_uget(v_bs_637_, v_i_636_);
v___x_640_ = lean_unsigned_to_nat(0u);
v_bs_x27_641_ = lean_array_uset(v_bs_637_, v_i_636_, v___x_640_);
v___x_642_ = l_Lean_Elab_Term_clearInMatchAlt(v_v_639_, v_vars_634_);
v___x_643_ = ((size_t)1ULL);
v___x_644_ = lean_usize_add(v_i_636_, v___x_643_);
v___x_645_ = lean_array_uset(v_bs_x27_641_, v_i_636_, v___x_642_);
v_i_636_ = v___x_644_;
v_bs_637_ = v___x_645_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_clearInMatch_spec__0___boxed(lean_object* v_vars_647_, lean_object* v_sz_648_, lean_object* v_i_649_, lean_object* v_bs_650_){
_start:
{
size_t v_sz_boxed_651_; size_t v_i_boxed_652_; lean_object* v_res_653_; 
v_sz_boxed_651_ = lean_unbox_usize(v_sz_648_);
lean_dec(v_sz_648_);
v_i_boxed_652_ = lean_unbox_usize(v_i_649_);
lean_dec(v_i_649_);
v_res_653_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_clearInMatch_spec__0(v_vars_647_, v_sz_boxed_651_, v_i_boxed_652_, v_bs_650_);
lean_dec_ref(v_vars_647_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatch(lean_object* v_stx_654_, lean_object* v_vars_655_, lean_object* v_a_656_, lean_object* v_a_657_){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; uint8_t v___x_660_; 
v___x_658_ = lean_array_get_size(v_vars_655_);
v___x_659_ = lean_unsigned_to_nat(0u);
v___x_660_ = lean_nat_dec_eq(v___x_658_, v___x_659_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_702_; lean_object* v_motive_703_; lean_object* v___y_704_; lean_object* v___y_705_; uint8_t v___x_727_; 
v___x_661_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__0));
v___x_662_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1));
lean_inc(v_stx_654_);
v___x_727_ = l_Lean_Syntax_isOfKind(v_stx_654_, v___x_662_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; 
v___x_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_728_, 0, v_stx_654_);
lean_ctor_set(v___x_728_, 1, v_a_657_);
return v___x_728_;
}
else
{
lean_object* v___x_729_; lean_object* v_gen_731_; lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v___x_742_; uint8_t v___x_743_; 
v___x_729_ = lean_unsigned_to_nat(1u);
v___x_742_ = l_Lean_Syntax_getArg(v_stx_654_, v___x_729_);
v___x_743_ = l_Lean_Syntax_isNone(v___x_742_);
if (v___x_743_ == 0)
{
uint8_t v___x_744_; 
lean_inc(v___x_742_);
v___x_744_ = l_Lean_Syntax_matchesNull(v___x_742_, v___x_729_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; 
lean_dec(v___x_742_);
v___x_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_745_, 0, v_stx_654_);
lean_ctor_set(v___x_745_, 1, v_a_657_);
return v___x_745_;
}
else
{
lean_object* v_gen_746_; lean_object* v___x_747_; 
v_gen_746_ = l_Lean_Syntax_getArg(v___x_742_, v___x_659_);
lean_dec(v___x_742_);
v___x_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_747_, 0, v_gen_746_);
v_gen_731_ = v___x_747_;
v___y_732_ = v_a_656_;
v___y_733_ = v_a_657_;
goto v___jp_730_;
}
}
else
{
lean_object* v___x_748_; 
lean_dec(v___x_742_);
v___x_748_ = lean_box(0);
v_gen_731_ = v___x_748_;
v___y_732_ = v_a_656_;
v___y_733_ = v_a_657_;
goto v___jp_730_;
}
v___jp_730_:
{
lean_object* v___x_734_; lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_734_ = lean_unsigned_to_nat(2u);
v___x_735_ = l_Lean_Syntax_getArg(v_stx_654_, v___x_734_);
v___x_736_ = l_Lean_Syntax_isNone(v___x_735_);
if (v___x_736_ == 0)
{
uint8_t v___x_737_; 
lean_inc(v___x_735_);
v___x_737_ = l_Lean_Syntax_matchesNull(v___x_735_, v___x_729_);
if (v___x_737_ == 0)
{
lean_object* v___x_738_; 
lean_dec(v___x_735_);
lean_dec(v_gen_731_);
v___x_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_738_, 0, v_stx_654_);
lean_ctor_set(v___x_738_, 1, v___y_733_);
return v___x_738_;
}
else
{
lean_object* v_motive_739_; lean_object* v___x_740_; 
v_motive_739_ = l_Lean_Syntax_getArg(v___x_735_, v___x_659_);
lean_dec(v___x_735_);
v___x_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_740_, 0, v_motive_739_);
v___y_702_ = v_gen_731_;
v_motive_703_ = v___x_740_;
v___y_704_ = v___y_732_;
v___y_705_ = v___y_733_;
goto v___jp_701_;
}
}
else
{
lean_object* v___x_741_; 
lean_dec(v___x_735_);
v___x_741_ = lean_box(0);
v___y_702_ = v_gen_731_;
v_motive_703_ = v___x_741_;
v___y_704_ = v___y_732_;
v___y_705_ = v___y_733_;
goto v___jp_701_;
}
}
}
v___jp_663_:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
lean_inc_ref_n(v___y_665_, 3);
v___x_674_ = l_Array_append___redArg(v___y_665_, v___y_673_);
lean_dec_ref(v___y_673_);
lean_inc_n(v___y_664_, 3);
lean_inc_n(v___y_668_, 5);
v___x_675_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_675_, 0, v___y_668_);
lean_ctor_set(v___x_675_, 1, v___y_664_);
lean_ctor_set(v___x_675_, 2, v___x_674_);
v___x_676_ = l_Array_append___redArg(v___y_665_, v___y_672_);
lean_dec_ref(v___y_672_);
v___x_677_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_677_, 0, v___y_668_);
lean_ctor_set(v___x_677_, 1, v___y_664_);
lean_ctor_set(v___x_677_, 2, v___x_676_);
v___x_678_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__2));
v___x_679_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_679_, 0, v___y_668_);
lean_ctor_set(v___x_679_, 1, v___x_678_);
v___x_680_ = l_Array_append___redArg(v___y_665_, v___y_667_);
lean_dec_ref(v___y_667_);
v___x_681_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_681_, 0, v___y_668_);
lean_ctor_set(v___x_681_, 1, v___y_664_);
lean_ctor_set(v___x_681_, 2, v___x_680_);
lean_inc(v___y_671_);
v___x_682_ = l_Lean_Syntax_node1(v___y_668_, v___y_671_, v___x_681_);
v___x_683_ = l_Lean_Syntax_node6(v___y_668_, v___x_662_, v___y_669_, v___y_666_, v___x_675_, v___x_677_, v___x_679_, v___x_682_);
v___x_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
lean_ctor_set(v___x_684_, 1, v___y_670_);
return v___x_684_;
}
v___jp_685_:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
lean_inc_ref(v___y_688_);
v___x_696_ = l_Array_append___redArg(v___y_688_, v___y_695_);
lean_dec_ref(v___y_695_);
lean_inc(v___y_687_);
lean_inc(v___y_690_);
v___x_697_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_697_, 0, v___y_690_);
lean_ctor_set(v___x_697_, 1, v___y_687_);
lean_ctor_set(v___x_697_, 2, v___x_696_);
if (lean_obj_tag(v___y_686_) == 1)
{
lean_object* v_val_698_; lean_object* v___x_699_; 
v_val_698_ = lean_ctor_get(v___y_686_, 0);
lean_inc(v_val_698_);
lean_dec_ref(v___y_686_);
v___x_699_ = l_Array_mkArray1___redArg(v_val_698_);
v___y_664_ = v___y_687_;
v___y_665_ = v___y_688_;
v___y_666_ = v___x_697_;
v___y_667_ = v___y_689_;
v___y_668_ = v___y_690_;
v___y_669_ = v___y_691_;
v___y_670_ = v___y_692_;
v___y_671_ = v___y_693_;
v___y_672_ = v___y_694_;
v___y_673_ = v___x_699_;
goto v___jp_663_;
}
else
{
lean_object* v___x_700_; 
lean_dec(v___y_686_);
v___x_700_ = ((lean_object*)(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5));
v___y_664_ = v___y_687_;
v___y_665_ = v___y_688_;
v___y_666_ = v___x_697_;
v___y_667_ = v___y_689_;
v___y_668_ = v___y_690_;
v___y_669_ = v___y_691_;
v___y_670_ = v___y_692_;
v___y_671_ = v___y_693_;
v___y_672_ = v___y_694_;
v___y_673_ = v___x_700_;
goto v___jp_663_;
}
}
v___jp_701_:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; uint8_t v___x_709_; 
v___x_706_ = lean_unsigned_to_nat(5u);
v___x_707_ = l_Lean_Syntax_getArg(v_stx_654_, v___x_706_);
v___x_708_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6));
lean_inc(v___x_707_);
v___x_709_ = l_Lean_Syntax_isOfKind(v___x_707_, v___x_708_);
if (v___x_709_ == 0)
{
lean_object* v___x_710_; 
lean_dec(v___x_707_);
lean_dec(v_motive_703_);
lean_dec(v___y_702_);
v___x_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_710_, 0, v_stx_654_);
lean_ctor_set(v___x_710_, 1, v___y_705_);
return v___x_710_;
}
else
{
lean_object* v_ref_711_; lean_object* v___x_712_; lean_object* v_alts_713_; size_t v_sz_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; size_t v___x_718_; lean_object* v_alts_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v_ref_711_ = lean_ctor_get(v___y_704_, 5);
v___x_712_ = l_Lean_Syntax_getArg(v___x_707_, v___x_659_);
lean_dec(v___x_707_);
v_alts_713_ = l_Lean_Syntax_getArgs(v___x_712_);
lean_dec(v___x_712_);
v_sz_714_ = lean_array_size(v_alts_713_);
v___x_715_ = lean_unsigned_to_nat(3u);
v___x_716_ = l_Lean_Syntax_getArg(v_stx_654_, v___x_715_);
lean_dec(v_stx_654_);
v___x_717_ = l_Lean_Syntax_getArgs(v___x_716_);
lean_dec(v___x_716_);
v___x_718_ = ((size_t)0ULL);
v_alts_719_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_clearInMatch_spec__0(v_vars_655_, v_sz_714_, v___x_718_, v_alts_713_);
v___x_720_ = l_Lean_SourceInfo_fromRef(v_ref_711_, v___x_660_);
lean_inc(v___x_720_);
v___x_721_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
lean_ctor_set(v___x_721_, 1, v___x_661_);
v___x_722_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__1));
v___x_723_ = lean_obj_once(&l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7, &l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7_once, _init_l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7);
if (lean_obj_tag(v___y_702_) == 1)
{
lean_object* v_val_724_; lean_object* v___x_725_; 
v_val_724_ = lean_ctor_get(v___y_702_, 0);
lean_inc(v_val_724_);
lean_dec_ref(v___y_702_);
v___x_725_ = l_Array_mkArray1___redArg(v_val_724_);
v___y_686_ = v_motive_703_;
v___y_687_ = v___x_722_;
v___y_688_ = v___x_723_;
v___y_689_ = v_alts_719_;
v___y_690_ = v___x_720_;
v___y_691_ = v___x_721_;
v___y_692_ = v___y_705_;
v___y_693_ = v___x_708_;
v___y_694_ = v___x_717_;
v___y_695_ = v___x_725_;
goto v___jp_685_;
}
else
{
lean_object* v___x_726_; 
lean_dec(v___y_702_);
v___x_726_ = ((lean_object*)(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5));
v___y_686_ = v_motive_703_;
v___y_687_ = v___x_722_;
v___y_688_ = v___x_723_;
v___y_689_ = v_alts_719_;
v___y_690_ = v___x_720_;
v___y_691_ = v___x_721_;
v___y_692_ = v___y_705_;
v___y_693_ = v___x_708_;
v___y_694_ = v___x_717_;
v___y_695_ = v___x_726_;
goto v___jp_685_;
}
}
}
}
else
{
lean_object* v___x_749_; 
v___x_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_749_, 0, v_stx_654_);
lean_ctor_set(v___x_749_, 1, v_a_657_);
return v___x_749_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatch___boxed(lean_object* v_stx_750_, lean_object* v_vars_751_, lean_object* v_a_752_, lean_object* v_a_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Lean_Elab_Term_clearInMatch(v_stx_750_, v_vars_751_, v_a_752_, v_a_753_);
lean_dec_ref(v_a_752_);
lean_dec_ref(v_vars_751_);
return v_res_754_;
}
}
lean_object* runtime_initialize_Lean_Parser_Term(uint8_t builtin);
lean_object* runtime_initialize_Init_Syntax(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_BindersUtil(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Term(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Do(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_BindersUtil(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Lean_Elab_BindersUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_BindersUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_BindersUtil(builtin);
}
#ifdef __cplusplus
}
#endif
