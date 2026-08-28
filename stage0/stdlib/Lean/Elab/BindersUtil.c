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
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
uint8_t v___x_404__boxed_130_; size_t v_i_boxed_131_; size_t v_stop_boxed_132_; lean_object* v_res_133_; 
v___x_404__boxed_130_ = lean_unbox(v___x_125_);
v_i_boxed_131_ = lean_unbox_usize(v_i_127_);
lean_dec(v_i_127_);
v_stop_boxed_132_ = lean_unbox_usize(v_stop_128_);
lean_dec(v_stop_128_);
v_res_133_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__1(v___x_404__boxed_130_, v_as_126_, v_i_boxed_131_, v_stop_boxed_132_, v_b_129_);
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
lean_object* v___x_164_; lean_object* v___x_165_; size_t v___x_166_; size_t v___x_167_; lean_object* v___x_168_; lean_object* v_snd_169_; 
v___x_164_ = lean_box(v___x_163_);
v___x_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
lean_ctor_set(v___x_165_, 1, v___x_161_);
v___x_166_ = ((size_t)0ULL);
v___x_167_ = lean_usize_of_nat(v___x_162_);
v___x_168_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__1(v___x_147_, v___x_159_, v___x_166_, v___x_167_, v___x_165_);
lean_dec_ref(v___x_159_);
v_snd_169_ = lean_ctor_get(v___x_168_, 1);
lean_inc(v_snd_169_);
lean_dec_ref(v___x_168_);
v___y_150_ = v_snd_169_;
goto v___jp_149_;
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
lean_dec_ref_known(v___x_153_, 1);
v___x_156_ = lean_array_get_size(v_val_155_);
lean_dec(v_val_155_);
v___x_157_ = lean_nat_dec_lt(v___x_148_, v___x_156_);
return v___x_157_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_shouldExpandMatchAlt___boxed(lean_object* v_x_170_){
_start:
{
uint8_t v_res_171_; lean_object* v_r_172_; 
v_res_171_ = l_Lean_Elab_Term_shouldExpandMatchAlt(v_x_170_);
v_r_172_ = lean_box(v_res_171_);
return v_r_172_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___redArg(lean_object* v_as_173_, size_t v_i_174_, size_t v_stop_175_, lean_object* v_b_176_, lean_object* v___y_177_){
_start:
{
uint8_t v___x_178_; 
v___x_178_ = lean_usize_dec_eq(v_i_174_, v_stop_175_);
if (v___x_178_ == 0)
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; size_t v___x_182_; size_t v___x_183_; 
v___x_179_ = lean_array_uget_borrowed(v_as_173_, v_i_174_);
lean_inc(v___x_179_);
v___x_180_ = l_Lean_Elab_Term_expandMatchAlt(v___x_179_);
v___x_181_ = l_Array_append___redArg(v_b_176_, v___x_180_);
lean_dec_ref(v___x_180_);
v___x_182_ = ((size_t)1ULL);
v___x_183_ = lean_usize_add(v_i_174_, v___x_182_);
v_i_174_ = v___x_183_;
v_b_176_ = v___x_181_;
goto _start;
}
else
{
lean_object* v___x_185_; 
v___x_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_185_, 0, v_b_176_);
lean_ctor_set(v___x_185_, 1, v___y_177_);
return v___x_185_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___redArg___boxed(lean_object* v_as_186_, lean_object* v_i_187_, lean_object* v_stop_188_, lean_object* v_b_189_, lean_object* v___y_190_){
_start:
{
size_t v_i_boxed_191_; size_t v_stop_boxed_192_; lean_object* v_res_193_; 
v_i_boxed_191_ = lean_unbox_usize(v_i_187_);
lean_dec(v_i_187_);
v_stop_boxed_192_ = lean_unbox_usize(v_stop_188_);
lean_dec(v_stop_188_);
v_res_193_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___redArg(v_as_186_, v_i_boxed_191_, v_stop_boxed_192_, v_b_189_, v___y_190_);
lean_dec_ref(v_as_186_);
return v_res_193_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__0(lean_object* v_as_194_, size_t v_i_195_, size_t v_stop_196_){
_start:
{
uint8_t v___x_197_; 
v___x_197_ = lean_usize_dec_eq(v_i_195_, v_stop_196_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; uint8_t v___x_199_; 
v___x_198_ = lean_array_uget_borrowed(v_as_194_, v_i_195_);
lean_inc(v___x_198_);
v___x_199_ = l_Lean_Elab_Term_shouldExpandMatchAlt(v___x_198_);
if (v___x_199_ == 0)
{
size_t v___x_200_; size_t v___x_201_; 
v___x_200_ = ((size_t)1ULL);
v___x_201_ = lean_usize_add(v_i_195_, v___x_200_);
v_i_195_ = v___x_201_;
goto _start;
}
else
{
return v___x_199_;
}
}
else
{
uint8_t v___x_203_; 
v___x_203_ = 0;
return v___x_203_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__0___boxed(lean_object* v_as_204_, lean_object* v_i_205_, lean_object* v_stop_206_){
_start:
{
size_t v_i_boxed_207_; size_t v_stop_boxed_208_; uint8_t v_res_209_; lean_object* v_r_210_; 
v_i_boxed_207_ = lean_unbox_usize(v_i_205_);
lean_dec(v_i_205_);
v_stop_boxed_208_ = lean_unbox_usize(v_stop_206_);
lean_dec(v_stop_206_);
v_res_209_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__0(v_as_204_, v_i_boxed_207_, v_stop_boxed_208_);
lean_dec_ref(v_as_204_);
v_r_210_ = lean_box(v_res_209_);
return v_r_210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand(lean_object* v_alts_213_, lean_object* v_a_214_, lean_object* v_a_215_){
_start:
{
lean_object* v_a_220_; lean_object* v_a_221_; lean_object* v___y_225_; lean_object* v___x_237_; lean_object* v___x_238_; uint8_t v___x_239_; 
v___x_237_ = lean_unsigned_to_nat(0u);
v___x_238_ = lean_array_get_size(v_alts_213_);
v___x_239_ = lean_nat_dec_lt(v___x_237_, v___x_238_);
if (v___x_239_ == 0)
{
goto v___jp_216_;
}
else
{
if (v___x_239_ == 0)
{
goto v___jp_216_;
}
else
{
size_t v___x_240_; size_t v___x_241_; uint8_t v___x_242_; 
v___x_240_ = ((size_t)0ULL);
v___x_241_ = lean_usize_of_nat(v___x_238_);
v___x_242_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__0(v_alts_213_, v___x_240_, v___x_241_);
if (v___x_242_ == 0)
{
goto v___jp_216_;
}
else
{
lean_object* v___x_243_; 
v___x_243_ = ((lean_object*)(l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand___closed__0));
if (v___x_239_ == 0)
{
v_a_220_ = v___x_243_;
v_a_221_ = v_a_215_;
goto v___jp_219_;
}
else
{
uint8_t v___x_244_; 
v___x_244_ = lean_nat_dec_le(v___x_238_, v___x_238_);
if (v___x_244_ == 0)
{
if (v___x_239_ == 0)
{
v_a_220_ = v___x_243_;
v_a_221_ = v_a_215_;
goto v___jp_219_;
}
else
{
lean_object* v___x_245_; 
v___x_245_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___redArg(v_alts_213_, v___x_240_, v___x_241_, v___x_243_, v_a_215_);
v___y_225_ = v___x_245_;
goto v___jp_224_;
}
}
else
{
lean_object* v___x_246_; 
v___x_246_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___redArg(v_alts_213_, v___x_240_, v___x_241_, v___x_243_, v_a_215_);
v___y_225_ = v___x_246_;
goto v___jp_224_;
}
}
}
}
}
v___jp_216_:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = lean_box(0);
v___x_218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
lean_ctor_set(v___x_218_, 1, v_a_215_);
return v___x_218_;
}
v___jp_219_:
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_222_, 0, v_a_220_);
v___x_223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
lean_ctor_set(v___x_223_, 1, v_a_221_);
return v___x_223_;
}
v___jp_224_:
{
if (lean_obj_tag(v___y_225_) == 0)
{
lean_object* v_a_226_; lean_object* v_a_227_; 
v_a_226_ = lean_ctor_get(v___y_225_, 0);
lean_inc(v_a_226_);
v_a_227_ = lean_ctor_get(v___y_225_, 1);
lean_inc(v_a_227_);
lean_dec_ref_known(v___y_225_, 2);
v_a_220_ = v_a_226_;
v_a_221_ = v_a_227_;
goto v___jp_219_;
}
else
{
lean_object* v_a_228_; lean_object* v_a_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_236_; 
v_a_228_ = lean_ctor_get(v___y_225_, 0);
v_a_229_ = lean_ctor_get(v___y_225_, 1);
v_isSharedCheck_236_ = !lean_is_exclusive(v___y_225_);
if (v_isSharedCheck_236_ == 0)
{
v___x_231_ = v___y_225_;
v_isShared_232_ = v_isSharedCheck_236_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_a_229_);
lean_inc(v_a_228_);
lean_dec(v___y_225_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_236_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_234_; 
if (v_isShared_232_ == 0)
{
v___x_234_ = v___x_231_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v_a_228_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v_a_229_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand___boxed(lean_object* v_alts_247_, lean_object* v_a_248_, lean_object* v_a_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand(v_alts_247_, v_a_248_, v_a_249_);
lean_dec_ref(v_a_248_);
lean_dec_ref(v_alts_247_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1(lean_object* v_as_251_, size_t v_i_252_, size_t v_stop_253_, lean_object* v_b_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___redArg(v_as_251_, v_i_252_, v_stop_253_, v_b_254_, v___y_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___boxed(lean_object* v_as_258_, lean_object* v_i_259_, lean_object* v_stop_260_, lean_object* v_b_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
size_t v_i_boxed_264_; size_t v_stop_boxed_265_; lean_object* v_res_266_; 
v_i_boxed_264_ = lean_unbox_usize(v_i_259_);
lean_dec(v_i_259_);
v_stop_boxed_265_ = lean_unbox_usize(v_stop_260_);
lean_dec(v_stop_260_);
v_res_266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1(v_as_258_, v_i_boxed_264_, v_stop_boxed_265_, v_b_261_, v___y_262_, v___y_263_);
lean_dec_ref(v___y_262_);
lean_dec_ref(v_as_258_);
return v_res_266_;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7(void){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = l_Array_mkArray0(lean_box(0));
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f(lean_object* v_stx_287_, lean_object* v_a_288_, lean_object* v_a_289_){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___y_293_; lean_object* v___y_294_; lean_object* v___y_295_; lean_object* v___y_296_; lean_object* v___y_297_; lean_object* v___y_298_; lean_object* v___y_299_; lean_object* v___y_300_; lean_object* v___y_301_; lean_object* v___y_302_; uint8_t v___x_315_; 
v___x_290_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__0));
v___x_291_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1));
lean_inc(v_stx_287_);
v___x_315_ = l_Lean_Syntax_isOfKind(v_stx_287_, v___x_291_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; lean_object* v___y_318_; lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___y_321_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___y_324_; lean_object* v___y_325_; lean_object* v___y_326_; lean_object* v___y_327_; lean_object* v___y_328_; uint8_t v___x_341_; 
v___x_316_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__4));
lean_inc(v_stx_287_);
v___x_341_ = l_Lean_Syntax_isOfKind(v_stx_287_, v___x_316_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; lean_object* v___x_343_; 
lean_dec(v_stx_287_);
v___x_342_ = lean_box(0);
v___x_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v_a_289_);
return v___x_343_;
}
else
{
lean_object* v___x_344_; lean_object* v___y_346_; lean_object* v___y_347_; lean_object* v___y_348_; lean_object* v___y_349_; lean_object* v___y_350_; lean_object* v___y_351_; lean_object* v___y_352_; lean_object* v___y_353_; lean_object* v___y_354_; lean_object* v___y_355_; lean_object* v___y_356_; lean_object* v___y_363_; lean_object* v___y_364_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___y_367_; lean_object* v___y_368_; lean_object* v___y_369_; lean_object* v___y_370_; lean_object* v___y_371_; lean_object* v___y_372_; lean_object* v___y_373_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v_motive_382_; lean_object* v___y_383_; lean_object* v___y_384_; lean_object* v___x_427_; lean_object* v___y_429_; lean_object* v_gen_430_; lean_object* v___y_431_; lean_object* v___y_432_; lean_object* v_dep_x3f_443_; lean_object* v___y_444_; lean_object* v___y_445_; lean_object* v___x_455_; uint8_t v___x_456_; 
v___x_344_ = lean_unsigned_to_nat(0u);
v___x_427_ = lean_unsigned_to_nat(1u);
v___x_455_ = l_Lean_Syntax_getArg(v_stx_287_, v___x_427_);
v___x_456_ = l_Lean_Syntax_isNone(v___x_455_);
if (v___x_456_ == 0)
{
uint8_t v___x_457_; 
lean_inc(v___x_455_);
v___x_457_ = l_Lean_Syntax_matchesNull(v___x_455_, v___x_427_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; lean_object* v___x_459_; 
lean_dec(v___x_455_);
lean_dec(v_stx_287_);
v___x_458_ = lean_box(0);
v___x_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
lean_ctor_set(v___x_459_, 1, v_a_289_);
return v___x_459_;
}
else
{
lean_object* v_dep_x3f_460_; lean_object* v___x_461_; 
v_dep_x3f_460_ = l_Lean_Syntax_getArg(v___x_455_, v___x_344_);
lean_dec(v___x_455_);
v___x_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_461_, 0, v_dep_x3f_460_);
v_dep_x3f_443_ = v___x_461_;
v___y_444_ = v_a_288_;
v___y_445_ = v_a_289_;
goto v___jp_442_;
}
}
else
{
lean_object* v___x_462_; 
lean_dec(v___x_455_);
v___x_462_ = lean_box(0);
v_dep_x3f_443_ = v___x_462_;
v___y_444_ = v_a_288_;
v___y_445_ = v_a_289_;
goto v___jp_442_;
}
v___jp_345_:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
lean_inc_ref(v___y_354_);
v___x_357_ = l_Array_append___redArg(v___y_354_, v___y_356_);
lean_dec_ref(v___y_356_);
lean_inc(v___y_353_);
lean_inc(v___y_347_);
v___x_358_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_358_, 0, v___y_347_);
lean_ctor_set(v___x_358_, 1, v___y_353_);
lean_ctor_set(v___x_358_, 2, v___x_357_);
if (lean_obj_tag(v___y_355_) == 1)
{
lean_object* v_val_359_; lean_object* v___x_360_; 
v_val_359_ = lean_ctor_get(v___y_355_, 0);
lean_inc(v_val_359_);
lean_dec_ref_known(v___y_355_, 1);
v___x_360_ = l_Array_mkArray1___redArg(v_val_359_);
v___y_318_ = v___y_346_;
v___y_319_ = v___y_347_;
v___y_320_ = v___y_348_;
v___y_321_ = v___y_349_;
v___y_322_ = v___y_350_;
v___y_323_ = v___x_358_;
v___y_324_ = v___y_351_;
v___y_325_ = v___y_352_;
v___y_326_ = v___y_353_;
v___y_327_ = v___y_354_;
v___y_328_ = v___x_360_;
goto v___jp_317_;
}
else
{
lean_object* v___x_361_; 
lean_dec(v___y_355_);
v___x_361_ = ((lean_object*)(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5));
v___y_318_ = v___y_346_;
v___y_319_ = v___y_347_;
v___y_320_ = v___y_348_;
v___y_321_ = v___y_349_;
v___y_322_ = v___y_350_;
v___y_323_ = v___x_358_;
v___y_324_ = v___y_351_;
v___y_325_ = v___y_352_;
v___y_326_ = v___y_353_;
v___y_327_ = v___y_354_;
v___y_328_ = v___x_361_;
goto v___jp_317_;
}
}
v___jp_362_:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
lean_inc_ref(v___y_371_);
v___x_374_ = l_Array_append___redArg(v___y_371_, v___y_373_);
lean_dec_ref(v___y_373_);
lean_inc(v___y_370_);
lean_inc(v___y_364_);
v___x_375_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_375_, 0, v___y_364_);
lean_ctor_set(v___x_375_, 1, v___y_370_);
lean_ctor_set(v___x_375_, 2, v___x_374_);
if (lean_obj_tag(v___y_366_) == 1)
{
lean_object* v_val_376_; lean_object* v___x_377_; 
v_val_376_ = lean_ctor_get(v___y_366_, 0);
lean_inc(v_val_376_);
lean_dec_ref_known(v___y_366_, 1);
v___x_377_ = l_Array_mkArray1___redArg(v_val_376_);
v___y_346_ = v___y_363_;
v___y_347_ = v___y_364_;
v___y_348_ = v___x_375_;
v___y_349_ = v___y_365_;
v___y_350_ = v___y_367_;
v___y_351_ = v___y_368_;
v___y_352_ = v___y_369_;
v___y_353_ = v___y_370_;
v___y_354_ = v___y_371_;
v___y_355_ = v___y_372_;
v___y_356_ = v___x_377_;
goto v___jp_345_;
}
else
{
lean_object* v___x_378_; 
lean_dec(v___y_366_);
v___x_378_ = ((lean_object*)(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5));
v___y_346_ = v___y_363_;
v___y_347_ = v___y_364_;
v___y_348_ = v___x_375_;
v___y_349_ = v___y_365_;
v___y_350_ = v___y_367_;
v___y_351_ = v___y_368_;
v___y_352_ = v___y_369_;
v___y_353_ = v___y_370_;
v___y_354_ = v___y_371_;
v___y_355_ = v___y_372_;
v___y_356_ = v___x_378_;
goto v___jp_345_;
}
}
v___jp_379_:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; uint8_t v___x_388_; 
v___x_385_ = lean_unsigned_to_nat(6u);
v___x_386_ = l_Lean_Syntax_getArg(v_stx_287_, v___x_385_);
v___x_387_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6));
lean_inc(v___x_386_);
v___x_388_ = l_Lean_Syntax_isOfKind(v___x_386_, v___x_387_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; lean_object* v___x_390_; 
lean_dec(v___x_386_);
lean_dec(v_motive_382_);
lean_dec(v___y_381_);
lean_dec(v___y_380_);
lean_dec(v_stx_287_);
v___x_389_ = lean_box(0);
v___x_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
lean_ctor_set(v___x_390_, 1, v___y_384_);
return v___x_390_;
}
else
{
lean_object* v___x_391_; lean_object* v_alts_392_; lean_object* v___x_393_; 
v___x_391_ = l_Lean_Syntax_getArg(v___x_386_, v___x_344_);
lean_dec(v___x_386_);
v_alts_392_ = l_Lean_Syntax_getArgs(v___x_391_);
lean_dec(v___x_391_);
v___x_393_ = l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand(v_alts_392_, v___y_383_, v___y_384_);
lean_dec_ref(v_alts_392_);
if (lean_obj_tag(v___x_393_) == 0)
{
lean_object* v_a_394_; 
v_a_394_ = lean_ctor_get(v___x_393_, 0);
lean_inc(v_a_394_);
if (lean_obj_tag(v_a_394_) == 0)
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_403_; 
lean_dec(v_motive_382_);
lean_dec(v___y_381_);
lean_dec(v___y_380_);
lean_dec(v_stx_287_);
v_a_395_ = lean_ctor_get(v___x_393_, 1);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_403_ == 0)
{
lean_object* v_unused_404_; 
v_unused_404_ = lean_ctor_get(v___x_393_, 0);
lean_dec(v_unused_404_);
v___x_397_ = v___x_393_;
v_isShared_398_ = v_isSharedCheck_403_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_393_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_403_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_399_; lean_object* v___x_401_; 
v___x_399_ = lean_box(0);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 0, v___x_399_);
v___x_401_ = v___x_397_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_399_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v_a_395_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
else
{
lean_object* v_a_405_; lean_object* v_val_406_; lean_object* v_ref_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v_a_405_ = lean_ctor_get(v___x_393_, 1);
lean_inc(v_a_405_);
lean_dec_ref_known(v___x_393_, 2);
v_val_406_ = lean_ctor_get(v_a_394_, 0);
lean_inc(v_val_406_);
lean_dec_ref_known(v_a_394_, 1);
v_ref_407_ = lean_ctor_get(v___y_383_, 5);
v___x_408_ = lean_unsigned_to_nat(4u);
v___x_409_ = l_Lean_Syntax_getArg(v_stx_287_, v___x_408_);
lean_dec(v_stx_287_);
v___x_410_ = l_Lean_Syntax_getArgs(v___x_409_);
lean_dec(v___x_409_);
v___x_411_ = l_Lean_SourceInfo_fromRef(v_ref_407_, v___x_315_);
lean_inc(v___x_411_);
v___x_412_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
lean_ctor_set(v___x_412_, 1, v___x_290_);
v___x_413_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__1));
v___x_414_ = lean_obj_once(&l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7, &l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7_once, _init_l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7);
if (lean_obj_tag(v___y_381_) == 1)
{
lean_object* v_val_415_; lean_object* v___x_416_; 
v_val_415_ = lean_ctor_get(v___y_381_, 0);
lean_inc(v_val_415_);
lean_dec_ref_known(v___y_381_, 1);
v___x_416_ = l_Array_mkArray1___redArg(v_val_415_);
v___y_363_ = v___x_410_;
v___y_364_ = v___x_411_;
v___y_365_ = v_a_405_;
v___y_366_ = v___y_380_;
v___y_367_ = v___x_387_;
v___y_368_ = v___x_412_;
v___y_369_ = v_val_406_;
v___y_370_ = v___x_413_;
v___y_371_ = v___x_414_;
v___y_372_ = v_motive_382_;
v___y_373_ = v___x_416_;
goto v___jp_362_;
}
else
{
lean_object* v___x_417_; 
lean_dec(v___y_381_);
v___x_417_ = ((lean_object*)(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5));
v___y_363_ = v___x_410_;
v___y_364_ = v___x_411_;
v___y_365_ = v_a_405_;
v___y_366_ = v___y_380_;
v___y_367_ = v___x_387_;
v___y_368_ = v___x_412_;
v___y_369_ = v_val_406_;
v___y_370_ = v___x_413_;
v___y_371_ = v___x_414_;
v___y_372_ = v_motive_382_;
v___y_373_ = v___x_417_;
goto v___jp_362_;
}
}
}
else
{
lean_object* v_a_418_; lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_426_; 
lean_dec(v_motive_382_);
lean_dec(v___y_381_);
lean_dec(v___y_380_);
lean_dec(v_stx_287_);
v_a_418_ = lean_ctor_get(v___x_393_, 0);
v_a_419_ = lean_ctor_get(v___x_393_, 1);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_426_ == 0)
{
v___x_421_ = v___x_393_;
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_inc(v_a_418_);
lean_dec(v___x_393_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_424_; 
if (v_isShared_422_ == 0)
{
v___x_424_ = v___x_421_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_a_418_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v_a_419_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
}
v___jp_428_:
{
lean_object* v___x_433_; lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_433_ = lean_unsigned_to_nat(3u);
v___x_434_ = l_Lean_Syntax_getArg(v_stx_287_, v___x_433_);
v___x_435_ = l_Lean_Syntax_isNone(v___x_434_);
if (v___x_435_ == 0)
{
uint8_t v___x_436_; 
lean_inc(v___x_434_);
v___x_436_ = l_Lean_Syntax_matchesNull(v___x_434_, v___x_427_);
if (v___x_436_ == 0)
{
lean_object* v___x_437_; lean_object* v___x_438_; 
lean_dec(v___x_434_);
lean_dec(v_gen_430_);
lean_dec(v___y_429_);
lean_dec(v_stx_287_);
v___x_437_ = lean_box(0);
v___x_438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
lean_ctor_set(v___x_438_, 1, v___y_432_);
return v___x_438_;
}
else
{
lean_object* v_motive_439_; lean_object* v___x_440_; 
v_motive_439_ = l_Lean_Syntax_getArg(v___x_434_, v___x_344_);
lean_dec(v___x_434_);
v___x_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_440_, 0, v_motive_439_);
v___y_380_ = v_gen_430_;
v___y_381_ = v___y_429_;
v_motive_382_ = v___x_440_;
v___y_383_ = v___y_431_;
v___y_384_ = v___y_432_;
goto v___jp_379_;
}
}
else
{
lean_object* v___x_441_; 
lean_dec(v___x_434_);
v___x_441_ = lean_box(0);
v___y_380_ = v_gen_430_;
v___y_381_ = v___y_429_;
v_motive_382_ = v___x_441_;
v___y_383_ = v___y_431_;
v___y_384_ = v___y_432_;
goto v___jp_379_;
}
}
v___jp_442_:
{
lean_object* v___x_446_; lean_object* v___x_447_; uint8_t v___x_448_; 
v___x_446_ = lean_unsigned_to_nat(2u);
v___x_447_ = l_Lean_Syntax_getArg(v_stx_287_, v___x_446_);
v___x_448_ = l_Lean_Syntax_isNone(v___x_447_);
if (v___x_448_ == 0)
{
uint8_t v___x_449_; 
lean_inc(v___x_447_);
v___x_449_ = l_Lean_Syntax_matchesNull(v___x_447_, v___x_427_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; lean_object* v___x_451_; 
lean_dec(v___x_447_);
lean_dec(v_dep_x3f_443_);
lean_dec(v_stx_287_);
v___x_450_ = lean_box(0);
v___x_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_451_, 0, v___x_450_);
lean_ctor_set(v___x_451_, 1, v___y_445_);
return v___x_451_;
}
else
{
lean_object* v_gen_452_; lean_object* v___x_453_; 
v_gen_452_ = l_Lean_Syntax_getArg(v___x_447_, v___x_344_);
lean_dec(v___x_447_);
v___x_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_453_, 0, v_gen_452_);
v___y_429_ = v_dep_x3f_443_;
v_gen_430_ = v___x_453_;
v___y_431_ = v___y_444_;
v___y_432_ = v___y_445_;
goto v___jp_428_;
}
}
else
{
lean_object* v___x_454_; 
lean_dec(v___x_447_);
v___x_454_ = lean_box(0);
v___y_429_ = v_dep_x3f_443_;
v_gen_430_ = v___x_454_;
v___y_431_ = v___y_444_;
v___y_432_ = v___y_445_;
goto v___jp_428_;
}
}
}
v___jp_317_:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
lean_inc_ref_n(v___y_327_, 3);
v___x_329_ = l_Array_append___redArg(v___y_327_, v___y_328_);
lean_dec_ref(v___y_328_);
lean_inc_n(v___y_326_, 3);
lean_inc_n(v___y_319_, 5);
v___x_330_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_330_, 0, v___y_319_);
lean_ctor_set(v___x_330_, 1, v___y_326_);
lean_ctor_set(v___x_330_, 2, v___x_329_);
v___x_331_ = l_Array_append___redArg(v___y_327_, v___y_318_);
lean_dec_ref(v___y_318_);
v___x_332_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_332_, 0, v___y_319_);
lean_ctor_set(v___x_332_, 1, v___y_326_);
lean_ctor_set(v___x_332_, 2, v___x_331_);
v___x_333_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__2));
v___x_334_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_334_, 0, v___y_319_);
lean_ctor_set(v___x_334_, 1, v___x_333_);
v___x_335_ = l_Array_append___redArg(v___y_327_, v___y_325_);
lean_dec_ref(v___y_325_);
v___x_336_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_336_, 0, v___y_319_);
lean_ctor_set(v___x_336_, 1, v___y_326_);
lean_ctor_set(v___x_336_, 2, v___x_335_);
lean_inc(v___y_322_);
v___x_337_ = l_Lean_Syntax_node1(v___y_319_, v___y_322_, v___x_336_);
v___x_338_ = l_Lean_Syntax_node7(v___y_319_, v___x_316_, v___y_324_, v___y_320_, v___y_323_, v___x_330_, v___x_332_, v___x_334_, v___x_337_);
v___x_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
v___x_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v___y_321_);
return v___x_340_;
}
}
else
{
lean_object* v___x_463_; lean_object* v___y_465_; lean_object* v___y_466_; lean_object* v___y_467_; lean_object* v___y_468_; lean_object* v___y_469_; lean_object* v___y_470_; lean_object* v___y_471_; lean_object* v___y_472_; lean_object* v___y_473_; lean_object* v___y_474_; lean_object* v___y_481_; lean_object* v_motive_482_; lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v___x_528_; lean_object* v_gen_530_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___x_542_; uint8_t v___x_543_; 
v___x_463_ = lean_unsigned_to_nat(0u);
v___x_528_ = lean_unsigned_to_nat(1u);
v___x_542_ = l_Lean_Syntax_getArg(v_stx_287_, v___x_528_);
v___x_543_ = l_Lean_Syntax_isNone(v___x_542_);
if (v___x_543_ == 0)
{
uint8_t v___x_544_; 
lean_inc(v___x_542_);
v___x_544_ = l_Lean_Syntax_matchesNull(v___x_542_, v___x_528_);
if (v___x_544_ == 0)
{
lean_object* v___x_545_; lean_object* v___x_546_; 
lean_dec(v___x_542_);
lean_dec(v_stx_287_);
v___x_545_ = lean_box(0);
v___x_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
lean_ctor_set(v___x_546_, 1, v_a_289_);
return v___x_546_;
}
else
{
lean_object* v_gen_547_; lean_object* v___x_548_; 
v_gen_547_ = l_Lean_Syntax_getArg(v___x_542_, v___x_463_);
lean_dec(v___x_542_);
v___x_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_548_, 0, v_gen_547_);
v_gen_530_ = v___x_548_;
v___y_531_ = v_a_288_;
v___y_532_ = v_a_289_;
goto v___jp_529_;
}
}
else
{
lean_object* v___x_549_; 
lean_dec(v___x_542_);
v___x_549_ = lean_box(0);
v_gen_530_ = v___x_549_;
v___y_531_ = v_a_288_;
v___y_532_ = v_a_289_;
goto v___jp_529_;
}
v___jp_464_:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
lean_inc_ref(v___y_468_);
v___x_475_ = l_Array_append___redArg(v___y_468_, v___y_474_);
lean_dec_ref(v___y_474_);
lean_inc(v___y_473_);
lean_inc(v___y_465_);
v___x_476_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_476_, 0, v___y_465_);
lean_ctor_set(v___x_476_, 1, v___y_473_);
lean_ctor_set(v___x_476_, 2, v___x_475_);
if (lean_obj_tag(v___y_471_) == 1)
{
lean_object* v_val_477_; lean_object* v___x_478_; 
v_val_477_ = lean_ctor_get(v___y_471_, 0);
lean_inc(v_val_477_);
lean_dec_ref_known(v___y_471_, 1);
v___x_478_ = l_Array_mkArray1___redArg(v_val_477_);
v___y_293_ = v___y_465_;
v___y_294_ = v___y_466_;
v___y_295_ = v___y_467_;
v___y_296_ = v___y_468_;
v___y_297_ = v___y_470_;
v___y_298_ = v___y_469_;
v___y_299_ = v___x_476_;
v___y_300_ = v___y_472_;
v___y_301_ = v___y_473_;
v___y_302_ = v___x_478_;
goto v___jp_292_;
}
else
{
lean_object* v___x_479_; 
lean_dec(v___y_471_);
v___x_479_ = ((lean_object*)(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5));
v___y_293_ = v___y_465_;
v___y_294_ = v___y_466_;
v___y_295_ = v___y_467_;
v___y_296_ = v___y_468_;
v___y_297_ = v___y_470_;
v___y_298_ = v___y_469_;
v___y_299_ = v___x_476_;
v___y_300_ = v___y_472_;
v___y_301_ = v___y_473_;
v___y_302_ = v___x_479_;
goto v___jp_292_;
}
}
v___jp_480_:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v___x_485_ = lean_unsigned_to_nat(5u);
v___x_486_ = l_Lean_Syntax_getArg(v_stx_287_, v___x_485_);
v___x_487_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6));
lean_inc(v___x_486_);
v___x_488_ = l_Lean_Syntax_isOfKind(v___x_486_, v___x_487_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; lean_object* v___x_490_; 
lean_dec(v___x_486_);
lean_dec(v_motive_482_);
lean_dec(v___y_481_);
lean_dec(v_stx_287_);
v___x_489_ = lean_box(0);
v___x_490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
lean_ctor_set(v___x_490_, 1, v___y_484_);
return v___x_490_;
}
else
{
lean_object* v___x_491_; lean_object* v_alts_492_; lean_object* v___x_493_; 
v___x_491_ = l_Lean_Syntax_getArg(v___x_486_, v___x_463_);
lean_dec(v___x_486_);
v_alts_492_ = l_Lean_Syntax_getArgs(v___x_491_);
lean_dec(v___x_491_);
v___x_493_ = l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand(v_alts_492_, v___y_483_, v___y_484_);
lean_dec_ref(v_alts_492_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_a_494_);
if (lean_obj_tag(v_a_494_) == 0)
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_503_; 
lean_dec(v_motive_482_);
lean_dec(v___y_481_);
lean_dec(v_stx_287_);
v_a_495_ = lean_ctor_get(v___x_493_, 1);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_503_ == 0)
{
lean_object* v_unused_504_; 
v_unused_504_ = lean_ctor_get(v___x_493_, 0);
lean_dec(v_unused_504_);
v___x_497_ = v___x_493_;
v_isShared_498_ = v_isSharedCheck_503_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_493_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_503_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_499_; lean_object* v___x_501_; 
v___x_499_ = lean_box(0);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 0, v___x_499_);
v___x_501_ = v___x_497_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_499_);
lean_ctor_set(v_reuseFailAlloc_502_, 1, v_a_495_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
else
{
lean_object* v_a_505_; lean_object* v_val_506_; lean_object* v_ref_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; uint8_t v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v_a_505_ = lean_ctor_get(v___x_493_, 1);
lean_inc(v_a_505_);
lean_dec_ref_known(v___x_493_, 2);
v_val_506_ = lean_ctor_get(v_a_494_, 0);
lean_inc(v_val_506_);
lean_dec_ref_known(v_a_494_, 1);
v_ref_507_ = lean_ctor_get(v___y_483_, 5);
v___x_508_ = lean_unsigned_to_nat(3u);
v___x_509_ = l_Lean_Syntax_getArg(v_stx_287_, v___x_508_);
lean_dec(v_stx_287_);
v___x_510_ = l_Lean_Syntax_getArgs(v___x_509_);
lean_dec(v___x_509_);
v___x_511_ = 0;
v___x_512_ = l_Lean_SourceInfo_fromRef(v_ref_507_, v___x_511_);
lean_inc(v___x_512_);
v___x_513_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
lean_ctor_set(v___x_513_, 1, v___x_290_);
v___x_514_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__1));
v___x_515_ = lean_obj_once(&l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7, &l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7_once, _init_l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7);
if (lean_obj_tag(v___y_481_) == 1)
{
lean_object* v_val_516_; lean_object* v___x_517_; 
v_val_516_ = lean_ctor_get(v___y_481_, 0);
lean_inc(v_val_516_);
lean_dec_ref_known(v___y_481_, 1);
v___x_517_ = l_Array_mkArray1___redArg(v_val_516_);
v___y_465_ = v___x_512_;
v___y_466_ = v___x_487_;
v___y_467_ = v_a_505_;
v___y_468_ = v___x_515_;
v___y_469_ = v_val_506_;
v___y_470_ = v___x_513_;
v___y_471_ = v_motive_482_;
v___y_472_ = v___x_510_;
v___y_473_ = v___x_514_;
v___y_474_ = v___x_517_;
goto v___jp_464_;
}
else
{
lean_object* v___x_518_; 
lean_dec(v___y_481_);
v___x_518_ = ((lean_object*)(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5));
v___y_465_ = v___x_512_;
v___y_466_ = v___x_487_;
v___y_467_ = v_a_505_;
v___y_468_ = v___x_515_;
v___y_469_ = v_val_506_;
v___y_470_ = v___x_513_;
v___y_471_ = v_motive_482_;
v___y_472_ = v___x_510_;
v___y_473_ = v___x_514_;
v___y_474_ = v___x_518_;
goto v___jp_464_;
}
}
}
else
{
lean_object* v_a_519_; lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_527_; 
lean_dec(v_motive_482_);
lean_dec(v___y_481_);
lean_dec(v_stx_287_);
v_a_519_ = lean_ctor_get(v___x_493_, 0);
v_a_520_ = lean_ctor_get(v___x_493_, 1);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_527_ == 0)
{
v___x_522_ = v___x_493_;
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_inc(v_a_519_);
lean_dec(v___x_493_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_525_; 
if (v_isShared_523_ == 0)
{
v___x_525_ = v___x_522_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_a_519_);
lean_ctor_set(v_reuseFailAlloc_526_, 1, v_a_520_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
}
}
v___jp_529_:
{
lean_object* v___x_533_; lean_object* v___x_534_; uint8_t v___x_535_; 
v___x_533_ = lean_unsigned_to_nat(2u);
v___x_534_ = l_Lean_Syntax_getArg(v_stx_287_, v___x_533_);
v___x_535_ = l_Lean_Syntax_isNone(v___x_534_);
if (v___x_535_ == 0)
{
uint8_t v___x_536_; 
lean_inc(v___x_534_);
v___x_536_ = l_Lean_Syntax_matchesNull(v___x_534_, v___x_528_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; lean_object* v___x_538_; 
lean_dec(v___x_534_);
lean_dec(v_gen_530_);
lean_dec(v_stx_287_);
v___x_537_ = lean_box(0);
v___x_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
lean_ctor_set(v___x_538_, 1, v___y_532_);
return v___x_538_;
}
else
{
lean_object* v_motive_539_; lean_object* v___x_540_; 
v_motive_539_ = l_Lean_Syntax_getArg(v___x_534_, v___x_463_);
lean_dec(v___x_534_);
v___x_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_540_, 0, v_motive_539_);
v___y_481_ = v_gen_530_;
v_motive_482_ = v___x_540_;
v___y_483_ = v___y_531_;
v___y_484_ = v___y_532_;
goto v___jp_480_;
}
}
else
{
lean_object* v___x_541_; 
lean_dec(v___x_534_);
v___x_541_ = lean_box(0);
v___y_481_ = v_gen_530_;
v_motive_482_ = v___x_541_;
v___y_483_ = v___y_531_;
v___y_484_ = v___y_532_;
goto v___jp_480_;
}
}
}
v___jp_292_:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
lean_inc_ref_n(v___y_296_, 3);
v___x_303_ = l_Array_append___redArg(v___y_296_, v___y_302_);
lean_dec_ref(v___y_302_);
lean_inc_n(v___y_301_, 3);
lean_inc_n(v___y_293_, 5);
v___x_304_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_304_, 0, v___y_293_);
lean_ctor_set(v___x_304_, 1, v___y_301_);
lean_ctor_set(v___x_304_, 2, v___x_303_);
v___x_305_ = l_Array_append___redArg(v___y_296_, v___y_300_);
lean_dec_ref(v___y_300_);
v___x_306_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_306_, 0, v___y_293_);
lean_ctor_set(v___x_306_, 1, v___y_301_);
lean_ctor_set(v___x_306_, 2, v___x_305_);
v___x_307_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__2));
v___x_308_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_308_, 0, v___y_293_);
lean_ctor_set(v___x_308_, 1, v___x_307_);
v___x_309_ = l_Array_append___redArg(v___y_296_, v___y_298_);
lean_dec_ref(v___y_298_);
v___x_310_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_310_, 0, v___y_293_);
lean_ctor_set(v___x_310_, 1, v___y_301_);
lean_ctor_set(v___x_310_, 2, v___x_309_);
lean_inc(v___y_294_);
v___x_311_ = l_Lean_Syntax_node1(v___y_293_, v___y_294_, v___x_310_);
v___x_312_ = l_Lean_Syntax_node6(v___y_293_, v___x_291_, v___y_297_, v___y_299_, v___x_304_, v___x_306_, v___x_308_, v___x_311_);
v___x_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
v___x_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
lean_ctor_set(v___x_314_, 1, v___y_295_);
return v___x_314_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___boxed(lean_object* v_stx_550_, lean_object* v_a_551_, lean_object* v_a_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lean_Elab_Term_expandMatchAlts_x3f(v_stx_550_, v_a_551_, v_a_552_);
lean_dec_ref(v_a_551_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0(lean_object* v_as_562_, size_t v_sz_563_, size_t v_i_564_, lean_object* v_b_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
uint8_t v___x_568_; 
v___x_568_ = lean_usize_dec_lt(v_i_564_, v_sz_563_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; 
v___x_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_569_, 0, v_b_565_);
lean_ctor_set(v___x_569_, 1, v___y_567_);
return v___x_569_;
}
else
{
lean_object* v_ref_570_; lean_object* v_a_571_; uint8_t v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; size_t v___x_580_; size_t v___x_581_; 
v_ref_570_ = lean_ctor_get(v___y_566_, 0);
v_a_571_ = lean_array_uget_borrowed(v_as_562_, v_i_564_);
v___x_572_ = 0;
v___x_573_ = l_Lean_SourceInfo_fromRef(v_ref_570_, v___x_572_);
v___x_574_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__1));
v___x_575_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__2));
lean_inc_n(v___x_573_, 2);
v___x_576_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_576_, 0, v___x_573_);
lean_ctor_set(v___x_576_, 1, v___x_575_);
v___x_577_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__3));
v___x_578_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_573_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
lean_inc(v_a_571_);
v___x_579_ = l_Lean_Syntax_node4(v___x_573_, v___x_574_, v___x_576_, v_a_571_, v___x_578_, v_b_565_);
v___x_580_ = ((size_t)1ULL);
v___x_581_ = lean_usize_add(v_i_564_, v___x_580_);
v_i_564_ = v___x_581_;
v_b_565_ = v___x_579_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___boxed(lean_object* v_as_583_, lean_object* v_sz_584_, lean_object* v_i_585_, lean_object* v_b_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
size_t v_sz_boxed_589_; size_t v_i_boxed_590_; lean_object* v_res_591_; 
v_sz_boxed_589_ = lean_unbox_usize(v_sz_584_);
lean_dec(v_sz_584_);
v_i_boxed_590_ = lean_unbox_usize(v_i_585_);
lean_dec(v_i_585_);
v_res_591_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0(v_as_583_, v_sz_boxed_589_, v_i_boxed_590_, v_b_586_, v___y_587_, v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec_ref(v_as_583_);
return v_res_591_;
}
}
static lean_object* _init_l_Lean_Elab_Term_clearInMatchAlt___closed__0(void){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_592_ = l_Lean_firstFrontendMacroScope;
v___x_593_ = lean_box(0);
v___x_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_594_, 0, v___x_593_);
lean_ctor_set(v___x_594_, 1, v___x_592_);
return v___x_594_;
}
}
static lean_object* _init_l_Lean_Elab_Term_clearInMatchAlt___closed__1(void){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_595_ = lean_unsigned_to_nat(1u);
v___x_596_ = l_Lean_firstFrontendMacroScope;
v___x_597_ = lean_nat_add(v___x_596_, v___x_595_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatchAlt(lean_object* v_stx_598_, lean_object* v_vars_599_){
_start:
{
if (lean_obj_tag(v_stx_598_) == 1)
{
lean_object* v_info_600_; lean_object* v_kind_601_; lean_object* v_args_602_; lean_object* v___x_603_; lean_object* v___x_604_; uint8_t v___x_605_; 
v_info_600_ = lean_ctor_get(v_stx_598_, 0);
v_kind_601_ = lean_ctor_get(v_stx_598_, 1);
v_args_602_ = lean_ctor_get(v_stx_598_, 2);
v___x_603_ = lean_unsigned_to_nat(3u);
v___x_604_ = lean_array_get_size(v_args_602_);
v___x_605_ = lean_nat_dec_lt(v___x_603_, v___x_604_);
if (v___x_605_ == 0)
{
return v_stx_598_;
}
else
{
lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_622_; 
lean_inc_ref(v_args_602_);
lean_inc(v_kind_601_);
lean_inc(v_info_600_);
v_isSharedCheck_622_ = !lean_is_exclusive(v_stx_598_);
if (v_isSharedCheck_622_ == 0)
{
lean_object* v_unused_623_; lean_object* v_unused_624_; lean_object* v_unused_625_; 
v_unused_623_ = lean_ctor_get(v_stx_598_, 2);
lean_dec(v_unused_623_);
v_unused_624_ = lean_ctor_get(v_stx_598_, 1);
lean_dec(v_unused_624_);
v_unused_625_ = lean_ctor_get(v_stx_598_, 0);
lean_dec(v_unused_625_);
v___x_607_ = v_stx_598_;
v_isShared_608_ = v_isSharedCheck_622_;
goto v_resetjp_606_;
}
else
{
lean_dec(v_stx_598_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_622_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v_v_609_; size_t v_sz_610_; size_t v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v_fst_615_; lean_object* v___x_616_; lean_object* v_xs_x27_617_; lean_object* v___x_618_; lean_object* v___x_620_; 
v_v_609_ = lean_array_fget_borrowed(v_args_602_, v___x_603_);
v_sz_610_ = lean_array_size(v_vars_599_);
v___x_611_ = ((size_t)0ULL);
v___x_612_ = lean_obj_once(&l_Lean_Elab_Term_clearInMatchAlt___closed__0, &l_Lean_Elab_Term_clearInMatchAlt___closed__0_once, _init_l_Lean_Elab_Term_clearInMatchAlt___closed__0);
v___x_613_ = lean_obj_once(&l_Lean_Elab_Term_clearInMatchAlt___closed__1, &l_Lean_Elab_Term_clearInMatchAlt___closed__1_once, _init_l_Lean_Elab_Term_clearInMatchAlt___closed__1);
lean_inc(v_v_609_);
v___x_614_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0(v_vars_599_, v_sz_610_, v___x_611_, v_v_609_, v___x_612_, v___x_613_);
v_fst_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc(v_fst_615_);
lean_dec_ref(v___x_614_);
v___x_616_ = lean_box(0);
v_xs_x27_617_ = lean_array_fset(v_args_602_, v___x_603_, v___x_616_);
v___x_618_ = lean_array_fset(v_xs_x27_617_, v___x_603_, v_fst_615_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 2, v___x_618_);
v___x_620_ = v___x_607_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_info_600_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v_kind_601_);
lean_ctor_set(v_reuseFailAlloc_621_, 2, v___x_618_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
else
{
return v_stx_598_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatchAlt___boxed(lean_object* v_stx_626_, lean_object* v_vars_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Lean_Elab_Term_clearInMatchAlt(v_stx_626_, v_vars_627_);
lean_dec_ref(v_vars_627_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_clearInMatch_spec__0(lean_object* v_vars_629_, size_t v_sz_630_, size_t v_i_631_, lean_object* v_bs_632_){
_start:
{
uint8_t v___x_633_; 
v___x_633_ = lean_usize_dec_lt(v_i_631_, v_sz_630_);
if (v___x_633_ == 0)
{
return v_bs_632_;
}
else
{
lean_object* v_v_634_; lean_object* v___x_635_; lean_object* v_bs_x27_636_; lean_object* v___x_637_; size_t v___x_638_; size_t v___x_639_; lean_object* v___x_640_; 
v_v_634_ = lean_array_uget(v_bs_632_, v_i_631_);
v___x_635_ = lean_unsigned_to_nat(0u);
v_bs_x27_636_ = lean_array_uset(v_bs_632_, v_i_631_, v___x_635_);
v___x_637_ = l_Lean_Elab_Term_clearInMatchAlt(v_v_634_, v_vars_629_);
v___x_638_ = ((size_t)1ULL);
v___x_639_ = lean_usize_add(v_i_631_, v___x_638_);
v___x_640_ = lean_array_uset(v_bs_x27_636_, v_i_631_, v___x_637_);
v_i_631_ = v___x_639_;
v_bs_632_ = v___x_640_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_clearInMatch_spec__0___boxed(lean_object* v_vars_642_, lean_object* v_sz_643_, lean_object* v_i_644_, lean_object* v_bs_645_){
_start:
{
size_t v_sz_boxed_646_; size_t v_i_boxed_647_; lean_object* v_res_648_; 
v_sz_boxed_646_ = lean_unbox_usize(v_sz_643_);
lean_dec(v_sz_643_);
v_i_boxed_647_ = lean_unbox_usize(v_i_644_);
lean_dec(v_i_644_);
v_res_648_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_clearInMatch_spec__0(v_vars_642_, v_sz_boxed_646_, v_i_boxed_647_, v_bs_645_);
lean_dec_ref(v_vars_642_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatch(lean_object* v_stx_649_, lean_object* v_vars_650_, lean_object* v_a_651_, lean_object* v_a_652_){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; uint8_t v___x_655_; 
v___x_653_ = lean_array_get_size(v_vars_650_);
v___x_654_ = lean_unsigned_to_nat(0u);
v___x_655_ = lean_nat_dec_eq(v___x_653_, v___x_654_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_697_; lean_object* v_motive_698_; lean_object* v___y_699_; lean_object* v___y_700_; uint8_t v___x_722_; 
v___x_656_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__0));
v___x_657_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1));
lean_inc(v_stx_649_);
v___x_722_ = l_Lean_Syntax_isOfKind(v_stx_649_, v___x_657_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; 
v___x_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_723_, 0, v_stx_649_);
lean_ctor_set(v___x_723_, 1, v_a_652_);
return v___x_723_;
}
else
{
lean_object* v___x_724_; lean_object* v_gen_726_; lean_object* v___y_727_; lean_object* v___y_728_; lean_object* v___x_737_; uint8_t v___x_738_; 
v___x_724_ = lean_unsigned_to_nat(1u);
v___x_737_ = l_Lean_Syntax_getArg(v_stx_649_, v___x_724_);
v___x_738_ = l_Lean_Syntax_isNone(v___x_737_);
if (v___x_738_ == 0)
{
uint8_t v___x_739_; 
lean_inc(v___x_737_);
v___x_739_ = l_Lean_Syntax_matchesNull(v___x_737_, v___x_724_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; 
lean_dec(v___x_737_);
v___x_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_740_, 0, v_stx_649_);
lean_ctor_set(v___x_740_, 1, v_a_652_);
return v___x_740_;
}
else
{
lean_object* v_gen_741_; lean_object* v___x_742_; 
v_gen_741_ = l_Lean_Syntax_getArg(v___x_737_, v___x_654_);
lean_dec(v___x_737_);
v___x_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_742_, 0, v_gen_741_);
v_gen_726_ = v___x_742_;
v___y_727_ = v_a_651_;
v___y_728_ = v_a_652_;
goto v___jp_725_;
}
}
else
{
lean_object* v___x_743_; 
lean_dec(v___x_737_);
v___x_743_ = lean_box(0);
v_gen_726_ = v___x_743_;
v___y_727_ = v_a_651_;
v___y_728_ = v_a_652_;
goto v___jp_725_;
}
v___jp_725_:
{
lean_object* v___x_729_; lean_object* v___x_730_; uint8_t v___x_731_; 
v___x_729_ = lean_unsigned_to_nat(2u);
v___x_730_ = l_Lean_Syntax_getArg(v_stx_649_, v___x_729_);
v___x_731_ = l_Lean_Syntax_isNone(v___x_730_);
if (v___x_731_ == 0)
{
uint8_t v___x_732_; 
lean_inc(v___x_730_);
v___x_732_ = l_Lean_Syntax_matchesNull(v___x_730_, v___x_724_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; 
lean_dec(v___x_730_);
lean_dec(v_gen_726_);
v___x_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_733_, 0, v_stx_649_);
lean_ctor_set(v___x_733_, 1, v___y_728_);
return v___x_733_;
}
else
{
lean_object* v_motive_734_; lean_object* v___x_735_; 
v_motive_734_ = l_Lean_Syntax_getArg(v___x_730_, v___x_654_);
lean_dec(v___x_730_);
v___x_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_735_, 0, v_motive_734_);
v___y_697_ = v_gen_726_;
v_motive_698_ = v___x_735_;
v___y_699_ = v___y_727_;
v___y_700_ = v___y_728_;
goto v___jp_696_;
}
}
else
{
lean_object* v___x_736_; 
lean_dec(v___x_730_);
v___x_736_ = lean_box(0);
v___y_697_ = v_gen_726_;
v_motive_698_ = v___x_736_;
v___y_699_ = v___y_727_;
v___y_700_ = v___y_728_;
goto v___jp_696_;
}
}
}
v___jp_658_:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
lean_inc_ref_n(v___y_666_, 3);
v___x_669_ = l_Array_append___redArg(v___y_666_, v___y_668_);
lean_dec_ref(v___y_668_);
lean_inc_n(v___y_660_, 3);
lean_inc_n(v___y_663_, 5);
v___x_670_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_670_, 0, v___y_663_);
lean_ctor_set(v___x_670_, 1, v___y_660_);
lean_ctor_set(v___x_670_, 2, v___x_669_);
v___x_671_ = l_Array_append___redArg(v___y_666_, v___y_665_);
lean_dec_ref(v___y_665_);
v___x_672_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_672_, 0, v___y_663_);
lean_ctor_set(v___x_672_, 1, v___y_660_);
lean_ctor_set(v___x_672_, 2, v___x_671_);
v___x_673_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__2));
v___x_674_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_674_, 0, v___y_663_);
lean_ctor_set(v___x_674_, 1, v___x_673_);
v___x_675_ = l_Array_append___redArg(v___y_666_, v___y_659_);
lean_dec_ref(v___y_659_);
v___x_676_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_676_, 0, v___y_663_);
lean_ctor_set(v___x_676_, 1, v___y_660_);
lean_ctor_set(v___x_676_, 2, v___x_675_);
lean_inc(v___y_662_);
v___x_677_ = l_Lean_Syntax_node1(v___y_663_, v___y_662_, v___x_676_);
v___x_678_ = l_Lean_Syntax_node6(v___y_663_, v___x_657_, v___y_667_, v___y_664_, v___x_670_, v___x_672_, v___x_674_, v___x_677_);
v___x_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
lean_ctor_set(v___x_679_, 1, v___y_661_);
return v___x_679_;
}
v___jp_680_:
{
lean_object* v___x_691_; lean_object* v___x_692_; 
lean_inc_ref(v___y_688_);
v___x_691_ = l_Array_append___redArg(v___y_688_, v___y_690_);
lean_dec_ref(v___y_690_);
lean_inc(v___y_682_);
lean_inc(v___y_685_);
v___x_692_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_692_, 0, v___y_685_);
lean_ctor_set(v___x_692_, 1, v___y_682_);
lean_ctor_set(v___x_692_, 2, v___x_691_);
if (lean_obj_tag(v___y_686_) == 1)
{
lean_object* v_val_693_; lean_object* v___x_694_; 
v_val_693_ = lean_ctor_get(v___y_686_, 0);
lean_inc(v_val_693_);
lean_dec_ref_known(v___y_686_, 1);
v___x_694_ = l_Array_mkArray1___redArg(v_val_693_);
v___y_659_ = v___y_681_;
v___y_660_ = v___y_682_;
v___y_661_ = v___y_684_;
v___y_662_ = v___y_683_;
v___y_663_ = v___y_685_;
v___y_664_ = v___x_692_;
v___y_665_ = v___y_687_;
v___y_666_ = v___y_688_;
v___y_667_ = v___y_689_;
v___y_668_ = v___x_694_;
goto v___jp_658_;
}
else
{
lean_object* v___x_695_; 
lean_dec(v___y_686_);
v___x_695_ = ((lean_object*)(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5));
v___y_659_ = v___y_681_;
v___y_660_ = v___y_682_;
v___y_661_ = v___y_684_;
v___y_662_ = v___y_683_;
v___y_663_ = v___y_685_;
v___y_664_ = v___x_692_;
v___y_665_ = v___y_687_;
v___y_666_ = v___y_688_;
v___y_667_ = v___y_689_;
v___y_668_ = v___x_695_;
goto v___jp_658_;
}
}
v___jp_696_:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; uint8_t v___x_704_; 
v___x_701_ = lean_unsigned_to_nat(5u);
v___x_702_ = l_Lean_Syntax_getArg(v_stx_649_, v___x_701_);
v___x_703_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6));
lean_inc(v___x_702_);
v___x_704_ = l_Lean_Syntax_isOfKind(v___x_702_, v___x_703_);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; 
lean_dec(v___x_702_);
lean_dec(v_motive_698_);
lean_dec(v___y_697_);
v___x_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_705_, 0, v_stx_649_);
lean_ctor_set(v___x_705_, 1, v___y_700_);
return v___x_705_;
}
else
{
lean_object* v_ref_706_; lean_object* v___x_707_; lean_object* v_alts_708_; size_t v_sz_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; size_t v___x_713_; lean_object* v_alts_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v_ref_706_ = lean_ctor_get(v___y_699_, 5);
v___x_707_ = l_Lean_Syntax_getArg(v___x_702_, v___x_654_);
lean_dec(v___x_702_);
v_alts_708_ = l_Lean_Syntax_getArgs(v___x_707_);
lean_dec(v___x_707_);
v_sz_709_ = lean_array_size(v_alts_708_);
v___x_710_ = lean_unsigned_to_nat(3u);
v___x_711_ = l_Lean_Syntax_getArg(v_stx_649_, v___x_710_);
lean_dec(v_stx_649_);
v___x_712_ = l_Lean_Syntax_getArgs(v___x_711_);
lean_dec(v___x_711_);
v___x_713_ = ((size_t)0ULL);
v_alts_714_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_clearInMatch_spec__0(v_vars_650_, v_sz_709_, v___x_713_, v_alts_708_);
v___x_715_ = l_Lean_SourceInfo_fromRef(v_ref_706_, v___x_655_);
lean_inc(v___x_715_);
v___x_716_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_716_, 0, v___x_715_);
lean_ctor_set(v___x_716_, 1, v___x_656_);
v___x_717_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__1));
v___x_718_ = lean_obj_once(&l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7, &l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7_once, _init_l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7);
if (lean_obj_tag(v___y_697_) == 1)
{
lean_object* v_val_719_; lean_object* v___x_720_; 
v_val_719_ = lean_ctor_get(v___y_697_, 0);
lean_inc(v_val_719_);
lean_dec_ref_known(v___y_697_, 1);
v___x_720_ = l_Array_mkArray1___redArg(v_val_719_);
v___y_681_ = v_alts_714_;
v___y_682_ = v___x_717_;
v___y_683_ = v___x_703_;
v___y_684_ = v___y_700_;
v___y_685_ = v___x_715_;
v___y_686_ = v_motive_698_;
v___y_687_ = v___x_712_;
v___y_688_ = v___x_718_;
v___y_689_ = v___x_716_;
v___y_690_ = v___x_720_;
goto v___jp_680_;
}
else
{
lean_object* v___x_721_; 
lean_dec(v___y_697_);
v___x_721_ = ((lean_object*)(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5));
v___y_681_ = v_alts_714_;
v___y_682_ = v___x_717_;
v___y_683_ = v___x_703_;
v___y_684_ = v___y_700_;
v___y_685_ = v___x_715_;
v___y_686_ = v_motive_698_;
v___y_687_ = v___x_712_;
v___y_688_ = v___x_718_;
v___y_689_ = v___x_716_;
v___y_690_ = v___x_721_;
goto v___jp_680_;
}
}
}
}
else
{
lean_object* v___x_744_; 
v___x_744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_744_, 0, v_stx_649_);
lean_ctor_set(v___x_744_, 1, v_a_652_);
return v___x_744_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatch___boxed(lean_object* v_stx_745_, lean_object* v_vars_746_, lean_object* v_a_747_, lean_object* v_a_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Lean_Elab_Term_clearInMatch(v_stx_745_, v_vars_746_, v_a_747_, v_a_748_);
lean_dec_ref(v_a_747_);
lean_dec_ref(v_vars_746_);
return v_res_749_;
}
}
lean_object* runtime_initialize_Lean_Parser_Term(uint8_t builtin);
lean_object* runtime_initialize_Init_Syntax(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_BindersUtil(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
