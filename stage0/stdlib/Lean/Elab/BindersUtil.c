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
lean_object* l_Array_mkArray0___redArg();
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandOptType(lean_object* v_ref_1_, lean_object* v_optType_2_){
_start:
{
uint8_t v___x_3_; 
v___x_3_ = l_Lean_Syntax_isNone(v_optType_2_);
if (v___x_3_ == 0)
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_4_ = lean_unsigned_to_nat(0u);
v___x_5_ = l_Lean_Syntax_getArg(v_optType_2_, v___x_4_);
v___x_6_ = lean_unsigned_to_nat(1u);
v___x_7_ = l_Lean_Syntax_getArg(v___x_5_, v___x_6_);
lean_dec(v___x_5_);
return v___x_7_;
}
else
{
uint8_t v___x_8_; lean_object* v___x_9_; 
v___x_8_ = 0;
v___x_9_ = l_Lean_mkHole(v_ref_1_, v___x_8_);
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandOptType___boxed(lean_object* v_ref_10_, lean_object* v_optType_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Lean_Elab_Term_expandOptType(v_ref_10_, v_optType_11_);
lean_dec(v_optType_11_);
lean_dec(v_ref_10_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getMatchAltsNumPatterns(lean_object* v_matchAlts_13_){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v_alt0_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v_pats_20_; lean_object* v___x_21_; 
v___x_14_ = lean_unsigned_to_nat(0u);
v___x_15_ = l_Lean_Syntax_getArg(v_matchAlts_13_, v___x_14_);
v_alt0_16_ = l_Lean_Syntax_getArg(v___x_15_, v___x_14_);
lean_dec(v___x_15_);
v___x_17_ = lean_unsigned_to_nat(1u);
v___x_18_ = l_Lean_Syntax_getArg(v_alt0_16_, v___x_17_);
lean_dec(v_alt0_16_);
v___x_19_ = l_Lean_Syntax_getArg(v___x_18_, v___x_14_);
lean_dec(v___x_18_);
v_pats_20_ = l_Lean_Syntax_getSepArgs(v___x_19_);
lean_dec(v___x_19_);
v___x_21_ = lean_array_get_size(v_pats_20_);
lean_dec_ref(v_pats_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getMatchAltsNumPatterns___boxed(lean_object* v_matchAlts_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_Elab_Term_getMatchAltsNumPatterns(v_matchAlts_22_);
lean_dec(v_matchAlts_22_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0(lean_object* v___x_27_, size_t v_sz_28_, size_t v_i_29_, lean_object* v_bs_30_){
_start:
{
uint8_t v___x_31_; 
v___x_31_ = lean_usize_dec_lt(v_i_29_, v_sz_28_);
if (v___x_31_ == 0)
{
lean_dec(v___x_27_);
return v_bs_30_;
}
else
{
lean_object* v___x_32_; lean_object* v_v_33_; lean_object* v___x_34_; lean_object* v_bs_x27_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; size_t v___x_42_; size_t v___x_43_; lean_object* v___x_44_; 
v___x_32_ = lean_unsigned_to_nat(1u);
v_v_33_ = lean_array_uget(v_bs_30_, v_i_29_);
v___x_34_ = lean_unsigned_to_nat(0u);
v_bs_x27_35_ = lean_array_uset(v_bs_30_, v_i_29_, v___x_34_);
v___x_36_ = lean_mk_empty_array_with_capacity(v___x_32_);
v___x_37_ = lean_array_push(v___x_36_, v_v_33_);
v___x_38_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__1));
v___x_39_ = lean_box(2);
v___x_40_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_40_, 0, v___x_39_);
lean_ctor_set(v___x_40_, 1, v___x_38_);
lean_ctor_set(v___x_40_, 2, v___x_37_);
lean_inc(v___x_27_);
v___x_41_ = l_Lean_Syntax_setArg(v___x_27_, v___x_32_, v___x_40_);
v___x_42_ = ((size_t)1ULL);
v___x_43_ = lean_usize_add(v_i_29_, v___x_42_);
v___x_44_ = lean_array_uset(v_bs_x27_35_, v_i_29_, v___x_41_);
v_i_29_ = v___x_43_;
v_bs_30_ = v___x_44_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___boxed(lean_object* v___x_46_, lean_object* v_sz_47_, lean_object* v_i_48_, lean_object* v_bs_49_){
_start:
{
size_t v_sz_boxed_50_; size_t v_i_boxed_51_; lean_object* v_res_52_; 
v_sz_boxed_50_ = lean_unbox_usize(v_sz_47_);
lean_dec(v_sz_47_);
v_i_boxed_51_ = lean_unbox_usize(v_i_48_);
lean_dec(v_i_48_);
v_res_52_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0(v___x_46_, v_sz_boxed_50_, v_i_boxed_51_, v_bs_49_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlt(lean_object* v_stx_53_){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v_patss_56_; lean_object* v___x_57_; uint8_t v___x_58_; 
v___x_54_ = lean_unsigned_to_nat(1u);
v___x_55_ = l_Lean_Syntax_getArg(v_stx_53_, v___x_54_);
v_patss_56_ = l_Lean_Syntax_getSepArgs(v___x_55_);
lean_dec(v___x_55_);
v___x_57_ = lean_array_get_size(v_patss_56_);
v___x_58_ = lean_nat_dec_le(v___x_57_, v___x_54_);
if (v___x_58_ == 0)
{
size_t v_sz_59_; size_t v___x_60_; lean_object* v___x_61_; 
v_sz_59_ = lean_array_size(v_patss_56_);
v___x_60_ = ((size_t)0ULL);
v___x_61_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0(v_stx_53_, v_sz_59_, v___x_60_, v_patss_56_);
return v___x_61_;
}
else
{
lean_object* v___x_62_; lean_object* v___x_63_; 
lean_dec_ref(v_patss_56_);
v___x_62_ = lean_mk_empty_array_with_capacity(v___x_54_);
v___x_63_ = lean_array_push(v___x_62_, v_stx_53_);
return v___x_63_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__0(size_t v_sz_64_, size_t v_i_65_, lean_object* v_bs_66_){
_start:
{
uint8_t v___x_67_; 
v___x_67_ = lean_usize_dec_lt(v_i_65_, v_sz_64_);
if (v___x_67_ == 0)
{
lean_object* v___x_68_; 
v___x_68_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_68_, 0, v_bs_66_);
return v___x_68_;
}
else
{
lean_object* v_v_69_; lean_object* v___x_70_; lean_object* v_bs_x27_71_; lean_object* v_patss_72_; size_t v___x_73_; size_t v___x_74_; lean_object* v___x_75_; 
v_v_69_ = lean_array_uget(v_bs_66_, v_i_65_);
v___x_70_ = lean_unsigned_to_nat(0u);
v_bs_x27_71_ = lean_array_uset(v_bs_66_, v_i_65_, v___x_70_);
v_patss_72_ = l_Lean_Syntax_getArgs(v_v_69_);
lean_dec(v_v_69_);
v___x_73_ = ((size_t)1ULL);
v___x_74_ = lean_usize_add(v_i_65_, v___x_73_);
v___x_75_ = lean_array_uset(v_bs_x27_71_, v_i_65_, v_patss_72_);
v_i_65_ = v___x_74_;
v_bs_66_ = v___x_75_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__0___boxed(lean_object* v_sz_77_, lean_object* v_i_78_, lean_object* v_bs_79_){
_start:
{
size_t v_sz_boxed_80_; size_t v_i_boxed_81_; lean_object* v_res_82_; 
v_sz_boxed_80_ = lean_unbox_usize(v_sz_77_);
lean_dec(v_sz_77_);
v_i_boxed_81_ = lean_unbox_usize(v_i_78_);
lean_dec(v_i_78_);
v_res_82_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__0(v_sz_boxed_80_, v_i_boxed_81_, v_bs_79_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__1(uint8_t v___x_83_, lean_object* v_as_84_, size_t v_i_85_, size_t v_stop_86_, lean_object* v_b_87_){
_start:
{
lean_object* v___y_89_; uint8_t v___x_93_; 
v___x_93_ = lean_usize_dec_eq(v_i_85_, v_stop_86_);
if (v___x_93_ == 0)
{
lean_object* v_fst_94_; uint8_t v___x_95_; 
v_fst_94_ = lean_ctor_get(v_b_87_, 0);
v___x_95_ = lean_unbox(v_fst_94_);
if (v___x_95_ == 0)
{
lean_object* v_snd_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_104_; 
v_snd_96_ = lean_ctor_get(v_b_87_, 1);
v_isSharedCheck_104_ = !lean_is_exclusive(v_b_87_);
if (v_isSharedCheck_104_ == 0)
{
lean_object* v_unused_105_; 
v_unused_105_ = lean_ctor_get(v_b_87_, 0);
lean_dec(v_unused_105_);
v___x_98_ = v_b_87_;
v_isShared_99_ = v_isSharedCheck_104_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_snd_96_);
lean_dec(v_b_87_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_104_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_100_; lean_object* v___x_102_; 
v___x_100_ = lean_box(v___x_83_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 0, v___x_100_);
v___x_102_ = v___x_98_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v___x_100_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v_snd_96_);
v___x_102_ = v_reuseFailAlloc_103_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
v___y_89_ = v___x_102_;
goto v___jp_88_;
}
}
}
else
{
lean_object* v_snd_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_116_; 
v_snd_106_ = lean_ctor_get(v_b_87_, 1);
v_isSharedCheck_116_ = !lean_is_exclusive(v_b_87_);
if (v_isSharedCheck_116_ == 0)
{
lean_object* v_unused_117_; 
v_unused_117_ = lean_ctor_get(v_b_87_, 0);
lean_dec(v_unused_117_);
v___x_108_ = v_b_87_;
v_isShared_109_ = v_isSharedCheck_116_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_snd_106_);
lean_dec(v_b_87_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_116_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_114_; 
v___x_110_ = lean_array_uget_borrowed(v_as_84_, v_i_85_);
lean_inc(v___x_110_);
v___x_111_ = lean_array_push(v_snd_106_, v___x_110_);
v___x_112_ = lean_box(v___x_93_);
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 1, v___x_111_);
lean_ctor_set(v___x_108_, 0, v___x_112_);
v___x_114_ = v___x_108_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v___x_112_);
lean_ctor_set(v_reuseFailAlloc_115_, 1, v___x_111_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
v___y_89_ = v___x_114_;
goto v___jp_88_;
}
}
}
}
else
{
return v_b_87_;
}
v___jp_88_:
{
size_t v___x_90_; size_t v___x_91_; 
v___x_90_ = ((size_t)1ULL);
v___x_91_ = lean_usize_add(v_i_85_, v___x_90_);
v_i_85_ = v___x_91_;
v_b_87_ = v___y_89_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__1___boxed(lean_object* v___x_118_, lean_object* v_as_119_, lean_object* v_i_120_, lean_object* v_stop_121_, lean_object* v_b_122_){
_start:
{
uint8_t v___x_404__boxed_123_; size_t v_i_boxed_124_; size_t v_stop_boxed_125_; lean_object* v_res_126_; 
v___x_404__boxed_123_ = lean_unbox(v___x_118_);
v_i_boxed_124_ = lean_unbox_usize(v_i_120_);
lean_dec(v_i_120_);
v_stop_boxed_125_ = lean_unbox_usize(v_stop_121_);
lean_dec(v_stop_121_);
v_res_126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__1(v___x_404__boxed_123_, v_as_119_, v_i_boxed_124_, v_stop_boxed_125_, v_b_122_);
lean_dec_ref(v_as_119_);
return v_res_126_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_shouldExpandMatchAlt(lean_object* v_x_138_){
_start:
{
lean_object* v___x_139_; uint8_t v___x_140_; 
v___x_139_ = ((lean_object*)(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__4));
lean_inc(v_x_138_);
v___x_140_ = l_Lean_Syntax_isOfKind(v_x_138_, v___x_139_);
if (v___x_140_ == 0)
{
lean_dec(v_x_138_);
return v___x_140_;
}
else
{
lean_object* v___x_141_; lean_object* v___y_143_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; uint8_t v___x_156_; 
v___x_141_ = lean_unsigned_to_nat(1u);
v___x_151_ = l_Lean_Syntax_getArg(v_x_138_, v___x_141_);
lean_dec(v_x_138_);
v___x_152_ = l_Lean_Syntax_getArgs(v___x_151_);
lean_dec(v___x_151_);
v___x_153_ = lean_unsigned_to_nat(0u);
v___x_154_ = ((lean_object*)(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5));
v___x_155_ = lean_array_get_size(v___x_152_);
v___x_156_ = lean_nat_dec_lt(v___x_153_, v___x_155_);
if (v___x_156_ == 0)
{
lean_dec_ref(v___x_152_);
v___y_143_ = v___x_154_;
goto v___jp_142_;
}
else
{
lean_object* v___x_157_; lean_object* v___x_158_; size_t v___x_159_; size_t v___x_160_; lean_object* v___x_161_; lean_object* v_snd_162_; 
v___x_157_ = lean_box(v___x_156_);
v___x_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
lean_ctor_set(v___x_158_, 1, v___x_154_);
v___x_159_ = ((size_t)0ULL);
v___x_160_ = lean_usize_of_nat(v___x_155_);
v___x_161_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__1(v___x_140_, v___x_152_, v___x_159_, v___x_160_, v___x_158_);
lean_dec_ref(v___x_152_);
v_snd_162_ = lean_ctor_get(v___x_161_, 1);
lean_inc(v_snd_162_);
lean_dec_ref(v___x_161_);
v___y_143_ = v_snd_162_;
goto v___jp_142_;
}
v___jp_142_:
{
size_t v_sz_144_; size_t v___x_145_; lean_object* v___x_146_; 
v_sz_144_ = lean_array_size(v___y_143_);
v___x_145_ = ((size_t)0ULL);
v___x_146_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__0(v_sz_144_, v___x_145_, v___y_143_);
if (lean_obj_tag(v___x_146_) == 0)
{
uint8_t v___x_147_; 
v___x_147_ = 0;
return v___x_147_;
}
else
{
lean_object* v_val_148_; lean_object* v___x_149_; uint8_t v___x_150_; 
v_val_148_ = lean_ctor_get(v___x_146_, 0);
lean_inc(v_val_148_);
lean_dec_ref_known(v___x_146_, 1);
v___x_149_ = lean_array_get_size(v_val_148_);
lean_dec(v_val_148_);
v___x_150_ = lean_nat_dec_lt(v___x_141_, v___x_149_);
return v___x_150_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_shouldExpandMatchAlt___boxed(lean_object* v_x_163_){
_start:
{
uint8_t v_res_164_; lean_object* v_r_165_; 
v_res_164_ = l_Lean_Elab_Term_shouldExpandMatchAlt(v_x_163_);
v_r_165_ = lean_box(v_res_164_);
return v_r_165_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___redArg(lean_object* v_as_166_, size_t v_i_167_, size_t v_stop_168_, lean_object* v_b_169_, lean_object* v___y_170_){
_start:
{
uint8_t v___x_171_; 
v___x_171_ = lean_usize_dec_eq(v_i_167_, v_stop_168_);
if (v___x_171_ == 0)
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; size_t v___x_175_; size_t v___x_176_; 
v___x_172_ = lean_array_uget_borrowed(v_as_166_, v_i_167_);
lean_inc(v___x_172_);
v___x_173_ = l_Lean_Elab_Term_expandMatchAlt(v___x_172_);
v___x_174_ = l_Array_append___redArg(v_b_169_, v___x_173_);
lean_dec_ref(v___x_173_);
v___x_175_ = ((size_t)1ULL);
v___x_176_ = lean_usize_add(v_i_167_, v___x_175_);
v_i_167_ = v___x_176_;
v_b_169_ = v___x_174_;
goto _start;
}
else
{
lean_object* v___x_178_; 
v___x_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_178_, 0, v_b_169_);
lean_ctor_set(v___x_178_, 1, v___y_170_);
return v___x_178_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___redArg___boxed(lean_object* v_as_179_, lean_object* v_i_180_, lean_object* v_stop_181_, lean_object* v_b_182_, lean_object* v___y_183_){
_start:
{
size_t v_i_boxed_184_; size_t v_stop_boxed_185_; lean_object* v_res_186_; 
v_i_boxed_184_ = lean_unbox_usize(v_i_180_);
lean_dec(v_i_180_);
v_stop_boxed_185_ = lean_unbox_usize(v_stop_181_);
lean_dec(v_stop_181_);
v_res_186_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___redArg(v_as_179_, v_i_boxed_184_, v_stop_boxed_185_, v_b_182_, v___y_183_);
lean_dec_ref(v_as_179_);
return v_res_186_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__0(lean_object* v_as_187_, size_t v_i_188_, size_t v_stop_189_){
_start:
{
uint8_t v___x_190_; 
v___x_190_ = lean_usize_dec_eq(v_i_188_, v_stop_189_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_191_ = lean_array_uget_borrowed(v_as_187_, v_i_188_);
lean_inc(v___x_191_);
v___x_192_ = l_Lean_Elab_Term_shouldExpandMatchAlt(v___x_191_);
if (v___x_192_ == 0)
{
size_t v___x_193_; size_t v___x_194_; 
v___x_193_ = ((size_t)1ULL);
v___x_194_ = lean_usize_add(v_i_188_, v___x_193_);
v_i_188_ = v___x_194_;
goto _start;
}
else
{
return v___x_192_;
}
}
else
{
uint8_t v___x_196_; 
v___x_196_ = 0;
return v___x_196_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__0___boxed(lean_object* v_as_197_, lean_object* v_i_198_, lean_object* v_stop_199_){
_start:
{
size_t v_i_boxed_200_; size_t v_stop_boxed_201_; uint8_t v_res_202_; lean_object* v_r_203_; 
v_i_boxed_200_ = lean_unbox_usize(v_i_198_);
lean_dec(v_i_198_);
v_stop_boxed_201_ = lean_unbox_usize(v_stop_199_);
lean_dec(v_stop_199_);
v_res_202_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__0(v_as_197_, v_i_boxed_200_, v_stop_boxed_201_);
lean_dec_ref(v_as_197_);
v_r_203_ = lean_box(v_res_202_);
return v_r_203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand(lean_object* v_alts_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v_a_213_; lean_object* v_a_214_; lean_object* v___x_217_; lean_object* v___x_218_; uint8_t v___x_219_; 
v___x_217_ = lean_unsigned_to_nat(0u);
v___x_218_ = lean_array_get_size(v_alts_206_);
v___x_219_ = lean_nat_dec_lt(v___x_217_, v___x_218_);
if (v___x_219_ == 0)
{
goto v___jp_209_;
}
else
{
if (v___x_219_ == 0)
{
goto v___jp_209_;
}
else
{
size_t v___x_220_; size_t v___x_221_; uint8_t v___x_222_; 
v___x_220_ = ((size_t)0ULL);
v___x_221_ = lean_usize_of_nat(v___x_218_);
v___x_222_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__0(v_alts_206_, v___x_220_, v___x_221_);
if (v___x_222_ == 0)
{
goto v___jp_209_;
}
else
{
lean_object* v___x_223_; 
v___x_223_ = ((lean_object*)(l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand___closed__0));
if (v___x_219_ == 0)
{
v_a_213_ = v___x_223_;
v_a_214_ = v_a_208_;
goto v___jp_212_;
}
else
{
lean_object* v___x_224_; 
v___x_224_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___redArg(v_alts_206_, v___x_220_, v___x_221_, v___x_223_, v_a_208_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v_a_225_; lean_object* v_a_226_; 
v_a_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_a_225_);
v_a_226_ = lean_ctor_get(v___x_224_, 1);
lean_inc(v_a_226_);
lean_dec_ref_known(v___x_224_, 2);
v_a_213_ = v_a_225_;
v_a_214_ = v_a_226_;
goto v___jp_212_;
}
else
{
lean_object* v_a_227_; lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_235_; 
v_a_227_ = lean_ctor_get(v___x_224_, 0);
v_a_228_ = lean_ctor_get(v___x_224_, 1);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_235_ == 0)
{
v___x_230_ = v___x_224_;
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_a_228_);
lean_inc(v_a_227_);
lean_dec(v___x_224_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_233_; 
if (v_isShared_231_ == 0)
{
v___x_233_ = v___x_230_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_a_227_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v_a_228_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
}
}
}
}
v___jp_209_:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = lean_box(0);
v___x_211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
lean_ctor_set(v___x_211_, 1, v_a_208_);
return v___x_211_;
}
v___jp_212_:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_215_, 0, v_a_213_);
v___x_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
lean_ctor_set(v___x_216_, 1, v_a_214_);
return v___x_216_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand___boxed(lean_object* v_alts_236_, lean_object* v_a_237_, lean_object* v_a_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand(v_alts_236_, v_a_237_, v_a_238_);
lean_dec_ref(v_a_237_);
lean_dec_ref(v_alts_236_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1(lean_object* v_as_240_, size_t v_i_241_, size_t v_stop_242_, lean_object* v_b_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___redArg(v_as_240_, v_i_241_, v_stop_242_, v_b_243_, v___y_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___boxed(lean_object* v_as_247_, lean_object* v_i_248_, lean_object* v_stop_249_, lean_object* v_b_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
size_t v_i_boxed_253_; size_t v_stop_boxed_254_; lean_object* v_res_255_; 
v_i_boxed_253_ = lean_unbox_usize(v_i_248_);
lean_dec(v_i_248_);
v_stop_boxed_254_ = lean_unbox_usize(v_stop_249_);
lean_dec(v_stop_249_);
v_res_255_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1(v_as_247_, v_i_boxed_253_, v_stop_boxed_254_, v_b_250_, v___y_251_, v___y_252_);
lean_dec_ref(v___y_251_);
lean_dec_ref(v_as_247_);
return v_res_255_;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7(void){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Array_mkArray0___redArg();
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f(lean_object* v_stx_276_, lean_object* v_a_277_, lean_object* v_a_278_){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___y_282_; lean_object* v___y_283_; lean_object* v___y_284_; lean_object* v___y_285_; lean_object* v___y_286_; lean_object* v___y_287_; lean_object* v___y_288_; lean_object* v___y_289_; lean_object* v___y_290_; lean_object* v___y_291_; uint8_t v___x_304_; 
v___x_279_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__0));
v___x_280_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1));
lean_inc(v_stx_276_);
v___x_304_ = l_Lean_Syntax_isOfKind(v_stx_276_, v___x_280_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; lean_object* v___y_307_; lean_object* v___y_308_; lean_object* v___y_309_; lean_object* v___y_310_; lean_object* v___y_311_; lean_object* v___y_312_; lean_object* v___y_313_; lean_object* v___y_314_; lean_object* v___y_315_; lean_object* v___y_316_; lean_object* v___y_317_; uint8_t v___x_330_; 
v___x_305_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__4));
lean_inc(v_stx_276_);
v___x_330_ = l_Lean_Syntax_isOfKind(v_stx_276_, v___x_305_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; lean_object* v___x_332_; 
lean_dec(v_stx_276_);
v___x_331_ = lean_box(0);
v___x_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
lean_ctor_set(v___x_332_, 1, v_a_278_);
return v___x_332_;
}
else
{
lean_object* v___x_333_; lean_object* v___y_335_; lean_object* v___y_336_; lean_object* v___y_337_; lean_object* v___y_338_; lean_object* v___y_339_; lean_object* v___y_340_; lean_object* v___y_341_; lean_object* v___y_342_; lean_object* v___y_343_; lean_object* v___y_344_; lean_object* v___y_345_; lean_object* v___y_352_; lean_object* v___y_353_; lean_object* v___y_354_; lean_object* v___y_355_; lean_object* v___y_356_; lean_object* v___y_357_; lean_object* v___y_358_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___y_369_; lean_object* v___y_370_; lean_object* v_motive_371_; lean_object* v___y_372_; lean_object* v___y_373_; lean_object* v___x_416_; lean_object* v___y_418_; lean_object* v_gen_419_; lean_object* v___y_420_; lean_object* v___y_421_; lean_object* v_dep_x3f_432_; lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_333_ = lean_unsigned_to_nat(0u);
v___x_416_ = lean_unsigned_to_nat(1u);
v___x_444_ = l_Lean_Syntax_getArg(v_stx_276_, v___x_416_);
v___x_445_ = l_Lean_Syntax_isNone(v___x_444_);
if (v___x_445_ == 0)
{
uint8_t v___x_446_; 
lean_inc(v___x_444_);
v___x_446_ = l_Lean_Syntax_matchesNull(v___x_444_, v___x_416_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; lean_object* v___x_448_; 
lean_dec(v___x_444_);
lean_dec(v_stx_276_);
v___x_447_ = lean_box(0);
v___x_448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
lean_ctor_set(v___x_448_, 1, v_a_278_);
return v___x_448_;
}
else
{
lean_object* v_dep_x3f_449_; lean_object* v___x_450_; 
v_dep_x3f_449_ = l_Lean_Syntax_getArg(v___x_444_, v___x_333_);
lean_dec(v___x_444_);
v___x_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_450_, 0, v_dep_x3f_449_);
v_dep_x3f_432_ = v___x_450_;
v___y_433_ = v_a_277_;
v___y_434_ = v_a_278_;
goto v___jp_431_;
}
}
else
{
lean_object* v___x_451_; 
lean_dec(v___x_444_);
v___x_451_ = lean_box(0);
v_dep_x3f_432_ = v___x_451_;
v___y_433_ = v_a_277_;
v___y_434_ = v_a_278_;
goto v___jp_431_;
}
v___jp_334_:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
lean_inc_ref(v___y_336_);
v___x_346_ = l_Array_append___redArg(v___y_336_, v___y_345_);
lean_dec_ref(v___y_345_);
lean_inc(v___y_342_);
lean_inc(v___y_344_);
v___x_347_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_347_, 0, v___y_344_);
lean_ctor_set(v___x_347_, 1, v___y_342_);
lean_ctor_set(v___x_347_, 2, v___x_346_);
if (lean_obj_tag(v___y_338_) == 1)
{
lean_object* v_val_348_; lean_object* v___x_349_; 
v_val_348_ = lean_ctor_get(v___y_338_, 0);
lean_inc(v_val_348_);
lean_dec_ref_known(v___y_338_, 1);
v___x_349_ = l_Array_mkArray1___redArg(v_val_348_);
v___y_307_ = v___y_335_;
v___y_308_ = v___y_336_;
v___y_309_ = v___y_337_;
v___y_310_ = v___y_340_;
v___y_311_ = v___y_339_;
v___y_312_ = v___x_347_;
v___y_313_ = v___y_341_;
v___y_314_ = v___y_342_;
v___y_315_ = v___y_343_;
v___y_316_ = v___y_344_;
v___y_317_ = v___x_349_;
goto v___jp_306_;
}
else
{
lean_object* v___x_350_; 
lean_dec(v___y_338_);
v___x_350_ = ((lean_object*)(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5));
v___y_307_ = v___y_335_;
v___y_308_ = v___y_336_;
v___y_309_ = v___y_337_;
v___y_310_ = v___y_340_;
v___y_311_ = v___y_339_;
v___y_312_ = v___x_347_;
v___y_313_ = v___y_341_;
v___y_314_ = v___y_342_;
v___y_315_ = v___y_343_;
v___y_316_ = v___y_344_;
v___y_317_ = v___x_350_;
goto v___jp_306_;
}
}
v___jp_351_:
{
lean_object* v___x_363_; lean_object* v___x_364_; 
lean_inc_ref(v___y_354_);
v___x_363_ = l_Array_append___redArg(v___y_354_, v___y_362_);
lean_dec_ref(v___y_362_);
lean_inc(v___y_360_);
lean_inc(v___y_361_);
v___x_364_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_364_, 0, v___y_361_);
lean_ctor_set(v___x_364_, 1, v___y_360_);
lean_ctor_set(v___x_364_, 2, v___x_363_);
if (lean_obj_tag(v___y_352_) == 1)
{
lean_object* v_val_365_; lean_object* v___x_366_; 
v_val_365_ = lean_ctor_get(v___y_352_, 0);
lean_inc(v_val_365_);
lean_dec_ref_known(v___y_352_, 1);
v___x_366_ = l_Array_mkArray1___redArg(v_val_365_);
v___y_335_ = v___y_353_;
v___y_336_ = v___y_354_;
v___y_337_ = v___y_355_;
v___y_338_ = v___y_356_;
v___y_339_ = v___y_358_;
v___y_340_ = v___y_357_;
v___y_341_ = v___y_359_;
v___y_342_ = v___y_360_;
v___y_343_ = v___x_364_;
v___y_344_ = v___y_361_;
v___y_345_ = v___x_366_;
goto v___jp_334_;
}
else
{
lean_object* v___x_367_; 
lean_dec(v___y_352_);
v___x_367_ = ((lean_object*)(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5));
v___y_335_ = v___y_353_;
v___y_336_ = v___y_354_;
v___y_337_ = v___y_355_;
v___y_338_ = v___y_356_;
v___y_339_ = v___y_358_;
v___y_340_ = v___y_357_;
v___y_341_ = v___y_359_;
v___y_342_ = v___y_360_;
v___y_343_ = v___x_364_;
v___y_344_ = v___y_361_;
v___y_345_ = v___x_367_;
goto v___jp_334_;
}
}
v___jp_368_:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_374_ = lean_unsigned_to_nat(6u);
v___x_375_ = l_Lean_Syntax_getArg(v_stx_276_, v___x_374_);
v___x_376_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6));
lean_inc(v___x_375_);
v___x_377_ = l_Lean_Syntax_isOfKind(v___x_375_, v___x_376_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; lean_object* v___x_379_; 
lean_dec(v___x_375_);
lean_dec(v_motive_371_);
lean_dec(v___y_370_);
lean_dec(v___y_369_);
lean_dec(v_stx_276_);
v___x_378_ = lean_box(0);
v___x_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
lean_ctor_set(v___x_379_, 1, v___y_373_);
return v___x_379_;
}
else
{
lean_object* v___x_380_; lean_object* v_alts_381_; lean_object* v___x_382_; 
v___x_380_ = l_Lean_Syntax_getArg(v___x_375_, v___x_333_);
lean_dec(v___x_375_);
v_alts_381_ = l_Lean_Syntax_getArgs(v___x_380_);
lean_dec(v___x_380_);
v___x_382_ = l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand(v_alts_381_, v___y_372_, v___y_373_);
lean_dec_ref(v_alts_381_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v_a_383_; 
v_a_383_ = lean_ctor_get(v___x_382_, 0);
if (lean_obj_tag(v_a_383_) == 0)
{
lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_392_; 
lean_dec(v_motive_371_);
lean_dec(v___y_370_);
lean_dec(v___y_369_);
lean_dec(v_stx_276_);
v_a_384_ = lean_ctor_get(v___x_382_, 1);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_392_ == 0)
{
lean_object* v_unused_393_; 
v_unused_393_ = lean_ctor_get(v___x_382_, 0);
lean_dec(v_unused_393_);
v___x_386_ = v___x_382_;
v_isShared_387_ = v_isSharedCheck_392_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v___x_382_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_392_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_388_; lean_object* v___x_390_; 
v___x_388_ = lean_box(0);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 0, v___x_388_);
v___x_390_ = v___x_386_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_388_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v_a_384_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
else
{
lean_object* v_a_394_; lean_object* v_val_395_; lean_object* v_ref_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
lean_inc_ref(v_a_383_);
v_a_394_ = lean_ctor_get(v___x_382_, 1);
lean_inc(v_a_394_);
lean_dec_ref_known(v___x_382_, 2);
v_val_395_ = lean_ctor_get(v_a_383_, 0);
lean_inc(v_val_395_);
lean_dec_ref_known(v_a_383_, 1);
v_ref_396_ = lean_ctor_get(v___y_372_, 5);
v___x_397_ = lean_unsigned_to_nat(4u);
v___x_398_ = l_Lean_Syntax_getArg(v_stx_276_, v___x_397_);
lean_dec(v_stx_276_);
v___x_399_ = l_Lean_Syntax_getArgs(v___x_398_);
lean_dec(v___x_398_);
v___x_400_ = l_Lean_SourceInfo_fromRef(v_ref_396_, v___x_304_);
lean_inc(v___x_400_);
v___x_401_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_400_);
lean_ctor_set(v___x_401_, 1, v___x_279_);
v___x_402_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__1));
v___x_403_ = lean_obj_once(&l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7, &l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7_once, _init_l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7);
if (lean_obj_tag(v___y_370_) == 1)
{
lean_object* v_val_404_; lean_object* v___x_405_; 
v_val_404_ = lean_ctor_get(v___y_370_, 0);
lean_inc(v_val_404_);
lean_dec_ref_known(v___y_370_, 1);
v___x_405_ = l_Array_mkArray1___redArg(v_val_404_);
v___y_352_ = v___y_369_;
v___y_353_ = v_a_394_;
v___y_354_ = v___x_403_;
v___y_355_ = v___x_401_;
v___y_356_ = v_motive_371_;
v___y_357_ = v___x_376_;
v___y_358_ = v___x_399_;
v___y_359_ = v_val_395_;
v___y_360_ = v___x_402_;
v___y_361_ = v___x_400_;
v___y_362_ = v___x_405_;
goto v___jp_351_;
}
else
{
lean_object* v___x_406_; 
lean_dec(v___y_370_);
v___x_406_ = ((lean_object*)(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5));
v___y_352_ = v___y_369_;
v___y_353_ = v_a_394_;
v___y_354_ = v___x_403_;
v___y_355_ = v___x_401_;
v___y_356_ = v_motive_371_;
v___y_357_ = v___x_376_;
v___y_358_ = v___x_399_;
v___y_359_ = v_val_395_;
v___y_360_ = v___x_402_;
v___y_361_ = v___x_400_;
v___y_362_ = v___x_406_;
goto v___jp_351_;
}
}
}
else
{
lean_object* v_a_407_; lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_415_; 
lean_dec(v_motive_371_);
lean_dec(v___y_370_);
lean_dec(v___y_369_);
lean_dec(v_stx_276_);
v_a_407_ = lean_ctor_get(v___x_382_, 0);
v_a_408_ = lean_ctor_get(v___x_382_, 1);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_415_ == 0)
{
v___x_410_ = v___x_382_;
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_inc(v_a_407_);
lean_dec(v___x_382_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_413_; 
if (v_isShared_411_ == 0)
{
v___x_413_ = v___x_410_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_a_407_);
lean_ctor_set(v_reuseFailAlloc_414_, 1, v_a_408_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
}
}
v___jp_417_:
{
lean_object* v___x_422_; lean_object* v___x_423_; uint8_t v___x_424_; 
v___x_422_ = lean_unsigned_to_nat(3u);
v___x_423_ = l_Lean_Syntax_getArg(v_stx_276_, v___x_422_);
v___x_424_ = l_Lean_Syntax_isNone(v___x_423_);
if (v___x_424_ == 0)
{
uint8_t v___x_425_; 
lean_inc(v___x_423_);
v___x_425_ = l_Lean_Syntax_matchesNull(v___x_423_, v___x_416_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; lean_object* v___x_427_; 
lean_dec(v___x_423_);
lean_dec(v_gen_419_);
lean_dec(v___y_418_);
lean_dec(v_stx_276_);
v___x_426_ = lean_box(0);
v___x_427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
lean_ctor_set(v___x_427_, 1, v___y_421_);
return v___x_427_;
}
else
{
lean_object* v_motive_428_; lean_object* v___x_429_; 
v_motive_428_ = l_Lean_Syntax_getArg(v___x_423_, v___x_333_);
lean_dec(v___x_423_);
v___x_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_429_, 0, v_motive_428_);
v___y_369_ = v_gen_419_;
v___y_370_ = v___y_418_;
v_motive_371_ = v___x_429_;
v___y_372_ = v___y_420_;
v___y_373_ = v___y_421_;
goto v___jp_368_;
}
}
else
{
lean_object* v___x_430_; 
lean_dec(v___x_423_);
v___x_430_ = lean_box(0);
v___y_369_ = v_gen_419_;
v___y_370_ = v___y_418_;
v_motive_371_ = v___x_430_;
v___y_372_ = v___y_420_;
v___y_373_ = v___y_421_;
goto v___jp_368_;
}
}
v___jp_431_:
{
lean_object* v___x_435_; lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_435_ = lean_unsigned_to_nat(2u);
v___x_436_ = l_Lean_Syntax_getArg(v_stx_276_, v___x_435_);
v___x_437_ = l_Lean_Syntax_isNone(v___x_436_);
if (v___x_437_ == 0)
{
uint8_t v___x_438_; 
lean_inc(v___x_436_);
v___x_438_ = l_Lean_Syntax_matchesNull(v___x_436_, v___x_416_);
if (v___x_438_ == 0)
{
lean_object* v___x_439_; lean_object* v___x_440_; 
lean_dec(v___x_436_);
lean_dec(v_dep_x3f_432_);
lean_dec(v_stx_276_);
v___x_439_ = lean_box(0);
v___x_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
lean_ctor_set(v___x_440_, 1, v___y_434_);
return v___x_440_;
}
else
{
lean_object* v_gen_441_; lean_object* v___x_442_; 
v_gen_441_ = l_Lean_Syntax_getArg(v___x_436_, v___x_333_);
lean_dec(v___x_436_);
v___x_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_442_, 0, v_gen_441_);
v___y_418_ = v_dep_x3f_432_;
v_gen_419_ = v___x_442_;
v___y_420_ = v___y_433_;
v___y_421_ = v___y_434_;
goto v___jp_417_;
}
}
else
{
lean_object* v___x_443_; 
lean_dec(v___x_436_);
v___x_443_ = lean_box(0);
v___y_418_ = v_dep_x3f_432_;
v_gen_419_ = v___x_443_;
v___y_420_ = v___y_433_;
v___y_421_ = v___y_434_;
goto v___jp_417_;
}
}
}
v___jp_306_:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
lean_inc_ref_n(v___y_308_, 3);
v___x_318_ = l_Array_append___redArg(v___y_308_, v___y_317_);
lean_dec_ref(v___y_317_);
lean_inc_n(v___y_314_, 3);
lean_inc_n(v___y_316_, 5);
v___x_319_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_319_, 0, v___y_316_);
lean_ctor_set(v___x_319_, 1, v___y_314_);
lean_ctor_set(v___x_319_, 2, v___x_318_);
v___x_320_ = l_Array_append___redArg(v___y_308_, v___y_311_);
lean_dec_ref(v___y_311_);
v___x_321_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_321_, 0, v___y_316_);
lean_ctor_set(v___x_321_, 1, v___y_314_);
lean_ctor_set(v___x_321_, 2, v___x_320_);
v___x_322_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__2));
v___x_323_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_323_, 0, v___y_316_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
v___x_324_ = l_Array_append___redArg(v___y_308_, v___y_313_);
lean_dec_ref(v___y_313_);
v___x_325_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_325_, 0, v___y_316_);
lean_ctor_set(v___x_325_, 1, v___y_314_);
lean_ctor_set(v___x_325_, 2, v___x_324_);
lean_inc(v___y_310_);
v___x_326_ = l_Lean_Syntax_node1(v___y_316_, v___y_310_, v___x_325_);
v___x_327_ = l_Lean_Syntax_node7(v___y_316_, v___x_305_, v___y_309_, v___y_315_, v___y_312_, v___x_319_, v___x_321_, v___x_323_, v___x_326_);
v___x_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
v___x_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
lean_ctor_set(v___x_329_, 1, v___y_307_);
return v___x_329_;
}
}
else
{
lean_object* v___x_452_; lean_object* v___y_454_; lean_object* v___y_455_; lean_object* v___y_456_; lean_object* v___y_457_; lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___y_460_; lean_object* v___y_461_; lean_object* v___y_462_; lean_object* v___y_463_; lean_object* v___y_470_; lean_object* v_motive_471_; lean_object* v___y_472_; lean_object* v___y_473_; lean_object* v___x_517_; lean_object* v_gen_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_452_ = lean_unsigned_to_nat(0u);
v___x_517_ = lean_unsigned_to_nat(1u);
v___x_531_ = l_Lean_Syntax_getArg(v_stx_276_, v___x_517_);
v___x_532_ = l_Lean_Syntax_isNone(v___x_531_);
if (v___x_532_ == 0)
{
uint8_t v___x_533_; 
lean_inc(v___x_531_);
v___x_533_ = l_Lean_Syntax_matchesNull(v___x_531_, v___x_517_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; lean_object* v___x_535_; 
lean_dec(v___x_531_);
lean_dec(v_stx_276_);
v___x_534_ = lean_box(0);
v___x_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
lean_ctor_set(v___x_535_, 1, v_a_278_);
return v___x_535_;
}
else
{
lean_object* v_gen_536_; lean_object* v___x_537_; 
v_gen_536_ = l_Lean_Syntax_getArg(v___x_531_, v___x_452_);
lean_dec(v___x_531_);
v___x_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_537_, 0, v_gen_536_);
v_gen_519_ = v___x_537_;
v___y_520_ = v_a_277_;
v___y_521_ = v_a_278_;
goto v___jp_518_;
}
}
else
{
lean_object* v___x_538_; 
lean_dec(v___x_531_);
v___x_538_ = lean_box(0);
v_gen_519_ = v___x_538_;
v___y_520_ = v_a_277_;
v___y_521_ = v_a_278_;
goto v___jp_518_;
}
v___jp_453_:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
lean_inc_ref(v___y_456_);
v___x_464_ = l_Array_append___redArg(v___y_456_, v___y_463_);
lean_dec_ref(v___y_463_);
lean_inc(v___y_457_);
lean_inc(v___y_458_);
v___x_465_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_465_, 0, v___y_458_);
lean_ctor_set(v___x_465_, 1, v___y_457_);
lean_ctor_set(v___x_465_, 2, v___x_464_);
if (lean_obj_tag(v___y_454_) == 1)
{
lean_object* v_val_466_; lean_object* v___x_467_; 
v_val_466_ = lean_ctor_get(v___y_454_, 0);
lean_inc(v_val_466_);
lean_dec_ref_known(v___y_454_, 1);
v___x_467_ = l_Array_mkArray1___redArg(v_val_466_);
v___y_282_ = v___y_455_;
v___y_283_ = v___y_456_;
v___y_284_ = v___y_457_;
v___y_285_ = v___x_465_;
v___y_286_ = v___y_458_;
v___y_287_ = v___y_459_;
v___y_288_ = v___y_461_;
v___y_289_ = v___y_460_;
v___y_290_ = v___y_462_;
v___y_291_ = v___x_467_;
goto v___jp_281_;
}
else
{
lean_object* v___x_468_; 
lean_dec(v___y_454_);
v___x_468_ = ((lean_object*)(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5));
v___y_282_ = v___y_455_;
v___y_283_ = v___y_456_;
v___y_284_ = v___y_457_;
v___y_285_ = v___x_465_;
v___y_286_ = v___y_458_;
v___y_287_ = v___y_459_;
v___y_288_ = v___y_461_;
v___y_289_ = v___y_460_;
v___y_290_ = v___y_462_;
v___y_291_ = v___x_468_;
goto v___jp_281_;
}
}
v___jp_469_:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_474_ = lean_unsigned_to_nat(5u);
v___x_475_ = l_Lean_Syntax_getArg(v_stx_276_, v___x_474_);
v___x_476_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6));
lean_inc(v___x_475_);
v___x_477_ = l_Lean_Syntax_isOfKind(v___x_475_, v___x_476_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; lean_object* v___x_479_; 
lean_dec(v___x_475_);
lean_dec(v_motive_471_);
lean_dec(v___y_470_);
lean_dec(v_stx_276_);
v___x_478_ = lean_box(0);
v___x_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
lean_ctor_set(v___x_479_, 1, v___y_473_);
return v___x_479_;
}
else
{
lean_object* v___x_480_; lean_object* v_alts_481_; lean_object* v___x_482_; 
v___x_480_ = l_Lean_Syntax_getArg(v___x_475_, v___x_452_);
lean_dec(v___x_475_);
v_alts_481_ = l_Lean_Syntax_getArgs(v___x_480_);
lean_dec(v___x_480_);
v___x_482_ = l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand(v_alts_481_, v___y_472_, v___y_473_);
lean_dec_ref(v_alts_481_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
if (lean_obj_tag(v_a_483_) == 0)
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_492_; 
lean_dec(v_motive_471_);
lean_dec(v___y_470_);
lean_dec(v_stx_276_);
v_a_484_ = lean_ctor_get(v___x_482_, 1);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_492_ == 0)
{
lean_object* v_unused_493_; 
v_unused_493_ = lean_ctor_get(v___x_482_, 0);
lean_dec(v_unused_493_);
v___x_486_ = v___x_482_;
v_isShared_487_ = v_isSharedCheck_492_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_482_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_492_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_488_; lean_object* v___x_490_; 
v___x_488_ = lean_box(0);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 0, v___x_488_);
v___x_490_ = v___x_486_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_488_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_a_484_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
else
{
lean_object* v_a_494_; lean_object* v_val_495_; lean_object* v_ref_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; uint8_t v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
lean_inc_ref(v_a_483_);
v_a_494_ = lean_ctor_get(v___x_482_, 1);
lean_inc(v_a_494_);
lean_dec_ref_known(v___x_482_, 2);
v_val_495_ = lean_ctor_get(v_a_483_, 0);
lean_inc(v_val_495_);
lean_dec_ref_known(v_a_483_, 1);
v_ref_496_ = lean_ctor_get(v___y_472_, 5);
v___x_497_ = lean_unsigned_to_nat(3u);
v___x_498_ = l_Lean_Syntax_getArg(v_stx_276_, v___x_497_);
lean_dec(v_stx_276_);
v___x_499_ = l_Lean_Syntax_getArgs(v___x_498_);
lean_dec(v___x_498_);
v___x_500_ = 0;
v___x_501_ = l_Lean_SourceInfo_fromRef(v_ref_496_, v___x_500_);
lean_inc(v___x_501_);
v___x_502_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
lean_ctor_set(v___x_502_, 1, v___x_279_);
v___x_503_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__1));
v___x_504_ = lean_obj_once(&l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7, &l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7_once, _init_l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7);
if (lean_obj_tag(v___y_470_) == 1)
{
lean_object* v_val_505_; lean_object* v___x_506_; 
v_val_505_ = lean_ctor_get(v___y_470_, 0);
lean_inc(v_val_505_);
lean_dec_ref_known(v___y_470_, 1);
v___x_506_ = l_Array_mkArray1___redArg(v_val_505_);
v___y_454_ = v_motive_471_;
v___y_455_ = v___x_499_;
v___y_456_ = v___x_504_;
v___y_457_ = v___x_503_;
v___y_458_ = v___x_501_;
v___y_459_ = v_a_494_;
v___y_460_ = v_val_495_;
v___y_461_ = v___x_476_;
v___y_462_ = v___x_502_;
v___y_463_ = v___x_506_;
goto v___jp_453_;
}
else
{
lean_object* v___x_507_; 
lean_dec(v___y_470_);
v___x_507_ = ((lean_object*)(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5));
v___y_454_ = v_motive_471_;
v___y_455_ = v___x_499_;
v___y_456_ = v___x_504_;
v___y_457_ = v___x_503_;
v___y_458_ = v___x_501_;
v___y_459_ = v_a_494_;
v___y_460_ = v_val_495_;
v___y_461_ = v___x_476_;
v___y_462_ = v___x_502_;
v___y_463_ = v___x_507_;
goto v___jp_453_;
}
}
}
else
{
lean_object* v_a_508_; lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_516_; 
lean_dec(v_motive_471_);
lean_dec(v___y_470_);
lean_dec(v_stx_276_);
v_a_508_ = lean_ctor_get(v___x_482_, 0);
v_a_509_ = lean_ctor_get(v___x_482_, 1);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_516_ == 0)
{
v___x_511_ = v___x_482_;
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_inc(v_a_508_);
lean_dec(v___x_482_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
if (v_isShared_512_ == 0)
{
v___x_514_ = v___x_511_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_a_508_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_a_509_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
}
v___jp_518_:
{
lean_object* v___x_522_; lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_522_ = lean_unsigned_to_nat(2u);
v___x_523_ = l_Lean_Syntax_getArg(v_stx_276_, v___x_522_);
v___x_524_ = l_Lean_Syntax_isNone(v___x_523_);
if (v___x_524_ == 0)
{
uint8_t v___x_525_; 
lean_inc(v___x_523_);
v___x_525_ = l_Lean_Syntax_matchesNull(v___x_523_, v___x_517_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; lean_object* v___x_527_; 
lean_dec(v___x_523_);
lean_dec(v_gen_519_);
lean_dec(v_stx_276_);
v___x_526_ = lean_box(0);
v___x_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
lean_ctor_set(v___x_527_, 1, v___y_521_);
return v___x_527_;
}
else
{
lean_object* v_motive_528_; lean_object* v___x_529_; 
v_motive_528_ = l_Lean_Syntax_getArg(v___x_523_, v___x_452_);
lean_dec(v___x_523_);
v___x_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_529_, 0, v_motive_528_);
v___y_470_ = v_gen_519_;
v_motive_471_ = v___x_529_;
v___y_472_ = v___y_520_;
v___y_473_ = v___y_521_;
goto v___jp_469_;
}
}
else
{
lean_object* v___x_530_; 
lean_dec(v___x_523_);
v___x_530_ = lean_box(0);
v___y_470_ = v_gen_519_;
v_motive_471_ = v___x_530_;
v___y_472_ = v___y_520_;
v___y_473_ = v___y_521_;
goto v___jp_469_;
}
}
}
v___jp_281_:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
lean_inc_ref_n(v___y_283_, 3);
v___x_292_ = l_Array_append___redArg(v___y_283_, v___y_291_);
lean_dec_ref(v___y_291_);
lean_inc_n(v___y_284_, 3);
lean_inc_n(v___y_286_, 5);
v___x_293_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_293_, 0, v___y_286_);
lean_ctor_set(v___x_293_, 1, v___y_284_);
lean_ctor_set(v___x_293_, 2, v___x_292_);
v___x_294_ = l_Array_append___redArg(v___y_283_, v___y_282_);
lean_dec_ref(v___y_282_);
v___x_295_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_295_, 0, v___y_286_);
lean_ctor_set(v___x_295_, 1, v___y_284_);
lean_ctor_set(v___x_295_, 2, v___x_294_);
v___x_296_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__2));
v___x_297_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_297_, 0, v___y_286_);
lean_ctor_set(v___x_297_, 1, v___x_296_);
v___x_298_ = l_Array_append___redArg(v___y_283_, v___y_289_);
lean_dec_ref(v___y_289_);
v___x_299_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_299_, 0, v___y_286_);
lean_ctor_set(v___x_299_, 1, v___y_284_);
lean_ctor_set(v___x_299_, 2, v___x_298_);
lean_inc(v___y_288_);
v___x_300_ = l_Lean_Syntax_node1(v___y_286_, v___y_288_, v___x_299_);
v___x_301_ = l_Lean_Syntax_node6(v___y_286_, v___x_280_, v___y_290_, v___y_285_, v___x_293_, v___x_295_, v___x_297_, v___x_300_);
v___x_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
v___x_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
lean_ctor_set(v___x_303_, 1, v___y_287_);
return v___x_303_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___boxed(lean_object* v_stx_539_, lean_object* v_a_540_, lean_object* v_a_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Lean_Elab_Term_expandMatchAlts_x3f(v_stx_539_, v_a_540_, v_a_541_);
lean_dec_ref(v_a_540_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0(lean_object* v_as_551_, size_t v_sz_552_, size_t v_i_553_, lean_object* v_b_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
uint8_t v___x_557_; 
v___x_557_ = lean_usize_dec_lt(v_i_553_, v_sz_552_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; 
v___x_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_558_, 0, v_b_554_);
lean_ctor_set(v___x_558_, 1, v___y_556_);
return v___x_558_;
}
else
{
lean_object* v_ref_559_; lean_object* v_a_560_; uint8_t v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; size_t v___x_569_; size_t v___x_570_; 
v_ref_559_ = lean_ctor_get(v___y_555_, 0);
v_a_560_ = lean_array_uget_borrowed(v_as_551_, v_i_553_);
v___x_561_ = 0;
v___x_562_ = l_Lean_SourceInfo_fromRef(v_ref_559_, v___x_561_);
v___x_563_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__1));
v___x_564_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__2));
lean_inc_n(v___x_562_, 2);
v___x_565_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_562_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
v___x_566_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__3));
v___x_567_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_562_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
lean_inc(v_a_560_);
v___x_568_ = l_Lean_Syntax_node4(v___x_562_, v___x_563_, v___x_565_, v_a_560_, v___x_567_, v_b_554_);
v___x_569_ = ((size_t)1ULL);
v___x_570_ = lean_usize_add(v_i_553_, v___x_569_);
v_i_553_ = v___x_570_;
v_b_554_ = v___x_568_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___boxed(lean_object* v_as_572_, lean_object* v_sz_573_, lean_object* v_i_574_, lean_object* v_b_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
size_t v_sz_boxed_578_; size_t v_i_boxed_579_; lean_object* v_res_580_; 
v_sz_boxed_578_ = lean_unbox_usize(v_sz_573_);
lean_dec(v_sz_573_);
v_i_boxed_579_ = lean_unbox_usize(v_i_574_);
lean_dec(v_i_574_);
v_res_580_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0(v_as_572_, v_sz_boxed_578_, v_i_boxed_579_, v_b_575_, v___y_576_, v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec_ref(v_as_572_);
return v_res_580_;
}
}
static lean_object* _init_l_Lean_Elab_Term_clearInMatchAlt___closed__0(void){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_581_ = l_Lean_firstFrontendMacroScope;
v___x_582_ = lean_box(0);
v___x_583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
lean_ctor_set(v___x_583_, 1, v___x_581_);
return v___x_583_;
}
}
static lean_object* _init_l_Lean_Elab_Term_clearInMatchAlt___closed__1(void){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_584_ = lean_unsigned_to_nat(1u);
v___x_585_ = l_Lean_firstFrontendMacroScope;
v___x_586_ = lean_nat_add(v___x_585_, v___x_584_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatchAlt(lean_object* v_stx_587_, lean_object* v_vars_588_){
_start:
{
if (lean_obj_tag(v_stx_587_) == 1)
{
lean_object* v_info_589_; lean_object* v_kind_590_; lean_object* v_args_591_; lean_object* v___x_592_; lean_object* v___x_593_; uint8_t v___x_594_; 
v_info_589_ = lean_ctor_get(v_stx_587_, 0);
v_kind_590_ = lean_ctor_get(v_stx_587_, 1);
v_args_591_ = lean_ctor_get(v_stx_587_, 2);
v___x_592_ = lean_unsigned_to_nat(3u);
v___x_593_ = lean_array_get_size(v_args_591_);
v___x_594_ = lean_nat_dec_lt(v___x_592_, v___x_593_);
if (v___x_594_ == 0)
{
return v_stx_587_;
}
else
{
lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_611_; 
lean_inc_ref(v_args_591_);
lean_inc(v_kind_590_);
lean_inc(v_info_589_);
v_isSharedCheck_611_ = !lean_is_exclusive(v_stx_587_);
if (v_isSharedCheck_611_ == 0)
{
lean_object* v_unused_612_; lean_object* v_unused_613_; lean_object* v_unused_614_; 
v_unused_612_ = lean_ctor_get(v_stx_587_, 2);
lean_dec(v_unused_612_);
v_unused_613_ = lean_ctor_get(v_stx_587_, 1);
lean_dec(v_unused_613_);
v_unused_614_ = lean_ctor_get(v_stx_587_, 0);
lean_dec(v_unused_614_);
v___x_596_ = v_stx_587_;
v_isShared_597_ = v_isSharedCheck_611_;
goto v_resetjp_595_;
}
else
{
lean_dec(v_stx_587_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_611_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v_v_598_; size_t v_sz_599_; size_t v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v_fst_604_; lean_object* v___x_605_; lean_object* v_xs_x27_606_; lean_object* v___x_607_; lean_object* v___x_609_; 
v_v_598_ = lean_array_fget_borrowed(v_args_591_, v___x_592_);
v_sz_599_ = lean_array_size(v_vars_588_);
v___x_600_ = ((size_t)0ULL);
v___x_601_ = lean_obj_once(&l_Lean_Elab_Term_clearInMatchAlt___closed__0, &l_Lean_Elab_Term_clearInMatchAlt___closed__0_once, _init_l_Lean_Elab_Term_clearInMatchAlt___closed__0);
v___x_602_ = lean_obj_once(&l_Lean_Elab_Term_clearInMatchAlt___closed__1, &l_Lean_Elab_Term_clearInMatchAlt___closed__1_once, _init_l_Lean_Elab_Term_clearInMatchAlt___closed__1);
lean_inc(v_v_598_);
v___x_603_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0(v_vars_588_, v_sz_599_, v___x_600_, v_v_598_, v___x_601_, v___x_602_);
v_fst_604_ = lean_ctor_get(v___x_603_, 0);
lean_inc(v_fst_604_);
lean_dec_ref(v___x_603_);
v___x_605_ = lean_box(0);
v_xs_x27_606_ = lean_array_fset(v_args_591_, v___x_592_, v___x_605_);
v___x_607_ = lean_array_fset(v_xs_x27_606_, v___x_592_, v_fst_604_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 2, v___x_607_);
v___x_609_ = v___x_596_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_info_589_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_kind_590_);
lean_ctor_set(v_reuseFailAlloc_610_, 2, v___x_607_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
else
{
return v_stx_587_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatchAlt___boxed(lean_object* v_stx_615_, lean_object* v_vars_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Lean_Elab_Term_clearInMatchAlt(v_stx_615_, v_vars_616_);
lean_dec_ref(v_vars_616_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_clearInMatch_spec__0(lean_object* v_vars_618_, size_t v_sz_619_, size_t v_i_620_, lean_object* v_bs_621_){
_start:
{
uint8_t v___x_622_; 
v___x_622_ = lean_usize_dec_lt(v_i_620_, v_sz_619_);
if (v___x_622_ == 0)
{
return v_bs_621_;
}
else
{
lean_object* v_v_623_; lean_object* v___x_624_; lean_object* v_bs_x27_625_; lean_object* v___x_626_; size_t v___x_627_; size_t v___x_628_; lean_object* v___x_629_; 
v_v_623_ = lean_array_uget(v_bs_621_, v_i_620_);
v___x_624_ = lean_unsigned_to_nat(0u);
v_bs_x27_625_ = lean_array_uset(v_bs_621_, v_i_620_, v___x_624_);
v___x_626_ = l_Lean_Elab_Term_clearInMatchAlt(v_v_623_, v_vars_618_);
v___x_627_ = ((size_t)1ULL);
v___x_628_ = lean_usize_add(v_i_620_, v___x_627_);
v___x_629_ = lean_array_uset(v_bs_x27_625_, v_i_620_, v___x_626_);
v_i_620_ = v___x_628_;
v_bs_621_ = v___x_629_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_clearInMatch_spec__0___boxed(lean_object* v_vars_631_, lean_object* v_sz_632_, lean_object* v_i_633_, lean_object* v_bs_634_){
_start:
{
size_t v_sz_boxed_635_; size_t v_i_boxed_636_; lean_object* v_res_637_; 
v_sz_boxed_635_ = lean_unbox_usize(v_sz_632_);
lean_dec(v_sz_632_);
v_i_boxed_636_ = lean_unbox_usize(v_i_633_);
lean_dec(v_i_633_);
v_res_637_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_clearInMatch_spec__0(v_vars_631_, v_sz_boxed_635_, v_i_boxed_636_, v_bs_634_);
lean_dec_ref(v_vars_631_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatch(lean_object* v_stx_638_, lean_object* v_vars_639_, lean_object* v_a_640_, lean_object* v_a_641_){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
v___x_642_ = lean_array_get_size(v_vars_639_);
v___x_643_ = lean_unsigned_to_nat(0u);
v___x_644_ = lean_nat_dec_eq(v___x_642_, v___x_643_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_686_; lean_object* v_motive_687_; lean_object* v___y_688_; lean_object* v___y_689_; uint8_t v___x_711_; 
v___x_645_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__0));
v___x_646_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1));
lean_inc(v_stx_638_);
v___x_711_ = l_Lean_Syntax_isOfKind(v_stx_638_, v___x_646_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; 
v___x_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_712_, 0, v_stx_638_);
lean_ctor_set(v___x_712_, 1, v_a_641_);
return v___x_712_;
}
else
{
lean_object* v___x_713_; lean_object* v_gen_715_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_713_ = lean_unsigned_to_nat(1u);
v___x_726_ = l_Lean_Syntax_getArg(v_stx_638_, v___x_713_);
v___x_727_ = l_Lean_Syntax_isNone(v___x_726_);
if (v___x_727_ == 0)
{
uint8_t v___x_728_; 
lean_inc(v___x_726_);
v___x_728_ = l_Lean_Syntax_matchesNull(v___x_726_, v___x_713_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; 
lean_dec(v___x_726_);
v___x_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_729_, 0, v_stx_638_);
lean_ctor_set(v___x_729_, 1, v_a_641_);
return v___x_729_;
}
else
{
lean_object* v_gen_730_; lean_object* v___x_731_; 
v_gen_730_ = l_Lean_Syntax_getArg(v___x_726_, v___x_643_);
lean_dec(v___x_726_);
v___x_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_731_, 0, v_gen_730_);
v_gen_715_ = v___x_731_;
v___y_716_ = v_a_640_;
v___y_717_ = v_a_641_;
goto v___jp_714_;
}
}
else
{
lean_object* v___x_732_; 
lean_dec(v___x_726_);
v___x_732_ = lean_box(0);
v_gen_715_ = v___x_732_;
v___y_716_ = v_a_640_;
v___y_717_ = v_a_641_;
goto v___jp_714_;
}
v___jp_714_:
{
lean_object* v___x_718_; lean_object* v___x_719_; uint8_t v___x_720_; 
v___x_718_ = lean_unsigned_to_nat(2u);
v___x_719_ = l_Lean_Syntax_getArg(v_stx_638_, v___x_718_);
v___x_720_ = l_Lean_Syntax_isNone(v___x_719_);
if (v___x_720_ == 0)
{
uint8_t v___x_721_; 
lean_inc(v___x_719_);
v___x_721_ = l_Lean_Syntax_matchesNull(v___x_719_, v___x_713_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; 
lean_dec(v___x_719_);
lean_dec(v_gen_715_);
v___x_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_722_, 0, v_stx_638_);
lean_ctor_set(v___x_722_, 1, v___y_717_);
return v___x_722_;
}
else
{
lean_object* v_motive_723_; lean_object* v___x_724_; 
v_motive_723_ = l_Lean_Syntax_getArg(v___x_719_, v___x_643_);
lean_dec(v___x_719_);
v___x_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_724_, 0, v_motive_723_);
v___y_686_ = v_gen_715_;
v_motive_687_ = v___x_724_;
v___y_688_ = v___y_716_;
v___y_689_ = v___y_717_;
goto v___jp_685_;
}
}
else
{
lean_object* v___x_725_; 
lean_dec(v___x_719_);
v___x_725_ = lean_box(0);
v___y_686_ = v_gen_715_;
v_motive_687_ = v___x_725_;
v___y_688_ = v___y_716_;
v___y_689_ = v___y_717_;
goto v___jp_685_;
}
}
}
v___jp_647_:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
lean_inc_ref_n(v___y_654_, 3);
v___x_658_ = l_Array_append___redArg(v___y_654_, v___y_657_);
lean_dec_ref(v___y_657_);
lean_inc_n(v___y_649_, 3);
lean_inc_n(v___y_653_, 5);
v___x_659_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_659_, 0, v___y_653_);
lean_ctor_set(v___x_659_, 1, v___y_649_);
lean_ctor_set(v___x_659_, 2, v___x_658_);
v___x_660_ = l_Array_append___redArg(v___y_654_, v___y_656_);
lean_dec_ref(v___y_656_);
v___x_661_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_661_, 0, v___y_653_);
lean_ctor_set(v___x_661_, 1, v___y_649_);
lean_ctor_set(v___x_661_, 2, v___x_660_);
v___x_662_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__2));
v___x_663_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_663_, 0, v___y_653_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
v___x_664_ = l_Array_append___redArg(v___y_654_, v___y_651_);
lean_dec_ref(v___y_651_);
v___x_665_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_665_, 0, v___y_653_);
lean_ctor_set(v___x_665_, 1, v___y_649_);
lean_ctor_set(v___x_665_, 2, v___x_664_);
lean_inc(v___y_648_);
v___x_666_ = l_Lean_Syntax_node1(v___y_653_, v___y_648_, v___x_665_);
v___x_667_ = l_Lean_Syntax_node6(v___y_653_, v___x_646_, v___y_655_, v___y_650_, v___x_659_, v___x_661_, v___x_663_, v___x_666_);
v___x_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
lean_ctor_set(v___x_668_, 1, v___y_652_);
return v___x_668_;
}
v___jp_669_:
{
lean_object* v___x_680_; lean_object* v___x_681_; 
lean_inc_ref(v___y_676_);
v___x_680_ = l_Array_append___redArg(v___y_676_, v___y_679_);
lean_dec_ref(v___y_679_);
lean_inc(v___y_671_);
lean_inc(v___y_675_);
v___x_681_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_681_, 0, v___y_675_);
lean_ctor_set(v___x_681_, 1, v___y_671_);
lean_ctor_set(v___x_681_, 2, v___x_680_);
if (lean_obj_tag(v___y_673_) == 1)
{
lean_object* v_val_682_; lean_object* v___x_683_; 
v_val_682_ = lean_ctor_get(v___y_673_, 0);
lean_inc(v_val_682_);
lean_dec_ref_known(v___y_673_, 1);
v___x_683_ = l_Array_mkArray1___redArg(v_val_682_);
v___y_648_ = v___y_670_;
v___y_649_ = v___y_671_;
v___y_650_ = v___x_681_;
v___y_651_ = v___y_672_;
v___y_652_ = v___y_674_;
v___y_653_ = v___y_675_;
v___y_654_ = v___y_676_;
v___y_655_ = v___y_678_;
v___y_656_ = v___y_677_;
v___y_657_ = v___x_683_;
goto v___jp_647_;
}
else
{
lean_object* v___x_684_; 
lean_dec(v___y_673_);
v___x_684_ = ((lean_object*)(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5));
v___y_648_ = v___y_670_;
v___y_649_ = v___y_671_;
v___y_650_ = v___x_681_;
v___y_651_ = v___y_672_;
v___y_652_ = v___y_674_;
v___y_653_ = v___y_675_;
v___y_654_ = v___y_676_;
v___y_655_ = v___y_678_;
v___y_656_ = v___y_677_;
v___y_657_ = v___x_684_;
goto v___jp_647_;
}
}
v___jp_685_:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; uint8_t v___x_693_; 
v___x_690_ = lean_unsigned_to_nat(5u);
v___x_691_ = l_Lean_Syntax_getArg(v_stx_638_, v___x_690_);
v___x_692_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6));
lean_inc(v___x_691_);
v___x_693_ = l_Lean_Syntax_isOfKind(v___x_691_, v___x_692_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; 
lean_dec(v___x_691_);
lean_dec(v_motive_687_);
lean_dec(v___y_686_);
v___x_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_694_, 0, v_stx_638_);
lean_ctor_set(v___x_694_, 1, v___y_689_);
return v___x_694_;
}
else
{
lean_object* v_ref_695_; lean_object* v___x_696_; lean_object* v_alts_697_; size_t v_sz_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; size_t v___x_702_; lean_object* v_alts_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v_ref_695_ = lean_ctor_get(v___y_688_, 5);
v___x_696_ = l_Lean_Syntax_getArg(v___x_691_, v___x_643_);
lean_dec(v___x_691_);
v_alts_697_ = l_Lean_Syntax_getArgs(v___x_696_);
lean_dec(v___x_696_);
v_sz_698_ = lean_array_size(v_alts_697_);
v___x_699_ = lean_unsigned_to_nat(3u);
v___x_700_ = l_Lean_Syntax_getArg(v_stx_638_, v___x_699_);
lean_dec(v_stx_638_);
v___x_701_ = l_Lean_Syntax_getArgs(v___x_700_);
lean_dec(v___x_700_);
v___x_702_ = ((size_t)0ULL);
v_alts_703_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_clearInMatch_spec__0(v_vars_639_, v_sz_698_, v___x_702_, v_alts_697_);
v___x_704_ = l_Lean_SourceInfo_fromRef(v_ref_695_, v___x_644_);
lean_inc(v___x_704_);
v___x_705_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
lean_ctor_set(v___x_705_, 1, v___x_645_);
v___x_706_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__1));
v___x_707_ = lean_obj_once(&l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7, &l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7_once, _init_l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7);
if (lean_obj_tag(v___y_686_) == 1)
{
lean_object* v_val_708_; lean_object* v___x_709_; 
v_val_708_ = lean_ctor_get(v___y_686_, 0);
lean_inc(v_val_708_);
lean_dec_ref_known(v___y_686_, 1);
v___x_709_ = l_Array_mkArray1___redArg(v_val_708_);
v___y_670_ = v___x_692_;
v___y_671_ = v___x_706_;
v___y_672_ = v_alts_703_;
v___y_673_ = v_motive_687_;
v___y_674_ = v___y_689_;
v___y_675_ = v___x_704_;
v___y_676_ = v___x_707_;
v___y_677_ = v___x_701_;
v___y_678_ = v___x_705_;
v___y_679_ = v___x_709_;
goto v___jp_669_;
}
else
{
lean_object* v___x_710_; 
lean_dec(v___y_686_);
v___x_710_ = ((lean_object*)(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5));
v___y_670_ = v___x_692_;
v___y_671_ = v___x_706_;
v___y_672_ = v_alts_703_;
v___y_673_ = v_motive_687_;
v___y_674_ = v___y_689_;
v___y_675_ = v___x_704_;
v___y_676_ = v___x_707_;
v___y_677_ = v___x_701_;
v___y_678_ = v___x_705_;
v___y_679_ = v___x_710_;
goto v___jp_669_;
}
}
}
}
else
{
lean_object* v___x_733_; 
v___x_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_733_, 0, v_stx_638_);
lean_ctor_set(v___x_733_, 1, v_a_641_);
return v___x_733_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatch___boxed(lean_object* v_stx_734_, lean_object* v_vars_735_, lean_object* v_a_736_, lean_object* v_a_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Lean_Elab_Term_clearInMatch(v_stx_734_, v_vars_735_, v_a_736_, v_a_737_);
lean_dec_ref(v_a_736_);
lean_dec_ref(v_vars_735_);
return v_res_738_;
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
