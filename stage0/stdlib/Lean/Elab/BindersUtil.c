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
lean_object* v_a_213_; lean_object* v_a_214_; lean_object* v___y_218_; lean_object* v___x_230_; lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_230_ = lean_unsigned_to_nat(0u);
v___x_231_ = lean_array_get_size(v_alts_206_);
v___x_232_ = lean_nat_dec_lt(v___x_230_, v___x_231_);
if (v___x_232_ == 0)
{
goto v___jp_209_;
}
else
{
if (v___x_232_ == 0)
{
goto v___jp_209_;
}
else
{
size_t v___x_233_; size_t v___x_234_; uint8_t v___x_235_; 
v___x_233_ = ((size_t)0ULL);
v___x_234_ = lean_usize_of_nat(v___x_231_);
v___x_235_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__0(v_alts_206_, v___x_233_, v___x_234_);
if (v___x_235_ == 0)
{
goto v___jp_209_;
}
else
{
lean_object* v___x_236_; 
v___x_236_ = ((lean_object*)(l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand___closed__0));
if (v___x_232_ == 0)
{
v_a_213_ = v___x_236_;
v_a_214_ = v_a_208_;
goto v___jp_212_;
}
else
{
uint8_t v___x_237_; 
v___x_237_ = lean_nat_dec_le(v___x_231_, v___x_231_);
if (v___x_237_ == 0)
{
if (v___x_232_ == 0)
{
v_a_213_ = v___x_236_;
v_a_214_ = v_a_208_;
goto v___jp_212_;
}
else
{
lean_object* v___x_238_; 
v___x_238_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___redArg(v_alts_206_, v___x_233_, v___x_234_, v___x_236_, v_a_208_);
v___y_218_ = v___x_238_;
goto v___jp_217_;
}
}
else
{
lean_object* v___x_239_; 
v___x_239_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___redArg(v_alts_206_, v___x_233_, v___x_234_, v___x_236_, v_a_208_);
v___y_218_ = v___x_239_;
goto v___jp_217_;
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
v___jp_217_:
{
if (lean_obj_tag(v___y_218_) == 0)
{
lean_object* v_a_219_; lean_object* v_a_220_; 
v_a_219_ = lean_ctor_get(v___y_218_, 0);
lean_inc(v_a_219_);
v_a_220_ = lean_ctor_get(v___y_218_, 1);
lean_inc(v_a_220_);
lean_dec_ref_known(v___y_218_, 2);
v_a_213_ = v_a_219_;
v_a_214_ = v_a_220_;
goto v___jp_212_;
}
else
{
lean_object* v_a_221_; lean_object* v_a_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_229_; 
v_a_221_ = lean_ctor_get(v___y_218_, 0);
v_a_222_ = lean_ctor_get(v___y_218_, 1);
v_isSharedCheck_229_ = !lean_is_exclusive(v___y_218_);
if (v_isSharedCheck_229_ == 0)
{
v___x_224_ = v___y_218_;
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_inc(v_a_221_);
lean_dec(v___y_218_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_227_; 
if (v_isShared_225_ == 0)
{
v___x_227_ = v___x_224_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_a_221_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v_a_222_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand___boxed(lean_object* v_alts_240_, lean_object* v_a_241_, lean_object* v_a_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand(v_alts_240_, v_a_241_, v_a_242_);
lean_dec_ref(v_a_241_);
lean_dec_ref(v_alts_240_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1(lean_object* v_as_244_, size_t v_i_245_, size_t v_stop_246_, lean_object* v_b_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___redArg(v_as_244_, v_i_245_, v_stop_246_, v_b_247_, v___y_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___boxed(lean_object* v_as_251_, lean_object* v_i_252_, lean_object* v_stop_253_, lean_object* v_b_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
size_t v_i_boxed_257_; size_t v_stop_boxed_258_; lean_object* v_res_259_; 
v_i_boxed_257_ = lean_unbox_usize(v_i_252_);
lean_dec(v_i_252_);
v_stop_boxed_258_ = lean_unbox_usize(v_stop_253_);
lean_dec(v_stop_253_);
v_res_259_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1(v_as_251_, v_i_boxed_257_, v_stop_boxed_258_, v_b_254_, v___y_255_, v___y_256_);
lean_dec_ref(v___y_255_);
lean_dec_ref(v_as_251_);
return v_res_259_;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7(void){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_Array_mkArray0___redArg();
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f(lean_object* v_stx_280_, lean_object* v_a_281_, lean_object* v_a_282_){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___y_286_; lean_object* v___y_287_; lean_object* v___y_288_; lean_object* v___y_289_; lean_object* v___y_290_; lean_object* v___y_291_; lean_object* v___y_292_; lean_object* v___y_293_; lean_object* v___y_294_; lean_object* v___y_295_; uint8_t v___x_308_; 
v___x_283_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__0));
v___x_284_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1));
lean_inc(v_stx_280_);
v___x_308_ = l_Lean_Syntax_isOfKind(v_stx_280_, v___x_284_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; lean_object* v___y_311_; lean_object* v___y_312_; lean_object* v___y_313_; lean_object* v___y_314_; lean_object* v___y_315_; lean_object* v___y_316_; lean_object* v___y_317_; lean_object* v___y_318_; lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___y_321_; uint8_t v___x_334_; 
v___x_309_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__4));
lean_inc(v_stx_280_);
v___x_334_ = l_Lean_Syntax_isOfKind(v_stx_280_, v___x_309_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; lean_object* v___x_336_; 
lean_dec(v_stx_280_);
v___x_335_ = lean_box(0);
v___x_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set(v___x_336_, 1, v_a_282_);
return v___x_336_;
}
else
{
lean_object* v___x_337_; lean_object* v___y_339_; lean_object* v___y_340_; lean_object* v___y_341_; lean_object* v___y_342_; lean_object* v___y_343_; lean_object* v___y_344_; lean_object* v___y_345_; lean_object* v___y_346_; lean_object* v___y_347_; lean_object* v___y_348_; lean_object* v___y_349_; lean_object* v___y_356_; lean_object* v___y_357_; lean_object* v___y_358_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v___y_364_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___y_373_; lean_object* v___y_374_; lean_object* v_motive_375_; lean_object* v___y_376_; lean_object* v___y_377_; lean_object* v___x_420_; lean_object* v___y_422_; lean_object* v_gen_423_; lean_object* v___y_424_; lean_object* v___y_425_; lean_object* v_dep_x3f_436_; lean_object* v___y_437_; lean_object* v___y_438_; lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_420_ = lean_unsigned_to_nat(1u);
v___x_448_ = l_Lean_Syntax_getArg(v_stx_280_, v___x_420_);
v___x_449_ = l_Lean_Syntax_isNone(v___x_448_);
if (v___x_449_ == 0)
{
uint8_t v___x_450_; 
lean_inc(v___x_448_);
v___x_450_ = l_Lean_Syntax_matchesNull(v___x_448_, v___x_420_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; lean_object* v___x_452_; 
lean_dec(v___x_448_);
lean_dec(v_stx_280_);
v___x_451_ = lean_box(0);
v___x_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
lean_ctor_set(v___x_452_, 1, v_a_282_);
return v___x_452_;
}
else
{
lean_object* v_dep_x3f_453_; lean_object* v___x_454_; 
v_dep_x3f_453_ = l_Lean_Syntax_getArg(v___x_448_, v___x_337_);
lean_dec(v___x_448_);
v___x_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_454_, 0, v_dep_x3f_453_);
v_dep_x3f_436_ = v___x_454_;
v___y_437_ = v_a_281_;
v___y_438_ = v_a_282_;
goto v___jp_435_;
}
}
else
{
lean_object* v___x_455_; 
lean_dec(v___x_448_);
v___x_455_ = lean_box(0);
v_dep_x3f_436_ = v___x_455_;
v___y_437_ = v_a_281_;
v___y_438_ = v_a_282_;
goto v___jp_435_;
}
v___jp_338_:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
lean_inc_ref(v___y_342_);
v___x_350_ = l_Array_append___redArg(v___y_342_, v___y_349_);
lean_dec_ref(v___y_349_);
lean_inc(v___y_341_);
lean_inc(v___y_346_);
v___x_351_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_351_, 0, v___y_346_);
lean_ctor_set(v___x_351_, 1, v___y_341_);
lean_ctor_set(v___x_351_, 2, v___x_350_);
if (lean_obj_tag(v___y_344_) == 1)
{
lean_object* v_val_352_; lean_object* v___x_353_; 
v_val_352_ = lean_ctor_get(v___y_344_, 0);
lean_inc(v_val_352_);
lean_dec_ref_known(v___y_344_, 1);
v___x_353_ = l_Array_mkArray1___redArg(v_val_352_);
v___y_311_ = v___y_339_;
v___y_312_ = v___y_340_;
v___y_313_ = v___x_351_;
v___y_314_ = v___y_341_;
v___y_315_ = v___y_342_;
v___y_316_ = v___y_343_;
v___y_317_ = v___y_345_;
v___y_318_ = v___y_346_;
v___y_319_ = v___y_347_;
v___y_320_ = v___y_348_;
v___y_321_ = v___x_353_;
goto v___jp_310_;
}
else
{
lean_object* v___x_354_; 
lean_dec(v___y_344_);
v___x_354_ = ((lean_object*)(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5));
v___y_311_ = v___y_339_;
v___y_312_ = v___y_340_;
v___y_313_ = v___x_351_;
v___y_314_ = v___y_341_;
v___y_315_ = v___y_342_;
v___y_316_ = v___y_343_;
v___y_317_ = v___y_345_;
v___y_318_ = v___y_346_;
v___y_319_ = v___y_347_;
v___y_320_ = v___y_348_;
v___y_321_ = v___x_354_;
goto v___jp_310_;
}
}
v___jp_355_:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
lean_inc_ref(v___y_358_);
v___x_367_ = l_Array_append___redArg(v___y_358_, v___y_366_);
lean_dec_ref(v___y_366_);
lean_inc(v___y_357_);
lean_inc(v___y_363_);
v___x_368_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_368_, 0, v___y_363_);
lean_ctor_set(v___x_368_, 1, v___y_357_);
lean_ctor_set(v___x_368_, 2, v___x_367_);
if (lean_obj_tag(v___y_362_) == 1)
{
lean_object* v_val_369_; lean_object* v___x_370_; 
v_val_369_ = lean_ctor_get(v___y_362_, 0);
lean_inc(v_val_369_);
lean_dec_ref_known(v___y_362_, 1);
v___x_370_ = l_Array_mkArray1___redArg(v_val_369_);
v___y_339_ = v___x_368_;
v___y_340_ = v___y_356_;
v___y_341_ = v___y_357_;
v___y_342_ = v___y_358_;
v___y_343_ = v___y_359_;
v___y_344_ = v___y_360_;
v___y_345_ = v___y_361_;
v___y_346_ = v___y_363_;
v___y_347_ = v___y_364_;
v___y_348_ = v___y_365_;
v___y_349_ = v___x_370_;
goto v___jp_338_;
}
else
{
lean_object* v___x_371_; 
lean_dec(v___y_362_);
v___x_371_ = ((lean_object*)(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5));
v___y_339_ = v___x_368_;
v___y_340_ = v___y_356_;
v___y_341_ = v___y_357_;
v___y_342_ = v___y_358_;
v___y_343_ = v___y_359_;
v___y_344_ = v___y_360_;
v___y_345_ = v___y_361_;
v___y_346_ = v___y_363_;
v___y_347_ = v___y_364_;
v___y_348_ = v___y_365_;
v___y_349_ = v___x_371_;
goto v___jp_338_;
}
}
v___jp_372_:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; uint8_t v___x_381_; 
v___x_378_ = lean_unsigned_to_nat(6u);
v___x_379_ = l_Lean_Syntax_getArg(v_stx_280_, v___x_378_);
v___x_380_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6));
lean_inc(v___x_379_);
v___x_381_ = l_Lean_Syntax_isOfKind(v___x_379_, v___x_380_);
if (v___x_381_ == 0)
{
lean_object* v___x_382_; lean_object* v___x_383_; 
lean_dec(v___x_379_);
lean_dec(v_motive_375_);
lean_dec(v___y_374_);
lean_dec(v___y_373_);
lean_dec(v_stx_280_);
v___x_382_ = lean_box(0);
v___x_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
lean_ctor_set(v___x_383_, 1, v___y_377_);
return v___x_383_;
}
else
{
lean_object* v___x_384_; lean_object* v_alts_385_; lean_object* v___x_386_; 
v___x_384_ = l_Lean_Syntax_getArg(v___x_379_, v___x_337_);
lean_dec(v___x_379_);
v_alts_385_ = l_Lean_Syntax_getArgs(v___x_384_);
lean_dec(v___x_384_);
v___x_386_ = l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand(v_alts_385_, v___y_376_, v___y_377_);
lean_dec_ref(v_alts_385_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v_a_387_; 
v_a_387_ = lean_ctor_get(v___x_386_, 0);
if (lean_obj_tag(v_a_387_) == 0)
{
lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_396_; 
lean_dec(v_motive_375_);
lean_dec(v___y_374_);
lean_dec(v___y_373_);
lean_dec(v_stx_280_);
v_a_388_ = lean_ctor_get(v___x_386_, 1);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_396_ == 0)
{
lean_object* v_unused_397_; 
v_unused_397_ = lean_ctor_get(v___x_386_, 0);
lean_dec(v_unused_397_);
v___x_390_ = v___x_386_;
v_isShared_391_ = v_isSharedCheck_396_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_a_388_);
lean_dec(v___x_386_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_396_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_392_ = lean_box(0);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 0, v___x_392_);
v___x_394_ = v___x_390_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_392_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v_a_388_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
else
{
lean_object* v_a_398_; lean_object* v_val_399_; lean_object* v_ref_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
lean_inc_ref(v_a_387_);
v_a_398_ = lean_ctor_get(v___x_386_, 1);
lean_inc(v_a_398_);
lean_dec_ref_known(v___x_386_, 2);
v_val_399_ = lean_ctor_get(v_a_387_, 0);
lean_inc(v_val_399_);
lean_dec_ref_known(v_a_387_, 1);
v_ref_400_ = lean_ctor_get(v___y_376_, 5);
v___x_401_ = lean_unsigned_to_nat(4u);
v___x_402_ = l_Lean_Syntax_getArg(v_stx_280_, v___x_401_);
lean_dec(v_stx_280_);
v___x_403_ = l_Lean_Syntax_getArgs(v___x_402_);
lean_dec(v___x_402_);
v___x_404_ = l_Lean_SourceInfo_fromRef(v_ref_400_, v___x_308_);
lean_inc(v___x_404_);
v___x_405_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v___x_283_);
v___x_406_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__1));
v___x_407_ = lean_obj_once(&l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7, &l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7_once, _init_l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7);
if (lean_obj_tag(v___y_373_) == 1)
{
lean_object* v_val_408_; lean_object* v___x_409_; 
v_val_408_ = lean_ctor_get(v___y_373_, 0);
lean_inc(v_val_408_);
lean_dec_ref_known(v___y_373_, 1);
v___x_409_ = l_Array_mkArray1___redArg(v_val_408_);
v___y_356_ = v_a_398_;
v___y_357_ = v___x_406_;
v___y_358_ = v___x_407_;
v___y_359_ = v___x_380_;
v___y_360_ = v_motive_375_;
v___y_361_ = v_val_399_;
v___y_362_ = v___y_374_;
v___y_363_ = v___x_404_;
v___y_364_ = v___x_405_;
v___y_365_ = v___x_403_;
v___y_366_ = v___x_409_;
goto v___jp_355_;
}
else
{
lean_object* v___x_410_; 
lean_dec(v___y_373_);
v___x_410_ = ((lean_object*)(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5));
v___y_356_ = v_a_398_;
v___y_357_ = v___x_406_;
v___y_358_ = v___x_407_;
v___y_359_ = v___x_380_;
v___y_360_ = v_motive_375_;
v___y_361_ = v_val_399_;
v___y_362_ = v___y_374_;
v___y_363_ = v___x_404_;
v___y_364_ = v___x_405_;
v___y_365_ = v___x_403_;
v___y_366_ = v___x_410_;
goto v___jp_355_;
}
}
}
else
{
lean_object* v_a_411_; lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
lean_dec(v_motive_375_);
lean_dec(v___y_374_);
lean_dec(v___y_373_);
lean_dec(v_stx_280_);
v_a_411_ = lean_ctor_get(v___x_386_, 0);
v_a_412_ = lean_ctor_get(v___x_386_, 1);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_419_ == 0)
{
v___x_414_ = v___x_386_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_inc(v_a_411_);
lean_dec(v___x_386_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_417_; 
if (v_isShared_415_ == 0)
{
v___x_417_ = v___x_414_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_a_411_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v_a_412_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
}
v___jp_421_:
{
lean_object* v___x_426_; lean_object* v___x_427_; uint8_t v___x_428_; 
v___x_426_ = lean_unsigned_to_nat(3u);
v___x_427_ = l_Lean_Syntax_getArg(v_stx_280_, v___x_426_);
v___x_428_ = l_Lean_Syntax_isNone(v___x_427_);
if (v___x_428_ == 0)
{
uint8_t v___x_429_; 
lean_inc(v___x_427_);
v___x_429_ = l_Lean_Syntax_matchesNull(v___x_427_, v___x_420_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; lean_object* v___x_431_; 
lean_dec(v___x_427_);
lean_dec(v_gen_423_);
lean_dec(v___y_422_);
lean_dec(v_stx_280_);
v___x_430_ = lean_box(0);
v___x_431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
lean_ctor_set(v___x_431_, 1, v___y_425_);
return v___x_431_;
}
else
{
lean_object* v_motive_432_; lean_object* v___x_433_; 
v_motive_432_ = l_Lean_Syntax_getArg(v___x_427_, v___x_337_);
lean_dec(v___x_427_);
v___x_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_433_, 0, v_motive_432_);
v___y_373_ = v___y_422_;
v___y_374_ = v_gen_423_;
v_motive_375_ = v___x_433_;
v___y_376_ = v___y_424_;
v___y_377_ = v___y_425_;
goto v___jp_372_;
}
}
else
{
lean_object* v___x_434_; 
lean_dec(v___x_427_);
v___x_434_ = lean_box(0);
v___y_373_ = v___y_422_;
v___y_374_ = v_gen_423_;
v_motive_375_ = v___x_434_;
v___y_376_ = v___y_424_;
v___y_377_ = v___y_425_;
goto v___jp_372_;
}
}
v___jp_435_:
{
lean_object* v___x_439_; lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_439_ = lean_unsigned_to_nat(2u);
v___x_440_ = l_Lean_Syntax_getArg(v_stx_280_, v___x_439_);
v___x_441_ = l_Lean_Syntax_isNone(v___x_440_);
if (v___x_441_ == 0)
{
uint8_t v___x_442_; 
lean_inc(v___x_440_);
v___x_442_ = l_Lean_Syntax_matchesNull(v___x_440_, v___x_420_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; lean_object* v___x_444_; 
lean_dec(v___x_440_);
lean_dec(v_dep_x3f_436_);
lean_dec(v_stx_280_);
v___x_443_ = lean_box(0);
v___x_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
lean_ctor_set(v___x_444_, 1, v___y_438_);
return v___x_444_;
}
else
{
lean_object* v_gen_445_; lean_object* v___x_446_; 
v_gen_445_ = l_Lean_Syntax_getArg(v___x_440_, v___x_337_);
lean_dec(v___x_440_);
v___x_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_446_, 0, v_gen_445_);
v___y_422_ = v_dep_x3f_436_;
v_gen_423_ = v___x_446_;
v___y_424_ = v___y_437_;
v___y_425_ = v___y_438_;
goto v___jp_421_;
}
}
else
{
lean_object* v___x_447_; 
lean_dec(v___x_440_);
v___x_447_ = lean_box(0);
v___y_422_ = v_dep_x3f_436_;
v_gen_423_ = v___x_447_;
v___y_424_ = v___y_437_;
v___y_425_ = v___y_438_;
goto v___jp_421_;
}
}
}
v___jp_310_:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
lean_inc_ref_n(v___y_315_, 3);
v___x_322_ = l_Array_append___redArg(v___y_315_, v___y_321_);
lean_dec_ref(v___y_321_);
lean_inc_n(v___y_314_, 3);
lean_inc_n(v___y_318_, 5);
v___x_323_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_323_, 0, v___y_318_);
lean_ctor_set(v___x_323_, 1, v___y_314_);
lean_ctor_set(v___x_323_, 2, v___x_322_);
v___x_324_ = l_Array_append___redArg(v___y_315_, v___y_320_);
lean_dec_ref(v___y_320_);
v___x_325_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_325_, 0, v___y_318_);
lean_ctor_set(v___x_325_, 1, v___y_314_);
lean_ctor_set(v___x_325_, 2, v___x_324_);
v___x_326_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__2));
v___x_327_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_327_, 0, v___y_318_);
lean_ctor_set(v___x_327_, 1, v___x_326_);
v___x_328_ = l_Array_append___redArg(v___y_315_, v___y_317_);
lean_dec_ref(v___y_317_);
v___x_329_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_329_, 0, v___y_318_);
lean_ctor_set(v___x_329_, 1, v___y_314_);
lean_ctor_set(v___x_329_, 2, v___x_328_);
lean_inc(v___y_316_);
v___x_330_ = l_Lean_Syntax_node1(v___y_318_, v___y_316_, v___x_329_);
v___x_331_ = l_Lean_Syntax_node7(v___y_318_, v___x_309_, v___y_319_, v___y_311_, v___y_313_, v___x_323_, v___x_325_, v___x_327_, v___x_330_);
v___x_332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
v___x_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v___y_312_);
return v___x_333_;
}
}
else
{
lean_object* v___x_456_; lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___y_460_; lean_object* v___y_461_; lean_object* v___y_462_; lean_object* v___y_463_; lean_object* v___y_464_; lean_object* v___y_465_; lean_object* v___y_466_; lean_object* v___y_467_; lean_object* v___y_474_; lean_object* v_motive_475_; lean_object* v___y_476_; lean_object* v___y_477_; lean_object* v___x_521_; lean_object* v_gen_523_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_456_ = lean_unsigned_to_nat(0u);
v___x_521_ = lean_unsigned_to_nat(1u);
v___x_535_ = l_Lean_Syntax_getArg(v_stx_280_, v___x_521_);
v___x_536_ = l_Lean_Syntax_isNone(v___x_535_);
if (v___x_536_ == 0)
{
uint8_t v___x_537_; 
lean_inc(v___x_535_);
v___x_537_ = l_Lean_Syntax_matchesNull(v___x_535_, v___x_521_);
if (v___x_537_ == 0)
{
lean_object* v___x_538_; lean_object* v___x_539_; 
lean_dec(v___x_535_);
lean_dec(v_stx_280_);
v___x_538_ = lean_box(0);
v___x_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
lean_ctor_set(v___x_539_, 1, v_a_282_);
return v___x_539_;
}
else
{
lean_object* v_gen_540_; lean_object* v___x_541_; 
v_gen_540_ = l_Lean_Syntax_getArg(v___x_535_, v___x_456_);
lean_dec(v___x_535_);
v___x_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_541_, 0, v_gen_540_);
v_gen_523_ = v___x_541_;
v___y_524_ = v_a_281_;
v___y_525_ = v_a_282_;
goto v___jp_522_;
}
}
else
{
lean_object* v___x_542_; 
lean_dec(v___x_535_);
v___x_542_ = lean_box(0);
v_gen_523_ = v___x_542_;
v___y_524_ = v_a_281_;
v___y_525_ = v_a_282_;
goto v___jp_522_;
}
v___jp_457_:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
lean_inc_ref(v___y_462_);
v___x_468_ = l_Array_append___redArg(v___y_462_, v___y_467_);
lean_dec_ref(v___y_467_);
lean_inc(v___y_460_);
lean_inc(v___y_465_);
v___x_469_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_469_, 0, v___y_465_);
lean_ctor_set(v___x_469_, 1, v___y_460_);
lean_ctor_set(v___x_469_, 2, v___x_468_);
if (lean_obj_tag(v___y_466_) == 1)
{
lean_object* v_val_470_; lean_object* v___x_471_; 
v_val_470_ = lean_ctor_get(v___y_466_, 0);
lean_inc(v_val_470_);
lean_dec_ref_known(v___y_466_, 1);
v___x_471_ = l_Array_mkArray1___redArg(v_val_470_);
v___y_286_ = v___x_469_;
v___y_287_ = v___y_459_;
v___y_288_ = v___y_458_;
v___y_289_ = v___y_460_;
v___y_290_ = v___y_461_;
v___y_291_ = v___y_462_;
v___y_292_ = v___y_464_;
v___y_293_ = v___y_463_;
v___y_294_ = v___y_465_;
v___y_295_ = v___x_471_;
goto v___jp_285_;
}
else
{
lean_object* v___x_472_; 
lean_dec(v___y_466_);
v___x_472_ = ((lean_object*)(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5));
v___y_286_ = v___x_469_;
v___y_287_ = v___y_459_;
v___y_288_ = v___y_458_;
v___y_289_ = v___y_460_;
v___y_290_ = v___y_461_;
v___y_291_ = v___y_462_;
v___y_292_ = v___y_464_;
v___y_293_ = v___y_463_;
v___y_294_ = v___y_465_;
v___y_295_ = v___x_472_;
goto v___jp_285_;
}
}
v___jp_473_:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_478_ = lean_unsigned_to_nat(5u);
v___x_479_ = l_Lean_Syntax_getArg(v_stx_280_, v___x_478_);
v___x_480_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6));
lean_inc(v___x_479_);
v___x_481_ = l_Lean_Syntax_isOfKind(v___x_479_, v___x_480_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; lean_object* v___x_483_; 
lean_dec(v___x_479_);
lean_dec(v_motive_475_);
lean_dec(v___y_474_);
lean_dec(v_stx_280_);
v___x_482_ = lean_box(0);
v___x_483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
lean_ctor_set(v___x_483_, 1, v___y_477_);
return v___x_483_;
}
else
{
lean_object* v___x_484_; lean_object* v_alts_485_; lean_object* v___x_486_; 
v___x_484_ = l_Lean_Syntax_getArg(v___x_479_, v___x_456_);
lean_dec(v___x_479_);
v_alts_485_ = l_Lean_Syntax_getArgs(v___x_484_);
lean_dec(v___x_484_);
v___x_486_ = l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand(v_alts_485_, v___y_476_, v___y_477_);
lean_dec_ref(v_alts_485_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v_a_487_; 
v_a_487_ = lean_ctor_get(v___x_486_, 0);
if (lean_obj_tag(v_a_487_) == 0)
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_496_; 
lean_dec(v_motive_475_);
lean_dec(v___y_474_);
lean_dec(v_stx_280_);
v_a_488_ = lean_ctor_get(v___x_486_, 1);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_496_ == 0)
{
lean_object* v_unused_497_; 
v_unused_497_ = lean_ctor_get(v___x_486_, 0);
lean_dec(v_unused_497_);
v___x_490_ = v___x_486_;
v_isShared_491_ = v_isSharedCheck_496_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_486_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_496_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_492_; lean_object* v___x_494_; 
v___x_492_ = lean_box(0);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 0, v___x_492_);
v___x_494_ = v___x_490_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_492_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v_a_488_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
else
{
lean_object* v_a_498_; lean_object* v_val_499_; lean_object* v_ref_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; uint8_t v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
lean_inc_ref(v_a_487_);
v_a_498_ = lean_ctor_get(v___x_486_, 1);
lean_inc(v_a_498_);
lean_dec_ref_known(v___x_486_, 2);
v_val_499_ = lean_ctor_get(v_a_487_, 0);
lean_inc(v_val_499_);
lean_dec_ref_known(v_a_487_, 1);
v_ref_500_ = lean_ctor_get(v___y_476_, 5);
v___x_501_ = lean_unsigned_to_nat(3u);
v___x_502_ = l_Lean_Syntax_getArg(v_stx_280_, v___x_501_);
lean_dec(v_stx_280_);
v___x_503_ = l_Lean_Syntax_getArgs(v___x_502_);
lean_dec(v___x_502_);
v___x_504_ = 0;
v___x_505_ = l_Lean_SourceInfo_fromRef(v_ref_500_, v___x_504_);
lean_inc(v___x_505_);
v___x_506_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
lean_ctor_set(v___x_506_, 1, v___x_283_);
v___x_507_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__1));
v___x_508_ = lean_obj_once(&l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7, &l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7_once, _init_l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7);
if (lean_obj_tag(v___y_474_) == 1)
{
lean_object* v_val_509_; lean_object* v___x_510_; 
v_val_509_ = lean_ctor_get(v___y_474_, 0);
lean_inc(v_val_509_);
lean_dec_ref_known(v___y_474_, 1);
v___x_510_ = l_Array_mkArray1___redArg(v_val_509_);
v___y_458_ = v___x_506_;
v___y_459_ = v_a_498_;
v___y_460_ = v___x_507_;
v___y_461_ = v___x_503_;
v___y_462_ = v___x_508_;
v___y_463_ = v_val_499_;
v___y_464_ = v___x_480_;
v___y_465_ = v___x_505_;
v___y_466_ = v_motive_475_;
v___y_467_ = v___x_510_;
goto v___jp_457_;
}
else
{
lean_object* v___x_511_; 
lean_dec(v___y_474_);
v___x_511_ = ((lean_object*)(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5));
v___y_458_ = v___x_506_;
v___y_459_ = v_a_498_;
v___y_460_ = v___x_507_;
v___y_461_ = v___x_503_;
v___y_462_ = v___x_508_;
v___y_463_ = v_val_499_;
v___y_464_ = v___x_480_;
v___y_465_ = v___x_505_;
v___y_466_ = v_motive_475_;
v___y_467_ = v___x_511_;
goto v___jp_457_;
}
}
}
else
{
lean_object* v_a_512_; lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_520_; 
lean_dec(v_motive_475_);
lean_dec(v___y_474_);
lean_dec(v_stx_280_);
v_a_512_ = lean_ctor_get(v___x_486_, 0);
v_a_513_ = lean_ctor_get(v___x_486_, 1);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_520_ == 0)
{
v___x_515_ = v___x_486_;
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_inc(v_a_512_);
lean_dec(v___x_486_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_518_; 
if (v_isShared_516_ == 0)
{
v___x_518_ = v___x_515_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_a_512_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v_a_513_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
}
}
v___jp_522_:
{
lean_object* v___x_526_; lean_object* v___x_527_; uint8_t v___x_528_; 
v___x_526_ = lean_unsigned_to_nat(2u);
v___x_527_ = l_Lean_Syntax_getArg(v_stx_280_, v___x_526_);
v___x_528_ = l_Lean_Syntax_isNone(v___x_527_);
if (v___x_528_ == 0)
{
uint8_t v___x_529_; 
lean_inc(v___x_527_);
v___x_529_ = l_Lean_Syntax_matchesNull(v___x_527_, v___x_521_);
if (v___x_529_ == 0)
{
lean_object* v___x_530_; lean_object* v___x_531_; 
lean_dec(v___x_527_);
lean_dec(v_gen_523_);
lean_dec(v_stx_280_);
v___x_530_ = lean_box(0);
v___x_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
lean_ctor_set(v___x_531_, 1, v___y_525_);
return v___x_531_;
}
else
{
lean_object* v_motive_532_; lean_object* v___x_533_; 
v_motive_532_ = l_Lean_Syntax_getArg(v___x_527_, v___x_456_);
lean_dec(v___x_527_);
v___x_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_533_, 0, v_motive_532_);
v___y_474_ = v_gen_523_;
v_motive_475_ = v___x_533_;
v___y_476_ = v___y_524_;
v___y_477_ = v___y_525_;
goto v___jp_473_;
}
}
else
{
lean_object* v___x_534_; 
lean_dec(v___x_527_);
v___x_534_ = lean_box(0);
v___y_474_ = v_gen_523_;
v_motive_475_ = v___x_534_;
v___y_476_ = v___y_524_;
v___y_477_ = v___y_525_;
goto v___jp_473_;
}
}
}
v___jp_285_:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
lean_inc_ref_n(v___y_291_, 3);
v___x_296_ = l_Array_append___redArg(v___y_291_, v___y_295_);
lean_dec_ref(v___y_295_);
lean_inc_n(v___y_289_, 3);
lean_inc_n(v___y_294_, 5);
v___x_297_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_297_, 0, v___y_294_);
lean_ctor_set(v___x_297_, 1, v___y_289_);
lean_ctor_set(v___x_297_, 2, v___x_296_);
v___x_298_ = l_Array_append___redArg(v___y_291_, v___y_290_);
lean_dec_ref(v___y_290_);
v___x_299_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_299_, 0, v___y_294_);
lean_ctor_set(v___x_299_, 1, v___y_289_);
lean_ctor_set(v___x_299_, 2, v___x_298_);
v___x_300_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__2));
v___x_301_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_301_, 0, v___y_294_);
lean_ctor_set(v___x_301_, 1, v___x_300_);
v___x_302_ = l_Array_append___redArg(v___y_291_, v___y_293_);
lean_dec_ref(v___y_293_);
v___x_303_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_303_, 0, v___y_294_);
lean_ctor_set(v___x_303_, 1, v___y_289_);
lean_ctor_set(v___x_303_, 2, v___x_302_);
lean_inc(v___y_292_);
v___x_304_ = l_Lean_Syntax_node1(v___y_294_, v___y_292_, v___x_303_);
v___x_305_ = l_Lean_Syntax_node6(v___y_294_, v___x_284_, v___y_288_, v___y_286_, v___x_297_, v___x_299_, v___x_301_, v___x_304_);
v___x_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
v___x_307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
lean_ctor_set(v___x_307_, 1, v___y_287_);
return v___x_307_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___boxed(lean_object* v_stx_543_, lean_object* v_a_544_, lean_object* v_a_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_Elab_Term_expandMatchAlts_x3f(v_stx_543_, v_a_544_, v_a_545_);
lean_dec_ref(v_a_544_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0(lean_object* v_as_555_, size_t v_sz_556_, size_t v_i_557_, lean_object* v_b_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
uint8_t v___x_561_; 
v___x_561_ = lean_usize_dec_lt(v_i_557_, v_sz_556_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; 
v___x_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_562_, 0, v_b_558_);
lean_ctor_set(v___x_562_, 1, v___y_560_);
return v___x_562_;
}
else
{
lean_object* v_ref_563_; lean_object* v_a_564_; uint8_t v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; size_t v___x_573_; size_t v___x_574_; 
v_ref_563_ = lean_ctor_get(v___y_559_, 0);
v_a_564_ = lean_array_uget_borrowed(v_as_555_, v_i_557_);
v___x_565_ = 0;
v___x_566_ = l_Lean_SourceInfo_fromRef(v_ref_563_, v___x_565_);
v___x_567_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__1));
v___x_568_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__2));
lean_inc_n(v___x_566_, 2);
v___x_569_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_566_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
v___x_570_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__3));
v___x_571_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_566_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
lean_inc(v_a_564_);
v___x_572_ = l_Lean_Syntax_node4(v___x_566_, v___x_567_, v___x_569_, v_a_564_, v___x_571_, v_b_558_);
v___x_573_ = ((size_t)1ULL);
v___x_574_ = lean_usize_add(v_i_557_, v___x_573_);
v_i_557_ = v___x_574_;
v_b_558_ = v___x_572_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___boxed(lean_object* v_as_576_, lean_object* v_sz_577_, lean_object* v_i_578_, lean_object* v_b_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
size_t v_sz_boxed_582_; size_t v_i_boxed_583_; lean_object* v_res_584_; 
v_sz_boxed_582_ = lean_unbox_usize(v_sz_577_);
lean_dec(v_sz_577_);
v_i_boxed_583_ = lean_unbox_usize(v_i_578_);
lean_dec(v_i_578_);
v_res_584_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0(v_as_576_, v_sz_boxed_582_, v_i_boxed_583_, v_b_579_, v___y_580_, v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec_ref(v_as_576_);
return v_res_584_;
}
}
static lean_object* _init_l_Lean_Elab_Term_clearInMatchAlt___closed__0(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_585_ = l_Lean_firstFrontendMacroScope;
v___x_586_ = lean_box(0);
v___x_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
lean_ctor_set(v___x_587_, 1, v___x_585_);
return v___x_587_;
}
}
static lean_object* _init_l_Lean_Elab_Term_clearInMatchAlt___closed__1(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_588_ = lean_unsigned_to_nat(1u);
v___x_589_ = l_Lean_firstFrontendMacroScope;
v___x_590_ = lean_nat_add(v___x_589_, v___x_588_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatchAlt(lean_object* v_stx_591_, lean_object* v_vars_592_){
_start:
{
if (lean_obj_tag(v_stx_591_) == 1)
{
lean_object* v_info_593_; lean_object* v_kind_594_; lean_object* v_args_595_; lean_object* v___x_596_; lean_object* v___x_597_; uint8_t v___x_598_; 
v_info_593_ = lean_ctor_get(v_stx_591_, 0);
v_kind_594_ = lean_ctor_get(v_stx_591_, 1);
v_args_595_ = lean_ctor_get(v_stx_591_, 2);
v___x_596_ = lean_unsigned_to_nat(3u);
v___x_597_ = lean_array_get_size(v_args_595_);
v___x_598_ = lean_nat_dec_lt(v___x_596_, v___x_597_);
if (v___x_598_ == 0)
{
return v_stx_591_;
}
else
{
lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_615_; 
lean_inc_ref(v_args_595_);
lean_inc(v_kind_594_);
lean_inc(v_info_593_);
v_isSharedCheck_615_ = !lean_is_exclusive(v_stx_591_);
if (v_isSharedCheck_615_ == 0)
{
lean_object* v_unused_616_; lean_object* v_unused_617_; lean_object* v_unused_618_; 
v_unused_616_ = lean_ctor_get(v_stx_591_, 2);
lean_dec(v_unused_616_);
v_unused_617_ = lean_ctor_get(v_stx_591_, 1);
lean_dec(v_unused_617_);
v_unused_618_ = lean_ctor_get(v_stx_591_, 0);
lean_dec(v_unused_618_);
v___x_600_ = v_stx_591_;
v_isShared_601_ = v_isSharedCheck_615_;
goto v_resetjp_599_;
}
else
{
lean_dec(v_stx_591_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_615_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v_v_602_; size_t v_sz_603_; size_t v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v_fst_608_; lean_object* v___x_609_; lean_object* v_xs_x27_610_; lean_object* v___x_611_; lean_object* v___x_613_; 
v_v_602_ = lean_array_fget_borrowed(v_args_595_, v___x_596_);
v_sz_603_ = lean_array_size(v_vars_592_);
v___x_604_ = ((size_t)0ULL);
v___x_605_ = lean_obj_once(&l_Lean_Elab_Term_clearInMatchAlt___closed__0, &l_Lean_Elab_Term_clearInMatchAlt___closed__0_once, _init_l_Lean_Elab_Term_clearInMatchAlt___closed__0);
v___x_606_ = lean_obj_once(&l_Lean_Elab_Term_clearInMatchAlt___closed__1, &l_Lean_Elab_Term_clearInMatchAlt___closed__1_once, _init_l_Lean_Elab_Term_clearInMatchAlt___closed__1);
lean_inc(v_v_602_);
v___x_607_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0(v_vars_592_, v_sz_603_, v___x_604_, v_v_602_, v___x_605_, v___x_606_);
v_fst_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_fst_608_);
lean_dec_ref(v___x_607_);
v___x_609_ = lean_box(0);
v_xs_x27_610_ = lean_array_fset(v_args_595_, v___x_596_, v___x_609_);
v___x_611_ = lean_array_fset(v_xs_x27_610_, v___x_596_, v_fst_608_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 2, v___x_611_);
v___x_613_ = v___x_600_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_info_593_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v_kind_594_);
lean_ctor_set(v_reuseFailAlloc_614_, 2, v___x_611_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
else
{
return v_stx_591_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatchAlt___boxed(lean_object* v_stx_619_, lean_object* v_vars_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_Elab_Term_clearInMatchAlt(v_stx_619_, v_vars_620_);
lean_dec_ref(v_vars_620_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_clearInMatch_spec__0(lean_object* v_vars_622_, size_t v_sz_623_, size_t v_i_624_, lean_object* v_bs_625_){
_start:
{
uint8_t v___x_626_; 
v___x_626_ = lean_usize_dec_lt(v_i_624_, v_sz_623_);
if (v___x_626_ == 0)
{
return v_bs_625_;
}
else
{
lean_object* v_v_627_; lean_object* v___x_628_; lean_object* v_bs_x27_629_; lean_object* v___x_630_; size_t v___x_631_; size_t v___x_632_; lean_object* v___x_633_; 
v_v_627_ = lean_array_uget(v_bs_625_, v_i_624_);
v___x_628_ = lean_unsigned_to_nat(0u);
v_bs_x27_629_ = lean_array_uset(v_bs_625_, v_i_624_, v___x_628_);
v___x_630_ = l_Lean_Elab_Term_clearInMatchAlt(v_v_627_, v_vars_622_);
v___x_631_ = ((size_t)1ULL);
v___x_632_ = lean_usize_add(v_i_624_, v___x_631_);
v___x_633_ = lean_array_uset(v_bs_x27_629_, v_i_624_, v___x_630_);
v_i_624_ = v___x_632_;
v_bs_625_ = v___x_633_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_clearInMatch_spec__0___boxed(lean_object* v_vars_635_, lean_object* v_sz_636_, lean_object* v_i_637_, lean_object* v_bs_638_){
_start:
{
size_t v_sz_boxed_639_; size_t v_i_boxed_640_; lean_object* v_res_641_; 
v_sz_boxed_639_ = lean_unbox_usize(v_sz_636_);
lean_dec(v_sz_636_);
v_i_boxed_640_ = lean_unbox_usize(v_i_637_);
lean_dec(v_i_637_);
v_res_641_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_clearInMatch_spec__0(v_vars_635_, v_sz_boxed_639_, v_i_boxed_640_, v_bs_638_);
lean_dec_ref(v_vars_635_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatch(lean_object* v_stx_642_, lean_object* v_vars_643_, lean_object* v_a_644_, lean_object* v_a_645_){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_646_ = lean_array_get_size(v_vars_643_);
v___x_647_ = lean_unsigned_to_nat(0u);
v___x_648_ = lean_nat_dec_eq(v___x_646_, v___x_647_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_690_; lean_object* v_motive_691_; lean_object* v___y_692_; lean_object* v___y_693_; uint8_t v___x_715_; 
v___x_649_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__0));
v___x_650_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1));
lean_inc(v_stx_642_);
v___x_715_ = l_Lean_Syntax_isOfKind(v_stx_642_, v___x_650_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; 
v___x_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_716_, 0, v_stx_642_);
lean_ctor_set(v___x_716_, 1, v_a_645_);
return v___x_716_;
}
else
{
lean_object* v___x_717_; lean_object* v_gen_719_; lean_object* v___y_720_; lean_object* v___y_721_; lean_object* v___x_730_; uint8_t v___x_731_; 
v___x_717_ = lean_unsigned_to_nat(1u);
v___x_730_ = l_Lean_Syntax_getArg(v_stx_642_, v___x_717_);
v___x_731_ = l_Lean_Syntax_isNone(v___x_730_);
if (v___x_731_ == 0)
{
uint8_t v___x_732_; 
lean_inc(v___x_730_);
v___x_732_ = l_Lean_Syntax_matchesNull(v___x_730_, v___x_717_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; 
lean_dec(v___x_730_);
v___x_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_733_, 0, v_stx_642_);
lean_ctor_set(v___x_733_, 1, v_a_645_);
return v___x_733_;
}
else
{
lean_object* v_gen_734_; lean_object* v___x_735_; 
v_gen_734_ = l_Lean_Syntax_getArg(v___x_730_, v___x_647_);
lean_dec(v___x_730_);
v___x_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_735_, 0, v_gen_734_);
v_gen_719_ = v___x_735_;
v___y_720_ = v_a_644_;
v___y_721_ = v_a_645_;
goto v___jp_718_;
}
}
else
{
lean_object* v___x_736_; 
lean_dec(v___x_730_);
v___x_736_ = lean_box(0);
v_gen_719_ = v___x_736_;
v___y_720_ = v_a_644_;
v___y_721_ = v_a_645_;
goto v___jp_718_;
}
v___jp_718_:
{
lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_722_ = lean_unsigned_to_nat(2u);
v___x_723_ = l_Lean_Syntax_getArg(v_stx_642_, v___x_722_);
v___x_724_ = l_Lean_Syntax_isNone(v___x_723_);
if (v___x_724_ == 0)
{
uint8_t v___x_725_; 
lean_inc(v___x_723_);
v___x_725_ = l_Lean_Syntax_matchesNull(v___x_723_, v___x_717_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; 
lean_dec(v___x_723_);
lean_dec(v_gen_719_);
v___x_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_726_, 0, v_stx_642_);
lean_ctor_set(v___x_726_, 1, v___y_721_);
return v___x_726_;
}
else
{
lean_object* v_motive_727_; lean_object* v___x_728_; 
v_motive_727_ = l_Lean_Syntax_getArg(v___x_723_, v___x_647_);
lean_dec(v___x_723_);
v___x_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_728_, 0, v_motive_727_);
v___y_690_ = v_gen_719_;
v_motive_691_ = v___x_728_;
v___y_692_ = v___y_720_;
v___y_693_ = v___y_721_;
goto v___jp_689_;
}
}
else
{
lean_object* v___x_729_; 
lean_dec(v___x_723_);
v___x_729_ = lean_box(0);
v___y_690_ = v_gen_719_;
v_motive_691_ = v___x_729_;
v___y_692_ = v___y_720_;
v___y_693_ = v___y_721_;
goto v___jp_689_;
}
}
}
v___jp_651_:
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
lean_inc_ref_n(v___y_658_, 3);
v___x_662_ = l_Array_append___redArg(v___y_658_, v___y_661_);
lean_dec_ref(v___y_661_);
lean_inc_n(v___y_660_, 3);
lean_inc_n(v___y_653_, 5);
v___x_663_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_663_, 0, v___y_653_);
lean_ctor_set(v___x_663_, 1, v___y_660_);
lean_ctor_set(v___x_663_, 2, v___x_662_);
v___x_664_ = l_Array_append___redArg(v___y_658_, v___y_659_);
lean_dec_ref(v___y_659_);
v___x_665_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_665_, 0, v___y_653_);
lean_ctor_set(v___x_665_, 1, v___y_660_);
lean_ctor_set(v___x_665_, 2, v___x_664_);
v___x_666_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__2));
v___x_667_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_667_, 0, v___y_653_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
v___x_668_ = l_Array_append___redArg(v___y_658_, v___y_652_);
lean_dec_ref(v___y_652_);
v___x_669_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_669_, 0, v___y_653_);
lean_ctor_set(v___x_669_, 1, v___y_660_);
lean_ctor_set(v___x_669_, 2, v___x_668_);
lean_inc(v___y_656_);
v___x_670_ = l_Lean_Syntax_node1(v___y_653_, v___y_656_, v___x_669_);
v___x_671_ = l_Lean_Syntax_node6(v___y_653_, v___x_650_, v___y_655_, v___y_657_, v___x_663_, v___x_665_, v___x_667_, v___x_670_);
v___x_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
lean_ctor_set(v___x_672_, 1, v___y_654_);
return v___x_672_;
}
v___jp_673_:
{
lean_object* v___x_684_; lean_object* v___x_685_; 
lean_inc_ref(v___y_680_);
v___x_684_ = l_Array_append___redArg(v___y_680_, v___y_683_);
lean_dec_ref(v___y_683_);
lean_inc(v___y_682_);
lean_inc(v___y_675_);
v___x_685_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_685_, 0, v___y_675_);
lean_ctor_set(v___x_685_, 1, v___y_682_);
lean_ctor_set(v___x_685_, 2, v___x_684_);
if (lean_obj_tag(v___y_679_) == 1)
{
lean_object* v_val_686_; lean_object* v___x_687_; 
v_val_686_ = lean_ctor_get(v___y_679_, 0);
lean_inc(v_val_686_);
lean_dec_ref_known(v___y_679_, 1);
v___x_687_ = l_Array_mkArray1___redArg(v_val_686_);
v___y_652_ = v___y_674_;
v___y_653_ = v___y_675_;
v___y_654_ = v___y_678_;
v___y_655_ = v___y_677_;
v___y_656_ = v___y_676_;
v___y_657_ = v___x_685_;
v___y_658_ = v___y_680_;
v___y_659_ = v___y_681_;
v___y_660_ = v___y_682_;
v___y_661_ = v___x_687_;
goto v___jp_651_;
}
else
{
lean_object* v___x_688_; 
lean_dec(v___y_679_);
v___x_688_ = ((lean_object*)(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5));
v___y_652_ = v___y_674_;
v___y_653_ = v___y_675_;
v___y_654_ = v___y_678_;
v___y_655_ = v___y_677_;
v___y_656_ = v___y_676_;
v___y_657_ = v___x_685_;
v___y_658_ = v___y_680_;
v___y_659_ = v___y_681_;
v___y_660_ = v___y_682_;
v___y_661_ = v___x_688_;
goto v___jp_651_;
}
}
v___jp_689_:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; uint8_t v___x_697_; 
v___x_694_ = lean_unsigned_to_nat(5u);
v___x_695_ = l_Lean_Syntax_getArg(v_stx_642_, v___x_694_);
v___x_696_ = ((lean_object*)(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6));
lean_inc(v___x_695_);
v___x_697_ = l_Lean_Syntax_isOfKind(v___x_695_, v___x_696_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; 
lean_dec(v___x_695_);
lean_dec(v_motive_691_);
lean_dec(v___y_690_);
v___x_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_698_, 0, v_stx_642_);
lean_ctor_set(v___x_698_, 1, v___y_693_);
return v___x_698_;
}
else
{
lean_object* v_ref_699_; lean_object* v___x_700_; lean_object* v_alts_701_; size_t v_sz_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; size_t v___x_706_; lean_object* v_alts_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v_ref_699_ = lean_ctor_get(v___y_692_, 5);
v___x_700_ = l_Lean_Syntax_getArg(v___x_695_, v___x_647_);
lean_dec(v___x_695_);
v_alts_701_ = l_Lean_Syntax_getArgs(v___x_700_);
lean_dec(v___x_700_);
v_sz_702_ = lean_array_size(v_alts_701_);
v___x_703_ = lean_unsigned_to_nat(3u);
v___x_704_ = l_Lean_Syntax_getArg(v_stx_642_, v___x_703_);
lean_dec(v_stx_642_);
v___x_705_ = l_Lean_Syntax_getArgs(v___x_704_);
lean_dec(v___x_704_);
v___x_706_ = ((size_t)0ULL);
v_alts_707_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_clearInMatch_spec__0(v_vars_643_, v_sz_702_, v___x_706_, v_alts_701_);
v___x_708_ = l_Lean_SourceInfo_fromRef(v_ref_699_, v___x_648_);
lean_inc(v___x_708_);
v___x_709_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
lean_ctor_set(v___x_709_, 1, v___x_649_);
v___x_710_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__1));
v___x_711_ = lean_obj_once(&l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7, &l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7_once, _init_l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7);
if (lean_obj_tag(v___y_690_) == 1)
{
lean_object* v_val_712_; lean_object* v___x_713_; 
v_val_712_ = lean_ctor_get(v___y_690_, 0);
lean_inc(v_val_712_);
lean_dec_ref_known(v___y_690_, 1);
v___x_713_ = l_Array_mkArray1___redArg(v_val_712_);
v___y_674_ = v_alts_707_;
v___y_675_ = v___x_708_;
v___y_676_ = v___x_696_;
v___y_677_ = v___x_709_;
v___y_678_ = v___y_693_;
v___y_679_ = v_motive_691_;
v___y_680_ = v___x_711_;
v___y_681_ = v___x_705_;
v___y_682_ = v___x_710_;
v___y_683_ = v___x_713_;
goto v___jp_673_;
}
else
{
lean_object* v___x_714_; 
lean_dec(v___y_690_);
v___x_714_ = ((lean_object*)(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5));
v___y_674_ = v_alts_707_;
v___y_675_ = v___x_708_;
v___y_676_ = v___x_696_;
v___y_677_ = v___x_709_;
v___y_678_ = v___y_693_;
v___y_679_ = v_motive_691_;
v___y_680_ = v___x_711_;
v___y_681_ = v___x_705_;
v___y_682_ = v___x_710_;
v___y_683_ = v___x_714_;
goto v___jp_673_;
}
}
}
}
else
{
lean_object* v___x_737_; 
v___x_737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_737_, 0, v_stx_642_);
lean_ctor_set(v___x_737_, 1, v_a_645_);
return v___x_737_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatch___boxed(lean_object* v_stx_738_, lean_object* v_vars_739_, lean_object* v_a_740_, lean_object* v_a_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lean_Elab_Term_clearInMatch(v_stx_738_, v_vars_739_, v_a_740_, v_a_741_);
lean_dec_ref(v_a_740_);
lean_dec_ref(v_vars_739_);
return v_res_742_;
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
