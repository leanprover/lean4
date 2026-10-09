// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.CollectParams
// Imports: public import Lean.Meta.Tactic.Grind.Types
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Syntax_structEq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushAnchor_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushAnchor_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushAnchor___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushAnchor___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushAnchor(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushAnchor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "thm"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__5_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__5_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__5_value_aux_3),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(235, 175, 92, 250, 215, 173, 92, 62)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindLemma"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__7_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__7_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__7_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(185, 180, 24, 243, 113, 54, 79, 133)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "grindLemmaMin"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__8_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__9_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__9_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__9_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(65, 124, 255, 191, 121, 182, 88, 219)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__9_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "anchor"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__10_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__11_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__11_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__11_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(168, 155, 228, 98, 168, 72, 115, 174)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__11_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindParam"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__12_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__13_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__13_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__13_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(16, 144, 208, 205, 52, 106, 220, 83)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__13_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "grindStep"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__1_value_aux_3),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(197, 239, 5, 217, 230, 199, 187, 87)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "sorry"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__0_value),LEAN_SCALAR_PTR_LITERAL(129, 71, 141, 15, 124, 86, 0, 175)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "next"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__3_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__2_value),LEAN_SCALAR_PTR_LITERAL(122, 67, 127, 148, 132, 17, 131, 108)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 7, .m_data = "grind·_"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__5_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__5_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__5_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__4_value),LEAN_SCALAR_PTR_LITERAL(27, 208, 22, 131, 194, 122, 241, 171)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grind_<;>_"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__7_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__7_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__7_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__7_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__7_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__6_value),LEAN_SCALAR_PTR_LITERAL(104, 7, 229, 204, 205, 179, 221, 240)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cases"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__9_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__9_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__9_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__9_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__9_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__8_value),LEAN_SCALAR_PTR_LITERAL(255, 233, 158, 17, 45, 135, 214, 137)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "use"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__11_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__11_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__11_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__11_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__11_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__10_value),LEAN_SCALAR_PTR_LITERAL(164, 64, 35, 249, 247, 52, 171, 66)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "instantiate"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__13_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__13_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__13_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__13_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__13_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__12_value),LEAN_SCALAR_PTR_LITERAL(22, 223, 197, 126, 28, 51, 106, 179)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grind_ref_"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__14_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__15_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__15_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__15_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__15_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__15_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__14_value),LEAN_SCALAR_PTR_LITERAL(236, 234, 46, 225, 9, 69, 165, 154)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__15_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "grind_ref__/__"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__16_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__17_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__17_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__17_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__17_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__17_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__16_value),LEAN_SCALAR_PTR_LITERAL(163, 78, 76, 1, 128, 192, 165, 233)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__17_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__18_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__18_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__19_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindSeq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__20_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__21_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__21_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__21_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__21_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__21_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__20_value),LEAN_SCALAR_PTR_LITERAL(158, 229, 98, 59, 247, 194, 34, 174)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__21_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "grindSeq1Indented"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__22_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__23_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__23_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__23_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__23_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__23_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__22_value),LEAN_SCALAR_PTR_LITERAL(35, 114, 22, 139, 17, 175, 241, 184)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__23_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_main_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_main_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_main(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore_spec__0___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore___closed__0_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParams(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_mkFinishTactic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "finish"};
static const lean_object* l_Lean_Meta_Grind_mkFinishTactic___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_mkFinishTactic___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkFinishTactic___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkFinishTactic___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkFinishTactic___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkFinishTactic___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkFinishTactic___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkFinishTactic___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkFinishTactic___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkFinishTactic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkFinishTactic___closed__1_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_mkFinishTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 141, 128, 132, 58, 161, 38, 215)}};
static const lean_object* l_Lean_Meta_Grind_mkFinishTactic___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_mkFinishTactic___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_mkFinishTactic___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Meta_Grind_mkFinishTactic___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_mkFinishTactic___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkFinishTactic___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_mkFinishTactic___closed__2_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Meta_Grind_mkFinishTactic___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_mkFinishTactic___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_mkFinishTactic___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkFinishTactic___closed__4;
static const lean_string_object l_Lean_Meta_Grind_mkFinishTactic___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "only"};
static const lean_object* l_Lean_Meta_Grind_mkFinishTactic___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_mkFinishTactic___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_mkFinishTactic___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Meta_Grind_mkFinishTactic___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_mkFinishTactic___closed__6_value;
static const lean_string_object l_Lean_Meta_Grind_mkFinishTactic___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Meta_Grind_mkFinishTactic___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_mkFinishTactic___closed__7_value;
static const lean_string_object l_Lean_Meta_Grind_mkFinishTactic___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Meta_Grind_mkFinishTactic___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_mkFinishTactic___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkFinishTactic(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkFinishTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(150, 98, 0, 78, 28, 79, 28, 100)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkGrindOnlyTactics(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkGrindOnlyTactics___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam_spec__0_spec__0(lean_object* v_a_1_, lean_object* v_as_2_, size_t v_i_3_, size_t v_stop_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_usize_dec_eq(v_i_3_, v_stop_4_);
if (v___x_5_ == 0)
{
lean_object* v___x_6_; uint8_t v___x_7_; 
v___x_6_ = lean_array_uget_borrowed(v_as_2_, v_i_3_);
v___x_7_ = l_Lean_Syntax_structEq(v_a_1_, v___x_6_);
if (v___x_7_ == 0)
{
size_t v___x_8_; size_t v___x_9_; 
v___x_8_ = ((size_t)1ULL);
v___x_9_ = lean_usize_add(v_i_3_, v___x_8_);
v_i_3_ = v___x_9_;
goto _start;
}
else
{
return v___x_7_;
}
}
else
{
uint8_t v___x_11_; 
v___x_11_ = 0;
return v___x_11_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1_ = stack[0].m_obj;
lean_object* v_as_2_ = stack[1].m_obj;
size_t v_i_3_ = stack[2].m_num;
size_t v_stop_4_ = stack[3].m_num;
uint8_t v_res_12_;
v_res_12_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam_spec__0_spec__0(v_a_1_, v_as_2_, v_i_3_, v_stop_4_);
stack->m_num = v_res_12_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam_spec__0_spec__0___boxed(lean_object* v_a_13_, lean_object* v_as_14_, lean_object* v_i_15_, lean_object* v_stop_16_){
_start:
{
size_t v_i_boxed_17_; size_t v_stop_boxed_18_; uint8_t v_res_19_; lean_object* v_r_20_; 
v_i_boxed_17_ = lean_unbox_usize(v_i_15_);
lean_dec(v_i_15_);
v_stop_boxed_18_ = lean_unbox_usize(v_stop_16_);
lean_dec(v_stop_16_);
v_res_19_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam_spec__0_spec__0(v_a_13_, v_as_14_, v_i_boxed_17_, v_stop_boxed_18_);
lean_dec_ref(v_as_14_);
lean_dec(v_a_13_);
v_r_20_ = lean_box(v_res_19_);
return v_r_20_;
}
}
uint8_t l_Array_contains___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam_spec__0(lean_object* v_as_21_, lean_object* v_a_22_){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; uint8_t v___x_25_; 
v___x_23_ = lean_unsigned_to_nat(0u);
v___x_24_ = lean_array_get_size(v_as_21_);
v___x_25_ = lean_nat_dec_lt(v___x_23_, v___x_24_);
if (v___x_25_ == 0)
{
return v___x_25_;
}
else
{
if (v___x_25_ == 0)
{
return v___x_25_;
}
else
{
size_t v___x_26_; size_t v___x_27_; uint8_t v___x_28_; 
v___x_26_ = ((size_t)0ULL);
v___x_27_ = lean_usize_of_nat(v___x_24_);
v___x_28_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam_spec__0_spec__0(v_a_22_, v_as_21_, v___x_26_, v___x_27_);
return v___x_28_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_21_ = stack[0].m_obj;
lean_object* v_a_22_ = stack[1].m_obj;
uint8_t v_res_29_;
v_res_29_ = l_Array_contains___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam_spec__0(v_as_21_, v_a_22_);
stack->m_num = v_res_29_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam_spec__0___boxed(lean_object* v_as_30_, lean_object* v_a_31_){
_start:
{
uint8_t v_res_32_; lean_object* v_r_33_; 
v_res_32_ = l_Array_contains___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam_spec__0(v_as_30_, v_a_31_);
lean_dec(v_a_31_);
lean_dec_ref(v_as_30_);
v_r_33_ = lean_box(v_res_32_);
return v_r_33_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam___redArg(lean_object* v_p_34_, lean_object* v_a_35_){
_start:
{
lean_object* v___x_37_; lean_object* v_params_38_; uint8_t v___x_39_; 
v___x_37_ = lean_st_ref_get(v_a_35_);
v_params_38_ = lean_ctor_get(v___x_37_, 0);
lean_inc_ref(v_params_38_);
lean_dec(v___x_37_);
v___x_39_ = l_Array_contains___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam_spec__0(v_params_38_, v_p_34_);
lean_dec_ref(v_params_38_);
if (v___x_39_ == 0)
{
lean_object* v___x_40_; lean_object* v_params_41_; lean_object* v_anchors_42_; uint8_t v_hasSorry_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_54_; 
v___x_40_ = lean_st_ref_take(v_a_35_);
v_params_41_ = lean_ctor_get(v___x_40_, 0);
v_anchors_42_ = lean_ctor_get(v___x_40_, 1);
v_hasSorry_43_ = lean_ctor_get_uint8(v___x_40_, sizeof(void*)*2);
v_isSharedCheck_54_ = !lean_is_exclusive(v___x_40_);
if (v_isSharedCheck_54_ == 0)
{
v___x_45_ = v___x_40_;
v_isShared_46_ = v_isSharedCheck_54_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_anchors_42_);
lean_inc(v_params_41_);
lean_dec(v___x_40_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_54_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_50_; 
v___x_47_ = lean_box(0);
v___x_48_ = lean_array_push(v_params_41_, v_p_34_);
if (v_isShared_46_ == 0)
{
lean_ctor_set(v___x_45_, 0, v___x_48_);
v___x_50_ = v___x_45_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v___x_48_);
lean_ctor_set(v_reuseFailAlloc_53_, 1, v_anchors_42_);
lean_ctor_set_uint8(v_reuseFailAlloc_53_, sizeof(void*)*2, v_hasSorry_43_);
v___x_50_ = v_reuseFailAlloc_53_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = lean_st_ref_put(v_a_35_, v___x_50_);
v___x_52_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_52_, 0, v___x_47_);
return v___x_52_;
}
}
}
else
{
lean_object* v___x_55_; lean_object* v___x_56_; 
lean_dec(v_p_34_);
v___x_55_ = lean_box(0);
v___x_56_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
return v___x_56_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_34_ = stack[0].m_obj;
lean_object* v_a_35_ = stack[1].m_obj;
lean_object* v_res_57_;
v_res_57_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam___redArg(v_p_34_, v_a_35_);
stack->m_obj
 = v_res_57_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam___redArg___boxed(lean_object* v_p_58_, lean_object* v_a_59_, lean_object* v_a_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam___redArg(v_p_58_, v_a_59_);
lean_dec(v_a_59_);
return v_res_61_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam(lean_object* v_p_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam___redArg(v_p_62_, v_a_63_);
return v___x_67_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_62_ = stack[0].m_obj;
lean_object* v_a_63_ = stack[1].m_obj;
lean_object* v_a_64_ = stack[2].m_obj;
lean_object* v_a_65_ = stack[3].m_obj;
lean_object* v_res_68_;
v_res_68_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam(v_p_62_, v_a_63_, v_a_64_, v_a_65_);
stack->m_obj
 = v_res_68_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam___boxed(lean_object* v_p_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam(v_p_69_, v_a_70_, v_a_71_, v_a_72_);
lean_dec(v_a_72_);
lean_dec_ref(v_a_71_);
lean_dec(v_a_70_);
return v_res_74_;
}
}
uint8_t l_Array_contains___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushAnchor_spec__0(lean_object* v_as_75_, lean_object* v_a_76_){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_77_ = lean_unsigned_to_nat(0u);
v___x_78_ = lean_array_get_size(v_as_75_);
v___x_79_ = lean_nat_dec_lt(v___x_77_, v___x_78_);
if (v___x_79_ == 0)
{
return v___x_79_;
}
else
{
if (v___x_79_ == 0)
{
return v___x_79_;
}
else
{
size_t v___x_80_; size_t v___x_81_; uint8_t v___x_82_; 
v___x_80_ = ((size_t)0ULL);
v___x_81_ = lean_usize_of_nat(v___x_78_);
v___x_82_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam_spec__0_spec__0(v_a_76_, v_as_75_, v___x_80_, v___x_81_);
return v___x_82_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushAnchor_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_75_ = stack[0].m_obj;
lean_object* v_a_76_ = stack[1].m_obj;
uint8_t v_res_83_;
v_res_83_ = l_Array_contains___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushAnchor_spec__0(v_as_75_, v_a_76_);
stack->m_num = v_res_83_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushAnchor_spec__0___boxed(lean_object* v_as_84_, lean_object* v_a_85_){
_start:
{
uint8_t v_res_86_; lean_object* v_r_87_; 
v_res_86_ = l_Array_contains___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushAnchor_spec__0(v_as_84_, v_a_85_);
lean_dec(v_a_85_);
lean_dec_ref(v_as_84_);
v_r_87_ = lean_box(v_res_86_);
return v_r_87_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushAnchor___redArg(lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v___x_91_; lean_object* v_anchors_92_; uint8_t v___x_93_; 
v___x_91_ = lean_st_ref_get(v_a_89_);
v_anchors_92_ = lean_ctor_get(v___x_91_, 1);
lean_inc_ref(v_anchors_92_);
lean_dec(v___x_91_);
v___x_93_ = l_Array_contains___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushAnchor_spec__0(v_anchors_92_, v_a_88_);
lean_dec_ref(v_anchors_92_);
if (v___x_93_ == 0)
{
lean_object* v___x_94_; lean_object* v_params_95_; lean_object* v_anchors_96_; uint8_t v_hasSorry_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_108_; 
v___x_94_ = lean_st_ref_take(v_a_89_);
v_params_95_ = lean_ctor_get(v___x_94_, 0);
v_anchors_96_ = lean_ctor_get(v___x_94_, 1);
v_hasSorry_97_ = lean_ctor_get_uint8(v___x_94_, sizeof(void*)*2);
v_isSharedCheck_108_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_108_ == 0)
{
v___x_99_ = v___x_94_;
v_isShared_100_ = v_isSharedCheck_108_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_anchors_96_);
lean_inc(v_params_95_);
lean_dec(v___x_94_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_108_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_104_; 
v___x_101_ = lean_box(0);
v___x_102_ = lean_array_push(v_anchors_96_, v_a_88_);
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 1, v___x_102_);
v___x_104_ = v___x_99_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_params_95_);
lean_ctor_set(v_reuseFailAlloc_107_, 1, v___x_102_);
lean_ctor_set_uint8(v_reuseFailAlloc_107_, sizeof(void*)*2, v_hasSorry_97_);
v___x_104_ = v_reuseFailAlloc_107_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = lean_st_ref_put(v_a_89_, v___x_104_);
v___x_106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_106_, 0, v___x_101_);
return v___x_106_;
}
}
}
else
{
lean_object* v___x_109_; lean_object* v___x_110_; 
lean_dec(v_a_88_);
v___x_109_ = lean_box(0);
v___x_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
return v___x_110_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushAnchor___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_88_ = stack[0].m_obj;
lean_object* v_a_89_ = stack[1].m_obj;
lean_object* v_res_111_;
v_res_111_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushAnchor___redArg(v_a_88_, v_a_89_);
stack->m_obj
 = v_res_111_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushAnchor___redArg___boxed(lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushAnchor___redArg(v_a_112_, v_a_113_);
lean_dec(v_a_113_);
return v_res_115_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushAnchor(lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushAnchor___redArg(v_a_116_, v_a_117_);
return v___x_121_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushAnchor_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_116_ = stack[0].m_obj;
lean_object* v_a_117_ = stack[1].m_obj;
lean_object* v_a_118_ = stack[2].m_obj;
lean_object* v_a_119_ = stack[3].m_obj;
lean_object* v_res_122_;
v_res_122_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushAnchor(v_a_116_, v_a_117_, v_a_118_, v_a_119_);
stack->m_obj
 = v_res_122_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushAnchor___boxed(lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushAnchor(v_a_123_, v_a_124_, v_a_125_, v_a_126_);
lean_dec(v_a_126_);
lean_dec_ref(v_a_125_);
lean_dec(v_a_124_);
return v_res_128_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg(lean_object* v_as_164_, size_t v_sz_165_, size_t v_i_166_, lean_object* v_b_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
lean_object* v_a_172_; uint8_t v___x_176_; 
v___x_176_ = lean_usize_dec_lt(v_i_166_, v_sz_165_);
if (v___x_176_ == 0)
{
lean_object* v___x_177_; 
v___x_177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_177_, 0, v_b_167_);
return v___x_177_;
}
else
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v_a_180_; uint8_t v___x_181_; 
v___x_178_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__5));
v___x_179_ = lean_box(0);
v_a_180_ = lean_array_uget_borrowed(v_as_164_, v_i_166_);
lean_inc(v_a_180_);
v___x_181_ = l_Lean_Syntax_isOfKind(v_a_180_, v___x_178_);
if (v___x_181_ == 0)
{
v_a_172_ = v___x_179_;
goto v___jp_171_;
}
else
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_182_ = lean_unsigned_to_nat(0u);
v___x_183_ = l_Lean_Syntax_getArg(v_a_180_, v___x_182_);
v___x_184_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__7));
lean_inc(v___x_183_);
v___x_185_ = l_Lean_Syntax_isOfKind(v___x_183_, v___x_184_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_186_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__9));
lean_inc(v___x_183_);
v___x_187_ = l_Lean_Syntax_isOfKind(v___x_183_, v___x_186_);
if (v___x_187_ == 0)
{
lean_object* v___x_188_; uint8_t v___x_189_; 
v___x_188_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__11));
lean_inc(v___x_183_);
v___x_189_ = l_Lean_Syntax_isOfKind(v___x_183_, v___x_188_);
if (v___x_189_ == 0)
{
lean_dec(v___x_183_);
v_a_172_ = v___x_179_;
goto v___jp_171_;
}
else
{
lean_object* v___x_190_; 
v___x_190_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushAnchor___redArg(v___x_183_, v___y_168_);
if (lean_obj_tag(v___x_190_) == 0)
{
lean_dec_ref_known(v___x_190_, 1);
v_a_172_ = v___x_179_;
goto v___jp_171_;
}
else
{
return v___x_190_;
}
}
}
else
{
lean_object* v_ref_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v_ref_191_ = lean_ctor_get(v___y_169_, 2);
v___x_192_ = l_Lean_SourceInfo_fromRef(v_ref_191_, v___x_185_);
v___x_193_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__13));
v___x_194_ = l_Lean_Syntax_node1(v___x_192_, v___x_193_, v___x_183_);
v___x_195_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam___redArg(v___x_194_, v___y_168_);
if (lean_obj_tag(v___x_195_) == 0)
{
lean_dec_ref_known(v___x_195_, 1);
v_a_172_ = v___x_179_;
goto v___jp_171_;
}
else
{
return v___x_195_;
}
}
}
else
{
lean_object* v_ref_196_; uint8_t v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v_ref_196_ = lean_ctor_get(v___y_169_, 2);
v___x_197_ = 0;
v___x_198_ = l_Lean_SourceInfo_fromRef(v_ref_196_, v___x_197_);
v___x_199_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__13));
v___x_200_ = l_Lean_Syntax_node1(v___x_198_, v___x_199_, v___x_183_);
v___x_201_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushParam___redArg(v___x_200_, v___y_168_);
if (lean_obj_tag(v___x_201_) == 0)
{
lean_dec_ref_known(v___x_201_, 1);
v_a_172_ = v___x_179_;
goto v___jp_171_;
}
else
{
return v___x_201_;
}
}
}
}
v___jp_171_:
{
size_t v___x_173_; size_t v___x_174_; 
v___x_173_ = ((size_t)1ULL);
v___x_174_ = lean_usize_add(v_i_166_, v___x_173_);
v_i_166_ = v___x_174_;
v_b_167_ = v_a_172_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_164_ = stack[0].m_obj;
size_t v_sz_165_ = stack[1].m_num;
size_t v_i_166_ = stack[2].m_num;
lean_object* v_b_167_ = stack[3].m_obj;
lean_object* v___y_168_ = stack[4].m_obj;
lean_object* v___y_169_ = stack[5].m_obj;
lean_object* v_res_202_;
v_res_202_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg(v_as_164_, v_sz_165_, v_i_166_, v_b_167_, v___y_168_, v___y_169_);
stack->m_obj
 = v_res_202_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___boxed(lean_object* v_as_203_, lean_object* v_sz_204_, lean_object* v_i_205_, lean_object* v_b_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
size_t v_sz_boxed_210_; size_t v_i_boxed_211_; lean_object* v_res_212_; 
v_sz_boxed_210_ = lean_unbox_usize(v_sz_204_);
lean_dec(v_sz_204_);
v_i_boxed_211_ = lean_unbox_usize(v_i_205_);
lean_dec(v_i_205_);
v_res_212_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg(v_as_203_, v_sz_boxed_210_, v_i_boxed_211_, v_b_206_, v___y_207_, v___y_208_);
lean_dec_ref(v___y_208_);
lean_dec(v___y_207_);
lean_dec_ref(v_as_203_);
return v_res_212_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams(lean_object* v_params_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; size_t v_sz_220_; size_t v___x_221_; lean_object* v___x_222_; 
v___x_218_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_params_213_);
v___x_219_ = lean_box(0);
v_sz_220_ = lean_array_size(v___x_218_);
v___x_221_ = ((size_t)0ULL);
v___x_222_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg(v___x_218_, v_sz_220_, v___x_221_, v___x_219_, v_a_214_, v_a_215_);
lean_dec_ref(v___x_218_);
if (lean_obj_tag(v___x_222_) == 0)
{
lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_229_; 
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_229_ == 0)
{
lean_object* v_unused_230_; 
v_unused_230_ = lean_ctor_get(v___x_222_, 0);
lean_dec(v_unused_230_);
v___x_224_ = v___x_222_;
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
else
{
lean_dec(v___x_222_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_227_; 
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_219_);
v___x_227_ = v___x_224_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v___x_219_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
else
{
return v___x_222_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_213_ = stack[0].m_obj;
lean_object* v_a_214_ = stack[1].m_obj;
lean_object* v_a_215_ = stack[2].m_obj;
lean_object* v_a_216_ = stack[3].m_obj;
lean_object* v_res_231_;
v_res_231_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams(v_params_213_, v_a_214_, v_a_215_, v_a_216_);
stack->m_obj
 = v_res_231_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams___boxed(lean_object* v_params_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams(v_params_232_, v_a_233_, v_a_234_, v_a_235_);
lean_dec(v_a_235_);
lean_dec_ref(v_a_234_);
lean_dec(v_a_233_);
lean_dec_ref(v_params_232_);
return v_res_237_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0(lean_object* v_as_238_, size_t v_sz_239_, size_t v_i_240_, lean_object* v_b_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg(v_as_238_, v_sz_239_, v_i_240_, v_b_241_, v___y_242_, v___y_243_);
return v___x_246_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_238_ = stack[0].m_obj;
size_t v_sz_239_ = stack[1].m_num;
size_t v_i_240_ = stack[2].m_num;
lean_object* v_b_241_ = stack[3].m_obj;
lean_object* v___y_242_ = stack[4].m_obj;
lean_object* v___y_243_ = stack[5].m_obj;
lean_object* v___y_244_ = stack[6].m_obj;
lean_object* v_res_247_;
v_res_247_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0(v_as_238_, v_sz_239_, v_i_240_, v_b_241_, v___y_242_, v___y_243_, v___y_244_);
stack->m_obj
 = v_res_247_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___boxed(lean_object* v_as_248_, lean_object* v_sz_249_, lean_object* v_i_250_, lean_object* v_b_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
size_t v_sz_boxed_256_; size_t v_i_boxed_257_; lean_object* v_res_258_; 
v_sz_boxed_256_ = lean_unbox_usize(v_sz_249_);
lean_dec(v_sz_249_);
v_i_boxed_257_ = lean_unbox_usize(v_i_250_);
lean_dec(v_i_250_);
v_res_258_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0(v_as_248_, v_sz_boxed_256_, v_i_boxed_257_, v_b_251_, v___y_252_, v___y_253_, v___y_254_);
lean_dec(v___y_254_);
lean_dec_ref(v___y_253_);
lean_dec(v___y_252_);
lean_dec_ref(v_as_248_);
return v_res_258_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__1(lean_object* v_as_354_, size_t v_sz_355_, size_t v_i_356_, lean_object* v_b_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
uint8_t v___x_362_; 
v___x_362_ = lean_usize_dec_lt(v_i_356_, v_sz_355_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; 
v___x_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_363_, 0, v_b_357_);
return v___x_363_;
}
else
{
lean_object* v___x_364_; lean_object* v_a_365_; uint8_t v___x_366_; 
lean_dec_ref(v_b_357_);
v___x_364_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__1));
v_a_365_ = lean_array_uget_borrowed(v_as_354_, v_i_356_);
lean_inc(v_a_365_);
v___x_366_ = l_Lean_Syntax_isOfKind(v_a_365_, v___x_364_);
if (v___x_366_ == 0)
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__3));
v___x_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
return v___x_368_;
}
else
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v___y_376_; lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_369_ = lean_unsigned_to_nat(0u);
v___x_370_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__4));
v___x_371_ = lean_unsigned_to_nat(1u);
v___x_372_ = l_Lean_Syntax_getArg(v_a_365_, v___x_369_);
v___x_389_ = l_Lean_Syntax_getArg(v_a_365_, v___x_371_);
v___x_390_ = l_Lean_Syntax_isNone(v___x_389_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; uint8_t v___x_392_; 
v___x_391_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_389_);
v___x_392_ = l_Lean_Syntax_matchesNull(v___x_389_, v___x_391_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; lean_object* v___x_394_; 
lean_dec(v___x_389_);
lean_dec(v___x_372_);
v___x_393_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__3));
v___x_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
return v___x_394_;
}
else
{
lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_395_ = l_Lean_Syntax_getArg(v___x_389_, v___x_371_);
lean_dec(v___x_389_);
v___x_396_ = l_Lean_Syntax_matchesNull(v___x_395_, v___x_371_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; lean_object* v___x_398_; 
lean_dec(v___x_372_);
v___x_397_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__3));
v___x_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
return v___x_398_;
}
else
{
v___y_374_ = v___y_358_;
v___y_375_ = v___y_359_;
v___y_376_ = v___y_360_;
goto v___jp_373_;
}
}
}
else
{
lean_dec(v___x_389_);
v___y_374_ = v___y_358_;
v___y_375_ = v___y_359_;
v___y_376_ = v___y_360_;
goto v___jp_373_;
}
v___jp_373_:
{
lean_object* v___x_377_; 
v___x_377_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect(v___x_372_, v___y_374_, v___y_375_, v___y_376_);
if (lean_obj_tag(v___x_377_) == 0)
{
size_t v___x_378_; size_t v___x_379_; 
lean_dec_ref_known(v___x_377_, 1);
v___x_378_ = ((size_t)1ULL);
v___x_379_ = lean_usize_add(v_i_356_, v___x_378_);
v_i_356_ = v___x_379_;
v_b_357_ = v___x_370_;
goto _start;
}
else
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_388_; 
v_a_381_ = lean_ctor_get(v___x_377_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_377_);
if (v_isSharedCheck_388_ == 0)
{
v___x_383_ = v___x_377_;
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_377_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_386_; 
if (v_isShared_384_ == 0)
{
v___x_386_ = v___x_383_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_a_381_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_354_ = stack[0].m_obj;
size_t v_sz_355_ = stack[1].m_num;
size_t v_i_356_ = stack[2].m_num;
lean_object* v_b_357_ = stack[3].m_obj;
lean_object* v___y_358_ = stack[4].m_obj;
lean_object* v___y_359_ = stack[5].m_obj;
lean_object* v___y_360_ = stack[6].m_obj;
lean_object* v_res_399_;
v_res_399_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__1(v_as_354_, v_sz_355_, v_i_356_, v_b_357_, v___y_358_, v___y_359_, v___y_360_);
stack->m_obj
 = v_res_399_;
}
lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect(lean_object* v_tac_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_){
_start:
{
lean_object* v___x_405_; uint8_t v___x_406_; 
v___x_405_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__1));
lean_inc(v_tac_400_);
v___x_406_ = l_Lean_Syntax_isOfKind(v_tac_400_, v___x_405_);
if (v___x_406_ == 0)
{
lean_object* v___x_407_; uint8_t v___x_408_; 
v___x_407_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__3));
lean_inc(v_tac_400_);
v___x_408_ = l_Lean_Syntax_isOfKind(v_tac_400_, v___x_407_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; uint8_t v___x_410_; 
v___x_409_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__5));
lean_inc(v_tac_400_);
v___x_410_ = l_Lean_Syntax_isOfKind(v_tac_400_, v___x_409_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; uint8_t v___x_412_; 
v___x_411_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__7));
lean_inc(v_tac_400_);
v___x_412_ = l_Lean_Syntax_isOfKind(v_tac_400_, v___x_411_);
if (v___x_412_ == 0)
{
lean_object* v___x_413_; uint8_t v___x_414_; 
v___x_413_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__9));
lean_inc(v_tac_400_);
v___x_414_ = l_Lean_Syntax_isOfKind(v_tac_400_, v___x_413_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; uint8_t v___x_416_; 
v___x_415_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__11));
lean_inc(v_tac_400_);
v___x_416_ = l_Lean_Syntax_isOfKind(v_tac_400_, v___x_415_);
if (v___x_416_ == 0)
{
lean_object* v___x_417_; uint8_t v___x_418_; 
v___x_417_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__13));
lean_inc(v_tac_400_);
v___x_418_ = l_Lean_Syntax_isOfKind(v_tac_400_, v___x_417_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; lean_object* v___x_420_; 
lean_dec(v_tac_400_);
v___x_419_ = lean_box(0);
v___x_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
return v___x_420_;
}
else
{
lean_object* v___x_421_; lean_object* v___y_423_; lean_object* v___y_424_; lean_object* v___y_425_; lean_object* v___y_438_; lean_object* v___y_439_; lean_object* v___y_440_; lean_object* v___x_447_; uint8_t v___x_448_; 
v___x_421_ = lean_unsigned_to_nat(1u);
v___x_447_ = l_Lean_Syntax_getArg(v_tac_400_, v___x_421_);
v___x_448_ = l_Lean_Syntax_isNone(v___x_447_);
if (v___x_448_ == 0)
{
uint8_t v___x_449_; 
v___x_449_ = l_Lean_Syntax_matchesNull(v___x_447_, v___x_421_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; lean_object* v___x_451_; 
lean_dec(v_tac_400_);
v___x_450_ = lean_box(0);
v___x_451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_451_, 0, v___x_450_);
return v___x_451_;
}
else
{
v___y_438_ = v_a_401_;
v___y_439_ = v_a_402_;
v___y_440_ = v_a_403_;
goto v___jp_437_;
}
}
else
{
lean_dec(v___x_447_);
v___y_438_ = v_a_401_;
v___y_439_ = v_a_402_;
v___y_440_ = v_a_403_;
goto v___jp_437_;
}
v___jp_422_:
{
lean_object* v___x_426_; lean_object* v___x_427_; uint8_t v___x_428_; 
v___x_426_ = lean_unsigned_to_nat(3u);
v___x_427_ = l_Lean_Syntax_getArg(v_tac_400_, v___x_426_);
lean_dec(v_tac_400_);
v___x_428_ = l_Lean_Syntax_isNone(v___x_427_);
if (v___x_428_ == 0)
{
uint8_t v___x_429_; 
lean_inc(v___x_427_);
v___x_429_ = l_Lean_Syntax_matchesNull(v___x_427_, v___x_426_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; lean_object* v___x_431_; 
lean_dec(v___x_427_);
v___x_430_ = lean_box(0);
v___x_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
return v___x_431_;
}
else
{
lean_object* v___x_432_; lean_object* v_params_x3f_433_; lean_object* v___x_434_; 
v___x_432_ = l_Lean_Syntax_getArg(v___x_427_, v___x_421_);
lean_dec(v___x_427_);
v_params_x3f_433_ = l_Lean_Syntax_getArgs(v___x_432_);
lean_dec(v___x_432_);
v___x_434_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams(v_params_x3f_433_, v___y_423_, v___y_424_, v___y_425_);
lean_dec_ref(v_params_x3f_433_);
return v___x_434_;
}
}
else
{
lean_object* v___x_435_; lean_object* v___x_436_; 
lean_dec(v___x_427_);
v___x_435_ = lean_box(0);
v___x_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
return v___x_436_;
}
}
v___jp_437_:
{
lean_object* v___x_441_; lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_441_ = lean_unsigned_to_nat(2u);
v___x_442_ = l_Lean_Syntax_getArg(v_tac_400_, v___x_441_);
v___x_443_ = l_Lean_Syntax_isNone(v___x_442_);
if (v___x_443_ == 0)
{
uint8_t v___x_444_; 
v___x_444_ = l_Lean_Syntax_matchesNull(v___x_442_, v___x_421_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; lean_object* v___x_446_; 
lean_dec(v_tac_400_);
v___x_445_ = lean_box(0);
v___x_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
return v___x_446_;
}
else
{
v___y_423_ = v___y_438_;
v___y_424_ = v___y_439_;
v___y_425_ = v___y_440_;
goto v___jp_422_;
}
}
else
{
lean_dec(v___x_442_);
v___y_423_ = v___y_438_;
v___y_424_ = v___y_439_;
v___y_425_ = v___y_440_;
goto v___jp_422_;
}
}
}
}
else
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v_params_454_; lean_object* v___x_455_; 
v___x_452_ = lean_unsigned_to_nat(2u);
v___x_453_ = l_Lean_Syntax_getArg(v_tac_400_, v___x_452_);
lean_dec(v_tac_400_);
v_params_454_ = l_Lean_Syntax_getArgs(v___x_453_);
lean_dec(v___x_453_);
v___x_455_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams(v_params_454_, v_a_401_, v_a_402_, v_a_403_);
lean_dec_ref(v_params_454_);
return v___x_455_;
}
}
else
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_456_ = lean_unsigned_to_nat(0u);
v___x_457_ = lean_unsigned_to_nat(1u);
v___x_458_ = l_Lean_Syntax_getArg(v_tac_400_, v___x_457_);
lean_dec(v_tac_400_);
v___x_459_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__15));
lean_inc(v___x_458_);
v___x_460_ = l_Lean_Syntax_isOfKind(v___x_458_, v___x_459_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_461_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__17));
lean_inc(v___x_458_);
v___x_462_ = l_Lean_Syntax_isOfKind(v___x_458_, v___x_461_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; lean_object* v___x_464_; 
lean_dec(v___x_458_);
v___x_463_ = lean_box(0);
v___x_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
return v___x_464_;
}
else
{
lean_object* v_a_465_; 
v_a_465_ = l_Lean_Syntax_getArg(v___x_458_, v___x_456_);
if (v___x_460_ == 0)
{
lean_object* v___x_475_; uint8_t v___x_476_; 
v___x_475_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__11));
lean_inc(v_a_465_);
v___x_476_ = l_Lean_Syntax_isOfKind(v_a_465_, v___x_475_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; lean_object* v___x_478_; 
lean_dec(v_a_465_);
lean_dec(v___x_458_);
v___x_477_ = lean_box(0);
v___x_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
return v___x_478_;
}
else
{
goto v___jp_466_;
}
}
else
{
goto v___jp_466_;
}
v___jp_466_:
{
if (v___x_460_ == 0)
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; uint8_t v___x_470_; 
v___x_467_ = lean_unsigned_to_nat(2u);
v___x_468_ = l_Lean_Syntax_getArg(v___x_458_, v___x_467_);
lean_dec(v___x_458_);
v___x_469_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__19));
v___x_470_ = l_Lean_Syntax_isOfKind(v___x_468_, v___x_469_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; lean_object* v___x_472_; 
lean_dec(v_a_465_);
v___x_471_ = lean_box(0);
v___x_472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
return v___x_472_;
}
else
{
lean_object* v___x_473_; 
v___x_473_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushAnchor___redArg(v_a_465_, v_a_401_);
return v___x_473_;
}
}
else
{
lean_object* v___x_474_; 
lean_dec(v___x_458_);
v___x_474_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushAnchor___redArg(v_a_465_, v_a_401_);
return v___x_474_;
}
}
}
}
else
{
lean_object* v_a_479_; 
v_a_479_ = l_Lean_Syntax_getArg(v___x_458_, v___x_456_);
lean_dec(v___x_458_);
if (v___x_412_ == 0)
{
lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_480_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__11));
lean_inc(v_a_479_);
v___x_481_ = l_Lean_Syntax_isOfKind(v_a_479_, v___x_480_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; lean_object* v___x_483_; 
lean_dec(v_a_479_);
v___x_482_ = lean_box(0);
v___x_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
return v___x_483_;
}
else
{
lean_object* v___x_484_; 
v___x_484_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushAnchor___redArg(v_a_479_, v_a_401_);
return v___x_484_;
}
}
else
{
lean_object* v___x_485_; 
v___x_485_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_pushAnchor___redArg(v_a_479_, v_a_401_);
return v___x_485_;
}
}
}
}
else
{
lean_object* v___x_486_; lean_object* v_tac_u2081_487_; lean_object* v___x_488_; lean_object* v_tac_u2082_489_; lean_object* v___x_490_; 
v___x_486_ = lean_unsigned_to_nat(0u);
v_tac_u2081_487_ = l_Lean_Syntax_getArg(v_tac_400_, v___x_486_);
v___x_488_ = lean_unsigned_to_nat(2u);
v_tac_u2082_489_ = l_Lean_Syntax_getArg(v_tac_400_, v___x_488_);
lean_dec(v_tac_400_);
v___x_490_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect(v_tac_u2081_487_, v_a_401_, v_a_402_, v_a_403_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_dec_ref_known(v___x_490_, 1);
v_tac_400_ = v_tac_u2082_489_;
goto _start;
}
else
{
lean_dec(v_tac_u2082_489_);
return v___x_490_;
}
}
}
else
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; uint8_t v___x_495_; 
v___x_492_ = lean_unsigned_to_nat(1u);
v___x_493_ = l_Lean_Syntax_getArg(v_tac_400_, v___x_492_);
lean_dec(v_tac_400_);
v___x_494_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__21));
lean_inc(v___x_493_);
v___x_495_ = l_Lean_Syntax_isOfKind(v___x_493_, v___x_494_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; lean_object* v___x_497_; 
lean_dec(v___x_493_);
v___x_496_ = lean_box(0);
v___x_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
return v___x_497_;
}
else
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; uint8_t v___x_501_; 
v___x_498_ = lean_unsigned_to_nat(0u);
v___x_499_ = l_Lean_Syntax_getArg(v___x_493_, v___x_498_);
lean_dec(v___x_493_);
v___x_500_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__23));
lean_inc(v___x_499_);
v___x_501_ = l_Lean_Syntax_isOfKind(v___x_499_, v___x_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; lean_object* v___x_503_; 
lean_dec(v___x_499_);
v___x_502_ = lean_box(0);
v___x_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
return v___x_503_;
}
else
{
lean_object* v___x_504_; lean_object* v_seq_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; size_t v_sz_509_; size_t v___x_510_; lean_object* v___x_511_; 
v___x_504_ = l_Lean_Syntax_getArg(v___x_499_, v___x_498_);
lean_dec(v___x_499_);
v_seq_505_ = l_Lean_Syntax_getArgs(v___x_504_);
lean_dec(v___x_504_);
v___x_506_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_seq_505_);
lean_dec_ref(v_seq_505_);
v___x_507_ = lean_box(0);
v___x_508_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__4));
v_sz_509_ = lean_array_size(v___x_506_);
v___x_510_ = ((size_t)0ULL);
v___x_511_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0(v___x_506_, v_sz_509_, v___x_510_, v___x_508_, v_a_401_, v_a_402_, v_a_403_);
lean_dec_ref(v___x_506_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_524_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_524_ == 0)
{
v___x_514_ = v___x_511_;
v_isShared_515_ = v_isSharedCheck_524_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___x_511_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_524_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v_fst_516_; 
v_fst_516_ = lean_ctor_get(v_a_512_, 0);
lean_inc(v_fst_516_);
lean_dec(v_a_512_);
if (lean_obj_tag(v_fst_516_) == 0)
{
lean_object* v___x_518_; 
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 0, v___x_507_);
v___x_518_ = v___x_514_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_507_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
else
{
lean_object* v_val_520_; lean_object* v___x_522_; 
v_val_520_ = lean_ctor_get(v_fst_516_, 0);
lean_inc(v_val_520_);
lean_dec_ref_known(v_fst_516_, 1);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 0, v_val_520_);
v___x_522_ = v___x_514_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_val_520_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
else
{
lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_532_; 
v_a_525_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_532_ == 0)
{
v___x_527_ = v___x_511_;
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_511_);
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
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_a_525_);
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
}
}
else
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_533_ = lean_unsigned_to_nat(0u);
v___x_534_ = lean_unsigned_to_nat(1u);
v___x_535_ = l_Lean_Syntax_getArg(v_tac_400_, v___x_534_);
v___x_536_ = l_Lean_Syntax_matchesNull(v___x_535_, v___x_533_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; lean_object* v___x_538_; 
lean_dec(v_tac_400_);
v___x_537_ = lean_box(0);
v___x_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
return v___x_538_;
}
else
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; 
v___x_539_ = lean_unsigned_to_nat(3u);
v___x_540_ = l_Lean_Syntax_getArg(v_tac_400_, v___x_539_);
lean_dec(v_tac_400_);
v___x_541_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__21));
lean_inc(v___x_540_);
v___x_542_ = l_Lean_Syntax_isOfKind(v___x_540_, v___x_541_);
if (v___x_542_ == 0)
{
lean_object* v___x_543_; lean_object* v___x_544_; 
lean_dec(v___x_540_);
v___x_543_ = lean_box(0);
v___x_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
return v___x_544_;
}
else
{
lean_object* v___x_545_; lean_object* v___x_546_; uint8_t v___x_547_; 
v___x_545_ = l_Lean_Syntax_getArg(v___x_540_, v___x_533_);
lean_dec(v___x_540_);
v___x_546_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___closed__23));
lean_inc(v___x_545_);
v___x_547_ = l_Lean_Syntax_isOfKind(v___x_545_, v___x_546_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; lean_object* v___x_549_; 
lean_dec(v___x_545_);
v___x_548_ = lean_box(0);
v___x_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
return v___x_549_;
}
else
{
lean_object* v___x_550_; lean_object* v_seq_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; size_t v_sz_555_; size_t v___x_556_; lean_object* v___x_557_; 
v___x_550_ = l_Lean_Syntax_getArg(v___x_545_, v___x_533_);
lean_dec(v___x_545_);
v_seq_551_ = l_Lean_Syntax_getArgs(v___x_550_);
lean_dec(v___x_550_);
v___x_552_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_seq_551_);
lean_dec_ref(v_seq_551_);
v___x_553_ = lean_box(0);
v___x_554_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__4));
v_sz_555_ = lean_array_size(v___x_552_);
v___x_556_ = ((size_t)0ULL);
v___x_557_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__1(v___x_552_, v_sz_555_, v___x_556_, v___x_554_, v_a_401_, v_a_402_, v_a_403_);
lean_dec_ref(v___x_552_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_object* v_a_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_570_; 
v_a_558_ = lean_ctor_get(v___x_557_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_570_ == 0)
{
v___x_560_ = v___x_557_;
v_isShared_561_ = v_isSharedCheck_570_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_a_558_);
lean_dec(v___x_557_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_570_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v_fst_562_; 
v_fst_562_ = lean_ctor_get(v_a_558_, 0);
lean_inc(v_fst_562_);
lean_dec(v_a_558_);
if (lean_obj_tag(v_fst_562_) == 0)
{
lean_object* v___x_564_; 
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 0, v___x_553_);
v___x_564_ = v___x_560_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_553_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
else
{
lean_object* v_val_566_; lean_object* v___x_568_; 
v_val_566_ = lean_ctor_get(v_fst_562_, 0);
lean_inc(v_val_566_);
lean_dec_ref_known(v_fst_562_, 1);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 0, v_val_566_);
v___x_568_ = v___x_560_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_val_566_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
else
{
lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_578_; 
v_a_571_ = lean_ctor_get(v___x_557_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_578_ == 0)
{
v___x_573_ = v___x_557_;
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_557_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_576_; 
if (v_isShared_574_ == 0)
{
v___x_576_ = v___x_573_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_571_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
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
lean_object* v___x_579_; lean_object* v_params_580_; lean_object* v_anchors_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_591_; 
lean_dec(v_tac_400_);
v___x_579_ = lean_st_ref_take(v_a_401_);
v_params_580_ = lean_ctor_get(v___x_579_, 0);
v_anchors_581_ = lean_ctor_get(v___x_579_, 1);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_591_ == 0)
{
v___x_583_ = v___x_579_;
v_isShared_584_ = v_isSharedCheck_591_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_anchors_581_);
lean_inc(v_params_580_);
lean_dec(v___x_579_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_591_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_585_; lean_object* v___x_587_; 
v___x_585_ = lean_box(0);
if (v_isShared_584_ == 0)
{
v___x_587_ = v___x_583_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_params_580_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v_anchors_581_);
v___x_587_ = v_reuseFailAlloc_590_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
lean_ctor_set_uint8(v___x_587_, sizeof(void*)*2, v___x_406_);
v___x_588_ = lean_st_ref_put(v_a_401_, v___x_587_);
v___x_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_589_, 0, v___x_585_);
return v___x_589_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_0interp(lean_interpreter_value* stack)
{
lean_object* v_tac_400_ = stack[0].m_obj;
lean_object* v_a_401_ = stack[1].m_obj;
lean_object* v_a_402_ = stack[2].m_obj;
lean_object* v_a_403_ = stack[3].m_obj;
lean_object* v_res_592_;
v_res_592_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect(v_tac_400_, v_a_401_, v_a_402_, v_a_403_);
stack->m_obj
 = v_res_592_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0(lean_object* v_as_593_, size_t v_sz_594_, size_t v_i_595_, lean_object* v_b_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
uint8_t v___x_601_; 
v___x_601_ = lean_usize_dec_lt(v_i_595_, v_sz_594_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; 
v___x_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_602_, 0, v_b_596_);
return v___x_602_;
}
else
{
lean_object* v___x_603_; lean_object* v_a_604_; uint8_t v___x_605_; 
lean_dec_ref(v_b_596_);
v___x_603_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__1));
v_a_604_ = lean_array_uget_borrowed(v_as_593_, v_i_595_);
lean_inc(v_a_604_);
v___x_605_ = l_Lean_Syntax_isOfKind(v_a_604_, v___x_603_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__3));
v___x_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
return v___x_607_;
}
else
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___y_613_; lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v___x_628_; uint8_t v___x_629_; 
v___x_608_ = lean_unsigned_to_nat(0u);
v___x_609_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__4));
v___x_610_ = lean_unsigned_to_nat(1u);
v___x_611_ = l_Lean_Syntax_getArg(v_a_604_, v___x_608_);
v___x_628_ = l_Lean_Syntax_getArg(v_a_604_, v___x_610_);
v___x_629_ = l_Lean_Syntax_isNone(v___x_628_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; uint8_t v___x_631_; 
v___x_630_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_628_);
v___x_631_ = l_Lean_Syntax_matchesNull(v___x_628_, v___x_630_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; lean_object* v___x_633_; 
lean_dec(v___x_628_);
lean_dec(v___x_611_);
v___x_632_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__3));
v___x_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
return v___x_633_;
}
else
{
lean_object* v___x_634_; uint8_t v___x_635_; 
v___x_634_ = l_Lean_Syntax_getArg(v___x_628_, v___x_610_);
lean_dec(v___x_628_);
v___x_635_ = l_Lean_Syntax_matchesNull(v___x_634_, v___x_610_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; lean_object* v___x_637_; 
lean_dec(v___x_611_);
v___x_636_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___closed__3));
v___x_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
return v___x_637_;
}
else
{
v___y_613_ = v___y_597_;
v___y_614_ = v___y_598_;
v___y_615_ = v___y_599_;
goto v___jp_612_;
}
}
}
else
{
lean_dec(v___x_628_);
v___y_613_ = v___y_597_;
v___y_614_ = v___y_598_;
v___y_615_ = v___y_599_;
goto v___jp_612_;
}
v___jp_612_:
{
lean_object* v___x_616_; 
v___x_616_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect(v___x_611_, v___y_613_, v___y_614_, v___y_615_);
if (lean_obj_tag(v___x_616_) == 0)
{
size_t v___x_617_; size_t v___x_618_; 
lean_dec_ref_known(v___x_616_, 1);
v___x_617_ = ((size_t)1ULL);
v___x_618_ = lean_usize_add(v_i_595_, v___x_617_);
v_i_595_ = v___x_618_;
v_b_596_ = v___x_609_;
goto _start;
}
else
{
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_627_; 
v_a_620_ = lean_ctor_get(v___x_616_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_616_);
if (v_isSharedCheck_627_ == 0)
{
v___x_622_ = v___x_616_;
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_616_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_625_; 
if (v_isShared_623_ == 0)
{
v___x_625_ = v___x_622_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_620_);
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
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_593_ = stack[0].m_obj;
size_t v_sz_594_ = stack[1].m_num;
size_t v_i_595_ = stack[2].m_num;
lean_object* v_b_596_ = stack[3].m_obj;
lean_object* v___y_597_ = stack[4].m_obj;
lean_object* v___y_598_ = stack[5].m_obj;
lean_object* v___y_599_ = stack[6].m_obj;
lean_object* v_res_638_;
v_res_638_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0(v_as_593_, v_sz_594_, v_i_595_, v_b_596_, v___y_597_, v___y_598_, v___y_599_);
stack->m_obj
 = v_res_638_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0___boxed(lean_object* v_as_639_, lean_object* v_sz_640_, lean_object* v_i_641_, lean_object* v_b_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
size_t v_sz_boxed_647_; size_t v_i_boxed_648_; lean_object* v_res_649_; 
v_sz_boxed_647_ = lean_unbox_usize(v_sz_640_);
lean_dec(v_sz_640_);
v_i_boxed_648_ = lean_unbox_usize(v_i_641_);
lean_dec(v_i_641_);
v_res_649_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__0(v_as_639_, v_sz_boxed_647_, v_i_boxed_648_, v_b_642_, v___y_643_, v___y_644_, v___y_645_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec(v___y_643_);
lean_dec_ref(v_as_639_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__1___boxed(lean_object* v_as_650_, lean_object* v_sz_651_, lean_object* v_i_652_, lean_object* v_b_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
size_t v_sz_boxed_658_; size_t v_i_boxed_659_; lean_object* v_res_660_; 
v_sz_boxed_658_ = lean_unbox_usize(v_sz_651_);
lean_dec(v_sz_651_);
v_i_boxed_659_ = lean_unbox_usize(v_i_652_);
lean_dec(v_i_652_);
v_res_660_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect_spec__1(v_as_650_, v_sz_boxed_658_, v_i_boxed_659_, v_b_653_, v___y_654_, v___y_655_, v___y_656_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec(v___y_654_);
lean_dec_ref(v_as_650_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect___boxed(lean_object* v_tac_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect(v_tac_661_, v_a_662_, v_a_663_, v_a_664_);
lean_dec(v_a_664_);
lean_dec_ref(v_a_663_);
lean_dec(v_a_662_);
return v_res_666_;
}
}
lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_main_spec__0(lean_object* v_as_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
if (lean_obj_tag(v_as_667_) == 0)
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = lean_box(0);
v___x_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
return v___x_673_;
}
else
{
lean_object* v_head_674_; lean_object* v_tail_675_; lean_object* v___x_676_; 
v_head_674_ = lean_ctor_get(v_as_667_, 0);
lean_inc(v_head_674_);
v_tail_675_ = lean_ctor_get(v_as_667_, 1);
lean_inc(v_tail_675_);
lean_dec_ref_known(v_as_667_, 2);
v___x_676_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collect(v_head_674_, v___y_668_, v___y_669_, v___y_670_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_dec_ref_known(v___x_676_, 1);
v_as_667_ = v_tail_675_;
goto _start;
}
else
{
lean_dec(v_tail_675_);
return v___x_676_;
}
}
}
}
LEAN_EXPORT void l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_main_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_667_ = stack[0].m_obj;
lean_object* v___y_668_ = stack[1].m_obj;
lean_object* v___y_669_ = stack[2].m_obj;
lean_object* v___y_670_ = stack[3].m_obj;
lean_object* v_res_678_;
v_res_678_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_main_spec__0(v_as_667_, v___y_668_, v___y_669_, v___y_670_);
stack->m_obj
 = v_res_678_;
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_main_spec__0___boxed(lean_object* v_as_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_main_spec__0(v_as_679_, v___y_680_, v___y_681_, v___y_682_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v___y_680_);
return v_res_684_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_main(lean_object* v_seq_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_main_spec__0(v_seq_685_, v_a_686_, v_a_687_, v_a_688_);
return v___x_690_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_main_0interp(lean_interpreter_value* stack)
{
lean_object* v_seq_685_ = stack[0].m_obj;
lean_object* v_a_686_ = stack[1].m_obj;
lean_object* v_a_687_ = stack[2].m_obj;
lean_object* v_a_688_ = stack[3].m_obj;
lean_object* v_res_691_;
v_res_691_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_main(v_seq_685_, v_a_686_, v_a_687_, v_a_688_);
stack->m_obj
 = v_res_691_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_main___boxed(lean_object* v_seq_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_main(v_seq_692_, v_a_693_, v_a_694_, v_a_695_);
lean_dec(v_a_695_);
lean_dec_ref(v_a_694_);
lean_dec(v_a_693_);
return v_res_697_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore_spec__0___redArg(size_t v_sz_698_, size_t v_i_699_, lean_object* v_bs_700_, lean_object* v___y_701_){
_start:
{
uint8_t v___x_703_; 
v___x_703_ = lean_usize_dec_lt(v_i_699_, v_sz_698_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; 
v___x_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_704_, 0, v_bs_700_);
return v___x_704_;
}
else
{
lean_object* v_ref_705_; lean_object* v_v_706_; lean_object* v___x_707_; lean_object* v_bs_x27_708_; uint8_t v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; size_t v___x_713_; size_t v___x_714_; lean_object* v___x_715_; 
v_ref_705_ = lean_ctor_get(v___y_701_, 2);
v_v_706_ = lean_array_uget(v_bs_700_, v_i_699_);
v___x_707_ = lean_unsigned_to_nat(0u);
v_bs_x27_708_ = lean_array_uset(v_bs_700_, v_i_699_, v___x_707_);
v___x_709_ = 0;
v___x_710_ = l_Lean_SourceInfo_fromRef(v_ref_705_, v___x_709_);
v___x_711_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_collectInstantiateParams_spec__0___redArg___closed__13));
v___x_712_ = l_Lean_Syntax_node1(v___x_710_, v___x_711_, v_v_706_);
v___x_713_ = ((size_t)1ULL);
v___x_714_ = lean_usize_add(v_i_699_, v___x_713_);
v___x_715_ = lean_array_uset(v_bs_x27_708_, v_i_699_, v___x_712_);
v_i_699_ = v___x_714_;
v_bs_700_ = v___x_715_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_698_ = stack[0].m_num;
size_t v_i_699_ = stack[1].m_num;
lean_object* v_bs_700_ = stack[2].m_obj;
lean_object* v___y_701_ = stack[3].m_obj;
lean_object* v_res_717_;
v_res_717_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore_spec__0___redArg(v_sz_698_, v_i_699_, v_bs_700_, v___y_701_);
stack->m_obj
 = v_res_717_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore_spec__0___redArg___boxed(lean_object* v_sz_718_, lean_object* v_i_719_, lean_object* v_bs_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
size_t v_sz_boxed_723_; size_t v_i_boxed_724_; lean_object* v_res_725_; 
v_sz_boxed_723_ = lean_unbox_usize(v_sz_718_);
lean_dec(v_sz_718_);
v_i_boxed_724_ = lean_unbox_usize(v_i_719_);
lean_dec(v_i_719_);
v_res_725_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore_spec__0___redArg(v_sz_boxed_723_, v_i_boxed_724_, v_bs_720_, v___y_721_);
lean_dec_ref(v___y_721_);
return v_res_725_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore(lean_object* v_seq_731_, lean_object* v_a_732_, lean_object* v_a_733_){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_735_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore___closed__1));
v___x_736_ = lean_st_mk_ref(v___x_735_);
v___x_737_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_Collector_main_spec__0(v_seq_731_, v___x_736_, v_a_732_, v_a_733_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v___x_738_; lean_object* v_params_739_; lean_object* v_anchors_740_; uint8_t v_hasSorry_741_; size_t v_sz_742_; size_t v___x_743_; lean_object* v___x_744_; 
lean_dec_ref_known(v___x_737_, 1);
v___x_738_ = lean_st_ref_get(v___x_736_);
lean_dec(v___x_736_);
v_params_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc_ref(v_params_739_);
v_anchors_740_ = lean_ctor_get(v___x_738_, 1);
lean_inc_ref(v_anchors_740_);
v_hasSorry_741_ = lean_ctor_get_uint8(v___x_738_, sizeof(void*)*2);
lean_dec(v___x_738_);
v_sz_742_ = lean_array_size(v_anchors_740_);
v___x_743_ = ((size_t)0ULL);
v___x_744_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore_spec__0___redArg(v_sz_742_, v___x_743_, v_anchors_740_, v_a_732_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_755_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_755_ == 0)
{
v___x_747_ = v___x_744_;
v_isShared_748_ = v_isSharedCheck_755_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_744_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_755_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_753_; 
v___x_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_749_, 0, v_params_739_);
lean_ctor_set(v___x_749_, 1, v_a_745_);
v___x_750_ = lean_box(v_hasSorry_741_);
v___x_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_751_, 0, v___x_750_);
lean_ctor_set(v___x_751_, 1, v___x_749_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 0, v___x_751_);
v___x_753_ = v___x_747_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_751_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
else
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_dec_ref(v_params_739_);
v_a_756_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_744_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_744_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_756_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
else
{
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
lean_dec(v___x_736_);
v_a_764_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_771_ == 0)
{
v___x_766_ = v___x_737_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_737_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_769_; 
if (v_isShared_767_ == 0)
{
v___x_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_764_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_seq_731_ = stack[0].m_obj;
lean_object* v_a_732_ = stack[1].m_obj;
lean_object* v_a_733_ = stack[2].m_obj;
lean_object* v_res_772_;
v_res_772_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore(v_seq_731_, v_a_732_, v_a_733_);
stack->m_obj
 = v_res_772_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore___boxed(lean_object* v_seq_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore(v_seq_773_, v_a_774_, v_a_775_);
lean_dec(v_a_775_);
lean_dec_ref(v_a_774_);
return v_res_777_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore_spec__0(size_t v_sz_778_, size_t v_i_779_, lean_object* v_bs_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore_spec__0___redArg(v_sz_778_, v_i_779_, v_bs_780_, v___y_781_);
return v___x_784_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_778_ = stack[0].m_num;
size_t v_i_779_ = stack[1].m_num;
lean_object* v_bs_780_ = stack[2].m_obj;
lean_object* v___y_781_ = stack[3].m_obj;
lean_object* v___y_782_ = stack[4].m_obj;
lean_object* v_res_785_;
v_res_785_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore_spec__0(v_sz_778_, v_i_779_, v_bs_780_, v___y_781_, v___y_782_);
stack->m_obj
 = v_res_785_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore_spec__0___boxed(lean_object* v_sz_786_, lean_object* v_i_787_, lean_object* v_bs_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
size_t v_sz_boxed_792_; size_t v_i_boxed_793_; lean_object* v_res_794_; 
v_sz_boxed_792_ = lean_unbox_usize(v_sz_786_);
lean_dec(v_sz_786_);
v_i_boxed_793_ = lean_unbox_usize(v_i_787_);
lean_dec(v_i_787_);
v_res_794_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore_spec__0(v_sz_boxed_792_, v_i_boxed_793_, v_bs_788_, v___y_789_, v___y_790_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
return v_res_794_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParams(lean_object* v_seq_795_, lean_object* v_a_796_, lean_object* v_a_797_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore(v_seq_795_, v_a_796_, v_a_797_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_811_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_811_ == 0)
{
v___x_802_ = v___x_799_;
v_isShared_803_ = v_isSharedCheck_811_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_799_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_811_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v_snd_804_; lean_object* v_fst_805_; lean_object* v_snd_806_; lean_object* v___x_807_; lean_object* v___x_809_; 
v_snd_804_ = lean_ctor_get(v_a_800_, 1);
lean_inc(v_snd_804_);
lean_dec(v_a_800_);
v_fst_805_ = lean_ctor_get(v_snd_804_, 0);
lean_inc(v_fst_805_);
v_snd_806_ = lean_ctor_get(v_snd_804_, 1);
lean_inc(v_snd_806_);
lean_dec(v_snd_804_);
v___x_807_ = l_Array_append___redArg(v_fst_805_, v_snd_806_);
lean_dec(v_snd_806_);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 0, v___x_807_);
v___x_809_ = v___x_802_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_807_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
v_a_812_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_799_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_799_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParams_0interp(lean_interpreter_value* stack)
{
lean_object* v_seq_795_ = stack[0].m_obj;
lean_object* v_a_796_ = stack[1].m_obj;
lean_object* v_a_797_ = stack[2].m_obj;
lean_object* v_res_820_;
v_res_820_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParams(v_seq_795_, v_a_796_, v_a_797_);
stack->m_obj
 = v_res_820_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParams___boxed(lean_object* v_seq_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParams(v_seq_821_, v_a_822_, v_a_823_);
lean_dec(v_a_823_);
lean_dec_ref(v_a_822_);
return v_res_825_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkFinishTactic___closed__4(void){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l_Array_mkArray0___redArg();
return v___x_836_;
}
}
lean_object* l_Lean_Meta_Grind_mkFinishTactic(lean_object* v_seq_841_, lean_object* v_a_842_, lean_object* v_a_843_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParams(v_seq_841_, v_a_842_, v_a_843_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_875_; 
v_a_846_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_875_ == 0)
{
v___x_848_ = v___x_845_;
v_isShared_849_ = v_isSharedCheck_875_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_845_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_875_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v_ref_850_; uint8_t v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_873_; 
v_ref_850_ = lean_ctor_get(v_a_842_, 2);
v___x_851_ = 0;
v___x_852_ = l_Lean_SourceInfo_fromRef(v_ref_850_, v___x_851_);
v___x_853_ = ((lean_object*)(l_Lean_Meta_Grind_mkFinishTactic___closed__0));
v___x_854_ = ((lean_object*)(l_Lean_Meta_Grind_mkFinishTactic___closed__1));
lean_inc_n(v___x_852_, 8);
v___x_855_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_852_);
lean_ctor_set(v___x_855_, 1, v___x_853_);
v___x_856_ = ((lean_object*)(l_Lean_Meta_Grind_mkFinishTactic___closed__3));
v___x_857_ = lean_obj_once(&l_Lean_Meta_Grind_mkFinishTactic___closed__4, &l_Lean_Meta_Grind_mkFinishTactic___closed__4_once, _init_l_Lean_Meta_Grind_mkFinishTactic___closed__4);
v___x_858_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_858_, 0, v___x_852_);
lean_ctor_set(v___x_858_, 1, v___x_856_);
lean_ctor_set(v___x_858_, 2, v___x_857_);
v___x_859_ = ((lean_object*)(l_Lean_Meta_Grind_mkFinishTactic___closed__5));
v___x_860_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_860_, 0, v___x_852_);
lean_ctor_set(v___x_860_, 1, v___x_859_);
v___x_861_ = l_Lean_Syntax_node1(v___x_852_, v___x_856_, v___x_860_);
v___x_862_ = ((lean_object*)(l_Lean_Meta_Grind_mkFinishTactic___closed__6));
v___x_863_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_852_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
v___x_864_ = ((lean_object*)(l_Lean_Meta_Grind_mkFinishTactic___closed__7));
v___x_865_ = l_Lean_Syntax_SepArray_ofElems(v___x_864_, v_a_846_);
lean_dec(v_a_846_);
v___x_866_ = l_Array_append___redArg(v___x_857_, v___x_865_);
lean_dec_ref(v___x_865_);
v___x_867_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_867_, 0, v___x_852_);
lean_ctor_set(v___x_867_, 1, v___x_856_);
lean_ctor_set(v___x_867_, 2, v___x_866_);
v___x_868_ = ((lean_object*)(l_Lean_Meta_Grind_mkFinishTactic___closed__8));
v___x_869_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_852_);
lean_ctor_set(v___x_869_, 1, v___x_868_);
v___x_870_ = l_Lean_Syntax_node3(v___x_852_, v___x_856_, v___x_863_, v___x_867_, v___x_869_);
v___x_871_ = l_Lean_Syntax_node4(v___x_852_, v___x_854_, v___x_855_, v___x_858_, v___x_861_, v___x_870_);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 0, v___x_871_);
v___x_873_ = v___x_848_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_871_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
v_a_876_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_845_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_845_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_mkFinishTactic_0interp(lean_interpreter_value* stack)
{
lean_object* v_seq_841_ = stack[0].m_obj;
lean_object* v_a_842_ = stack[1].m_obj;
lean_object* v_a_843_ = stack[2].m_obj;
lean_object* v_res_884_;
v_res_884_ = l_Lean_Meta_Grind_mkFinishTactic(v_seq_841_, v_a_842_, v_a_843_);
stack->m_obj
 = v_res_884_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkFinishTactic___boxed(lean_object* v_seq_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Lean_Meta_Grind_mkFinishTactic(v_seq_885_, v_a_886_, v_a_887_);
lean_dec(v_a_887_);
lean_dec_ref(v_a_886_);
return v_res_889_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg(lean_object* v_cfg_896_, lean_object* v_params_897_, lean_object* v_a_898_){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; uint8_t v___x_902_; 
v___x_900_ = lean_array_get_size(v_params_897_);
v___x_901_ = lean_unsigned_to_nat(0u);
v___x_902_ = lean_nat_dec_eq(v___x_900_, v___x_901_);
if (v___x_902_ == 0)
{
lean_object* v_ref_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v_ref_903_ = lean_ctor_get(v_a_898_, 2);
v___x_904_ = l_Lean_SourceInfo_fromRef(v_ref_903_, v___x_902_);
v___x_905_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg___closed__0));
v___x_906_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg___closed__1));
lean_inc_n(v___x_904_, 8);
v___x_907_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_904_);
lean_ctor_set(v___x_907_, 1, v___x_905_);
v___x_908_ = ((lean_object*)(l_Lean_Meta_Grind_mkFinishTactic___closed__3));
v___x_909_ = ((lean_object*)(l_Lean_Meta_Grind_mkFinishTactic___closed__5));
v___x_910_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_904_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = l_Lean_Syntax_node1(v___x_904_, v___x_908_, v___x_910_);
v___x_912_ = ((lean_object*)(l_Lean_Meta_Grind_mkFinishTactic___closed__6));
v___x_913_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_904_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = lean_obj_once(&l_Lean_Meta_Grind_mkFinishTactic___closed__4, &l_Lean_Meta_Grind_mkFinishTactic___closed__4_once, _init_l_Lean_Meta_Grind_mkFinishTactic___closed__4);
v___x_915_ = ((lean_object*)(l_Lean_Meta_Grind_mkFinishTactic___closed__7));
v___x_916_ = l_Lean_Syntax_SepArray_ofElems(v___x_915_, v_params_897_);
v___x_917_ = l_Array_append___redArg(v___x_914_, v___x_916_);
lean_dec_ref(v___x_916_);
v___x_918_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_918_, 0, v___x_904_);
lean_ctor_set(v___x_918_, 1, v___x_908_);
lean_ctor_set(v___x_918_, 2, v___x_917_);
v___x_919_ = ((lean_object*)(l_Lean_Meta_Grind_mkFinishTactic___closed__8));
v___x_920_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_904_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
v___x_921_ = l_Lean_Syntax_node3(v___x_904_, v___x_908_, v___x_913_, v___x_918_, v___x_920_);
v___x_922_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_922_, 0, v___x_904_);
lean_ctor_set(v___x_922_, 1, v___x_908_);
lean_ctor_set(v___x_922_, 2, v___x_914_);
v___x_923_ = l_Lean_Syntax_node5(v___x_904_, v___x_906_, v___x_907_, v_cfg_896_, v___x_911_, v___x_921_, v___x_922_);
v___x_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_924_, 0, v___x_923_);
return v___x_924_;
}
else
{
lean_object* v_ref_925_; uint8_t v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v_ref_925_ = lean_ctor_get(v_a_898_, 2);
v___x_926_ = 0;
v___x_927_ = l_Lean_SourceInfo_fromRef(v_ref_925_, v___x_926_);
v___x_928_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg___closed__0));
v___x_929_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg___closed__1));
lean_inc_n(v___x_927_, 4);
v___x_930_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_927_);
lean_ctor_set(v___x_930_, 1, v___x_928_);
v___x_931_ = ((lean_object*)(l_Lean_Meta_Grind_mkFinishTactic___closed__3));
v___x_932_ = ((lean_object*)(l_Lean_Meta_Grind_mkFinishTactic___closed__5));
v___x_933_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_927_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
v___x_934_ = l_Lean_Syntax_node1(v___x_927_, v___x_931_, v___x_933_);
v___x_935_ = lean_obj_once(&l_Lean_Meta_Grind_mkFinishTactic___closed__4, &l_Lean_Meta_Grind_mkFinishTactic___closed__4_once, _init_l_Lean_Meta_Grind_mkFinishTactic___closed__4);
v___x_936_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_936_, 0, v___x_927_);
lean_ctor_set(v___x_936_, 1, v___x_931_);
lean_ctor_set(v___x_936_, 2, v___x_935_);
lean_inc_ref(v___x_936_);
v___x_937_ = l_Lean_Syntax_node5(v___x_927_, v___x_929_, v___x_930_, v_cfg_896_, v___x_934_, v___x_936_, v___x_936_);
v___x_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
return v___x_938_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_896_ = stack[0].m_obj;
lean_object* v_params_897_ = stack[1].m_obj;
lean_object* v_a_898_ = stack[2].m_obj;
lean_object* v_res_939_;
v_res_939_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg(v_cfg_896_, v_params_897_, v_a_898_);
stack->m_obj
 = v_res_939_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg___boxed(lean_object* v_cfg_940_, lean_object* v_params_941_, lean_object* v_a_942_, lean_object* v_a_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg(v_cfg_940_, v_params_941_, v_a_942_);
lean_dec_ref(v_a_942_);
lean_dec_ref(v_params_941_);
return v_res_944_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac(lean_object* v_cfg_945_, lean_object* v_params_946_, lean_object* v_a_947_, lean_object* v_a_948_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg(v_cfg_945_, v_params_946_, v_a_947_);
return v___x_950_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_945_ = stack[0].m_obj;
lean_object* v_params_946_ = stack[1].m_obj;
lean_object* v_a_947_ = stack[2].m_obj;
lean_object* v_a_948_ = stack[3].m_obj;
lean_object* v_res_951_;
v_res_951_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac(v_cfg_945_, v_params_946_, v_a_947_, v_a_948_);
stack->m_obj
 = v_res_951_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___boxed(lean_object* v_cfg_952_, lean_object* v_params_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac(v_cfg_952_, v_params_953_, v_a_954_, v_a_955_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
lean_dec_ref(v_params_953_);
return v_res_957_;
}
}
lean_object* l_Lean_Meta_Grind_mkGrindOnlyTactics(lean_object* v_cfg_958_, lean_object* v_seq_959_, lean_object* v_extraParams_960_, lean_object* v_a_961_, lean_object* v_a_962_){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore(v_seq_959_, v_a_961_, v_a_962_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v_a_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_1009_; 
v_a_965_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_967_ = v___x_964_;
v_isShared_968_ = v_isSharedCheck_1009_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_a_965_);
lean_dec(v___x_964_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_1009_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v_snd_969_; lean_object* v_fst_970_; uint8_t v___x_971_; 
v_snd_969_ = lean_ctor_get(v_a_965_, 1);
lean_inc(v_snd_969_);
v_fst_970_ = lean_ctor_get(v_a_965_, 0);
lean_inc(v_fst_970_);
lean_dec(v_a_965_);
v___x_971_ = lean_unbox(v_fst_970_);
lean_dec(v_fst_970_);
if (v___x_971_ == 0)
{
lean_object* v_fst_972_; lean_object* v_snd_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_1004_; 
lean_del_object(v___x_967_);
v_fst_972_ = lean_ctor_get(v_snd_969_, 0);
lean_inc_n(v_fst_972_, 2);
v_snd_973_ = lean_ctor_get(v_snd_969_, 1);
lean_inc(v_snd_973_);
lean_dec(v_snd_969_);
v___x_974_ = l_Array_append___redArg(v_fst_972_, v_snd_973_);
v___x_975_ = l_Array_append___redArg(v___x_974_, v_extraParams_960_);
lean_inc(v_cfg_958_);
v___x_976_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg(v_cfg_958_, v___x_975_, v_a_961_);
lean_dec_ref(v___x_975_);
v_a_977_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_979_ = v___x_976_;
v_isShared_980_ = v_isSharedCheck_1004_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_dec(v___x_976_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_1004_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_981_; lean_object* v___x_982_; uint8_t v___x_983_; 
v___x_981_ = lean_array_get_size(v_snd_973_);
lean_dec(v_snd_973_);
v___x_982_ = lean_unsigned_to_nat(0u);
v___x_983_ = lean_nat_dec_eq(v___x_981_, v___x_982_);
if (v___x_983_ == 0)
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_997_; 
lean_del_object(v___x_979_);
v___x_984_ = l_Array_append___redArg(v_fst_972_, v_extraParams_960_);
v___x_985_ = l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_mkGrindOnlyTactics_mkTac___redArg(v_cfg_958_, v___x_984_, v_a_961_);
lean_dec_ref(v___x_984_);
v_a_986_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_997_ == 0)
{
v___x_988_ = v___x_985_;
v_isShared_989_ = v_isSharedCheck_997_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_985_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_997_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_995_; 
v___x_990_ = lean_unsigned_to_nat(2u);
v___x_991_ = lean_mk_empty_array_with_capacity(v___x_990_);
v___x_992_ = lean_array_push(v___x_991_, v_a_977_);
v___x_993_ = lean_array_push(v___x_992_, v_a_986_);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 0, v___x_993_);
v___x_995_ = v___x_988_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_993_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
else
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1002_; 
lean_dec(v_fst_972_);
lean_dec(v_cfg_958_);
v___x_998_ = lean_unsigned_to_nat(1u);
v___x_999_ = lean_mk_empty_array_with_capacity(v___x_998_);
v___x_1000_ = lean_array_push(v___x_999_, v_a_977_);
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 0, v___x_1000_);
v___x_1002_ = v___x_979_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v___x_1000_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
}
else
{
lean_object* v___x_1005_; lean_object* v___x_1007_; 
lean_dec(v_snd_969_);
lean_dec(v_cfg_958_);
v___x_1005_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_CollectParams_0__Lean_Meta_Grind_collectParamsCore___closed__0));
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 0, v___x_1005_);
v___x_1007_ = v___x_967_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v___x_1005_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
lean_dec(v_cfg_958_);
v_a_1010_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_964_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_964_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1010_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_mkGrindOnlyTactics_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_958_ = stack[0].m_obj;
lean_object* v_seq_959_ = stack[1].m_obj;
lean_object* v_extraParams_960_ = stack[2].m_obj;
lean_object* v_a_961_ = stack[3].m_obj;
lean_object* v_a_962_ = stack[4].m_obj;
lean_object* v_res_1018_;
v_res_1018_ = l_Lean_Meta_Grind_mkGrindOnlyTactics(v_cfg_958_, v_seq_959_, v_extraParams_960_, v_a_961_, v_a_962_);
stack->m_obj
 = v_res_1018_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkGrindOnlyTactics___boxed(lean_object* v_cfg_1019_, lean_object* v_seq_1020_, lean_object* v_extraParams_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lean_Meta_Grind_mkGrindOnlyTactics(v_cfg_1019_, v_seq_1020_, v_extraParams_1021_, v_a_1022_, v_a_1023_);
lean_dec(v_a_1023_);
lean_dec_ref(v_a_1022_);
lean_dec_ref(v_extraParams_1021_);
return v_res_1025_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_CollectParams(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_CollectParams(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_CollectParams(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_CollectParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_CollectParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_CollectParams(builtin);
}
#ifdef __cplusplus
}
#endif
