// Lean compiler output
// Module: Lean.Elab.PreDefinition.Structural.RecArgInfo
// Imports: public import Lean.Elab.PreDefinition.FixedParams public import Lean.Elab.PreDefinition.Structural.IndGroupInfo
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
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_string_length(lean_object*);
extern lean_object* l_Lean_Elab_Structural_instInhabitedIndGroupInst_default;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Elab_FixedParamPerm_isFixed(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_numFixed(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
extern lean_object* l_Lean_instInhabitedExpr;
static const lean_array_object l_Lean_Elab_Structural_instInhabitedRecArgInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Structural_instInhabitedRecArgInfo_default___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_instInhabitedRecArgInfo_default___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Structural_instInhabitedRecArgInfo_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instInhabitedRecArgInfo_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_instInhabitedRecArgInfo;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__2(lean_object*);
static const lean_string_object l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0___closed__0 = (const lean_object*)&l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0___closed__0_value;
static const lean_ctor_object l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0___closed__0_value)}};
static const lean_object* l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0___closed__1 = (const lean_object*)&l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0___closed__1_value;
static const lean_string_object l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "some "};
static const lean_object* l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0___closed__2 = (const lean_object*)&l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0___closed__2_value;
static const lean_ctor_object l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0___closed__2_value)}};
static const lean_object* l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0___closed__3 = (const lean_object*)&l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__1___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__1(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__0 = (const lean_object*)&l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__0_value;
static const lean_string_object l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__1 = (const lean_object*)&l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__1_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__1_value)}};
static const lean_object* l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__2 = (const lean_object*)&l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__2_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__3 = (const lean_object*)&l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__3_value;
static const lean_string_object l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__4 = (const lean_object*)&l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__4_value;
static lean_once_cell_t l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__5;
static lean_once_cell_t l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__6;
static const lean_ctor_object l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__7 = (const lean_object*)&l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__7_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__4_value)}};
static const lean_object* l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__8 = (const lean_object*)&l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__8_value;
static const lean_string_object l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__9 = (const lean_object*)&l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__9_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__9_value)}};
static const lean_object* l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__10 = (const lean_object*)&l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__10_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__1_spec__3_spec__6_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__1_spec__3___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__1(lean_object*);
static const lean_string_object l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "fnName"};
static const lean_object* l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__3_value),((lean_object*)&l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__7;
static const lean_string_object l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fixedParamPerm"};
static const lean_object* l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__9_value;
static lean_once_cell_t l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__10;
static const lean_string_object l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "recArgPos"};
static const lean_object* l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__11_value)}};
static const lean_object* l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__12_value;
static lean_once_cell_t l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__13;
static const lean_string_object l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "indicesPos"};
static const lean_object* l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__14 = (const lean_object*)&l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__14_value)}};
static const lean_object* l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__15 = (const lean_object*)&l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__15_value;
static lean_once_cell_t l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__16;
static const lean_string_object l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "indGroupInst"};
static const lean_object* l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__17 = (const lean_object*)&l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__17_value;
static const lean_ctor_object l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__17_value)}};
static const lean_object* l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__18 = (const lean_object*)&l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__18_value;
static lean_once_cell_t l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__19;
static const lean_string_object l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "indIdx"};
static const lean_object* l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__20 = (const lean_object*)&l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__20_value;
static const lean_ctor_object l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__20_value)}};
static const lean_object* l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__21 = (const lean_object*)&l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__21_value;
static const lean_string_object l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__22 = (const lean_object*)&l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__22_value;
static lean_once_cell_t l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__23;
static lean_once_cell_t l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__24;
static const lean_ctor_object l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__25 = (const lean_object*)&l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__25_value;
static const lean_ctor_object l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__22_value)}};
static const lean_object* l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__26 = (const lean_object*)&l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__26_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_instReprRecArgInfo_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_instReprRecArgInfo_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Structural_instReprRecArgInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Structural_instReprRecArgInfo_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_instReprRecArgInfo___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_instReprRecArgInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Structural_instReprRecArgInfo = (const lean_object*)&l_Lean_Elab_Structural_instReprRecArgInfo___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_RecArgInfo_indicesAndRecArgPos(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__0;
static lean_once_cell_t l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__1;
static const lean_array_object l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__2 = (const lean_object*)&l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_RecArgInfo_indName_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_RecArgInfo_indName_x21___boxed(lean_object*);
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedRecArgInfo_default___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_3_ = l_Lean_Elab_Structural_instInhabitedIndGroupInst_default;
v___x_4_ = lean_unsigned_to_nat(0u);
v___x_5_ = ((lean_object*)(l_Lean_Elab_Structural_instInhabitedRecArgInfo_default___closed__0));
v___x_6_ = lean_box(0);
v___x_7_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_7_, 0, v___x_6_);
lean_ctor_set(v___x_7_, 1, v___x_5_);
lean_ctor_set(v___x_7_, 2, v___x_4_);
lean_ctor_set(v___x_7_, 3, v___x_5_);
lean_ctor_set(v___x_7_, 4, v___x_3_);
lean_ctor_set(v___x_7_, 5, v___x_4_);
return v___x_7_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedRecArgInfo_default(void){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_obj_once(&l_Lean_Elab_Structural_instInhabitedRecArgInfo_default___closed__1, &l_Lean_Elab_Structural_instInhabitedRecArgInfo_default___closed__1_once, _init_l_Lean_Elab_Structural_instInhabitedRecArgInfo_default___closed__1);
return v___x_8_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedRecArgInfo(void){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__2(lean_object* v_a_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_nat_to_int(v_a_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0(lean_object* v_x_18_, lean_object* v_x_19_){
_start:
{
if (lean_obj_tag(v_x_18_) == 0)
{
lean_object* v___x_20_; 
v___x_20_ = ((lean_object*)(l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0___closed__1));
return v___x_20_;
}
else
{
lean_object* v_val_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_32_; 
v_val_21_ = lean_ctor_get(v_x_18_, 0);
v_isSharedCheck_32_ = !lean_is_exclusive(v_x_18_);
if (v_isSharedCheck_32_ == 0)
{
v___x_23_ = v_x_18_;
v_isShared_24_ = v_isSharedCheck_32_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_val_21_);
lean_dec(v_x_18_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_32_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_28_; 
v___x_25_ = ((lean_object*)(l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0___closed__3));
v___x_26_ = l_Nat_reprFast(v_val_21_);
if (v_isShared_24_ == 0)
{
lean_ctor_set_tag(v___x_23_, 3);
lean_ctor_set(v___x_23_, 0, v___x_26_);
v___x_28_ = v___x_23_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v___x_26_);
v___x_28_ = v_reuseFailAlloc_31_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_29_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_29_, 0, v___x_25_);
lean_ctor_set(v___x_29_, 1, v___x_28_);
v___x_30_ = l_Repr_addAppParen(v___x_29_, v_x_19_);
return v___x_30_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0___boxed(lean_object* v_x_33_, lean_object* v_x_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0(v_x_33_, v_x_34_);
lean_dec(v_x_34_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__1___lam__0(lean_object* v___y_36_){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = lean_unsigned_to_nat(0u);
v___x_38_ = l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0(v___y_36_, v___x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__1_spec__3_spec__5(lean_object* v_x_39_, lean_object* v_x_40_, lean_object* v_x_41_){
_start:
{
if (lean_obj_tag(v_x_41_) == 0)
{
lean_dec(v_x_39_);
return v_x_40_;
}
else
{
lean_object* v_head_42_; lean_object* v_tail_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_54_; 
v_head_42_ = lean_ctor_get(v_x_41_, 0);
v_tail_43_ = lean_ctor_get(v_x_41_, 1);
v_isSharedCheck_54_ = !lean_is_exclusive(v_x_41_);
if (v_isSharedCheck_54_ == 0)
{
v___x_45_ = v_x_41_;
v_isShared_46_ = v_isSharedCheck_54_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_tail_43_);
lean_inc(v_head_42_);
lean_dec(v_x_41_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_54_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
lean_object* v___x_48_; 
lean_inc(v_x_39_);
if (v_isShared_46_ == 0)
{
lean_ctor_set_tag(v___x_45_, 5);
lean_ctor_set(v___x_45_, 1, v_x_39_);
lean_ctor_set(v___x_45_, 0, v_x_40_);
v___x_48_ = v___x_45_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v_x_40_);
lean_ctor_set(v_reuseFailAlloc_53_, 1, v_x_39_);
v___x_48_ = v_reuseFailAlloc_53_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = lean_unsigned_to_nat(0u);
v___x_50_ = l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0(v_head_42_, v___x_49_);
v___x_51_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_51_, 0, v___x_48_);
lean_ctor_set(v___x_51_, 1, v___x_50_);
v_x_40_ = v___x_51_;
v_x_41_ = v_tail_43_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__1_spec__3(lean_object* v_x_55_, lean_object* v_x_56_, lean_object* v_x_57_){
_start:
{
if (lean_obj_tag(v_x_57_) == 0)
{
lean_dec(v_x_55_);
return v_x_56_;
}
else
{
lean_object* v_head_58_; lean_object* v_tail_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_70_; 
v_head_58_ = lean_ctor_get(v_x_57_, 0);
v_tail_59_ = lean_ctor_get(v_x_57_, 1);
v_isSharedCheck_70_ = !lean_is_exclusive(v_x_57_);
if (v_isSharedCheck_70_ == 0)
{
v___x_61_ = v_x_57_;
v_isShared_62_ = v_isSharedCheck_70_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_tail_59_);
lean_inc(v_head_58_);
lean_dec(v_x_57_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_70_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v___x_64_; 
lean_inc(v_x_55_);
if (v_isShared_62_ == 0)
{
lean_ctor_set_tag(v___x_61_, 5);
lean_ctor_set(v___x_61_, 1, v_x_55_);
lean_ctor_set(v___x_61_, 0, v_x_56_);
v___x_64_ = v___x_61_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v_x_56_);
lean_ctor_set(v_reuseFailAlloc_69_, 1, v_x_55_);
v___x_64_ = v_reuseFailAlloc_69_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_65_ = lean_unsigned_to_nat(0u);
v___x_66_ = l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0(v_head_58_, v___x_65_);
v___x_67_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_67_, 0, v___x_64_);
lean_ctor_set(v___x_67_, 1, v___x_66_);
v___x_68_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__1_spec__3_spec__5(v_x_55_, v___x_67_, v_tail_59_);
return v___x_68_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__1(lean_object* v_x_71_, lean_object* v_x_72_){
_start:
{
if (lean_obj_tag(v_x_71_) == 0)
{
lean_object* v___x_73_; 
lean_dec(v_x_72_);
v___x_73_ = lean_box(0);
return v___x_73_;
}
else
{
lean_object* v_tail_74_; 
v_tail_74_ = lean_ctor_get(v_x_71_, 1);
if (lean_obj_tag(v_tail_74_) == 0)
{
lean_object* v_head_75_; lean_object* v___x_76_; 
lean_dec(v_x_72_);
v_head_75_ = lean_ctor_get(v_x_71_, 0);
lean_inc(v_head_75_);
lean_dec_ref(v_x_71_);
v___x_76_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__1___lam__0(v_head_75_);
return v___x_76_;
}
else
{
lean_object* v_head_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
lean_inc(v_tail_74_);
v_head_77_ = lean_ctor_get(v_x_71_, 0);
lean_inc(v_head_77_);
lean_dec_ref(v_x_71_);
v___x_78_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__1___lam__0(v_head_77_);
v___x_79_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__1_spec__3(v_x_72_, v___x_78_, v_tail_74_);
return v___x_79_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__0));
v___x_89_ = lean_string_length(v___x_88_);
return v___x_89_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__6(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = lean_obj_once(&l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__5, &l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__5);
v___x_91_ = lean_nat_to_int(v___x_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0(lean_object* v_xs_99_){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_100_ = lean_array_get_size(v_xs_99_);
v___x_101_ = lean_unsigned_to_nat(0u);
v___x_102_ = lean_nat_dec_eq(v___x_100_, v___x_101_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_103_ = lean_array_to_list(v_xs_99_);
v___x_104_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__3));
v___x_105_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__1(v___x_103_, v___x_104_);
v___x_106_ = lean_obj_once(&l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__6, &l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__6);
v___x_107_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__7));
v___x_108_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
lean_ctor_set(v___x_108_, 1, v___x_105_);
v___x_109_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__8));
v___x_110_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_110_, 0, v___x_108_);
lean_ctor_set(v___x_110_, 1, v___x_109_);
v___x_111_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_106_);
lean_ctor_set(v___x_111_, 1, v___x_110_);
v___x_112_ = l_Std_Format_fill(v___x_111_);
return v___x_112_;
}
else
{
lean_object* v___x_113_; 
lean_dec_ref(v_xs_99_);
v___x_113_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__10));
return v___x_113_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__1_spec__3_spec__6_spec__8(lean_object* v_x_114_, lean_object* v_x_115_, lean_object* v_x_116_){
_start:
{
if (lean_obj_tag(v_x_116_) == 0)
{
lean_dec(v_x_114_);
return v_x_115_;
}
else
{
lean_object* v_head_117_; lean_object* v_tail_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_129_; 
v_head_117_ = lean_ctor_get(v_x_116_, 0);
v_tail_118_ = lean_ctor_get(v_x_116_, 1);
v_isSharedCheck_129_ = !lean_is_exclusive(v_x_116_);
if (v_isSharedCheck_129_ == 0)
{
v___x_120_ = v_x_116_;
v_isShared_121_ = v_isSharedCheck_129_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_tail_118_);
lean_inc(v_head_117_);
lean_dec(v_x_116_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_129_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_123_; 
lean_inc(v_x_114_);
if (v_isShared_121_ == 0)
{
lean_ctor_set_tag(v___x_120_, 5);
lean_ctor_set(v___x_120_, 1, v_x_114_);
lean_ctor_set(v___x_120_, 0, v_x_115_);
v___x_123_ = v___x_120_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_x_115_);
lean_ctor_set(v_reuseFailAlloc_128_, 1, v_x_114_);
v___x_123_ = v_reuseFailAlloc_128_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_124_ = l_Nat_reprFast(v_head_117_);
v___x_125_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
v___x_126_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_123_);
lean_ctor_set(v___x_126_, 1, v___x_125_);
v_x_115_ = v___x_126_;
v_x_116_ = v_tail_118_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__1_spec__3_spec__6(lean_object* v_x_130_, lean_object* v_x_131_, lean_object* v_x_132_){
_start:
{
if (lean_obj_tag(v_x_132_) == 0)
{
lean_dec(v_x_130_);
return v_x_131_;
}
else
{
lean_object* v_head_133_; lean_object* v_tail_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_145_; 
v_head_133_ = lean_ctor_get(v_x_132_, 0);
v_tail_134_ = lean_ctor_get(v_x_132_, 1);
v_isSharedCheck_145_ = !lean_is_exclusive(v_x_132_);
if (v_isSharedCheck_145_ == 0)
{
v___x_136_ = v_x_132_;
v_isShared_137_ = v_isSharedCheck_145_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_tail_134_);
lean_inc(v_head_133_);
lean_dec(v_x_132_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_145_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_139_; 
lean_inc(v_x_130_);
if (v_isShared_137_ == 0)
{
lean_ctor_set_tag(v___x_136_, 5);
lean_ctor_set(v___x_136_, 1, v_x_130_);
lean_ctor_set(v___x_136_, 0, v_x_131_);
v___x_139_ = v___x_136_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_x_131_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v_x_130_);
v___x_139_ = v_reuseFailAlloc_144_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_140_ = l_Nat_reprFast(v_head_133_);
v___x_141_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
v___x_142_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_139_);
lean_ctor_set(v___x_142_, 1, v___x_141_);
v___x_143_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__1_spec__3_spec__6_spec__8(v_x_130_, v___x_142_, v_tail_134_);
return v___x_143_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__1_spec__3___lam__0(lean_object* v___y_146_){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = l_Nat_reprFast(v___y_146_);
v___x_148_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__1_spec__3(lean_object* v_x_149_, lean_object* v_x_150_){
_start:
{
if (lean_obj_tag(v_x_149_) == 0)
{
lean_object* v___x_151_; 
lean_dec(v_x_150_);
v___x_151_ = lean_box(0);
return v___x_151_;
}
else
{
lean_object* v_tail_152_; 
v_tail_152_ = lean_ctor_get(v_x_149_, 1);
if (lean_obj_tag(v_tail_152_) == 0)
{
lean_object* v_head_153_; lean_object* v___x_154_; 
lean_dec(v_x_150_);
v_head_153_ = lean_ctor_get(v_x_149_, 0);
lean_inc(v_head_153_);
lean_dec_ref(v_x_149_);
v___x_154_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__1_spec__3___lam__0(v_head_153_);
return v___x_154_;
}
else
{
lean_object* v_head_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
lean_inc(v_tail_152_);
v_head_155_ = lean_ctor_get(v_x_149_, 0);
lean_inc(v_head_155_);
lean_dec_ref(v_x_149_);
v___x_156_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__1_spec__3___lam__0(v_head_155_);
v___x_157_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__1_spec__3_spec__6(v_x_150_, v___x_156_, v_tail_152_);
return v___x_157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__1(lean_object* v_xs_158_){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_159_ = lean_array_get_size(v_xs_158_);
v___x_160_ = lean_unsigned_to_nat(0u);
v___x_161_ = lean_nat_dec_eq(v___x_159_, v___x_160_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_162_ = lean_array_to_list(v_xs_158_);
v___x_163_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__3));
v___x_164_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__1_spec__3(v___x_162_, v___x_163_);
v___x_165_ = lean_obj_once(&l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__6, &l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__6);
v___x_166_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__7));
v___x_167_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
lean_ctor_set(v___x_167_, 1, v___x_164_);
v___x_168_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__8));
v___x_169_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_169_, 0, v___x_167_);
lean_ctor_set(v___x_169_, 1, v___x_168_);
v___x_170_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_165_);
lean_ctor_set(v___x_170_, 1, v___x_169_);
v___x_171_ = l_Std_Format_fill(v___x_170_);
return v___x_171_;
}
else
{
lean_object* v___x_172_; 
lean_dec_ref(v_xs_158_);
v___x_172_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__10));
return v___x_172_;
}
}
}
static lean_object* _init_l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_186_ = lean_unsigned_to_nat(10u);
v___x_187_ = lean_nat_to_int(v___x_186_);
return v___x_187_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = lean_unsigned_to_nat(18u);
v___x_192_ = lean_nat_to_int(v___x_191_);
return v___x_192_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = lean_unsigned_to_nat(13u);
v___x_197_ = lean_nat_to_int(v___x_196_);
return v___x_197_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = lean_unsigned_to_nat(14u);
v___x_202_ = lean_nat_to_int(v___x_201_);
return v___x_202_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = lean_unsigned_to_nat(16u);
v___x_207_ = lean_nat_to_int(v___x_206_);
return v___x_207_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__23(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = ((lean_object*)(l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__0));
v___x_213_ = lean_string_length(v___x_212_);
return v___x_213_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__24(void){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_214_ = lean_obj_once(&l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__23, &l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__23_once, _init_l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__23);
v___x_215_ = lean_nat_to_int(v___x_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(lean_object* v_x_220_){
_start:
{
lean_object* v_fnName_221_; lean_object* v_fixedParamPerm_222_; lean_object* v_recArgPos_223_; lean_object* v_indicesPos_224_; lean_object* v_indGroupInst_225_; lean_object* v_indIdx_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; uint8_t v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v_fnName_221_ = lean_ctor_get(v_x_220_, 0);
lean_inc(v_fnName_221_);
v_fixedParamPerm_222_ = lean_ctor_get(v_x_220_, 1);
lean_inc_ref(v_fixedParamPerm_222_);
v_recArgPos_223_ = lean_ctor_get(v_x_220_, 2);
lean_inc(v_recArgPos_223_);
v_indicesPos_224_ = lean_ctor_get(v_x_220_, 3);
lean_inc_ref(v_indicesPos_224_);
v_indGroupInst_225_ = lean_ctor_get(v_x_220_, 4);
lean_inc_ref(v_indGroupInst_225_);
v_indIdx_226_ = lean_ctor_get(v_x_220_, 5);
lean_inc(v_indIdx_226_);
lean_dec_ref(v_x_220_);
v___x_227_ = ((lean_object*)(l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__5));
v___x_228_ = ((lean_object*)(l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__6));
v___x_229_ = lean_obj_once(&l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__7, &l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__7_once, _init_l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__7);
v___x_230_ = lean_unsigned_to_nat(0u);
v___x_231_ = l_Lean_Name_reprPrec(v_fnName_221_, v___x_230_);
v___x_232_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_229_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
v___x_233_ = 0;
v___x_234_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_234_, 0, v___x_232_);
lean_ctor_set_uint8(v___x_234_, sizeof(void*)*1, v___x_233_);
v___x_235_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_228_);
lean_ctor_set(v___x_235_, 1, v___x_234_);
v___x_236_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__2));
v___x_237_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_235_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
v___x_238_ = lean_box(1);
v___x_239_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_237_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
v___x_240_ = ((lean_object*)(l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__9));
v___x_241_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_241_, 0, v___x_239_);
lean_ctor_set(v___x_241_, 1, v___x_240_);
v___x_242_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
lean_ctor_set(v___x_242_, 1, v___x_227_);
v___x_243_ = lean_obj_once(&l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__10, &l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__10_once, _init_l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__10);
v___x_244_ = l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0(v_fixedParamPerm_222_);
v___x_245_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_243_);
lean_ctor_set(v___x_245_, 1, v___x_244_);
v___x_246_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_246_, 0, v___x_245_);
lean_ctor_set_uint8(v___x_246_, sizeof(void*)*1, v___x_233_);
v___x_247_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_242_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
v___x_248_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
lean_ctor_set(v___x_248_, 1, v___x_236_);
v___x_249_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
lean_ctor_set(v___x_249_, 1, v___x_238_);
v___x_250_ = ((lean_object*)(l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__12));
v___x_251_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_249_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
v___x_252_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
lean_ctor_set(v___x_252_, 1, v___x_227_);
v___x_253_ = lean_obj_once(&l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__13, &l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__13_once, _init_l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__13);
v___x_254_ = l_Nat_reprFast(v_recArgPos_223_);
v___x_255_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
v___x_256_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_253_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
v___x_257_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_257_, 0, v___x_256_);
lean_ctor_set_uint8(v___x_257_, sizeof(void*)*1, v___x_233_);
v___x_258_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_252_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
v___x_259_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
lean_ctor_set(v___x_259_, 1, v___x_236_);
v___x_260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
lean_ctor_set(v___x_260_, 1, v___x_238_);
v___x_261_ = ((lean_object*)(l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__15));
v___x_262_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_260_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
v___x_263_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
lean_ctor_set(v___x_263_, 1, v___x_227_);
v___x_264_ = lean_obj_once(&l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__16, &l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__16_once, _init_l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__16);
v___x_265_ = l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__1(v_indicesPos_224_);
v___x_266_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_264_);
lean_ctor_set(v___x_266_, 1, v___x_265_);
v___x_267_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_267_, 0, v___x_266_);
lean_ctor_set_uint8(v___x_267_, sizeof(void*)*1, v___x_233_);
v___x_268_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_263_);
lean_ctor_set(v___x_268_, 1, v___x_267_);
v___x_269_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
lean_ctor_set(v___x_269_, 1, v___x_236_);
v___x_270_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
lean_ctor_set(v___x_270_, 1, v___x_238_);
v___x_271_ = ((lean_object*)(l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__18));
v___x_272_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_270_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
v___x_273_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
lean_ctor_set(v___x_273_, 1, v___x_227_);
v___x_274_ = lean_obj_once(&l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__19, &l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__19_once, _init_l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__19);
v___x_275_ = l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg(v_indGroupInst_225_);
v___x_276_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_276_, 0, v___x_274_);
lean_ctor_set(v___x_276_, 1, v___x_275_);
v___x_277_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_277_, 0, v___x_276_);
lean_ctor_set_uint8(v___x_277_, sizeof(void*)*1, v___x_233_);
v___x_278_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_273_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
v___x_279_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
lean_ctor_set(v___x_279_, 1, v___x_236_);
v___x_280_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
lean_ctor_set(v___x_280_, 1, v___x_238_);
v___x_281_ = ((lean_object*)(l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__21));
v___x_282_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_280_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
v___x_283_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
lean_ctor_set(v___x_283_, 1, v___x_227_);
v___x_284_ = l_Nat_reprFast(v_indIdx_226_);
v___x_285_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
v___x_286_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_229_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v___x_287_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_287_, 0, v___x_286_);
lean_ctor_set_uint8(v___x_287_, sizeof(void*)*1, v___x_233_);
v___x_288_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_283_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
v___x_289_ = lean_obj_once(&l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__24, &l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__24_once, _init_l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__24);
v___x_290_ = ((lean_object*)(l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__25));
v___x_291_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
lean_ctor_set(v___x_291_, 1, v___x_288_);
v___x_292_ = ((lean_object*)(l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__26));
v___x_293_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_291_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
v___x_294_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_289_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
v___x_295_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_295_, 0, v___x_294_);
lean_ctor_set_uint8(v___x_295_, sizeof(void*)*1, v___x_233_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_instReprRecArgInfo_repr(lean_object* v_x_296_, lean_object* v_prec_297_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_x_296_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_instReprRecArgInfo_repr___boxed(lean_object* v_x_299_, lean_object* v_prec_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr(v_x_299_, v_prec_300_);
lean_dec(v_prec_300_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_RecArgInfo_indicesAndRecArgPos(lean_object* v_info_304_){
_start:
{
lean_object* v_recArgPos_305_; lean_object* v_indicesPos_306_; lean_object* v___x_307_; 
v_recArgPos_305_ = lean_ctor_get(v_info_304_, 2);
lean_inc(v_recArgPos_305_);
v_indicesPos_306_ = lean_ctor_get(v_info_304_, 3);
lean_inc_ref(v_indicesPos_306_);
lean_dec_ref(v_info_304_);
v___x_307_ = lean_array_push(v_indicesPos_306_, v_recArgPos_305_);
return v___x_307_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__0_spec__0(lean_object* v_a_308_, lean_object* v_as_309_, size_t v_i_310_, size_t v_stop_311_){
_start:
{
uint8_t v___x_312_; 
v___x_312_ = lean_usize_dec_eq(v_i_310_, v_stop_311_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; uint8_t v___x_314_; 
v___x_313_ = lean_array_uget_borrowed(v_as_309_, v_i_310_);
v___x_314_ = lean_nat_dec_eq(v_a_308_, v___x_313_);
if (v___x_314_ == 0)
{
size_t v___x_315_; size_t v___x_316_; 
v___x_315_ = ((size_t)1ULL);
v___x_316_ = lean_usize_add(v_i_310_, v___x_315_);
v_i_310_ = v___x_316_;
goto _start;
}
else
{
return v___x_314_;
}
}
else
{
uint8_t v___x_318_; 
v___x_318_ = 0;
return v___x_318_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__0_spec__0___boxed(lean_object* v_a_319_, lean_object* v_as_320_, lean_object* v_i_321_, lean_object* v_stop_322_){
_start:
{
size_t v_i_boxed_323_; size_t v_stop_boxed_324_; uint8_t v_res_325_; lean_object* v_r_326_; 
v_i_boxed_323_ = lean_unbox_usize(v_i_321_);
lean_dec(v_i_321_);
v_stop_boxed_324_ = lean_unbox_usize(v_stop_322_);
lean_dec(v_stop_322_);
v_res_325_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__0_spec__0(v_a_319_, v_as_320_, v_i_boxed_323_, v_stop_boxed_324_);
lean_dec_ref(v_as_320_);
lean_dec(v_a_319_);
v_r_326_ = lean_box(v_res_325_);
return v_r_326_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__0(lean_object* v_as_327_, lean_object* v_a_328_){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; uint8_t v___x_331_; 
v___x_329_ = lean_unsigned_to_nat(0u);
v___x_330_ = lean_array_get_size(v_as_327_);
v___x_331_ = lean_nat_dec_lt(v___x_329_, v___x_330_);
if (v___x_331_ == 0)
{
return v___x_331_;
}
else
{
if (v___x_331_ == 0)
{
return v___x_331_;
}
else
{
size_t v___x_332_; size_t v___x_333_; uint8_t v___x_334_; 
v___x_332_ = ((size_t)0ULL);
v___x_333_ = lean_usize_of_nat(v___x_330_);
v___x_334_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__0_spec__0(v_a_328_, v_as_327_, v___x_332_, v___x_333_);
return v___x_334_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__0___boxed(lean_object* v_as_335_, lean_object* v_a_336_){
_start:
{
uint8_t v_res_337_; lean_object* v_r_338_; 
v_res_337_ = l_Array_contains___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__0(v_as_335_, v_a_336_);
lean_dec(v_a_336_);
lean_dec_ref(v_as_335_);
v_r_338_ = lean_box(v_res_337_);
return v_r_338_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__2___redArg(lean_object* v_upperBound_339_, lean_object* v_indexMajorPos_340_, lean_object* v___x_341_, lean_object* v_xs_342_, lean_object* v_a_343_, lean_object* v_b_344_){
_start:
{
lean_object* v_a_346_; uint8_t v___x_350_; 
v___x_350_ = lean_nat_dec_lt(v_a_343_, v_upperBound_339_);
if (v___x_350_ == 0)
{
lean_dec(v_a_343_);
return v_b_344_;
}
else
{
uint8_t v___x_351_; 
v___x_351_ = l_Array_contains___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__0(v_indexMajorPos_340_, v_a_343_);
if (v___x_351_ == 0)
{
uint8_t v___x_352_; 
v___x_352_ = l_Lean_Elab_FixedParamPerm_isFixed(v___x_341_, v_a_343_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = lean_array_fget_borrowed(v_xs_342_, v_a_343_);
lean_inc(v___x_353_);
v___x_354_ = lean_array_push(v_b_344_, v___x_353_);
v_a_346_ = v___x_354_;
goto v___jp_345_;
}
else
{
v_a_346_ = v_b_344_;
goto v___jp_345_;
}
}
else
{
v_a_346_ = v_b_344_;
goto v___jp_345_;
}
}
v___jp_345_:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = lean_unsigned_to_nat(1u);
v___x_348_ = lean_nat_add(v_a_343_, v___x_347_);
lean_dec(v_a_343_);
v_a_343_ = v___x_348_;
v_b_344_ = v_a_346_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__2___redArg___boxed(lean_object* v_upperBound_355_, lean_object* v_indexMajorPos_356_, lean_object* v___x_357_, lean_object* v_xs_358_, lean_object* v_a_359_, lean_object* v_b_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__2___redArg(v_upperBound_355_, v_indexMajorPos_356_, v___x_357_, v_xs_358_, v_a_359_, v_b_360_);
lean_dec_ref(v_xs_358_);
lean_dec_ref(v___x_357_);
lean_dec_ref(v_indexMajorPos_356_);
lean_dec(v_upperBound_355_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__1(lean_object* v_xs_362_, lean_object* v_as_363_, size_t v_sz_364_, size_t v_i_365_, lean_object* v_b_366_){
_start:
{
uint8_t v___x_367_; 
v___x_367_ = lean_usize_dec_lt(v_i_365_, v_sz_364_);
if (v___x_367_ == 0)
{
return v_b_366_;
}
else
{
lean_object* v___x_368_; lean_object* v_a_369_; lean_object* v___x_370_; lean_object* v___x_371_; size_t v___x_372_; size_t v___x_373_; 
v___x_368_ = l_Lean_instInhabitedExpr;
v_a_369_ = lean_array_uget_borrowed(v_as_363_, v_i_365_);
v___x_370_ = lean_array_get_borrowed(v___x_368_, v_xs_362_, v_a_369_);
lean_inc(v___x_370_);
v___x_371_ = lean_array_push(v_b_366_, v___x_370_);
v___x_372_ = ((size_t)1ULL);
v___x_373_ = lean_usize_add(v_i_365_, v___x_372_);
v_i_365_ = v___x_373_;
v_b_366_ = v___x_371_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__1___boxed(lean_object* v_xs_375_, lean_object* v_as_376_, lean_object* v_sz_377_, lean_object* v_i_378_, lean_object* v_b_379_){
_start:
{
size_t v_sz_boxed_380_; size_t v_i_boxed_381_; lean_object* v_res_382_; 
v_sz_boxed_380_ = lean_unbox_usize(v_sz_377_);
lean_dec(v_sz_377_);
v_i_boxed_381_ = lean_unbox_usize(v_i_378_);
lean_dec(v_i_378_);
v_res_382_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__1(v_xs_375_, v_as_376_, v_sz_boxed_380_, v_i_boxed_381_, v_b_379_);
lean_dec_ref(v_as_376_);
lean_dec_ref(v_xs_375_);
return v_res_382_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__0(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = lean_unsigned_to_nat(0u);
v___x_384_ = l_Lean_Level_ofNat(v___x_383_);
return v___x_384_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__1(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = lean_obj_once(&l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__0, &l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__0_once, _init_l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__0);
v___x_386_ = l_Lean_mkSort(v___x_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(lean_object* v_info_389_, lean_object* v_xs_390_){
_start:
{
lean_object* v_fixedParamPerm_391_; lean_object* v_recArgPos_392_; lean_object* v_indicesPos_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v_xs_398_; lean_object* v_indexMajorPos_399_; size_t v_sz_400_; lean_object* v___x_401_; lean_object* v_indexMajorArgs_402_; size_t v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v_fixedParamPerm_391_ = lean_ctor_get(v_info_389_, 1);
lean_inc_ref(v_fixedParamPerm_391_);
v_recArgPos_392_ = lean_ctor_get(v_info_389_, 2);
lean_inc(v_recArgPos_392_);
v_indicesPos_393_ = lean_ctor_get(v_info_389_, 3);
lean_inc_ref(v_indicesPos_393_);
lean_dec_ref(v_info_389_);
v___x_394_ = l_Lean_Elab_FixedParamPerm_numFixed(v_fixedParamPerm_391_);
v___x_395_ = lean_unsigned_to_nat(0u);
v___x_396_ = lean_obj_once(&l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__1, &l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__1_once, _init_l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__1);
v___x_397_ = lean_mk_array(v___x_394_, v___x_396_);
lean_inc_ref(v_fixedParamPerm_391_);
v_xs_398_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_fixedParamPerm_391_, v___x_397_, v_xs_390_);
lean_dec_ref(v___x_397_);
v_indexMajorPos_399_ = lean_array_push(v_indicesPos_393_, v_recArgPos_392_);
v_sz_400_ = lean_array_size(v_indexMajorPos_399_);
v___x_401_ = lean_array_get_size(v_xs_398_);
v_indexMajorArgs_402_ = ((lean_object*)(l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__2));
v___x_403_ = ((size_t)0ULL);
v___x_404_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__1(v_xs_398_, v_indexMajorPos_399_, v_sz_400_, v___x_403_, v_indexMajorArgs_402_);
v___x_405_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__2___redArg(v___x_401_, v_indexMajorPos_399_, v_fixedParamPerm_391_, v_xs_398_, v___x_395_, v_indexMajorArgs_402_);
lean_dec_ref(v_xs_398_);
lean_dec_ref(v_fixedParamPerm_391_);
lean_dec_ref(v_indexMajorPos_399_);
v___x_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_404_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__2(lean_object* v_upperBound_407_, lean_object* v_indexMajorPos_408_, lean_object* v___x_409_, lean_object* v_xs_410_, lean_object* v_inst_411_, lean_object* v_R_412_, lean_object* v_a_413_, lean_object* v_b_414_, lean_object* v_c_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__2___redArg(v_upperBound_407_, v_indexMajorPos_408_, v___x_409_, v_xs_410_, v_a_413_, v_b_414_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__2___boxed(lean_object* v_upperBound_417_, lean_object* v_indexMajorPos_418_, lean_object* v___x_419_, lean_object* v_xs_420_, lean_object* v_inst_421_, lean_object* v_R_422_, lean_object* v_a_423_, lean_object* v_b_424_, lean_object* v_c_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__2(v_upperBound_417_, v_indexMajorPos_418_, v___x_419_, v_xs_420_, v_inst_421_, v_R_422_, v_a_423_, v_b_424_, v_c_425_);
lean_dec_ref(v_xs_420_);
lean_dec_ref(v___x_419_);
lean_dec_ref(v_indexMajorPos_418_);
lean_dec(v_upperBound_417_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_RecArgInfo_indName_x21(lean_object* v_info_427_){
_start:
{
lean_object* v_indGroupInst_428_; lean_object* v_toIndGroupInfo_429_; lean_object* v_indIdx_430_; lean_object* v_all_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v_indGroupInst_428_ = lean_ctor_get(v_info_427_, 4);
v_toIndGroupInfo_429_ = lean_ctor_get(v_indGroupInst_428_, 0);
v_indIdx_430_ = lean_ctor_get(v_info_427_, 5);
v_all_431_ = lean_ctor_get(v_toIndGroupInfo_429_, 0);
v___x_432_ = lean_box(0);
v___x_433_ = lean_array_get_borrowed(v___x_432_, v_all_431_, v_indIdx_430_);
lean_inc(v___x_433_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_RecArgInfo_indName_x21___boxed(lean_object* v_info_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Lean_Elab_Structural_RecArgInfo_indName_x21(v_info_434_);
lean_dec_ref(v_info_434_);
return v_res_435_;
}
}
lean_object* runtime_initialize_Lean_Elab_PreDefinition_FixedParams(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_Structural_IndGroupInfo(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_Structural_RecArgInfo(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_PreDefinition_FixedParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_Structural_IndGroupInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Structural_instInhabitedRecArgInfo_default = _init_l_Lean_Elab_Structural_instInhabitedRecArgInfo_default();
lean_mark_persistent(l_Lean_Elab_Structural_instInhabitedRecArgInfo_default);
l_Lean_Elab_Structural_instInhabitedRecArgInfo = _init_l_Lean_Elab_Structural_instInhabitedRecArgInfo();
lean_mark_persistent(l_Lean_Elab_Structural_instInhabitedRecArgInfo);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_PreDefinition_Structural_RecArgInfo(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_PreDefinition_FixedParams(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_Structural_IndGroupInfo(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_Structural_RecArgInfo(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_PreDefinition_FixedParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Structural_IndGroupInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_Structural_RecArgInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_PreDefinition_Structural_RecArgInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_PreDefinition_Structural_RecArgInfo(builtin);
}
#ifdef __cplusplus
}
#endif
