// Lean compiler output
// Module: Lean.Meta.Match.MatchEqsExt
// Imports: public import Lean.Meta.Match.Basic public import Lean.Meta.Match.MatcherInfo import Lean.Meta.Eqns
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_EnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Match_instInhabitedMatcherInfo_default;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
uint8_t l_Lean_Meta_isEqnLikeSuffix(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Match_instInhabitedMatchEqns_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Match_instInhabitedMatchEqns_default___closed__0 = (const lean_object*)&l_Lean_Meta_Match_instInhabitedMatchEqns_default___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Match_instInhabitedMatchEqns_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_instInhabitedMatchEqns_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instInhabitedMatchEqns_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instInhabitedMatchEqns;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__0 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__0_value;
static const lean_string_object l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__1 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__1_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__1_value)}};
static const lean_object* l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__2 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__2_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__3 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__3_value;
static const lean_string_object l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__4 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__4_value;
static lean_once_cell_t l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__5;
static lean_once_cell_t l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__6;
static const lean_ctor_object l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__7 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__7_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__4_value)}};
static const lean_object* l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__8 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__8_value;
static const lean_string_object l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__9 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__9_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__9_value)}};
static const lean_object* l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__10 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__10_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "eqnNames"};
static const lean_object* l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__3_value),((lean_object*)&l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__7;
static const lean_string_object l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "splitterName"};
static const lean_object* l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__10;
static const lean_string_object l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "splitterMatchInfo"};
static const lean_object* l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__11_value)}};
static const lean_object* l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__13;
static const lean_string_object l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__14 = (const lean_object*)&l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__14_value;
static lean_once_cell_t l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__15;
static lean_once_cell_t l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__16;
static const lean_ctor_object l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__17 = (const lean_object*)&l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__17_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__14_value)}};
static const lean_object* l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__18 = (const lean_object*)&l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__18_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprMatchEqns_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprMatchEqns_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprMatchEqns_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Match_instReprMatchEqns___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Match_instReprMatchEqns_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Match_instReprMatchEqns___closed__0 = (const lean_object*)&l_Lean_Meta_Match_instReprMatchEqns___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Match_instReprMatchEqns = (const lean_object*)&l_Lean_Meta_Match_instReprMatchEqns___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatchEqns_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatchEqns_size___boxed(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0(lean_object*);
static lean_once_cell_t l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__1;
static lean_once_cell_t l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__2;
static lean_once_cell_t l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instInhabitedMatchEqnsExtState;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_matchEqnsExt;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_registerMatchEqns_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_registerMatchEqns_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_registerMatchEqns___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Match_registerMatchEqns___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_registerMatchEqns___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Match_registerMatchEqns___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_registerMatchEqns___redArg___closed__1;
static lean_once_cell_t l_Lean_Meta_Match_registerMatchEqns___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_registerMatchEqns___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_registerMatchEqns___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_registerMatchEqns___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_registerMatchEqns(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_registerMatchEqns___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_match_equations_for(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getEquationsFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_congr_match_equations_for(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_genMatchCongrEqns___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Match_isMatchEqnTheorem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Match_isMatchEqnTheorem___closed__0 = (const lean_object*)&l_Lean_Meta_Match_isMatchEqnTheorem___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Match_isMatchEqnTheorem(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_isMatchEqnTheorem___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Match_instInhabitedMatchEqns_default___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_3_ = l_Lean_Meta_Match_instInhabitedMatcherInfo_default;
v___x_4_ = lean_box(0);
v___x_5_ = ((lean_object*)(l_Lean_Meta_Match_instInhabitedMatchEqns_default___closed__0));
v___x_6_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_4_);
lean_ctor_set(v___x_6_, 2, v___x_3_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedMatchEqns_default(void){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_obj_once(&l_Lean_Meta_Match_instInhabitedMatchEqns_default___closed__1, &l_Lean_Meta_Match_instInhabitedMatchEqns_default___closed__1_once, _init_l_Lean_Meta_Match_instInhabitedMatchEqns_default___closed__1);
return v___x_7_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedMatchEqns(void){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Lean_Meta_Match_instInhabitedMatchEqns_default;
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__1(lean_object* v_a_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_nat_to_int(v_a_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0_spec__0_spec__2_spec__3(lean_object* v_x_11_, lean_object* v_x_12_, lean_object* v_x_13_){
_start:
{
if (lean_obj_tag(v_x_13_) == 0)
{
lean_dec(v_x_11_);
return v_x_12_;
}
else
{
lean_object* v_head_14_; lean_object* v_tail_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_26_; 
v_head_14_ = lean_ctor_get(v_x_13_, 0);
v_tail_15_ = lean_ctor_get(v_x_13_, 1);
v_isSharedCheck_26_ = !lean_is_exclusive(v_x_13_);
if (v_isSharedCheck_26_ == 0)
{
v___x_17_ = v_x_13_;
v_isShared_18_ = v_isSharedCheck_26_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_tail_15_);
lean_inc(v_head_14_);
lean_dec(v_x_13_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_26_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_20_; 
lean_inc(v_x_11_);
if (v_isShared_18_ == 0)
{
lean_ctor_set_tag(v___x_17_, 5);
lean_ctor_set(v___x_17_, 1, v_x_11_);
lean_ctor_set(v___x_17_, 0, v_x_12_);
v___x_20_ = v___x_17_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_25_; 
v_reuseFailAlloc_25_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_25_, 0, v_x_12_);
lean_ctor_set(v_reuseFailAlloc_25_, 1, v_x_11_);
v___x_20_ = v_reuseFailAlloc_25_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_21_ = lean_unsigned_to_nat(0u);
v___x_22_ = l_Lean_Name_reprPrec(v_head_14_, v___x_21_);
v___x_23_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_23_, 0, v___x_20_);
lean_ctor_set(v___x_23_, 1, v___x_22_);
v_x_12_ = v___x_23_;
v_x_13_ = v_tail_15_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0_spec__0_spec__2(lean_object* v_x_27_, lean_object* v_x_28_, lean_object* v_x_29_){
_start:
{
if (lean_obj_tag(v_x_29_) == 0)
{
lean_dec(v_x_27_);
return v_x_28_;
}
else
{
lean_object* v_head_30_; lean_object* v_tail_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_42_; 
v_head_30_ = lean_ctor_get(v_x_29_, 0);
v_tail_31_ = lean_ctor_get(v_x_29_, 1);
v_isSharedCheck_42_ = !lean_is_exclusive(v_x_29_);
if (v_isSharedCheck_42_ == 0)
{
v___x_33_ = v_x_29_;
v_isShared_34_ = v_isSharedCheck_42_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_tail_31_);
lean_inc(v_head_30_);
lean_dec(v_x_29_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_42_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_36_; 
lean_inc(v_x_27_);
if (v_isShared_34_ == 0)
{
lean_ctor_set_tag(v___x_33_, 5);
lean_ctor_set(v___x_33_, 1, v_x_27_);
lean_ctor_set(v___x_33_, 0, v_x_28_);
v___x_36_ = v___x_33_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v_x_28_);
lean_ctor_set(v_reuseFailAlloc_41_, 1, v_x_27_);
v___x_36_ = v_reuseFailAlloc_41_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_37_ = lean_unsigned_to_nat(0u);
v___x_38_ = l_Lean_Name_reprPrec(v_head_30_, v___x_37_);
v___x_39_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_39_, 0, v___x_36_);
lean_ctor_set(v___x_39_, 1, v___x_38_);
v___x_40_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0_spec__0_spec__2_spec__3(v_x_27_, v___x_39_, v_tail_31_);
return v___x_40_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0_spec__0___lam__0(lean_object* v___y_43_){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = lean_unsigned_to_nat(0u);
v___x_45_ = l_Lean_Name_reprPrec(v___y_43_, v___x_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0_spec__0(lean_object* v_x_46_, lean_object* v_x_47_){
_start:
{
if (lean_obj_tag(v_x_46_) == 0)
{
lean_object* v___x_48_; 
lean_dec(v_x_47_);
v___x_48_ = lean_box(0);
return v___x_48_;
}
else
{
lean_object* v_tail_49_; 
v_tail_49_ = lean_ctor_get(v_x_46_, 1);
if (lean_obj_tag(v_tail_49_) == 0)
{
lean_object* v_head_50_; lean_object* v___x_51_; 
lean_dec(v_x_47_);
v_head_50_ = lean_ctor_get(v_x_46_, 0);
lean_inc(v_head_50_);
lean_dec_ref_known(v_x_46_, 2);
v___x_51_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0_spec__0___lam__0(v_head_50_);
return v___x_51_;
}
else
{
lean_object* v_head_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
lean_inc(v_tail_49_);
v_head_52_ = lean_ctor_get(v_x_46_, 0);
lean_inc(v_head_52_);
lean_dec_ref_known(v_x_46_, 2);
v___x_53_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0_spec__0___lam__0(v_head_52_);
v___x_54_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0_spec__0_spec__2(v_x_47_, v___x_53_, v_tail_49_);
return v___x_54_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__0));
v___x_64_ = lean_string_length(v___x_63_);
return v___x_64_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__6(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__5, &l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__5);
v___x_66_ = lean_nat_to_int(v___x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0(lean_object* v_xs_74_){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; uint8_t v___x_77_; 
v___x_75_ = lean_array_get_size(v_xs_74_);
v___x_76_ = lean_unsigned_to_nat(0u);
v___x_77_ = lean_nat_dec_eq(v___x_75_, v___x_76_);
if (v___x_77_ == 0)
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_78_ = lean_array_to_list(v_xs_74_);
v___x_79_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__3));
v___x_80_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0_spec__0(v___x_78_, v___x_79_);
v___x_81_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__6, &l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__6);
v___x_82_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__7));
v___x_83_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
lean_ctor_set(v___x_83_, 1, v___x_80_);
v___x_84_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__8));
v___x_85_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_83_);
lean_ctor_set(v___x_85_, 1, v___x_84_);
v___x_86_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_86_, 0, v___x_81_);
lean_ctor_set(v___x_86_, 1, v___x_85_);
v___x_87_ = l_Std_Format_fill(v___x_86_);
return v___x_87_;
}
else
{
lean_object* v___x_88_; 
lean_dec_ref(v_xs_74_);
v___x_88_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__10));
return v___x_88_;
}
}
}
static lean_object* _init_l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_102_ = lean_unsigned_to_nat(12u);
v___x_103_ = lean_nat_to_int(v___x_102_);
return v___x_103_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = lean_unsigned_to_nat(16u);
v___x_108_ = lean_nat_to_int(v___x_107_);
return v___x_108_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = lean_unsigned_to_nat(21u);
v___x_113_ = lean_nat_to_int(v___x_112_);
return v___x_113_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = ((lean_object*)(l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__0));
v___x_116_ = lean_string_length(v___x_115_);
return v___x_116_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = lean_obj_once(&l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__15, &l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__15_once, _init_l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__15);
v___x_118_ = lean_nat_to_int(v___x_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprMatchEqns_repr___redArg(lean_object* v_x_123_){
_start:
{
lean_object* v_eqnNames_124_; lean_object* v_splitterName_125_; lean_object* v_splitterMatchInfo_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v_eqnNames_124_ = lean_ctor_get(v_x_123_, 0);
lean_inc_ref(v_eqnNames_124_);
v_splitterName_125_ = lean_ctor_get(v_x_123_, 1);
lean_inc(v_splitterName_125_);
v_splitterMatchInfo_126_ = lean_ctor_get(v_x_123_, 2);
lean_inc_ref(v_splitterMatchInfo_126_);
lean_dec_ref(v_x_123_);
v___x_127_ = ((lean_object*)(l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__5));
v___x_128_ = ((lean_object*)(l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__6));
v___x_129_ = lean_obj_once(&l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__7, &l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__7_once, _init_l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__7);
v___x_130_ = l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0(v_eqnNames_124_);
v___x_131_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_129_);
lean_ctor_set(v___x_131_, 1, v___x_130_);
v___x_132_ = 0;
v___x_133_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_133_, 0, v___x_131_);
lean_ctor_set_uint8(v___x_133_, sizeof(void*)*1, v___x_132_);
v___x_134_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_128_);
lean_ctor_set(v___x_134_, 1, v___x_133_);
v___x_135_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__2));
v___x_136_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_136_, 0, v___x_134_);
lean_ctor_set(v___x_136_, 1, v___x_135_);
v___x_137_ = lean_box(1);
v___x_138_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_138_, 0, v___x_136_);
lean_ctor_set(v___x_138_, 1, v___x_137_);
v___x_139_ = ((lean_object*)(l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__9));
v___x_140_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_140_, 0, v___x_138_);
lean_ctor_set(v___x_140_, 1, v___x_139_);
v___x_141_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
lean_ctor_set(v___x_141_, 1, v___x_127_);
v___x_142_ = lean_obj_once(&l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__10, &l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__10_once, _init_l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__10);
v___x_143_ = lean_unsigned_to_nat(0u);
v___x_144_ = l_Lean_Name_reprPrec(v_splitterName_125_, v___x_143_);
v___x_145_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_145_, 0, v___x_142_);
lean_ctor_set(v___x_145_, 1, v___x_144_);
v___x_146_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_146_, 0, v___x_145_);
lean_ctor_set_uint8(v___x_146_, sizeof(void*)*1, v___x_132_);
v___x_147_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_141_);
lean_ctor_set(v___x_147_, 1, v___x_146_);
v___x_148_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
lean_ctor_set(v___x_148_, 1, v___x_135_);
v___x_149_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
lean_ctor_set(v___x_149_, 1, v___x_137_);
v___x_150_ = ((lean_object*)(l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__12));
v___x_151_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_149_);
lean_ctor_set(v___x_151_, 1, v___x_150_);
v___x_152_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
lean_ctor_set(v___x_152_, 1, v___x_127_);
v___x_153_ = lean_obj_once(&l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__13, &l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__13_once, _init_l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__13);
v___x_154_ = l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg(v_splitterMatchInfo_126_);
v___x_155_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_153_);
lean_ctor_set(v___x_155_, 1, v___x_154_);
v___x_156_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_156_, 0, v___x_155_);
lean_ctor_set_uint8(v___x_156_, sizeof(void*)*1, v___x_132_);
v___x_157_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_152_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
v___x_158_ = lean_obj_once(&l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__16, &l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__16_once, _init_l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__16);
v___x_159_ = ((lean_object*)(l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__17));
v___x_160_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
lean_ctor_set(v___x_160_, 1, v___x_157_);
v___x_161_ = ((lean_object*)(l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__18));
v___x_162_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_160_);
lean_ctor_set(v___x_162_, 1, v___x_161_);
v___x_163_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_158_);
lean_ctor_set(v___x_163_, 1, v___x_162_);
v___x_164_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set_uint8(v___x_164_, sizeof(void*)*1, v___x_132_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprMatchEqns_repr(lean_object* v_x_165_, lean_object* v_prec_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Lean_Meta_Match_instReprMatchEqns_repr___redArg(v_x_165_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprMatchEqns_repr___boxed(lean_object* v_x_168_, lean_object* v_prec_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Lean_Meta_Match_instReprMatchEqns_repr(v_x_168_, v_prec_169_);
lean_dec(v_prec_169_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatchEqns_size(lean_object* v_e_173_){
_start:
{
lean_object* v_eqnNames_174_; lean_object* v___x_175_; 
v_eqnNames_174_ = lean_ctor_get(v_e_173_, 0);
v___x_175_ = lean_array_get_size(v_eqnNames_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatchEqns_size___boxed(lean_object* v_e_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lean_Meta_Match_MatchEqns_size(v_e_176_);
lean_dec_ref(v_e_176_);
return v_res_177_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___closed__0(void){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_178_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___closed__1(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_179_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___closed__0);
v___x_180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0(lean_object* v_00_u03b2_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___closed__1);
return v___x_182_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__0(void){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_183_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__1(void){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = lean_obj_once(&l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__0, &l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__0_once, _init_l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__0);
v___x_185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
return v___x_185_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__2(void){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0(lean_box(0));
return v___x_186_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__3(void){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_187_ = lean_obj_once(&l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__2, &l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__2_once, _init_l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__2);
v___x_188_ = lean_obj_once(&l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__1, &l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__1_once, _init_l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__1);
v___x_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
lean_ctor_set(v___x_189_, 1, v___x_187_);
return v___x_189_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default(void){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = lean_obj_once(&l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__3, &l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__3_once, _init_l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__3);
return v___x_190_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedMatchEqnsExtState(void){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default;
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2_(lean_object* v___x_192_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_194_, 0, v___x_192_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2____boxed(lean_object* v___x_195_, lean_object* v___y_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2_(v___x_195_);
return v_res_197_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_198_; lean_object* v___f_199_; 
v___x_198_ = lean_obj_once(&l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__3, &l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__3_once, _init_l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__3);
v___f_199_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_199_, 0, v___x_198_);
return v___f_199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___f_201_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2_);
v___x_202_ = lean_box(0);
v___x_203_ = lean_box(1);
v___x_204_ = l_Lean_registerEnvExtension___redArg(v___f_201_, v___x_202_, v___x_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2____boxed(lean_object* v_a_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2_();
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_207_, lean_object* v_x_208_, lean_object* v_x_209_, lean_object* v_x_210_){
_start:
{
lean_object* v_ks_211_; lean_object* v_vs_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_236_; 
v_ks_211_ = lean_ctor_get(v_x_207_, 0);
v_vs_212_ = lean_ctor_get(v_x_207_, 1);
v_isSharedCheck_236_ = !lean_is_exclusive(v_x_207_);
if (v_isSharedCheck_236_ == 0)
{
v___x_214_ = v_x_207_;
v_isShared_215_ = v_isSharedCheck_236_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_vs_212_);
lean_inc(v_ks_211_);
lean_dec(v_x_207_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_236_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_216_; uint8_t v___x_217_; 
v___x_216_ = lean_array_get_size(v_ks_211_);
v___x_217_ = lean_nat_dec_lt(v_x_208_, v___x_216_);
if (v___x_217_ == 0)
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_221_; 
lean_dec(v_x_208_);
v___x_218_ = lean_array_push(v_ks_211_, v_x_209_);
v___x_219_ = lean_array_push(v_vs_212_, v_x_210_);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 1, v___x_219_);
lean_ctor_set(v___x_214_, 0, v___x_218_);
v___x_221_ = v___x_214_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v___x_218_);
lean_ctor_set(v_reuseFailAlloc_222_, 1, v___x_219_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
else
{
lean_object* v_k_x27_223_; uint8_t v___x_224_; 
v_k_x27_223_ = lean_array_fget_borrowed(v_ks_211_, v_x_208_);
v___x_224_ = lean_name_eq(v_x_209_, v_k_x27_223_);
if (v___x_224_ == 0)
{
lean_object* v___x_226_; 
if (v_isShared_215_ == 0)
{
v___x_226_ = v___x_214_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_ks_211_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v_vs_212_);
v___x_226_ = v_reuseFailAlloc_230_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = lean_unsigned_to_nat(1u);
v___x_228_ = lean_nat_add(v_x_208_, v___x_227_);
lean_dec(v_x_208_);
v_x_207_ = v___x_226_;
v_x_208_ = v___x_228_;
goto _start;
}
}
else
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_234_; 
v___x_231_ = lean_array_fset(v_ks_211_, v_x_208_, v_x_209_);
v___x_232_ = lean_array_fset(v_vs_212_, v_x_208_, v_x_210_);
lean_dec(v_x_208_);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 1, v___x_232_);
lean_ctor_set(v___x_214_, 0, v___x_231_);
v___x_234_ = v___x_214_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_231_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v___x_232_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__1___redArg(lean_object* v_n_237_, lean_object* v_k_238_, lean_object* v_v_239_){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = lean_unsigned_to_nat(0u);
v___x_241_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__1_spec__3___redArg(v_n_237_, v___x_240_, v_k_238_, v_v_239_);
return v___x_241_;
}
}
static uint64_t _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_242_; uint64_t v___x_243_; 
v___x_242_ = lean_unsigned_to_nat(1723u);
v___x_243_ = lean_uint64_of_nat(v___x_242_);
return v___x_243_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg(lean_object* v_x_245_, size_t v_x_246_, size_t v_x_247_, lean_object* v_x_248_, lean_object* v_x_249_){
_start:
{
if (lean_obj_tag(v_x_245_) == 0)
{
lean_object* v_es_250_; size_t v___x_251_; size_t v___x_252_; lean_object* v_j_253_; lean_object* v___x_254_; uint8_t v___x_255_; 
v_es_250_ = lean_ctor_get(v_x_245_, 0);
v___x_251_ = ((size_t)31ULL);
v___x_252_ = lean_usize_land(v_x_246_, v___x_251_);
v_j_253_ = lean_usize_to_nat(v___x_252_);
v___x_254_ = lean_array_get_size(v_es_250_);
v___x_255_ = lean_nat_dec_lt(v_j_253_, v___x_254_);
if (v___x_255_ == 0)
{
lean_dec(v_j_253_);
lean_dec(v_x_249_);
lean_dec(v_x_248_);
return v_x_245_;
}
else
{
lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_294_; 
lean_inc_ref(v_es_250_);
v_isSharedCheck_294_ = !lean_is_exclusive(v_x_245_);
if (v_isSharedCheck_294_ == 0)
{
lean_object* v_unused_295_; 
v_unused_295_ = lean_ctor_get(v_x_245_, 0);
lean_dec(v_unused_295_);
v___x_257_ = v_x_245_;
v_isShared_258_ = v_isSharedCheck_294_;
goto v_resetjp_256_;
}
else
{
lean_dec(v_x_245_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_294_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v_v_259_; lean_object* v___x_260_; lean_object* v_xs_x27_261_; lean_object* v___y_263_; 
v_v_259_ = lean_array_fget(v_es_250_, v_j_253_);
v___x_260_ = lean_box(0);
v_xs_x27_261_ = lean_array_fset(v_es_250_, v_j_253_, v___x_260_);
switch(lean_obj_tag(v_v_259_))
{
case 0:
{
lean_object* v_key_268_; lean_object* v_val_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_279_; 
v_key_268_ = lean_ctor_get(v_v_259_, 0);
v_val_269_ = lean_ctor_get(v_v_259_, 1);
v_isSharedCheck_279_ = !lean_is_exclusive(v_v_259_);
if (v_isSharedCheck_279_ == 0)
{
v___x_271_ = v_v_259_;
v_isShared_272_ = v_isSharedCheck_279_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_val_269_);
lean_inc(v_key_268_);
lean_dec(v_v_259_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_279_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
uint8_t v___x_273_; 
v___x_273_ = lean_name_eq(v_x_248_, v_key_268_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; lean_object* v___x_275_; 
lean_del_object(v___x_271_);
v___x_274_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_268_, v_val_269_, v_x_248_, v_x_249_);
v___x_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
v___y_263_ = v___x_275_;
goto v___jp_262_;
}
else
{
lean_object* v___x_277_; 
lean_dec(v_val_269_);
lean_dec(v_key_268_);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 1, v_x_249_);
lean_ctor_set(v___x_271_, 0, v_x_248_);
v___x_277_ = v___x_271_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_x_248_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v_x_249_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
v___y_263_ = v___x_277_;
goto v___jp_262_;
}
}
}
}
case 1:
{
lean_object* v_node_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_292_; 
v_node_280_ = lean_ctor_get(v_v_259_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v_v_259_);
if (v_isSharedCheck_292_ == 0)
{
v___x_282_ = v_v_259_;
v_isShared_283_ = v_isSharedCheck_292_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_node_280_);
lean_dec(v_v_259_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_292_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
size_t v___x_284_; size_t v___x_285_; size_t v___x_286_; size_t v___x_287_; lean_object* v___x_288_; lean_object* v___x_290_; 
v___x_284_ = ((size_t)5ULL);
v___x_285_ = lean_usize_shift_right(v_x_246_, v___x_284_);
v___x_286_ = ((size_t)1ULL);
v___x_287_ = lean_usize_add(v_x_247_, v___x_286_);
v___x_288_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg(v_node_280_, v___x_285_, v___x_287_, v_x_248_, v_x_249_);
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 0, v___x_288_);
v___x_290_ = v___x_282_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v___x_288_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
v___y_263_ = v___x_290_;
goto v___jp_262_;
}
}
}
default: 
{
lean_object* v___x_293_; 
v___x_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_293_, 0, v_x_248_);
lean_ctor_set(v___x_293_, 1, v_x_249_);
v___y_263_ = v___x_293_;
goto v___jp_262_;
}
}
v___jp_262_:
{
lean_object* v___x_264_; lean_object* v___x_266_; 
v___x_264_ = lean_array_fset(v_xs_x27_261_, v_j_253_, v___y_263_);
lean_dec(v_j_253_);
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 0, v___x_264_);
v___x_266_ = v___x_257_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v___x_264_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
}
else
{
lean_object* v_ks_296_; lean_object* v_vs_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_317_; 
v_ks_296_ = lean_ctor_get(v_x_245_, 0);
v_vs_297_ = lean_ctor_get(v_x_245_, 1);
v_isSharedCheck_317_ = !lean_is_exclusive(v_x_245_);
if (v_isSharedCheck_317_ == 0)
{
v___x_299_ = v_x_245_;
v_isShared_300_ = v_isSharedCheck_317_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_vs_297_);
lean_inc(v_ks_296_);
lean_dec(v_x_245_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_317_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_302_; 
if (v_isShared_300_ == 0)
{
v___x_302_ = v___x_299_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_ks_296_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v_vs_297_);
v___x_302_ = v_reuseFailAlloc_316_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
lean_object* v_newNode_303_; uint8_t v___y_305_; size_t v___x_311_; uint8_t v___x_312_; 
v_newNode_303_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__1___redArg(v___x_302_, v_x_248_, v_x_249_);
v___x_311_ = ((size_t)7ULL);
v___x_312_ = lean_usize_dec_le(v___x_311_, v_x_247_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_313_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_303_);
v___x_314_ = lean_unsigned_to_nat(4u);
v___x_315_ = lean_nat_dec_lt(v___x_313_, v___x_314_);
lean_dec(v___x_313_);
v___y_305_ = v___x_315_;
goto v___jp_304_;
}
else
{
v___y_305_ = v___x_312_;
goto v___jp_304_;
}
v___jp_304_:
{
if (v___y_305_ == 0)
{
lean_object* v_ks_306_; lean_object* v_vs_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v_ks_306_ = lean_ctor_get(v_newNode_303_, 0);
lean_inc_ref(v_ks_306_);
v_vs_307_ = lean_ctor_get(v_newNode_303_, 1);
lean_inc_ref(v_vs_307_);
lean_dec_ref(v_newNode_303_);
v___x_308_ = lean_unsigned_to_nat(0u);
v___x_309_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__0);
v___x_310_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg(v_x_247_, v_ks_306_, v_vs_307_, v___x_308_, v___x_309_);
lean_dec_ref(v_vs_307_);
lean_dec_ref(v_ks_306_);
return v___x_310_;
}
else
{
return v_newNode_303_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg(size_t v_depth_318_, lean_object* v_keys_319_, lean_object* v_vals_320_, lean_object* v_i_321_, lean_object* v_entries_322_){
_start:
{
lean_object* v___x_323_; uint8_t v___x_324_; 
v___x_323_ = lean_array_get_size(v_keys_319_);
v___x_324_ = lean_nat_dec_lt(v_i_321_, v___x_323_);
if (v___x_324_ == 0)
{
lean_dec(v_i_321_);
return v_entries_322_;
}
else
{
lean_object* v_k_325_; lean_object* v_v_326_; uint64_t v___y_328_; 
v_k_325_ = lean_array_fget_borrowed(v_keys_319_, v_i_321_);
v_v_326_ = lean_array_fget_borrowed(v_vals_320_, v_i_321_);
if (lean_obj_tag(v_k_325_) == 0)
{
uint64_t v___x_339_; 
v___x_339_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_328_ = v___x_339_;
goto v___jp_327_;
}
else
{
uint64_t v_hash_340_; 
v_hash_340_ = lean_ctor_get_uint64(v_k_325_, sizeof(void*)*2);
v___y_328_ = v_hash_340_;
goto v___jp_327_;
}
v___jp_327_:
{
size_t v_h_329_; size_t v___x_330_; lean_object* v___x_331_; size_t v___x_332_; size_t v___x_333_; size_t v___x_334_; size_t v_h_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v_h_329_ = lean_uint64_to_usize(v___y_328_);
v___x_330_ = ((size_t)5ULL);
v___x_331_ = lean_unsigned_to_nat(1u);
v___x_332_ = ((size_t)1ULL);
v___x_333_ = lean_usize_sub(v_depth_318_, v___x_332_);
v___x_334_ = lean_usize_mul(v___x_330_, v___x_333_);
v_h_335_ = lean_usize_shift_right(v_h_329_, v___x_334_);
v___x_336_ = lean_nat_add(v_i_321_, v___x_331_);
lean_dec(v_i_321_);
lean_inc(v_v_326_);
lean_inc(v_k_325_);
v___x_337_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg(v_entries_322_, v_h_335_, v_depth_318_, v_k_325_, v_v_326_);
v_i_321_ = v___x_336_;
v_entries_322_ = v___x_337_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_341_, lean_object* v_keys_342_, lean_object* v_vals_343_, lean_object* v_i_344_, lean_object* v_entries_345_){
_start:
{
size_t v_depth_boxed_346_; lean_object* v_res_347_; 
v_depth_boxed_346_ = lean_unbox_usize(v_depth_341_);
lean_dec(v_depth_341_);
v_res_347_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg(v_depth_boxed_346_, v_keys_342_, v_vals_343_, v_i_344_, v_entries_345_);
lean_dec_ref(v_vals_343_);
lean_dec_ref(v_keys_342_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___boxed(lean_object* v_x_348_, lean_object* v_x_349_, lean_object* v_x_350_, lean_object* v_x_351_, lean_object* v_x_352_){
_start:
{
size_t v_x_705__boxed_353_; size_t v_x_706__boxed_354_; lean_object* v_res_355_; 
v_x_705__boxed_353_ = lean_unbox_usize(v_x_349_);
lean_dec(v_x_349_);
v_x_706__boxed_354_ = lean_unbox_usize(v_x_350_);
lean_dec(v_x_350_);
v_res_355_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg(v_x_348_, v_x_705__boxed_353_, v_x_706__boxed_354_, v_x_351_, v_x_352_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0___redArg(lean_object* v_x_356_, lean_object* v_x_357_, lean_object* v_x_358_){
_start:
{
uint64_t v___y_360_; 
if (lean_obj_tag(v_x_357_) == 0)
{
uint64_t v___x_364_; 
v___x_364_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_360_ = v___x_364_;
goto v___jp_359_;
}
else
{
uint64_t v_hash_365_; 
v_hash_365_ = lean_ctor_get_uint64(v_x_357_, sizeof(void*)*2);
v___y_360_ = v_hash_365_;
goto v___jp_359_;
}
v___jp_359_:
{
size_t v___x_361_; size_t v___x_362_; lean_object* v___x_363_; 
v___x_361_ = lean_uint64_to_usize(v___y_360_);
v___x_362_ = ((size_t)1ULL);
v___x_363_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg(v_x_356_, v___x_361_, v___x_362_, v_x_357_, v_x_358_);
return v___x_363_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_registerMatchEqns_spec__1(lean_object* v_as_366_, size_t v_i_367_, size_t v_stop_368_, lean_object* v_b_369_){
_start:
{
uint8_t v___x_370_; 
v___x_370_ = lean_usize_dec_eq(v_i_367_, v_stop_368_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; size_t v___x_374_; size_t v___x_375_; 
v___x_371_ = lean_array_uget_borrowed(v_as_366_, v_i_367_);
v___x_372_ = lean_box(0);
lean_inc(v___x_371_);
v___x_373_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0___redArg(v_b_369_, v___x_371_, v___x_372_);
v___x_374_ = ((size_t)1ULL);
v___x_375_ = lean_usize_add(v_i_367_, v___x_374_);
v_i_367_ = v___x_375_;
v_b_369_ = v___x_373_;
goto _start;
}
else
{
return v_b_369_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_registerMatchEqns_spec__1___boxed(lean_object* v_as_377_, lean_object* v_i_378_, lean_object* v_stop_379_, lean_object* v_b_380_){
_start:
{
size_t v_i_boxed_381_; size_t v_stop_boxed_382_; lean_object* v_res_383_; 
v_i_boxed_381_ = lean_unbox_usize(v_i_378_);
lean_dec(v_i_378_);
v_stop_boxed_382_ = lean_unbox_usize(v_stop_379_);
lean_dec(v_stop_379_);
v_res_383_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_registerMatchEqns_spec__1(v_as_377_, v_i_boxed_381_, v_stop_boxed_382_, v_b_380_);
lean_dec_ref(v_as_377_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_registerMatchEqns___redArg___lam__0(lean_object* v_matchEqns_384_, lean_object* v_matchDeclName_385_, lean_object* v_x_386_){
_start:
{
lean_object* v_map_387_; lean_object* v_eqns_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_416_; 
v_map_387_ = lean_ctor_get(v_x_386_, 0);
v_eqns_388_ = lean_ctor_get(v_x_386_, 1);
v_isSharedCheck_416_ = !lean_is_exclusive(v_x_386_);
if (v_isSharedCheck_416_ == 0)
{
v___x_390_ = v_x_386_;
v_isShared_391_ = v_isSharedCheck_416_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_eqns_388_);
lean_inc(v_map_387_);
lean_dec(v_x_386_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_416_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v_eqnNames_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; uint8_t v___x_396_; 
v_eqnNames_392_ = lean_ctor_get(v_matchEqns_384_, 0);
lean_inc_ref(v_eqnNames_392_);
v___x_393_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0___redArg(v_map_387_, v_matchDeclName_385_, v_matchEqns_384_);
v___x_394_ = lean_unsigned_to_nat(0u);
v___x_395_ = lean_array_get_size(v_eqnNames_392_);
v___x_396_ = lean_nat_dec_lt(v___x_394_, v___x_395_);
if (v___x_396_ == 0)
{
lean_object* v___x_398_; 
lean_dec_ref(v_eqnNames_392_);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 0, v___x_393_);
v___x_398_ = v___x_390_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_393_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v_eqns_388_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
else
{
uint8_t v___x_400_; 
v___x_400_ = lean_nat_dec_le(v___x_395_, v___x_395_);
if (v___x_400_ == 0)
{
if (v___x_396_ == 0)
{
lean_object* v___x_402_; 
lean_dec_ref(v_eqnNames_392_);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 0, v___x_393_);
v___x_402_ = v___x_390_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_393_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v_eqns_388_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
else
{
size_t v___x_404_; size_t v___x_405_; lean_object* v___x_406_; lean_object* v___x_408_; 
v___x_404_ = ((size_t)0ULL);
v___x_405_ = lean_usize_of_nat(v___x_395_);
v___x_406_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_registerMatchEqns_spec__1(v_eqnNames_392_, v___x_404_, v___x_405_, v_eqns_388_);
lean_dec_ref(v_eqnNames_392_);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 1, v___x_406_);
lean_ctor_set(v___x_390_, 0, v___x_393_);
v___x_408_ = v___x_390_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_393_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v___x_406_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
else
{
size_t v___x_410_; size_t v___x_411_; lean_object* v___x_412_; lean_object* v___x_414_; 
v___x_410_ = ((size_t)0ULL);
v___x_411_ = lean_usize_of_nat(v___x_395_);
v___x_412_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_registerMatchEqns_spec__1(v_eqnNames_392_, v___x_410_, v___x_411_, v_eqns_388_);
lean_dec_ref(v_eqnNames_392_);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 1, v___x_412_);
lean_ctor_set(v___x_390_, 0, v___x_393_);
v___x_414_ = v___x_390_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v___x_393_);
lean_ctor_set(v_reuseFailAlloc_415_, 1, v___x_412_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_registerMatchEqns___redArg___closed__0(void){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_417_;
}
}
static lean_object* _init_l_Lean_Meta_Match_registerMatchEqns___redArg___closed__1(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = lean_obj_once(&l_Lean_Meta_Match_registerMatchEqns___redArg___closed__0, &l_Lean_Meta_Match_registerMatchEqns___redArg___closed__0_once, _init_l_Lean_Meta_Match_registerMatchEqns___redArg___closed__0);
v___x_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
return v___x_419_;
}
}
static lean_object* _init_l_Lean_Meta_Match_registerMatchEqns___redArg___closed__2(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = lean_obj_once(&l_Lean_Meta_Match_registerMatchEqns___redArg___closed__1, &l_Lean_Meta_Match_registerMatchEqns___redArg___closed__1_once, _init_l_Lean_Meta_Match_registerMatchEqns___redArg___closed__1);
v___x_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
lean_ctor_set(v___x_421_, 1, v___x_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_registerMatchEqns___redArg(lean_object* v_matchDeclName_422_, lean_object* v_matchEqns_423_, lean_object* v_a_424_){
_start:
{
lean_object* v___x_426_; lean_object* v_env_427_; lean_object* v_nextMacroScope_428_; lean_object* v_ngen_429_; lean_object* v_auxDeclNGen_430_; lean_object* v_traceState_431_; lean_object* v_messages_432_; lean_object* v_infoState_433_; lean_object* v_snapshotTasks_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_450_; 
v___x_426_ = lean_st_ref_take(v_a_424_);
v_env_427_ = lean_ctor_get(v___x_426_, 0);
v_nextMacroScope_428_ = lean_ctor_get(v___x_426_, 1);
v_ngen_429_ = lean_ctor_get(v___x_426_, 2);
v_auxDeclNGen_430_ = lean_ctor_get(v___x_426_, 3);
v_traceState_431_ = lean_ctor_get(v___x_426_, 4);
v_messages_432_ = lean_ctor_get(v___x_426_, 6);
v_infoState_433_ = lean_ctor_get(v___x_426_, 7);
v_snapshotTasks_434_ = lean_ctor_get(v___x_426_, 8);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_450_ == 0)
{
lean_object* v_unused_451_; 
v_unused_451_ = lean_ctor_get(v___x_426_, 5);
lean_dec(v_unused_451_);
v___x_436_ = v___x_426_;
v_isShared_437_ = v_isSharedCheck_450_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_snapshotTasks_434_);
lean_inc(v_infoState_433_);
lean_inc(v_messages_432_);
lean_inc(v_traceState_431_);
lean_inc(v_auxDeclNGen_430_);
lean_inc(v_ngen_429_);
lean_inc(v_nextMacroScope_428_);
lean_inc(v_env_427_);
lean_dec(v___x_426_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_450_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_438_; lean_object* v_asyncMode_439_; lean_object* v___f_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_445_; 
v___x_438_ = l_Lean_Meta_Match_matchEqnsExt;
v_asyncMode_439_ = lean_ctor_get(v___x_438_, 2);
v___f_440_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_registerMatchEqns___redArg___lam__0), 3, 2);
lean_closure_set(v___f_440_, 0, v_matchEqns_423_);
lean_closure_set(v___f_440_, 1, v_matchDeclName_422_);
v___x_441_ = lean_box(0);
v___x_442_ = l_Lean_EnvExtension_modifyState___redArg(v___x_438_, v_env_427_, v___f_440_, v_asyncMode_439_, v___x_441_);
v___x_443_ = lean_obj_once(&l_Lean_Meta_Match_registerMatchEqns___redArg___closed__2, &l_Lean_Meta_Match_registerMatchEqns___redArg___closed__2_once, _init_l_Lean_Meta_Match_registerMatchEqns___redArg___closed__2);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 5, v___x_443_);
lean_ctor_set(v___x_436_, 0, v___x_442_);
v___x_445_ = v___x_436_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_442_);
lean_ctor_set(v_reuseFailAlloc_449_, 1, v_nextMacroScope_428_);
lean_ctor_set(v_reuseFailAlloc_449_, 2, v_ngen_429_);
lean_ctor_set(v_reuseFailAlloc_449_, 3, v_auxDeclNGen_430_);
lean_ctor_set(v_reuseFailAlloc_449_, 4, v_traceState_431_);
lean_ctor_set(v_reuseFailAlloc_449_, 5, v___x_443_);
lean_ctor_set(v_reuseFailAlloc_449_, 6, v_messages_432_);
lean_ctor_set(v_reuseFailAlloc_449_, 7, v_infoState_433_);
lean_ctor_set(v_reuseFailAlloc_449_, 8, v_snapshotTasks_434_);
v___x_445_ = v_reuseFailAlloc_449_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_446_ = lean_st_ref_set(v_a_424_, v___x_445_);
v___x_447_ = lean_box(0);
v___x_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
return v___x_448_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_registerMatchEqns___redArg___boxed(lean_object* v_matchDeclName_452_, lean_object* v_matchEqns_453_, lean_object* v_a_454_, lean_object* v_a_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_Meta_Match_registerMatchEqns___redArg(v_matchDeclName_452_, v_matchEqns_453_, v_a_454_);
lean_dec(v_a_454_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_registerMatchEqns(lean_object* v_matchDeclName_457_, lean_object* v_matchEqns_458_, lean_object* v_a_459_, lean_object* v_a_460_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_Lean_Meta_Match_registerMatchEqns___redArg(v_matchDeclName_457_, v_matchEqns_458_, v_a_460_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_registerMatchEqns___boxed(lean_object* v_matchDeclName_463_, lean_object* v_matchEqns_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Lean_Meta_Match_registerMatchEqns(v_matchDeclName_463_, v_matchEqns_464_, v_a_465_, v_a_466_);
lean_dec(v_a_466_);
lean_dec_ref(v_a_465_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0(lean_object* v_00_u03b2_469_, lean_object* v_x_470_, lean_object* v_x_471_, lean_object* v_x_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0___redArg(v_x_470_, v_x_471_, v_x_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0(lean_object* v_00_u03b2_474_, lean_object* v_x_475_, size_t v_x_476_, size_t v_x_477_, lean_object* v_x_478_, lean_object* v_x_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg(v_x_475_, v_x_476_, v_x_477_, v_x_478_, v_x_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___boxed(lean_object* v_00_u03b2_481_, lean_object* v_x_482_, lean_object* v_x_483_, lean_object* v_x_484_, lean_object* v_x_485_, lean_object* v_x_486_){
_start:
{
size_t v_x_1027__boxed_487_; size_t v_x_1028__boxed_488_; lean_object* v_res_489_; 
v_x_1027__boxed_487_ = lean_unbox_usize(v_x_483_);
lean_dec(v_x_483_);
v_x_1028__boxed_488_ = lean_unbox_usize(v_x_484_);
lean_dec(v_x_484_);
v_res_489_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0(v_00_u03b2_481_, v_x_482_, v_x_1027__boxed_487_, v_x_1028__boxed_488_, v_x_485_, v_x_486_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_490_, lean_object* v_n_491_, lean_object* v_k_492_, lean_object* v_v_493_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__1___redArg(v_n_491_, v_k_492_, v_v_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_495_, size_t v_depth_496_, lean_object* v_keys_497_, lean_object* v_vals_498_, lean_object* v_heq_499_, lean_object* v_i_500_, lean_object* v_entries_501_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg(v_depth_496_, v_keys_497_, v_vals_498_, v_i_500_, v_entries_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_503_, lean_object* v_depth_504_, lean_object* v_keys_505_, lean_object* v_vals_506_, lean_object* v_heq_507_, lean_object* v_i_508_, lean_object* v_entries_509_){
_start:
{
size_t v_depth_boxed_510_; lean_object* v_res_511_; 
v_depth_boxed_510_ = lean_unbox_usize(v_depth_504_);
lean_dec(v_depth_504_);
v_res_511_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2(v_00_u03b2_503_, v_depth_boxed_510_, v_keys_505_, v_vals_506_, v_heq_507_, v_i_508_, v_entries_509_);
lean_dec_ref(v_vals_506_);
lean_dec_ref(v_keys_505_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_512_, lean_object* v_x_513_, lean_object* v_x_514_, lean_object* v_x_515_, lean_object* v_x_516_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__1_spec__3___redArg(v_x_513_, v_x_514_, v_x_515_, v_x_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getEquationsFor___boxed(lean_object* v_matchDeclName_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_00___x40___internal___hyg_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = lean_get_match_equations_for(v_matchDeclName_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_genMatchCongrEqns___boxed(lean_object* v_matchDeclName_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_00___x40___internal___hyg_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = lean_get_congr_match_equations_for(v_matchDeclName_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_);
return v_res_543_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_544_, lean_object* v_i_545_, lean_object* v_k_546_){
_start:
{
lean_object* v___x_547_; uint8_t v___x_548_; 
v___x_547_ = lean_array_get_size(v_keys_544_);
v___x_548_ = lean_nat_dec_lt(v_i_545_, v___x_547_);
if (v___x_548_ == 0)
{
lean_dec(v_i_545_);
return v___x_548_;
}
else
{
lean_object* v_k_x27_549_; uint8_t v___x_550_; 
v_k_x27_549_ = lean_array_fget_borrowed(v_keys_544_, v_i_545_);
v___x_550_ = lean_name_eq(v_k_546_, v_k_x27_549_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = lean_unsigned_to_nat(1u);
v___x_552_ = lean_nat_add(v_i_545_, v___x_551_);
lean_dec(v_i_545_);
v_i_545_ = v___x_552_;
goto _start;
}
else
{
lean_dec(v_i_545_);
return v___x_550_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_554_, lean_object* v_i_555_, lean_object* v_k_556_){
_start:
{
uint8_t v_res_557_; lean_object* v_r_558_; 
v_res_557_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1___redArg(v_keys_554_, v_i_555_, v_k_556_);
lean_dec(v_k_556_);
lean_dec_ref(v_keys_554_);
v_r_558_ = lean_box(v_res_557_);
return v_r_558_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0___redArg(lean_object* v_x_559_, size_t v_x_560_, lean_object* v_x_561_){
_start:
{
if (lean_obj_tag(v_x_559_) == 0)
{
lean_object* v_es_562_; lean_object* v___x_563_; size_t v___x_564_; size_t v___x_565_; lean_object* v_j_566_; lean_object* v___x_567_; 
v_es_562_ = lean_ctor_get(v_x_559_, 0);
v___x_563_ = lean_box(2);
v___x_564_ = ((size_t)31ULL);
v___x_565_ = lean_usize_land(v_x_560_, v___x_564_);
v_j_566_ = lean_usize_to_nat(v___x_565_);
v___x_567_ = lean_array_get_borrowed(v___x_563_, v_es_562_, v_j_566_);
lean_dec(v_j_566_);
switch(lean_obj_tag(v___x_567_))
{
case 0:
{
lean_object* v_key_568_; uint8_t v___x_569_; 
v_key_568_ = lean_ctor_get(v___x_567_, 0);
v___x_569_ = lean_name_eq(v_x_561_, v_key_568_);
return v___x_569_;
}
case 1:
{
lean_object* v_node_570_; size_t v___x_571_; size_t v___x_572_; 
v_node_570_ = lean_ctor_get(v___x_567_, 0);
v___x_571_ = ((size_t)5ULL);
v___x_572_ = lean_usize_shift_right(v_x_560_, v___x_571_);
v_x_559_ = v_node_570_;
v_x_560_ = v___x_572_;
goto _start;
}
default: 
{
uint8_t v___x_574_; 
v___x_574_ = 0;
return v___x_574_;
}
}
}
else
{
lean_object* v_ks_575_; lean_object* v___x_576_; uint8_t v___x_577_; 
v_ks_575_ = lean_ctor_get(v_x_559_, 0);
v___x_576_ = lean_unsigned_to_nat(0u);
v___x_577_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1___redArg(v_ks_575_, v___x_576_, v_x_561_);
return v___x_577_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0___redArg___boxed(lean_object* v_x_578_, lean_object* v_x_579_, lean_object* v_x_580_){
_start:
{
size_t v_x_334__boxed_581_; uint8_t v_res_582_; lean_object* v_r_583_; 
v_x_334__boxed_581_ = lean_unbox_usize(v_x_579_);
lean_dec(v_x_579_);
v_res_582_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0___redArg(v_x_578_, v_x_334__boxed_581_, v_x_580_);
lean_dec(v_x_580_);
lean_dec_ref(v_x_578_);
v_r_583_ = lean_box(v_res_582_);
return v_r_583_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0___redArg(lean_object* v_x_584_, lean_object* v_x_585_){
_start:
{
uint64_t v___y_587_; 
if (lean_obj_tag(v_x_585_) == 0)
{
uint64_t v___x_590_; 
v___x_590_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_587_ = v___x_590_;
goto v___jp_586_;
}
else
{
uint64_t v_hash_591_; 
v_hash_591_ = lean_ctor_get_uint64(v_x_585_, sizeof(void*)*2);
v___y_587_ = v_hash_591_;
goto v___jp_586_;
}
v___jp_586_:
{
size_t v___x_588_; uint8_t v___x_589_; 
v___x_588_ = lean_uint64_to_usize(v___y_587_);
v___x_589_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0___redArg(v_x_584_, v___x_588_, v_x_585_);
return v___x_589_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0___redArg___boxed(lean_object* v_x_592_, lean_object* v_x_593_){
_start:
{
uint8_t v_res_594_; lean_object* v_r_595_; 
v_res_594_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0___redArg(v_x_592_, v_x_593_);
lean_dec(v_x_593_);
lean_dec_ref(v_x_592_);
v_r_595_ = lean_box(v_res_594_);
return v_r_595_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Match_isMatchEqnTheorem(lean_object* v_env_598_, lean_object* v_declName_599_){
_start:
{
lean_object* v___x_600_; 
lean_inc(v_declName_599_);
v___x_600_ = lean_erase_macro_scopes(v_declName_599_);
if (lean_obj_tag(v___x_600_) == 1)
{
lean_object* v_str_601_; uint8_t v___x_602_; 
v_str_601_ = lean_ctor_get(v___x_600_, 1);
lean_inc_ref(v_str_601_);
lean_dec_ref_known(v___x_600_, 2);
v___x_602_ = l_Lean_Meta_isEqnLikeSuffix(v_str_601_);
if (v___x_602_ == 0)
{
lean_dec(v_declName_599_);
lean_dec_ref(v_env_598_);
return v___x_602_;
}
else
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v_eqns_607_; uint8_t v___x_608_; 
v___x_603_ = l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default;
v___x_604_ = l_Lean_Meta_Match_matchEqnsExt;
v___x_605_ = ((lean_object*)(l_Lean_Meta_Match_isMatchEqnTheorem___closed__0));
lean_inc(v_declName_599_);
v___x_606_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_603_, v___x_604_, v_env_598_, v___x_605_, v_declName_599_);
v_eqns_607_ = lean_ctor_get(v___x_606_, 1);
lean_inc_ref(v_eqns_607_);
lean_dec(v___x_606_);
v___x_608_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0___redArg(v_eqns_607_, v_declName_599_);
lean_dec(v_declName_599_);
lean_dec_ref(v_eqns_607_);
return v___x_608_;
}
}
else
{
uint8_t v___x_609_; 
lean_dec(v___x_600_);
lean_dec(v_declName_599_);
lean_dec_ref(v_env_598_);
v___x_609_ = 0;
return v___x_609_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_isMatchEqnTheorem___boxed(lean_object* v_env_610_, lean_object* v_declName_611_){
_start:
{
uint8_t v_res_612_; lean_object* v_r_613_; 
v_res_612_ = l_Lean_Meta_Match_isMatchEqnTheorem(v_env_610_, v_declName_611_);
v_r_613_ = lean_box(v_res_612_);
return v_r_613_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0(lean_object* v_00_u03b2_614_, lean_object* v_x_615_, lean_object* v_x_616_){
_start:
{
uint8_t v___x_617_; 
v___x_617_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0___redArg(v_x_615_, v_x_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0___boxed(lean_object* v_00_u03b2_618_, lean_object* v_x_619_, lean_object* v_x_620_){
_start:
{
uint8_t v_res_621_; lean_object* v_r_622_; 
v_res_621_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0(v_00_u03b2_618_, v_x_619_, v_x_620_);
lean_dec(v_x_620_);
lean_dec_ref(v_x_619_);
v_r_622_ = lean_box(v_res_621_);
return v_r_622_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0(lean_object* v_00_u03b2_623_, lean_object* v_x_624_, size_t v_x_625_, lean_object* v_x_626_){
_start:
{
uint8_t v___x_627_; 
v___x_627_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0___redArg(v_x_624_, v_x_625_, v_x_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0___boxed(lean_object* v_00_u03b2_628_, lean_object* v_x_629_, lean_object* v_x_630_, lean_object* v_x_631_){
_start:
{
size_t v_x_427__boxed_632_; uint8_t v_res_633_; lean_object* v_r_634_; 
v_x_427__boxed_632_ = lean_unbox_usize(v_x_630_);
lean_dec(v_x_630_);
v_res_633_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0(v_00_u03b2_628_, v_x_629_, v_x_427__boxed_632_, v_x_631_);
lean_dec(v_x_631_);
lean_dec_ref(v_x_629_);
v_r_634_ = lean_box(v_res_633_);
return v_r_634_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_635_, lean_object* v_keys_636_, lean_object* v_vals_637_, lean_object* v_heq_638_, lean_object* v_i_639_, lean_object* v_k_640_){
_start:
{
uint8_t v___x_641_; 
v___x_641_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1___redArg(v_keys_636_, v_i_639_, v_k_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_642_, lean_object* v_keys_643_, lean_object* v_vals_644_, lean_object* v_heq_645_, lean_object* v_i_646_, lean_object* v_k_647_){
_start:
{
uint8_t v_res_648_; lean_object* v_r_649_; 
v_res_648_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1(v_00_u03b2_642_, v_keys_643_, v_vals_644_, v_heq_645_, v_i_646_, v_k_647_);
lean_dec(v_k_647_);
lean_dec_ref(v_vals_644_);
lean_dec_ref(v_keys_643_);
v_r_649_ = lean_box(v_res_648_);
return v_r_649_;
}
}
lean_object* runtime_initialize_Lean_Meta_Match_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Eqns(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Match_MatchEqsExt(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Match_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_MatcherInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Eqns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Match_instInhabitedMatchEqns_default = _init_l_Lean_Meta_Match_instInhabitedMatchEqns_default();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedMatchEqns_default);
l_Lean_Meta_Match_instInhabitedMatchEqns = _init_l_Lean_Meta_Match_instInhabitedMatchEqns();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedMatchEqns);
l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default = _init_l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default);
l_Lean_Meta_Match_instInhabitedMatchEqnsExtState = _init_l_Lean_Meta_Match_instInhabitedMatchEqnsExtState();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedMatchEqnsExtState);
res = l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Match_matchEqnsExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Match_matchEqnsExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Match_MatchEqsExt(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Match_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin);
lean_object* initialize_Lean_Meta_Eqns(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Match_MatchEqsExt(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Match_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatcherInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Eqns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_MatchEqsExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Match_MatchEqsExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Match_MatchEqsExt(builtin);
}
#ifdef __cplusplus
}
#endif
