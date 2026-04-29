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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__2;
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
lean_dec_ref(v_x_46_);
v___x_51_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0_spec__0___lam__0(v_head_50_);
return v___x_51_;
}
else
{
lean_object* v_head_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
lean_inc(v_tail_49_);
v_head_52_ = lean_ctor_get(v_x_46_, 0);
lean_inc(v_head_52_);
lean_dec_ref(v_x_46_);
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
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_244_; size_t v___x_245_; size_t v___x_246_; 
v___x_244_ = ((size_t)5ULL);
v___x_245_ = ((size_t)1ULL);
v___x_246_ = lean_usize_shift_left(v___x_245_, v___x_244_);
return v___x_246_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_247_; size_t v___x_248_; size_t v___x_249_; 
v___x_247_ = ((size_t)1ULL);
v___x_248_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__0);
v___x_249_ = lean_usize_sub(v___x_248_, v___x_247_);
return v___x_249_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg(lean_object* v_x_251_, size_t v_x_252_, size_t v_x_253_, lean_object* v_x_254_, lean_object* v_x_255_){
_start:
{
if (lean_obj_tag(v_x_251_) == 0)
{
lean_object* v_es_256_; size_t v___x_257_; size_t v___x_258_; size_t v___x_259_; size_t v___x_260_; lean_object* v_j_261_; lean_object* v___x_262_; uint8_t v___x_263_; 
v_es_256_ = lean_ctor_get(v_x_251_, 0);
v___x_257_ = ((size_t)5ULL);
v___x_258_ = ((size_t)1ULL);
v___x_259_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__1);
v___x_260_ = lean_usize_land(v_x_252_, v___x_259_);
v_j_261_ = lean_usize_to_nat(v___x_260_);
v___x_262_ = lean_array_get_size(v_es_256_);
v___x_263_ = lean_nat_dec_lt(v_j_261_, v___x_262_);
if (v___x_263_ == 0)
{
lean_dec(v_j_261_);
lean_dec(v_x_255_);
lean_dec(v_x_254_);
return v_x_251_;
}
else
{
lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_300_; 
lean_inc_ref(v_es_256_);
v_isSharedCheck_300_ = !lean_is_exclusive(v_x_251_);
if (v_isSharedCheck_300_ == 0)
{
lean_object* v_unused_301_; 
v_unused_301_ = lean_ctor_get(v_x_251_, 0);
lean_dec(v_unused_301_);
v___x_265_ = v_x_251_;
v_isShared_266_ = v_isSharedCheck_300_;
goto v_resetjp_264_;
}
else
{
lean_dec(v_x_251_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_300_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v_v_267_; lean_object* v___x_268_; lean_object* v_xs_x27_269_; lean_object* v___y_271_; 
v_v_267_ = lean_array_fget(v_es_256_, v_j_261_);
v___x_268_ = lean_box(0);
v_xs_x27_269_ = lean_array_fset(v_es_256_, v_j_261_, v___x_268_);
switch(lean_obj_tag(v_v_267_))
{
case 0:
{
lean_object* v_key_276_; lean_object* v_val_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_287_; 
v_key_276_ = lean_ctor_get(v_v_267_, 0);
v_val_277_ = lean_ctor_get(v_v_267_, 1);
v_isSharedCheck_287_ = !lean_is_exclusive(v_v_267_);
if (v_isSharedCheck_287_ == 0)
{
v___x_279_ = v_v_267_;
v_isShared_280_ = v_isSharedCheck_287_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_val_277_);
lean_inc(v_key_276_);
lean_dec(v_v_267_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_287_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
uint8_t v___x_281_; 
v___x_281_ = lean_name_eq(v_x_254_, v_key_276_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; lean_object* v___x_283_; 
lean_del_object(v___x_279_);
v___x_282_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_276_, v_val_277_, v_x_254_, v_x_255_);
v___x_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
v___y_271_ = v___x_283_;
goto v___jp_270_;
}
else
{
lean_object* v___x_285_; 
lean_dec(v_val_277_);
lean_dec(v_key_276_);
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 1, v_x_255_);
lean_ctor_set(v___x_279_, 0, v_x_254_);
v___x_285_ = v___x_279_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_x_254_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v_x_255_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
v___y_271_ = v___x_285_;
goto v___jp_270_;
}
}
}
}
case 1:
{
lean_object* v_node_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_298_; 
v_node_288_ = lean_ctor_get(v_v_267_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v_v_267_);
if (v_isSharedCheck_298_ == 0)
{
v___x_290_ = v_v_267_;
v_isShared_291_ = v_isSharedCheck_298_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_node_288_);
lean_dec(v_v_267_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_298_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
size_t v___x_292_; size_t v___x_293_; lean_object* v___x_294_; lean_object* v___x_296_; 
v___x_292_ = lean_usize_shift_right(v_x_252_, v___x_257_);
v___x_293_ = lean_usize_add(v_x_253_, v___x_258_);
v___x_294_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg(v_node_288_, v___x_292_, v___x_293_, v_x_254_, v_x_255_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 0, v___x_294_);
v___x_296_ = v___x_290_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_294_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
v___y_271_ = v___x_296_;
goto v___jp_270_;
}
}
}
default: 
{
lean_object* v___x_299_; 
v___x_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_299_, 0, v_x_254_);
lean_ctor_set(v___x_299_, 1, v_x_255_);
v___y_271_ = v___x_299_;
goto v___jp_270_;
}
}
v___jp_270_:
{
lean_object* v___x_272_; lean_object* v___x_274_; 
v___x_272_ = lean_array_fset(v_xs_x27_269_, v_j_261_, v___y_271_);
lean_dec(v_j_261_);
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 0, v___x_272_);
v___x_274_ = v___x_265_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v___x_272_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
}
else
{
lean_object* v_ks_302_; lean_object* v_vs_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_323_; 
v_ks_302_ = lean_ctor_get(v_x_251_, 0);
v_vs_303_ = lean_ctor_get(v_x_251_, 1);
v_isSharedCheck_323_ = !lean_is_exclusive(v_x_251_);
if (v_isSharedCheck_323_ == 0)
{
v___x_305_ = v_x_251_;
v_isShared_306_ = v_isSharedCheck_323_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_vs_303_);
lean_inc(v_ks_302_);
lean_dec(v_x_251_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_323_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_308_; 
if (v_isShared_306_ == 0)
{
v___x_308_ = v___x_305_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_ks_302_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v_vs_303_);
v___x_308_ = v_reuseFailAlloc_322_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
lean_object* v_newNode_309_; uint8_t v___y_311_; size_t v___x_317_; uint8_t v___x_318_; 
v_newNode_309_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__1___redArg(v___x_308_, v_x_254_, v_x_255_);
v___x_317_ = ((size_t)7ULL);
v___x_318_ = lean_usize_dec_le(v___x_317_, v_x_253_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; lean_object* v___x_320_; uint8_t v___x_321_; 
v___x_319_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_309_);
v___x_320_ = lean_unsigned_to_nat(4u);
v___x_321_ = lean_nat_dec_lt(v___x_319_, v___x_320_);
lean_dec(v___x_319_);
v___y_311_ = v___x_321_;
goto v___jp_310_;
}
else
{
v___y_311_ = v___x_318_;
goto v___jp_310_;
}
v___jp_310_:
{
if (v___y_311_ == 0)
{
lean_object* v_ks_312_; lean_object* v_vs_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v_ks_312_ = lean_ctor_get(v_newNode_309_, 0);
lean_inc_ref(v_ks_312_);
v_vs_313_ = lean_ctor_get(v_newNode_309_, 1);
lean_inc_ref(v_vs_313_);
lean_dec_ref(v_newNode_309_);
v___x_314_ = lean_unsigned_to_nat(0u);
v___x_315_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__2);
v___x_316_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg(v_x_253_, v_ks_312_, v_vs_313_, v___x_314_, v___x_315_);
lean_dec_ref(v_vs_313_);
lean_dec_ref(v_ks_312_);
return v___x_316_;
}
else
{
return v_newNode_309_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg(size_t v_depth_324_, lean_object* v_keys_325_, lean_object* v_vals_326_, lean_object* v_i_327_, lean_object* v_entries_328_){
_start:
{
lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_329_ = lean_array_get_size(v_keys_325_);
v___x_330_ = lean_nat_dec_lt(v_i_327_, v___x_329_);
if (v___x_330_ == 0)
{
lean_dec(v_i_327_);
return v_entries_328_;
}
else
{
lean_object* v_k_331_; lean_object* v_v_332_; uint64_t v___y_334_; 
v_k_331_ = lean_array_fget_borrowed(v_keys_325_, v_i_327_);
v_v_332_ = lean_array_fget_borrowed(v_vals_326_, v_i_327_);
if (lean_obj_tag(v_k_331_) == 0)
{
uint64_t v___x_345_; 
v___x_345_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_334_ = v___x_345_;
goto v___jp_333_;
}
else
{
uint64_t v_hash_346_; 
v_hash_346_ = lean_ctor_get_uint64(v_k_331_, sizeof(void*)*2);
v___y_334_ = v_hash_346_;
goto v___jp_333_;
}
v___jp_333_:
{
size_t v_h_335_; size_t v___x_336_; lean_object* v___x_337_; size_t v___x_338_; size_t v___x_339_; size_t v___x_340_; size_t v_h_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v_h_335_ = lean_uint64_to_usize(v___y_334_);
v___x_336_ = ((size_t)5ULL);
v___x_337_ = lean_unsigned_to_nat(1u);
v___x_338_ = ((size_t)1ULL);
v___x_339_ = lean_usize_sub(v_depth_324_, v___x_338_);
v___x_340_ = lean_usize_mul(v___x_336_, v___x_339_);
v_h_341_ = lean_usize_shift_right(v_h_335_, v___x_340_);
v___x_342_ = lean_nat_add(v_i_327_, v___x_337_);
lean_dec(v_i_327_);
lean_inc(v_v_332_);
lean_inc(v_k_331_);
v___x_343_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg(v_entries_328_, v_h_341_, v_depth_324_, v_k_331_, v_v_332_);
v_i_327_ = v___x_342_;
v_entries_328_ = v___x_343_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_347_, lean_object* v_keys_348_, lean_object* v_vals_349_, lean_object* v_i_350_, lean_object* v_entries_351_){
_start:
{
size_t v_depth_boxed_352_; lean_object* v_res_353_; 
v_depth_boxed_352_ = lean_unbox_usize(v_depth_347_);
lean_dec(v_depth_347_);
v_res_353_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg(v_depth_boxed_352_, v_keys_348_, v_vals_349_, v_i_350_, v_entries_351_);
lean_dec_ref(v_vals_349_);
lean_dec_ref(v_keys_348_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___boxed(lean_object* v_x_354_, lean_object* v_x_355_, lean_object* v_x_356_, lean_object* v_x_357_, lean_object* v_x_358_){
_start:
{
size_t v_x_719__boxed_359_; size_t v_x_720__boxed_360_; lean_object* v_res_361_; 
v_x_719__boxed_359_ = lean_unbox_usize(v_x_355_);
lean_dec(v_x_355_);
v_x_720__boxed_360_ = lean_unbox_usize(v_x_356_);
lean_dec(v_x_356_);
v_res_361_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg(v_x_354_, v_x_719__boxed_359_, v_x_720__boxed_360_, v_x_357_, v_x_358_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0___redArg(lean_object* v_x_362_, lean_object* v_x_363_, lean_object* v_x_364_){
_start:
{
uint64_t v___y_366_; 
if (lean_obj_tag(v_x_363_) == 0)
{
uint64_t v___x_370_; 
v___x_370_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_366_ = v___x_370_;
goto v___jp_365_;
}
else
{
uint64_t v_hash_371_; 
v_hash_371_ = lean_ctor_get_uint64(v_x_363_, sizeof(void*)*2);
v___y_366_ = v_hash_371_;
goto v___jp_365_;
}
v___jp_365_:
{
size_t v___x_367_; size_t v___x_368_; lean_object* v___x_369_; 
v___x_367_ = lean_uint64_to_usize(v___y_366_);
v___x_368_ = ((size_t)1ULL);
v___x_369_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg(v_x_362_, v___x_367_, v___x_368_, v_x_363_, v_x_364_);
return v___x_369_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_registerMatchEqns_spec__1(lean_object* v_as_372_, size_t v_i_373_, size_t v_stop_374_, lean_object* v_b_375_){
_start:
{
uint8_t v___x_376_; 
v___x_376_ = lean_usize_dec_eq(v_i_373_, v_stop_374_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; size_t v___x_380_; size_t v___x_381_; 
v___x_377_ = lean_array_uget_borrowed(v_as_372_, v_i_373_);
v___x_378_ = lean_box(0);
lean_inc(v___x_377_);
v___x_379_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0___redArg(v_b_375_, v___x_377_, v___x_378_);
v___x_380_ = ((size_t)1ULL);
v___x_381_ = lean_usize_add(v_i_373_, v___x_380_);
v_i_373_ = v___x_381_;
v_b_375_ = v___x_379_;
goto _start;
}
else
{
return v_b_375_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_registerMatchEqns_spec__1___boxed(lean_object* v_as_383_, lean_object* v_i_384_, lean_object* v_stop_385_, lean_object* v_b_386_){
_start:
{
size_t v_i_boxed_387_; size_t v_stop_boxed_388_; lean_object* v_res_389_; 
v_i_boxed_387_ = lean_unbox_usize(v_i_384_);
lean_dec(v_i_384_);
v_stop_boxed_388_ = lean_unbox_usize(v_stop_385_);
lean_dec(v_stop_385_);
v_res_389_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_registerMatchEqns_spec__1(v_as_383_, v_i_boxed_387_, v_stop_boxed_388_, v_b_386_);
lean_dec_ref(v_as_383_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_registerMatchEqns___redArg___lam__0(lean_object* v_matchEqns_390_, lean_object* v_matchDeclName_391_, lean_object* v_x_392_){
_start:
{
lean_object* v_map_393_; lean_object* v_eqns_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_422_; 
v_map_393_ = lean_ctor_get(v_x_392_, 0);
v_eqns_394_ = lean_ctor_get(v_x_392_, 1);
v_isSharedCheck_422_ = !lean_is_exclusive(v_x_392_);
if (v_isSharedCheck_422_ == 0)
{
v___x_396_ = v_x_392_;
v_isShared_397_ = v_isSharedCheck_422_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_eqns_394_);
lean_inc(v_map_393_);
lean_dec(v_x_392_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_422_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v_eqnNames_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; uint8_t v___x_402_; 
v_eqnNames_398_ = lean_ctor_get(v_matchEqns_390_, 0);
lean_inc_ref(v_eqnNames_398_);
v___x_399_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0___redArg(v_map_393_, v_matchDeclName_391_, v_matchEqns_390_);
v___x_400_ = lean_unsigned_to_nat(0u);
v___x_401_ = lean_array_get_size(v_eqnNames_398_);
v___x_402_ = lean_nat_dec_lt(v___x_400_, v___x_401_);
if (v___x_402_ == 0)
{
lean_object* v___x_404_; 
lean_dec_ref(v_eqnNames_398_);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 0, v___x_399_);
v___x_404_ = v___x_396_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_399_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_eqns_394_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
else
{
uint8_t v___x_406_; 
v___x_406_ = lean_nat_dec_le(v___x_401_, v___x_401_);
if (v___x_406_ == 0)
{
if (v___x_402_ == 0)
{
lean_object* v___x_408_; 
lean_dec_ref(v_eqnNames_398_);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 0, v___x_399_);
v___x_408_ = v___x_396_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_399_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v_eqns_394_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
else
{
size_t v___x_410_; size_t v___x_411_; lean_object* v___x_412_; lean_object* v___x_414_; 
v___x_410_ = ((size_t)0ULL);
v___x_411_ = lean_usize_of_nat(v___x_401_);
v___x_412_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_registerMatchEqns_spec__1(v_eqnNames_398_, v___x_410_, v___x_411_, v_eqns_394_);
lean_dec_ref(v_eqnNames_398_);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 1, v___x_412_);
lean_ctor_set(v___x_396_, 0, v___x_399_);
v___x_414_ = v___x_396_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v___x_399_);
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
else
{
size_t v___x_416_; size_t v___x_417_; lean_object* v___x_418_; lean_object* v___x_420_; 
v___x_416_ = ((size_t)0ULL);
v___x_417_ = lean_usize_of_nat(v___x_401_);
v___x_418_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_registerMatchEqns_spec__1(v_eqnNames_398_, v___x_416_, v___x_417_, v_eqns_394_);
lean_dec_ref(v_eqnNames_398_);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 1, v___x_418_);
lean_ctor_set(v___x_396_, 0, v___x_399_);
v___x_420_ = v___x_396_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_399_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v___x_418_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_registerMatchEqns___redArg___closed__0(void){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_423_;
}
}
static lean_object* _init_l_Lean_Meta_Match_registerMatchEqns___redArg___closed__1(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = lean_obj_once(&l_Lean_Meta_Match_registerMatchEqns___redArg___closed__0, &l_Lean_Meta_Match_registerMatchEqns___redArg___closed__0_once, _init_l_Lean_Meta_Match_registerMatchEqns___redArg___closed__0);
v___x_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
return v___x_425_;
}
}
static lean_object* _init_l_Lean_Meta_Match_registerMatchEqns___redArg___closed__2(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = lean_obj_once(&l_Lean_Meta_Match_registerMatchEqns___redArg___closed__1, &l_Lean_Meta_Match_registerMatchEqns___redArg___closed__1_once, _init_l_Lean_Meta_Match_registerMatchEqns___redArg___closed__1);
v___x_427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
lean_ctor_set(v___x_427_, 1, v___x_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_registerMatchEqns___redArg(lean_object* v_matchDeclName_428_, lean_object* v_matchEqns_429_, lean_object* v_a_430_){
_start:
{
lean_object* v___x_432_; lean_object* v_env_433_; lean_object* v_nextMacroScope_434_; lean_object* v_ngen_435_; lean_object* v_auxDeclNGen_436_; lean_object* v_traceState_437_; lean_object* v_messages_438_; lean_object* v_infoState_439_; lean_object* v_snapshotTasks_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_456_; 
v___x_432_ = lean_st_ref_take(v_a_430_);
v_env_433_ = lean_ctor_get(v___x_432_, 0);
v_nextMacroScope_434_ = lean_ctor_get(v___x_432_, 1);
v_ngen_435_ = lean_ctor_get(v___x_432_, 2);
v_auxDeclNGen_436_ = lean_ctor_get(v___x_432_, 3);
v_traceState_437_ = lean_ctor_get(v___x_432_, 4);
v_messages_438_ = lean_ctor_get(v___x_432_, 6);
v_infoState_439_ = lean_ctor_get(v___x_432_, 7);
v_snapshotTasks_440_ = lean_ctor_get(v___x_432_, 8);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_456_ == 0)
{
lean_object* v_unused_457_; 
v_unused_457_ = lean_ctor_get(v___x_432_, 5);
lean_dec(v_unused_457_);
v___x_442_ = v___x_432_;
v_isShared_443_ = v_isSharedCheck_456_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_snapshotTasks_440_);
lean_inc(v_infoState_439_);
lean_inc(v_messages_438_);
lean_inc(v_traceState_437_);
lean_inc(v_auxDeclNGen_436_);
lean_inc(v_ngen_435_);
lean_inc(v_nextMacroScope_434_);
lean_inc(v_env_433_);
lean_dec(v___x_432_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_456_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_444_; lean_object* v_asyncMode_445_; lean_object* v___f_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_451_; 
v___x_444_ = l_Lean_Meta_Match_matchEqnsExt;
v_asyncMode_445_ = lean_ctor_get(v___x_444_, 2);
v___f_446_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_registerMatchEqns___redArg___lam__0), 3, 2);
lean_closure_set(v___f_446_, 0, v_matchEqns_429_);
lean_closure_set(v___f_446_, 1, v_matchDeclName_428_);
v___x_447_ = lean_box(0);
v___x_448_ = l_Lean_EnvExtension_modifyState___redArg(v___x_444_, v_env_433_, v___f_446_, v_asyncMode_445_, v___x_447_);
v___x_449_ = lean_obj_once(&l_Lean_Meta_Match_registerMatchEqns___redArg___closed__2, &l_Lean_Meta_Match_registerMatchEqns___redArg___closed__2_once, _init_l_Lean_Meta_Match_registerMatchEqns___redArg___closed__2);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 5, v___x_449_);
lean_ctor_set(v___x_442_, 0, v___x_448_);
v___x_451_ = v___x_442_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_448_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_nextMacroScope_434_);
lean_ctor_set(v_reuseFailAlloc_455_, 2, v_ngen_435_);
lean_ctor_set(v_reuseFailAlloc_455_, 3, v_auxDeclNGen_436_);
lean_ctor_set(v_reuseFailAlloc_455_, 4, v_traceState_437_);
lean_ctor_set(v_reuseFailAlloc_455_, 5, v___x_449_);
lean_ctor_set(v_reuseFailAlloc_455_, 6, v_messages_438_);
lean_ctor_set(v_reuseFailAlloc_455_, 7, v_infoState_439_);
lean_ctor_set(v_reuseFailAlloc_455_, 8, v_snapshotTasks_440_);
v___x_451_ = v_reuseFailAlloc_455_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_452_ = lean_st_ref_set(v_a_430_, v___x_451_);
v___x_453_ = lean_box(0);
v___x_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_454_, 0, v___x_453_);
return v___x_454_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_registerMatchEqns___redArg___boxed(lean_object* v_matchDeclName_458_, lean_object* v_matchEqns_459_, lean_object* v_a_460_, lean_object* v_a_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lean_Meta_Match_registerMatchEqns___redArg(v_matchDeclName_458_, v_matchEqns_459_, v_a_460_);
lean_dec(v_a_460_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_registerMatchEqns(lean_object* v_matchDeclName_463_, lean_object* v_matchEqns_464_, lean_object* v_a_465_, lean_object* v_a_466_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_Meta_Match_registerMatchEqns___redArg(v_matchDeclName_463_, v_matchEqns_464_, v_a_466_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_registerMatchEqns___boxed(lean_object* v_matchDeclName_469_, lean_object* v_matchEqns_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Lean_Meta_Match_registerMatchEqns(v_matchDeclName_469_, v_matchEqns_470_, v_a_471_, v_a_472_);
lean_dec(v_a_472_);
lean_dec_ref(v_a_471_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0(lean_object* v_00_u03b2_475_, lean_object* v_x_476_, lean_object* v_x_477_, lean_object* v_x_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0___redArg(v_x_476_, v_x_477_, v_x_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0(lean_object* v_00_u03b2_480_, lean_object* v_x_481_, size_t v_x_482_, size_t v_x_483_, lean_object* v_x_484_, lean_object* v_x_485_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg(v_x_481_, v_x_482_, v_x_483_, v_x_484_, v_x_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___boxed(lean_object* v_00_u03b2_487_, lean_object* v_x_488_, lean_object* v_x_489_, lean_object* v_x_490_, lean_object* v_x_491_, lean_object* v_x_492_){
_start:
{
size_t v_x_1047__boxed_493_; size_t v_x_1048__boxed_494_; lean_object* v_res_495_; 
v_x_1047__boxed_493_ = lean_unbox_usize(v_x_489_);
lean_dec(v_x_489_);
v_x_1048__boxed_494_ = lean_unbox_usize(v_x_490_);
lean_dec(v_x_490_);
v_res_495_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0(v_00_u03b2_487_, v_x_488_, v_x_1047__boxed_493_, v_x_1048__boxed_494_, v_x_491_, v_x_492_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_496_, lean_object* v_n_497_, lean_object* v_k_498_, lean_object* v_v_499_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__1___redArg(v_n_497_, v_k_498_, v_v_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_501_, size_t v_depth_502_, lean_object* v_keys_503_, lean_object* v_vals_504_, lean_object* v_heq_505_, lean_object* v_i_506_, lean_object* v_entries_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg(v_depth_502_, v_keys_503_, v_vals_504_, v_i_506_, v_entries_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_509_, lean_object* v_depth_510_, lean_object* v_keys_511_, lean_object* v_vals_512_, lean_object* v_heq_513_, lean_object* v_i_514_, lean_object* v_entries_515_){
_start:
{
size_t v_depth_boxed_516_; lean_object* v_res_517_; 
v_depth_boxed_516_ = lean_unbox_usize(v_depth_510_);
lean_dec(v_depth_510_);
v_res_517_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2(v_00_u03b2_509_, v_depth_boxed_516_, v_keys_511_, v_vals_512_, v_heq_513_, v_i_514_, v_entries_515_);
lean_dec_ref(v_vals_512_);
lean_dec_ref(v_keys_511_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_518_, lean_object* v_x_519_, lean_object* v_x_520_, lean_object* v_x_521_, lean_object* v_x_522_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__1_spec__3___redArg(v_x_519_, v_x_520_, v_x_521_, v_x_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getEquationsFor___boxed(lean_object* v_matchDeclName_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_00___x40___internal___hyg_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = lean_get_match_equations_for(v_matchDeclName_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_genMatchCongrEqns___boxed(lean_object* v_matchDeclName_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_00___x40___internal___hyg_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = lean_get_congr_match_equations_for(v_matchDeclName_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_);
return v_res_549_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_550_, lean_object* v_i_551_, lean_object* v_k_552_){
_start:
{
lean_object* v___x_553_; uint8_t v___x_554_; 
v___x_553_ = lean_array_get_size(v_keys_550_);
v___x_554_ = lean_nat_dec_lt(v_i_551_, v___x_553_);
if (v___x_554_ == 0)
{
lean_dec(v_i_551_);
return v___x_554_;
}
else
{
lean_object* v_k_x27_555_; uint8_t v___x_556_; 
v_k_x27_555_ = lean_array_fget_borrowed(v_keys_550_, v_i_551_);
v___x_556_ = lean_name_eq(v_k_552_, v_k_x27_555_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = lean_unsigned_to_nat(1u);
v___x_558_ = lean_nat_add(v_i_551_, v___x_557_);
lean_dec(v_i_551_);
v_i_551_ = v___x_558_;
goto _start;
}
else
{
lean_dec(v_i_551_);
return v___x_556_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_560_, lean_object* v_i_561_, lean_object* v_k_562_){
_start:
{
uint8_t v_res_563_; lean_object* v_r_564_; 
v_res_563_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1___redArg(v_keys_560_, v_i_561_, v_k_562_);
lean_dec(v_k_562_);
lean_dec_ref(v_keys_560_);
v_r_564_ = lean_box(v_res_563_);
return v_r_564_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0___redArg(lean_object* v_x_565_, size_t v_x_566_, lean_object* v_x_567_){
_start:
{
if (lean_obj_tag(v_x_565_) == 0)
{
lean_object* v_es_568_; lean_object* v___x_569_; size_t v___x_570_; size_t v___x_571_; size_t v___x_572_; lean_object* v_j_573_; lean_object* v___x_574_; 
v_es_568_ = lean_ctor_get(v_x_565_, 0);
v___x_569_ = lean_box(2);
v___x_570_ = ((size_t)5ULL);
v___x_571_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__1);
v___x_572_ = lean_usize_land(v_x_566_, v___x_571_);
v_j_573_ = lean_usize_to_nat(v___x_572_);
v___x_574_ = lean_array_get_borrowed(v___x_569_, v_es_568_, v_j_573_);
lean_dec(v_j_573_);
switch(lean_obj_tag(v___x_574_))
{
case 0:
{
lean_object* v_key_575_; uint8_t v___x_576_; 
v_key_575_ = lean_ctor_get(v___x_574_, 0);
v___x_576_ = lean_name_eq(v_x_567_, v_key_575_);
return v___x_576_;
}
case 1:
{
lean_object* v_node_577_; size_t v___x_578_; 
v_node_577_ = lean_ctor_get(v___x_574_, 0);
v___x_578_ = lean_usize_shift_right(v_x_566_, v___x_570_);
v_x_565_ = v_node_577_;
v_x_566_ = v___x_578_;
goto _start;
}
default: 
{
uint8_t v___x_580_; 
v___x_580_ = 0;
return v___x_580_;
}
}
}
else
{
lean_object* v_ks_581_; lean_object* v___x_582_; uint8_t v___x_583_; 
v_ks_581_ = lean_ctor_get(v_x_565_, 0);
v___x_582_ = lean_unsigned_to_nat(0u);
v___x_583_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1___redArg(v_ks_581_, v___x_582_, v_x_567_);
return v___x_583_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0___redArg___boxed(lean_object* v_x_584_, lean_object* v_x_585_, lean_object* v_x_586_){
_start:
{
size_t v_x_344__boxed_587_; uint8_t v_res_588_; lean_object* v_r_589_; 
v_x_344__boxed_587_ = lean_unbox_usize(v_x_585_);
lean_dec(v_x_585_);
v_res_588_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0___redArg(v_x_584_, v_x_344__boxed_587_, v_x_586_);
lean_dec(v_x_586_);
lean_dec_ref(v_x_584_);
v_r_589_ = lean_box(v_res_588_);
return v_r_589_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0___redArg(lean_object* v_x_590_, lean_object* v_x_591_){
_start:
{
uint64_t v___y_593_; 
if (lean_obj_tag(v_x_591_) == 0)
{
uint64_t v___x_596_; 
v___x_596_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_593_ = v___x_596_;
goto v___jp_592_;
}
else
{
uint64_t v_hash_597_; 
v_hash_597_ = lean_ctor_get_uint64(v_x_591_, sizeof(void*)*2);
v___y_593_ = v_hash_597_;
goto v___jp_592_;
}
v___jp_592_:
{
size_t v___x_594_; uint8_t v___x_595_; 
v___x_594_ = lean_uint64_to_usize(v___y_593_);
v___x_595_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0___redArg(v_x_590_, v___x_594_, v_x_591_);
return v___x_595_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0___redArg___boxed(lean_object* v_x_598_, lean_object* v_x_599_){
_start:
{
uint8_t v_res_600_; lean_object* v_r_601_; 
v_res_600_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0___redArg(v_x_598_, v_x_599_);
lean_dec(v_x_599_);
lean_dec_ref(v_x_598_);
v_r_601_ = lean_box(v_res_600_);
return v_r_601_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Match_isMatchEqnTheorem(lean_object* v_env_604_, lean_object* v_declName_605_){
_start:
{
lean_object* v___x_606_; 
lean_inc(v_declName_605_);
v___x_606_ = lean_erase_macro_scopes(v_declName_605_);
if (lean_obj_tag(v___x_606_) == 1)
{
lean_object* v_str_607_; uint8_t v___x_608_; 
v_str_607_ = lean_ctor_get(v___x_606_, 1);
lean_inc_ref(v_str_607_);
lean_dec_ref(v___x_606_);
v___x_608_ = l_Lean_Meta_isEqnLikeSuffix(v_str_607_);
if (v___x_608_ == 0)
{
lean_dec(v_declName_605_);
lean_dec_ref(v_env_604_);
return v___x_608_;
}
else
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v_eqns_613_; uint8_t v___x_614_; 
v___x_609_ = l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default;
v___x_610_ = l_Lean_Meta_Match_matchEqnsExt;
v___x_611_ = ((lean_object*)(l_Lean_Meta_Match_isMatchEqnTheorem___closed__0));
lean_inc(v_declName_605_);
v___x_612_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_609_, v___x_610_, v_env_604_, v___x_611_, v_declName_605_);
v_eqns_613_ = lean_ctor_get(v___x_612_, 1);
lean_inc_ref(v_eqns_613_);
lean_dec(v___x_612_);
v___x_614_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0___redArg(v_eqns_613_, v_declName_605_);
lean_dec(v_declName_605_);
lean_dec_ref(v_eqns_613_);
return v___x_614_;
}
}
else
{
uint8_t v___x_615_; 
lean_dec(v___x_606_);
lean_dec(v_declName_605_);
lean_dec_ref(v_env_604_);
v___x_615_ = 0;
return v___x_615_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_isMatchEqnTheorem___boxed(lean_object* v_env_616_, lean_object* v_declName_617_){
_start:
{
uint8_t v_res_618_; lean_object* v_r_619_; 
v_res_618_ = l_Lean_Meta_Match_isMatchEqnTheorem(v_env_616_, v_declName_617_);
v_r_619_ = lean_box(v_res_618_);
return v_r_619_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0(lean_object* v_00_u03b2_620_, lean_object* v_x_621_, lean_object* v_x_622_){
_start:
{
uint8_t v___x_623_; 
v___x_623_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0___redArg(v_x_621_, v_x_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0___boxed(lean_object* v_00_u03b2_624_, lean_object* v_x_625_, lean_object* v_x_626_){
_start:
{
uint8_t v_res_627_; lean_object* v_r_628_; 
v_res_627_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0(v_00_u03b2_624_, v_x_625_, v_x_626_);
lean_dec(v_x_626_);
lean_dec_ref(v_x_625_);
v_r_628_ = lean_box(v_res_627_);
return v_r_628_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0(lean_object* v_00_u03b2_629_, lean_object* v_x_630_, size_t v_x_631_, lean_object* v_x_632_){
_start:
{
uint8_t v___x_633_; 
v___x_633_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0___redArg(v_x_630_, v_x_631_, v_x_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0___boxed(lean_object* v_00_u03b2_634_, lean_object* v_x_635_, lean_object* v_x_636_, lean_object* v_x_637_){
_start:
{
size_t v_x_439__boxed_638_; uint8_t v_res_639_; lean_object* v_r_640_; 
v_x_439__boxed_638_ = lean_unbox_usize(v_x_636_);
lean_dec(v_x_636_);
v_res_639_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0(v_00_u03b2_634_, v_x_635_, v_x_439__boxed_638_, v_x_637_);
lean_dec(v_x_637_);
lean_dec_ref(v_x_635_);
v_r_640_ = lean_box(v_res_639_);
return v_r_640_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_641_, lean_object* v_keys_642_, lean_object* v_vals_643_, lean_object* v_heq_644_, lean_object* v_i_645_, lean_object* v_k_646_){
_start:
{
uint8_t v___x_647_; 
v___x_647_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1___redArg(v_keys_642_, v_i_645_, v_k_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_648_, lean_object* v_keys_649_, lean_object* v_vals_650_, lean_object* v_heq_651_, lean_object* v_i_652_, lean_object* v_k_653_){
_start:
{
uint8_t v_res_654_; lean_object* v_r_655_; 
v_res_654_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1(v_00_u03b2_648_, v_keys_649_, v_vals_650_, v_heq_651_, v_i_652_, v_k_653_);
lean_dec(v_k_653_);
lean_dec_ref(v_vals_650_);
lean_dec_ref(v_keys_649_);
v_r_655_ = lean_box(v_res_654_);
return v_r_655_;
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
