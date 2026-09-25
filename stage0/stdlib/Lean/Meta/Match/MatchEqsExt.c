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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg(lean_object*);
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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Match_instInhabitedMatcherInfo_default;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0(lean_object*);
static lean_once_cell_t l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__1;
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
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_178_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_179_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___redArg___closed__0);
v___x_180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___redArg(){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___redArg___closed__1);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___redArg___boxed(lean_object* v___dummy_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___redArg();
return v_res_184_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___closed__0(void){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___redArg();
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0(lean_object* v_00_u03b2_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___closed__0);
return v___x_187_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__0(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___redArg___closed__0);
v___x_189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
return v___x_189_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__1(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_190_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___closed__0);
v___x_191_ = lean_obj_once(&l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__0, &l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__0_once, _init_l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__0);
v___x_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v___x_190_);
return v___x_192_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default(void){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = lean_obj_once(&l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__1, &l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__1_once, _init_l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__1);
return v___x_193_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedMatchEqnsExtState(void){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default;
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2_(lean_object* v___x_195_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_197_, 0, v___x_195_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2____boxed(lean_object* v___x_198_, lean_object* v___y_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2_(v___x_198_);
return v_res_200_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_201_; lean_object* v___f_202_; 
v___x_201_ = lean_obj_once(&l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__1, &l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__1_once, _init_l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__1);
v___f_202_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_202_, 0, v___x_201_);
return v___f_202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___f_204_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2_);
v___x_205_ = lean_box(0);
v___x_206_ = lean_box(1);
v___x_207_ = l_Lean_registerEnvExtension___redArg(v___f_204_, v___x_205_, v___x_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2____boxed(lean_object* v_a_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2_();
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_210_, lean_object* v_x_211_, lean_object* v_x_212_, lean_object* v_x_213_){
_start:
{
lean_object* v_ks_214_; lean_object* v_vs_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_239_; 
v_ks_214_ = lean_ctor_get(v_x_210_, 0);
v_vs_215_ = lean_ctor_get(v_x_210_, 1);
v_isSharedCheck_239_ = !lean_is_exclusive(v_x_210_);
if (v_isSharedCheck_239_ == 0)
{
v___x_217_ = v_x_210_;
v_isShared_218_ = v_isSharedCheck_239_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_vs_215_);
lean_inc(v_ks_214_);
lean_dec(v_x_210_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_239_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_219_ = lean_array_get_size(v_ks_214_);
v___x_220_ = lean_nat_dec_lt(v_x_211_, v___x_219_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_224_; 
lean_dec(v_x_211_);
v___x_221_ = lean_array_push(v_ks_214_, v_x_212_);
v___x_222_ = lean_array_push(v_vs_215_, v_x_213_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 1, v___x_222_);
lean_ctor_set(v___x_217_, 0, v___x_221_);
v___x_224_ = v___x_217_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_221_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v___x_222_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
else
{
lean_object* v_k_x27_226_; uint8_t v___x_227_; 
v_k_x27_226_ = lean_array_fget_borrowed(v_ks_214_, v_x_211_);
v___x_227_ = lean_name_eq(v_x_212_, v_k_x27_226_);
if (v___x_227_ == 0)
{
lean_object* v___x_229_; 
if (v_isShared_218_ == 0)
{
v___x_229_ = v___x_217_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_ks_214_);
lean_ctor_set(v_reuseFailAlloc_233_, 1, v_vs_215_);
v___x_229_ = v_reuseFailAlloc_233_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = lean_unsigned_to_nat(1u);
v___x_231_ = lean_nat_add(v_x_211_, v___x_230_);
lean_dec(v_x_211_);
v_x_210_ = v___x_229_;
v_x_211_ = v___x_231_;
goto _start;
}
}
else
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_237_; 
v___x_234_ = lean_array_fset(v_ks_214_, v_x_211_, v_x_212_);
v___x_235_ = lean_array_fset(v_vs_215_, v_x_211_, v_x_213_);
lean_dec(v_x_211_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 1, v___x_235_);
lean_ctor_set(v___x_217_, 0, v___x_234_);
v___x_237_ = v___x_217_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_234_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v___x_235_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__1___redArg(lean_object* v_n_240_, lean_object* v_k_241_, lean_object* v_v_242_){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = lean_unsigned_to_nat(0u);
v___x_244_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__1_spec__3___redArg(v_n_240_, v___x_243_, v_k_241_, v_v_242_);
return v___x_244_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg(lean_object* v_x_246_, size_t v_x_247_, size_t v_x_248_, lean_object* v_x_249_, lean_object* v_x_250_){
_start:
{
if (lean_obj_tag(v_x_246_) == 0)
{
lean_object* v_es_251_; size_t v___x_252_; size_t v___x_253_; lean_object* v_j_254_; lean_object* v___x_255_; uint8_t v___x_256_; 
v_es_251_ = lean_ctor_get(v_x_246_, 0);
v___x_252_ = ((size_t)31ULL);
v___x_253_ = lean_usize_land(v_x_247_, v___x_252_);
v_j_254_ = lean_usize_to_nat(v___x_253_);
v___x_255_ = lean_array_get_size(v_es_251_);
v___x_256_ = lean_nat_dec_lt(v_j_254_, v___x_255_);
if (v___x_256_ == 0)
{
lean_dec(v_j_254_);
lean_dec(v_x_250_);
lean_dec(v_x_249_);
return v_x_246_;
}
else
{
lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_295_; 
lean_inc_ref(v_es_251_);
v_isSharedCheck_295_ = !lean_is_exclusive(v_x_246_);
if (v_isSharedCheck_295_ == 0)
{
lean_object* v_unused_296_; 
v_unused_296_ = lean_ctor_get(v_x_246_, 0);
lean_dec(v_unused_296_);
v___x_258_ = v_x_246_;
v_isShared_259_ = v_isSharedCheck_295_;
goto v_resetjp_257_;
}
else
{
lean_dec(v_x_246_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_295_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v_v_260_; lean_object* v___x_261_; lean_object* v_xs_x27_262_; lean_object* v___y_264_; 
v_v_260_ = lean_array_fget(v_es_251_, v_j_254_);
v___x_261_ = lean_box(0);
v_xs_x27_262_ = lean_array_fset(v_es_251_, v_j_254_, v___x_261_);
switch(lean_obj_tag(v_v_260_))
{
case 0:
{
lean_object* v_key_269_; lean_object* v_val_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_280_; 
v_key_269_ = lean_ctor_get(v_v_260_, 0);
v_val_270_ = lean_ctor_get(v_v_260_, 1);
v_isSharedCheck_280_ = !lean_is_exclusive(v_v_260_);
if (v_isSharedCheck_280_ == 0)
{
v___x_272_ = v_v_260_;
v_isShared_273_ = v_isSharedCheck_280_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_val_270_);
lean_inc(v_key_269_);
lean_dec(v_v_260_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_280_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
uint8_t v___x_274_; 
v___x_274_ = lean_name_eq(v_x_249_, v_key_269_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; lean_object* v___x_276_; 
lean_del_object(v___x_272_);
v___x_275_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_269_, v_val_270_, v_x_249_, v_x_250_);
v___x_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
v___y_264_ = v___x_276_;
goto v___jp_263_;
}
else
{
lean_object* v___x_278_; 
lean_dec(v_val_270_);
lean_dec(v_key_269_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 1, v_x_250_);
lean_ctor_set(v___x_272_, 0, v_x_249_);
v___x_278_ = v___x_272_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_x_249_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v_x_250_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
v___y_264_ = v___x_278_;
goto v___jp_263_;
}
}
}
}
case 1:
{
lean_object* v_node_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_293_; 
v_node_281_ = lean_ctor_get(v_v_260_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v_v_260_);
if (v_isSharedCheck_293_ == 0)
{
v___x_283_ = v_v_260_;
v_isShared_284_ = v_isSharedCheck_293_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_node_281_);
lean_dec(v_v_260_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_293_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
size_t v___x_285_; size_t v___x_286_; size_t v___x_287_; size_t v___x_288_; lean_object* v___x_289_; lean_object* v___x_291_; 
v___x_285_ = ((size_t)5ULL);
v___x_286_ = lean_usize_shift_right(v_x_247_, v___x_285_);
v___x_287_ = ((size_t)1ULL);
v___x_288_ = lean_usize_add(v_x_248_, v___x_287_);
v___x_289_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg(v_node_281_, v___x_286_, v___x_288_, v_x_249_, v_x_250_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 0, v___x_289_);
v___x_291_ = v___x_283_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_289_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
v___y_264_ = v___x_291_;
goto v___jp_263_;
}
}
}
default: 
{
lean_object* v___x_294_; 
v___x_294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_294_, 0, v_x_249_);
lean_ctor_set(v___x_294_, 1, v_x_250_);
v___y_264_ = v___x_294_;
goto v___jp_263_;
}
}
v___jp_263_:
{
lean_object* v___x_265_; lean_object* v___x_267_; 
v___x_265_ = lean_array_fset(v_xs_x27_262_, v_j_254_, v___y_264_);
lean_dec(v_j_254_);
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 0, v___x_265_);
v___x_267_ = v___x_258_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_265_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
}
else
{
lean_object* v_ks_297_; lean_object* v_vs_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_316_; 
v_ks_297_ = lean_ctor_get(v_x_246_, 0);
v_vs_298_ = lean_ctor_get(v_x_246_, 1);
v_isSharedCheck_316_ = !lean_is_exclusive(v_x_246_);
if (v_isSharedCheck_316_ == 0)
{
v___x_300_ = v_x_246_;
v_isShared_301_ = v_isSharedCheck_316_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_vs_298_);
lean_inc(v_ks_297_);
lean_dec(v_x_246_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_316_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_303_; 
if (v_isShared_301_ == 0)
{
v___x_303_ = v___x_300_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_ks_297_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v_vs_298_);
v___x_303_ = v_reuseFailAlloc_315_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
lean_object* v_newNode_304_; size_t v___x_305_; uint8_t v___x_306_; 
v_newNode_304_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__1___redArg(v___x_303_, v_x_249_, v_x_250_);
v___x_305_ = ((size_t)7ULL);
v___x_306_ = lean_usize_dec_le(v___x_305_, v_x_248_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_307_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_304_);
v___x_308_ = lean_unsigned_to_nat(4u);
v___x_309_ = lean_nat_dec_lt(v___x_307_, v___x_308_);
lean_dec(v___x_307_);
if (v___x_309_ == 0)
{
lean_object* v_ks_310_; lean_object* v_vs_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v_ks_310_ = lean_ctor_get(v_newNode_304_, 0);
lean_inc_ref(v_ks_310_);
v_vs_311_ = lean_ctor_get(v_newNode_304_, 1);
lean_inc_ref(v_vs_311_);
lean_dec_ref(v_newNode_304_);
v___x_312_ = lean_unsigned_to_nat(0u);
v___x_313_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__0);
v___x_314_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg(v_x_248_, v_ks_310_, v_vs_311_, v___x_312_, v___x_313_);
lean_dec_ref(v_vs_311_);
lean_dec_ref(v_ks_310_);
return v___x_314_;
}
else
{
return v_newNode_304_;
}
}
else
{
return v_newNode_304_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg(size_t v_depth_317_, lean_object* v_keys_318_, lean_object* v_vals_319_, lean_object* v_i_320_, lean_object* v_entries_321_){
_start:
{
lean_object* v___x_322_; uint8_t v___x_323_; 
v___x_322_ = lean_array_get_size(v_keys_318_);
v___x_323_ = lean_nat_dec_lt(v_i_320_, v___x_322_);
if (v___x_323_ == 0)
{
lean_dec(v_i_320_);
return v_entries_321_;
}
else
{
lean_object* v_k_324_; lean_object* v_v_325_; uint64_t v___y_327_; 
v_k_324_ = lean_array_fget_borrowed(v_keys_318_, v_i_320_);
v_v_325_ = lean_array_fget_borrowed(v_vals_319_, v_i_320_);
if (lean_obj_tag(v_k_324_) == 0)
{
uint64_t v___x_338_; 
v___x_338_ = 1723ULL;
v___y_327_ = v___x_338_;
goto v___jp_326_;
}
else
{
uint64_t v_hash_339_; 
v_hash_339_ = lean_ctor_get_uint64(v_k_324_, sizeof(void*)*2);
v___y_327_ = v_hash_339_;
goto v___jp_326_;
}
v___jp_326_:
{
size_t v_h_328_; size_t v___x_329_; lean_object* v___x_330_; size_t v___x_331_; size_t v___x_332_; size_t v___x_333_; size_t v_h_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v_h_328_ = lean_uint64_to_usize(v___y_327_);
v___x_329_ = ((size_t)5ULL);
v___x_330_ = lean_unsigned_to_nat(1u);
v___x_331_ = ((size_t)1ULL);
v___x_332_ = lean_usize_sub(v_depth_317_, v___x_331_);
v___x_333_ = lean_usize_mul(v___x_329_, v___x_332_);
v_h_334_ = lean_usize_shift_right(v_h_328_, v___x_333_);
v___x_335_ = lean_nat_add(v_i_320_, v___x_330_);
lean_dec(v_i_320_);
lean_inc(v_v_325_);
lean_inc(v_k_324_);
v___x_336_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg(v_entries_321_, v_h_334_, v_depth_317_, v_k_324_, v_v_325_);
v_i_320_ = v___x_335_;
v_entries_321_ = v___x_336_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_340_, lean_object* v_keys_341_, lean_object* v_vals_342_, lean_object* v_i_343_, lean_object* v_entries_344_){
_start:
{
size_t v_depth_boxed_345_; lean_object* v_res_346_; 
v_depth_boxed_345_ = lean_unbox_usize(v_depth_340_);
lean_dec(v_depth_340_);
v_res_346_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg(v_depth_boxed_345_, v_keys_341_, v_vals_342_, v_i_343_, v_entries_344_);
lean_dec_ref(v_vals_342_);
lean_dec_ref(v_keys_341_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___boxed(lean_object* v_x_347_, lean_object* v_x_348_, lean_object* v_x_349_, lean_object* v_x_350_, lean_object* v_x_351_){
_start:
{
size_t v_x_705__boxed_352_; size_t v_x_706__boxed_353_; lean_object* v_res_354_; 
v_x_705__boxed_352_ = lean_unbox_usize(v_x_348_);
lean_dec(v_x_348_);
v_x_706__boxed_353_ = lean_unbox_usize(v_x_349_);
lean_dec(v_x_349_);
v_res_354_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg(v_x_347_, v_x_705__boxed_352_, v_x_706__boxed_353_, v_x_350_, v_x_351_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0___redArg(lean_object* v_x_355_, lean_object* v_x_356_, lean_object* v_x_357_){
_start:
{
uint64_t v___y_359_; 
if (lean_obj_tag(v_x_356_) == 0)
{
uint64_t v___x_363_; 
v___x_363_ = 1723ULL;
v___y_359_ = v___x_363_;
goto v___jp_358_;
}
else
{
uint64_t v_hash_364_; 
v_hash_364_ = lean_ctor_get_uint64(v_x_356_, sizeof(void*)*2);
v___y_359_ = v_hash_364_;
goto v___jp_358_;
}
v___jp_358_:
{
size_t v___x_360_; size_t v___x_361_; lean_object* v___x_362_; 
v___x_360_ = lean_uint64_to_usize(v___y_359_);
v___x_361_ = ((size_t)1ULL);
v___x_362_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg(v_x_355_, v___x_360_, v___x_361_, v_x_356_, v_x_357_);
return v___x_362_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_registerMatchEqns_spec__1(lean_object* v_as_365_, size_t v_i_366_, size_t v_stop_367_, lean_object* v_b_368_){
_start:
{
uint8_t v___x_369_; 
v___x_369_ = lean_usize_dec_eq(v_i_366_, v_stop_367_);
if (v___x_369_ == 0)
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; size_t v___x_373_; size_t v___x_374_; 
v___x_370_ = lean_array_uget_borrowed(v_as_365_, v_i_366_);
v___x_371_ = lean_box(0);
lean_inc(v___x_370_);
v___x_372_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0___redArg(v_b_368_, v___x_370_, v___x_371_);
v___x_373_ = ((size_t)1ULL);
v___x_374_ = lean_usize_add(v_i_366_, v___x_373_);
v_i_366_ = v___x_374_;
v_b_368_ = v___x_372_;
goto _start;
}
else
{
return v_b_368_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_registerMatchEqns_spec__1___boxed(lean_object* v_as_376_, lean_object* v_i_377_, lean_object* v_stop_378_, lean_object* v_b_379_){
_start:
{
size_t v_i_boxed_380_; size_t v_stop_boxed_381_; lean_object* v_res_382_; 
v_i_boxed_380_ = lean_unbox_usize(v_i_377_);
lean_dec(v_i_377_);
v_stop_boxed_381_ = lean_unbox_usize(v_stop_378_);
lean_dec(v_stop_378_);
v_res_382_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_registerMatchEqns_spec__1(v_as_376_, v_i_boxed_380_, v_stop_boxed_381_, v_b_379_);
lean_dec_ref(v_as_376_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_registerMatchEqns___redArg___lam__0(lean_object* v_matchEqns_383_, lean_object* v_matchDeclName_384_, lean_object* v_x_385_){
_start:
{
lean_object* v_map_386_; lean_object* v_eqns_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_415_; 
v_map_386_ = lean_ctor_get(v_x_385_, 0);
v_eqns_387_ = lean_ctor_get(v_x_385_, 1);
v_isSharedCheck_415_ = !lean_is_exclusive(v_x_385_);
if (v_isSharedCheck_415_ == 0)
{
v___x_389_ = v_x_385_;
v_isShared_390_ = v_isSharedCheck_415_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_eqns_387_);
lean_inc(v_map_386_);
lean_dec(v_x_385_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_415_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v_eqnNames_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; uint8_t v___x_395_; 
v_eqnNames_391_ = lean_ctor_get(v_matchEqns_383_, 0);
lean_inc_ref(v_eqnNames_391_);
v___x_392_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0___redArg(v_map_386_, v_matchDeclName_384_, v_matchEqns_383_);
v___x_393_ = lean_unsigned_to_nat(0u);
v___x_394_ = lean_array_get_size(v_eqnNames_391_);
v___x_395_ = lean_nat_dec_lt(v___x_393_, v___x_394_);
if (v___x_395_ == 0)
{
lean_object* v___x_397_; 
lean_dec_ref(v_eqnNames_391_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v___x_392_);
v___x_397_ = v___x_389_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_392_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v_eqns_387_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
else
{
uint8_t v___x_399_; 
v___x_399_ = lean_nat_dec_le(v___x_394_, v___x_394_);
if (v___x_399_ == 0)
{
if (v___x_395_ == 0)
{
lean_object* v___x_401_; 
lean_dec_ref(v_eqnNames_391_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v___x_392_);
v___x_401_ = v___x_389_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_392_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v_eqns_387_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
else
{
size_t v___x_403_; size_t v___x_404_; lean_object* v___x_405_; lean_object* v___x_407_; 
v___x_403_ = ((size_t)0ULL);
v___x_404_ = lean_usize_of_nat(v___x_394_);
v___x_405_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_registerMatchEqns_spec__1(v_eqnNames_391_, v___x_403_, v___x_404_, v_eqns_387_);
lean_dec_ref(v_eqnNames_391_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 1, v___x_405_);
lean_ctor_set(v___x_389_, 0, v___x_392_);
v___x_407_ = v___x_389_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_392_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v___x_405_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
else
{
size_t v___x_409_; size_t v___x_410_; lean_object* v___x_411_; lean_object* v___x_413_; 
v___x_409_ = ((size_t)0ULL);
v___x_410_ = lean_usize_of_nat(v___x_394_);
v___x_411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_registerMatchEqns_spec__1(v_eqnNames_391_, v___x_409_, v___x_410_, v_eqns_387_);
lean_dec_ref(v_eqnNames_391_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 1, v___x_411_);
lean_ctor_set(v___x_389_, 0, v___x_392_);
v___x_413_ = v___x_389_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_392_);
lean_ctor_set(v_reuseFailAlloc_414_, 1, v___x_411_);
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
}
static lean_object* _init_l_Lean_Meta_Match_registerMatchEqns___redArg___closed__0(void){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___redArg___closed__0);
v___x_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
return v___x_417_;
}
}
static lean_object* _init_l_Lean_Meta_Match_registerMatchEqns___redArg___closed__1(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = lean_obj_once(&l_Lean_Meta_Match_registerMatchEqns___redArg___closed__0, &l_Lean_Meta_Match_registerMatchEqns___redArg___closed__0_once, _init_l_Lean_Meta_Match_registerMatchEqns___redArg___closed__0);
v___x_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
lean_ctor_set(v___x_419_, 1, v___x_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_registerMatchEqns___redArg(lean_object* v_matchDeclName_420_, lean_object* v_matchEqns_421_, lean_object* v_a_422_){
_start:
{
lean_object* v___f_424_; lean_object* v___x_425_; lean_object* v_env_426_; lean_object* v_nextMacroScope_427_; lean_object* v_ngen_428_; lean_object* v_auxDeclNGen_429_; lean_object* v_traceState_430_; lean_object* v_messages_431_; lean_object* v_infoState_432_; lean_object* v_snapshotTasks_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_448_; 
v___f_424_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_registerMatchEqns___redArg___lam__0), 3, 2);
lean_closure_set(v___f_424_, 0, v_matchEqns_421_);
lean_closure_set(v___f_424_, 1, v_matchDeclName_420_);
v___x_425_ = lean_st_ref_take(v_a_422_);
v_env_426_ = lean_ctor_get(v___x_425_, 0);
v_nextMacroScope_427_ = lean_ctor_get(v___x_425_, 1);
v_ngen_428_ = lean_ctor_get(v___x_425_, 2);
v_auxDeclNGen_429_ = lean_ctor_get(v___x_425_, 3);
v_traceState_430_ = lean_ctor_get(v___x_425_, 4);
v_messages_431_ = lean_ctor_get(v___x_425_, 6);
v_infoState_432_ = lean_ctor_get(v___x_425_, 7);
v_snapshotTasks_433_ = lean_ctor_get(v___x_425_, 8);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_448_ == 0)
{
lean_object* v_unused_449_; 
v_unused_449_ = lean_ctor_get(v___x_425_, 5);
lean_dec(v_unused_449_);
v___x_435_ = v___x_425_;
v_isShared_436_ = v_isSharedCheck_448_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_snapshotTasks_433_);
lean_inc(v_infoState_432_);
lean_inc(v_messages_431_);
lean_inc(v_traceState_430_);
lean_inc(v_auxDeclNGen_429_);
lean_inc(v_ngen_428_);
lean_inc(v_nextMacroScope_427_);
lean_inc(v_env_426_);
lean_dec(v___x_425_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_448_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_437_; lean_object* v_asyncMode_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_444_; 
v___x_437_ = l_Lean_Meta_Match_matchEqnsExt;
v_asyncMode_438_ = lean_ctor_get(v___x_437_, 2);
v___x_439_ = lean_box(0);
v___x_440_ = lean_box(0);
v___x_441_ = l_Lean_EnvExtension_modifyState___redArg(v___x_437_, v_env_426_, v___f_424_, v_asyncMode_438_, v___x_440_);
v___x_442_ = lean_obj_once(&l_Lean_Meta_Match_registerMatchEqns___redArg___closed__1, &l_Lean_Meta_Match_registerMatchEqns___redArg___closed__1_once, _init_l_Lean_Meta_Match_registerMatchEqns___redArg___closed__1);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 5, v___x_442_);
lean_ctor_set(v___x_435_, 0, v___x_441_);
v___x_444_ = v___x_435_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_441_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v_nextMacroScope_427_);
lean_ctor_set(v_reuseFailAlloc_447_, 2, v_ngen_428_);
lean_ctor_set(v_reuseFailAlloc_447_, 3, v_auxDeclNGen_429_);
lean_ctor_set(v_reuseFailAlloc_447_, 4, v_traceState_430_);
lean_ctor_set(v_reuseFailAlloc_447_, 5, v___x_442_);
lean_ctor_set(v_reuseFailAlloc_447_, 6, v_messages_431_);
lean_ctor_set(v_reuseFailAlloc_447_, 7, v_infoState_432_);
lean_ctor_set(v_reuseFailAlloc_447_, 8, v_snapshotTasks_433_);
v___x_444_ = v_reuseFailAlloc_447_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = lean_st_ref_put(v_a_422_, v___x_444_);
v___x_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_446_, 0, v___x_439_);
return v___x_446_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_registerMatchEqns___redArg___boxed(lean_object* v_matchDeclName_450_, lean_object* v_matchEqns_451_, lean_object* v_a_452_, lean_object* v_a_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_Meta_Match_registerMatchEqns___redArg(v_matchDeclName_450_, v_matchEqns_451_, v_a_452_);
lean_dec(v_a_452_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_registerMatchEqns(lean_object* v_matchDeclName_455_, lean_object* v_matchEqns_456_, lean_object* v_a_457_, lean_object* v_a_458_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_Lean_Meta_Match_registerMatchEqns___redArg(v_matchDeclName_455_, v_matchEqns_456_, v_a_458_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_registerMatchEqns___boxed(lean_object* v_matchDeclName_461_, lean_object* v_matchEqns_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Lean_Meta_Match_registerMatchEqns(v_matchDeclName_461_, v_matchEqns_462_, v_a_463_, v_a_464_);
lean_dec(v_a_464_);
lean_dec_ref(v_a_463_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0(lean_object* v_00_u03b2_467_, lean_object* v_x_468_, lean_object* v_x_469_, lean_object* v_x_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0___redArg(v_x_468_, v_x_469_, v_x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0(lean_object* v_00_u03b2_472_, lean_object* v_x_473_, size_t v_x_474_, size_t v_x_475_, lean_object* v_x_476_, lean_object* v_x_477_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg(v_x_473_, v_x_474_, v_x_475_, v_x_476_, v_x_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___boxed(lean_object* v_00_u03b2_479_, lean_object* v_x_480_, lean_object* v_x_481_, lean_object* v_x_482_, lean_object* v_x_483_, lean_object* v_x_484_){
_start:
{
size_t v_x_1016__boxed_485_; size_t v_x_1017__boxed_486_; lean_object* v_res_487_; 
v_x_1016__boxed_485_ = lean_unbox_usize(v_x_481_);
lean_dec(v_x_481_);
v_x_1017__boxed_486_ = lean_unbox_usize(v_x_482_);
lean_dec(v_x_482_);
v_res_487_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0(v_00_u03b2_479_, v_x_480_, v_x_1016__boxed_485_, v_x_1017__boxed_486_, v_x_483_, v_x_484_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_488_, lean_object* v_n_489_, lean_object* v_k_490_, lean_object* v_v_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__1___redArg(v_n_489_, v_k_490_, v_v_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_493_, size_t v_depth_494_, lean_object* v_keys_495_, lean_object* v_vals_496_, lean_object* v_heq_497_, lean_object* v_i_498_, lean_object* v_entries_499_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg(v_depth_494_, v_keys_495_, v_vals_496_, v_i_498_, v_entries_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_501_, lean_object* v_depth_502_, lean_object* v_keys_503_, lean_object* v_vals_504_, lean_object* v_heq_505_, lean_object* v_i_506_, lean_object* v_entries_507_){
_start:
{
size_t v_depth_boxed_508_; lean_object* v_res_509_; 
v_depth_boxed_508_ = lean_unbox_usize(v_depth_502_);
lean_dec(v_depth_502_);
v_res_509_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2(v_00_u03b2_501_, v_depth_boxed_508_, v_keys_503_, v_vals_504_, v_heq_505_, v_i_506_, v_entries_507_);
lean_dec_ref(v_vals_504_);
lean_dec_ref(v_keys_503_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_510_, lean_object* v_x_511_, lean_object* v_x_512_, lean_object* v_x_513_, lean_object* v_x_514_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__1_spec__3___redArg(v_x_511_, v_x_512_, v_x_513_, v_x_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getEquationsFor___boxed(lean_object* v_matchDeclName_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_00___x40___internal___hyg_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = lean_get_match_equations_for(v_matchDeclName_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_genMatchCongrEqns___boxed(lean_object* v_matchDeclName_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_00___x40___internal___hyg_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = lean_get_congr_match_equations_for(v_matchDeclName_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_);
return v_res_541_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_542_, lean_object* v_i_543_, lean_object* v_k_544_){
_start:
{
lean_object* v___x_545_; uint8_t v___x_546_; 
v___x_545_ = lean_array_get_size(v_keys_542_);
v___x_546_ = lean_nat_dec_lt(v_i_543_, v___x_545_);
if (v___x_546_ == 0)
{
lean_dec(v_i_543_);
return v___x_546_;
}
else
{
lean_object* v_k_x27_547_; uint8_t v___x_548_; 
v_k_x27_547_ = lean_array_fget_borrowed(v_keys_542_, v_i_543_);
v___x_548_ = lean_name_eq(v_k_544_, v_k_x27_547_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_549_ = lean_unsigned_to_nat(1u);
v___x_550_ = lean_nat_add(v_i_543_, v___x_549_);
lean_dec(v_i_543_);
v_i_543_ = v___x_550_;
goto _start;
}
else
{
lean_dec(v_i_543_);
return v___x_546_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_552_, lean_object* v_i_553_, lean_object* v_k_554_){
_start:
{
uint8_t v_res_555_; lean_object* v_r_556_; 
v_res_555_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1___redArg(v_keys_552_, v_i_553_, v_k_554_);
lean_dec(v_k_554_);
lean_dec_ref(v_keys_552_);
v_r_556_ = lean_box(v_res_555_);
return v_r_556_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0___redArg(lean_object* v_x_557_, size_t v_x_558_, lean_object* v_x_559_){
_start:
{
if (lean_obj_tag(v_x_557_) == 0)
{
lean_object* v_es_560_; lean_object* v___x_561_; size_t v___x_562_; size_t v___x_563_; lean_object* v_j_564_; lean_object* v___x_565_; 
v_es_560_ = lean_ctor_get(v_x_557_, 0);
v___x_561_ = lean_box(2);
v___x_562_ = ((size_t)31ULL);
v___x_563_ = lean_usize_land(v_x_558_, v___x_562_);
v_j_564_ = lean_usize_to_nat(v___x_563_);
v___x_565_ = lean_array_get_borrowed(v___x_561_, v_es_560_, v_j_564_);
lean_dec(v_j_564_);
switch(lean_obj_tag(v___x_565_))
{
case 0:
{
lean_object* v_key_566_; uint8_t v___x_567_; 
v_key_566_ = lean_ctor_get(v___x_565_, 0);
v___x_567_ = lean_name_eq(v_x_559_, v_key_566_);
return v___x_567_;
}
case 1:
{
lean_object* v_node_568_; size_t v___x_569_; size_t v___x_570_; 
v_node_568_ = lean_ctor_get(v___x_565_, 0);
v___x_569_ = ((size_t)5ULL);
v___x_570_ = lean_usize_shift_right(v_x_558_, v___x_569_);
v_x_557_ = v_node_568_;
v_x_558_ = v___x_570_;
goto _start;
}
default: 
{
uint8_t v___x_572_; 
v___x_572_ = 0;
return v___x_572_;
}
}
}
else
{
lean_object* v_ks_573_; lean_object* v___x_574_; uint8_t v___x_575_; 
v_ks_573_ = lean_ctor_get(v_x_557_, 0);
v___x_574_ = lean_unsigned_to_nat(0u);
v___x_575_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1___redArg(v_ks_573_, v___x_574_, v_x_559_);
return v___x_575_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0___redArg___boxed(lean_object* v_x_576_, lean_object* v_x_577_, lean_object* v_x_578_){
_start:
{
size_t v_x_298__boxed_579_; uint8_t v_res_580_; lean_object* v_r_581_; 
v_x_298__boxed_579_ = lean_unbox_usize(v_x_577_);
lean_dec(v_x_577_);
v_res_580_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0___redArg(v_x_576_, v_x_298__boxed_579_, v_x_578_);
lean_dec(v_x_578_);
lean_dec_ref(v_x_576_);
v_r_581_ = lean_box(v_res_580_);
return v_r_581_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0___redArg(lean_object* v_x_582_, lean_object* v_x_583_){
_start:
{
uint64_t v___y_585_; 
if (lean_obj_tag(v_x_583_) == 0)
{
uint64_t v___x_588_; 
v___x_588_ = 1723ULL;
v___y_585_ = v___x_588_;
goto v___jp_584_;
}
else
{
uint64_t v_hash_589_; 
v_hash_589_ = lean_ctor_get_uint64(v_x_583_, sizeof(void*)*2);
v___y_585_ = v_hash_589_;
goto v___jp_584_;
}
v___jp_584_:
{
size_t v___x_586_; uint8_t v___x_587_; 
v___x_586_ = lean_uint64_to_usize(v___y_585_);
v___x_587_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0___redArg(v_x_582_, v___x_586_, v_x_583_);
return v___x_587_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0___redArg___boxed(lean_object* v_x_590_, lean_object* v_x_591_){
_start:
{
uint8_t v_res_592_; lean_object* v_r_593_; 
v_res_592_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0___redArg(v_x_590_, v_x_591_);
lean_dec(v_x_591_);
lean_dec_ref(v_x_590_);
v_r_593_ = lean_box(v_res_592_);
return v_r_593_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Match_isMatchEqnTheorem(lean_object* v_env_596_, lean_object* v_declName_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l_Lean_Name_eraseMacroScopes(v_declName_597_);
if (lean_obj_tag(v___x_598_) == 1)
{
lean_object* v_str_599_; uint8_t v___x_600_; 
v_str_599_ = lean_ctor_get(v___x_598_, 1);
lean_inc_ref(v_str_599_);
lean_dec_ref_known(v___x_598_, 2);
v___x_600_ = l_Lean_Meta_isEqnLikeSuffix(v_str_599_);
if (v___x_600_ == 0)
{
lean_dec(v_declName_597_);
lean_dec_ref(v_env_596_);
return v___x_600_;
}
else
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v_eqns_605_; uint8_t v___x_606_; 
v___x_601_ = l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default;
v___x_602_ = l_Lean_Meta_Match_matchEqnsExt;
v___x_603_ = ((lean_object*)(l_Lean_Meta_Match_isMatchEqnTheorem___closed__0));
lean_inc(v_declName_597_);
v___x_604_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_601_, v___x_602_, v_env_596_, v___x_603_, v_declName_597_);
v_eqns_605_ = lean_ctor_get(v___x_604_, 1);
lean_inc_ref(v_eqns_605_);
lean_dec(v___x_604_);
v___x_606_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0___redArg(v_eqns_605_, v_declName_597_);
lean_dec(v_declName_597_);
lean_dec_ref(v_eqns_605_);
return v___x_606_;
}
}
else
{
uint8_t v___x_607_; 
lean_dec(v___x_598_);
lean_dec(v_declName_597_);
lean_dec_ref(v_env_596_);
v___x_607_ = 0;
return v___x_607_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_isMatchEqnTheorem___boxed(lean_object* v_env_608_, lean_object* v_declName_609_){
_start:
{
uint8_t v_res_610_; lean_object* v_r_611_; 
v_res_610_ = l_Lean_Meta_Match_isMatchEqnTheorem(v_env_608_, v_declName_609_);
v_r_611_ = lean_box(v_res_610_);
return v_r_611_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0(lean_object* v_00_u03b2_612_, lean_object* v_x_613_, lean_object* v_x_614_){
_start:
{
uint8_t v___x_615_; 
v___x_615_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0___redArg(v_x_613_, v_x_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0___boxed(lean_object* v_00_u03b2_616_, lean_object* v_x_617_, lean_object* v_x_618_){
_start:
{
uint8_t v_res_619_; lean_object* v_r_620_; 
v_res_619_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0(v_00_u03b2_616_, v_x_617_, v_x_618_);
lean_dec(v_x_618_);
lean_dec_ref(v_x_617_);
v_r_620_ = lean_box(v_res_619_);
return v_r_620_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0(lean_object* v_00_u03b2_621_, lean_object* v_x_622_, size_t v_x_623_, lean_object* v_x_624_){
_start:
{
uint8_t v___x_625_; 
v___x_625_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0___redArg(v_x_622_, v_x_623_, v_x_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0___boxed(lean_object* v_00_u03b2_626_, lean_object* v_x_627_, lean_object* v_x_628_, lean_object* v_x_629_){
_start:
{
size_t v_x_388__boxed_630_; uint8_t v_res_631_; lean_object* v_r_632_; 
v_x_388__boxed_630_ = lean_unbox_usize(v_x_628_);
lean_dec(v_x_628_);
v_res_631_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0(v_00_u03b2_626_, v_x_627_, v_x_388__boxed_630_, v_x_629_);
lean_dec(v_x_629_);
lean_dec_ref(v_x_627_);
v_r_632_ = lean_box(v_res_631_);
return v_r_632_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_633_, lean_object* v_keys_634_, lean_object* v_vals_635_, lean_object* v_heq_636_, lean_object* v_i_637_, lean_object* v_k_638_){
_start:
{
uint8_t v___x_639_; 
v___x_639_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1___redArg(v_keys_634_, v_i_637_, v_k_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_640_, lean_object* v_keys_641_, lean_object* v_vals_642_, lean_object* v_heq_643_, lean_object* v_i_644_, lean_object* v_k_645_){
_start:
{
uint8_t v_res_646_; lean_object* v_r_647_; 
v_res_646_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1(v_00_u03b2_640_, v_keys_641_, v_vals_642_, v_heq_643_, v_i_644_, v_k_645_);
lean_dec(v_k_645_);
lean_dec_ref(v_vals_642_);
lean_dec_ref(v_keys_641_);
v_r_647_ = lean_box(v_res_646_);
return v_r_647_;
}
}
lean_object* runtime_initialize_Lean_Meta_Match_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Eqns(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Match_MatchEqsExt(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
