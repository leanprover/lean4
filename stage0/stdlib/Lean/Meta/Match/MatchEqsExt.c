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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
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
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Match_instInhabitedMatcherInfo_default;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
uint8_t l_Lean_Meta_isEqnLikeSuffix(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__1_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__1_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__1_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__2_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__2_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__2_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__3_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Match"};
static const lean_object* l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__3_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__3_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__4_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "matchEqnsExt"};
static const lean_object* l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__4_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__4_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__5_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__1_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__5_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__5_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__2_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__5_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__5_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__3_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(63, 134, 186, 123, 61, 240, 95, 75)}};
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__5_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__5_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__4_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(94, 180, 80, 49, 40, 81, 123, 195)}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__5_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__5_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_matchEqnsExt;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Match_registerMatchEqns_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Match_registerMatchEqns_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Meta_Match_registerMatchEqns_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Meta_Match_registerMatchEqns_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_registerMatchEqns_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_registerMatchEqns_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Match_registerMatchEqns___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Meta.Match.MatchEqsExt"};
static const lean_object* l_Lean_Meta_Match_registerMatchEqns___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Match_registerMatchEqns___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_Meta_Match_registerMatchEqns___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Lean.Meta.Match.registerMatchEqns"};
static const lean_object* l_Lean_Meta_Match_registerMatchEqns___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Match_registerMatchEqns___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_Meta_Match_registerMatchEqns___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "match equations for `"};
static const lean_object* l_Lean_Meta_Match_registerMatchEqns___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Match_registerMatchEqns___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_Meta_Match_registerMatchEqns___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "` are already registered"};
static const lean_object* l_Lean_Meta_Match_registerMatchEqns___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_Match_registerMatchEqns___redArg___lam__0___closed__3_value;
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Meta_Match_registerMatchEqns_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Meta_Match_registerMatchEqns_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___redArg(){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___redArg___closed__1);
return v___x_182_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_183_;
v_res_183_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___redArg();
stack->m_obj
 = v_res_183_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___redArg___boxed(lean_object* v___dummy_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___redArg();
return v_res_185_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___closed__0(void){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___redArg();
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0(lean_object* v_00_u03b2_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___closed__0);
return v___x_188_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__0(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___redArg___closed__0);
v___x_190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
return v___x_190_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__1(void){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_191_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___closed__0);
v___x_192_ = lean_obj_once(&l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__0, &l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__0_once, _init_l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__0);
v___x_193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
lean_ctor_set(v___x_193_, 1, v___x_191_);
return v___x_193_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default(void){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = lean_obj_once(&l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__1, &l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__1_once, _init_l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__1);
return v___x_194_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedMatchEqnsExtState(void){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default;
return v___x_195_;
}
}
lean_object* l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2_(lean_object* v___x_196_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_198_, 0, v___x_196_);
return v___x_198_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_196_ = stack[0].m_obj;
lean_object* v_res_199_;
v_res_199_ = l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2_(v___x_196_);
stack->m_obj
 = v_res_199_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2____boxed(lean_object* v___x_200_, lean_object* v___y_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2_(v___x_200_);
return v_res_202_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_203_; lean_object* v___f_204_; 
v___x_203_ = lean_obj_once(&l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__1, &l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__1_once, _init_l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__1);
v___f_204_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_204_, 0, v___x_203_);
return v___f_204_;
}
}
lean_object* l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; uint8_t v___x_219_; uint8_t v___x_220_; lean_object* v___x_221_; 
v___f_215_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2_);
v___x_216_ = lean_box(0);
v___x_217_ = lean_box(1);
v___x_218_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__5_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2_));
v___x_219_ = 0;
v___x_220_ = 1;
v___x_221_ = l_Lean_registerEnvExtension___redArg(v___f_215_, v___x_216_, v___x_217_, v___x_218_, v___x_219_, v___x_220_);
return v___x_221_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_222_;
v_res_222_ = l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2_();
stack->m_obj
 = v_res_222_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2____boxed(lean_object* v_a_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2_();
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Match_registerMatchEqns_spec__2(lean_object* v_map_225_, lean_object* v_msg_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = lean_panic_fn_borrowed(v_map_225_, v_msg_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Match_registerMatchEqns_spec__2___boxed(lean_object* v_map_228_, lean_object* v_msg_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_panic___at___00Lean_Meta_Match_registerMatchEqns_spec__2(v_map_228_, v_msg_229_);
lean_dec_ref(v_map_228_);
return v_res_230_;
}
}
uint8_t l_Array_isEqvAux___at___00Lean_Meta_Match_registerMatchEqns_spec__4___redArg(lean_object* v_xs_231_, lean_object* v_ys_232_, lean_object* v_x_233_){
_start:
{
lean_object* v_zero_234_; uint8_t v_isZero_235_; 
v_zero_234_ = lean_unsigned_to_nat(0u);
v_isZero_235_ = lean_nat_dec_eq(v_x_233_, v_zero_234_);
if (v_isZero_235_ == 1)
{
lean_dec(v_x_233_);
return v_isZero_235_;
}
else
{
lean_object* v_one_236_; lean_object* v_n_237_; lean_object* v___x_238_; lean_object* v___x_239_; uint8_t v___x_240_; 
v_one_236_ = lean_unsigned_to_nat(1u);
v_n_237_ = lean_nat_sub(v_x_233_, v_one_236_);
lean_dec(v_x_233_);
v___x_238_ = lean_array_fget_borrowed(v_xs_231_, v_n_237_);
v___x_239_ = lean_array_fget_borrowed(v_ys_232_, v_n_237_);
v___x_240_ = lean_name_eq(v___x_238_, v___x_239_);
if (v___x_240_ == 0)
{
lean_dec(v_n_237_);
return v___x_240_;
}
else
{
v_x_233_ = v_n_237_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00Lean_Meta_Match_registerMatchEqns_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_231_ = stack[0].m_obj;
lean_object* v_ys_232_ = stack[1].m_obj;
lean_object* v_x_233_ = stack[2].m_obj;
uint8_t v_res_242_;
v_res_242_ = l_Array_isEqvAux___at___00Lean_Meta_Match_registerMatchEqns_spec__4___redArg(v_xs_231_, v_ys_232_, v_x_233_);
stack->m_num = v_res_242_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Meta_Match_registerMatchEqns_spec__4___redArg___boxed(lean_object* v_xs_243_, lean_object* v_ys_244_, lean_object* v_x_245_){
_start:
{
uint8_t v_res_246_; lean_object* v_r_247_; 
v_res_246_ = l_Array_isEqvAux___at___00Lean_Meta_Match_registerMatchEqns_spec__4___redArg(v_xs_243_, v_ys_244_, v_x_245_);
lean_dec_ref(v_ys_244_);
lean_dec_ref(v_xs_243_);
v_r_247_ = lean_box(v_res_246_);
return v_r_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2_spec__6___redArg(lean_object* v_x_248_, lean_object* v_x_249_, lean_object* v_x_250_, lean_object* v_x_251_){
_start:
{
lean_object* v_ks_252_; lean_object* v_vs_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_277_; 
v_ks_252_ = lean_ctor_get(v_x_248_, 0);
v_vs_253_ = lean_ctor_get(v_x_248_, 1);
v_isSharedCheck_277_ = !lean_is_exclusive(v_x_248_);
if (v_isSharedCheck_277_ == 0)
{
v___x_255_ = v_x_248_;
v_isShared_256_ = v_isSharedCheck_277_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_vs_253_);
lean_inc(v_ks_252_);
lean_dec(v_x_248_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_277_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_257_ = lean_array_get_size(v_ks_252_);
v___x_258_ = lean_nat_dec_lt(v_x_249_, v___x_257_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_262_; 
lean_dec(v_x_249_);
v___x_259_ = lean_array_push(v_ks_252_, v_x_250_);
v___x_260_ = lean_array_push(v_vs_253_, v_x_251_);
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 1, v___x_260_);
lean_ctor_set(v___x_255_, 0, v___x_259_);
v___x_262_ = v___x_255_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_259_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v___x_260_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
else
{
lean_object* v_k_x27_264_; uint8_t v___x_265_; 
v_k_x27_264_ = lean_array_fget_borrowed(v_ks_252_, v_x_249_);
v___x_265_ = lean_name_eq(v_x_250_, v_k_x27_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_267_; 
if (v_isShared_256_ == 0)
{
v___x_267_ = v___x_255_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_ks_252_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v_vs_253_);
v___x_267_ = v_reuseFailAlloc_271_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = lean_unsigned_to_nat(1u);
v___x_269_ = lean_nat_add(v_x_249_, v___x_268_);
lean_dec(v_x_249_);
v_x_248_ = v___x_267_;
v_x_249_ = v___x_269_;
goto _start;
}
}
else
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_275_; 
v___x_272_ = lean_array_fset(v_ks_252_, v_x_249_, v_x_250_);
v___x_273_ = lean_array_fset(v_vs_253_, v_x_249_, v_x_251_);
lean_dec(v_x_249_);
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 1, v___x_273_);
lean_ctor_set(v___x_255_, 0, v___x_272_);
v___x_275_ = v___x_255_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_272_);
lean_ctor_set(v_reuseFailAlloc_276_, 1, v___x_273_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg(lean_object* v_n_278_, lean_object* v_k_279_, lean_object* v_v_280_){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = lean_unsigned_to_nat(0u);
v___x_282_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2_spec__6___redArg(v_n_278_, v___x_281_, v_k_279_, v_v_280_);
return v___x_282_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_283_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg(lean_object* v_x_284_, size_t v_x_285_, size_t v_x_286_, lean_object* v_x_287_, lean_object* v_x_288_){
_start:
{
if (lean_obj_tag(v_x_284_) == 0)
{
lean_object* v_es_289_; size_t v___x_290_; size_t v___x_291_; lean_object* v_j_292_; lean_object* v___x_293_; uint8_t v___x_294_; 
v_es_289_ = lean_ctor_get(v_x_284_, 0);
v___x_290_ = ((size_t)31ULL);
v___x_291_ = lean_usize_land(v_x_285_, v___x_290_);
v_j_292_ = lean_usize_to_nat(v___x_291_);
v___x_293_ = lean_array_get_size(v_es_289_);
v___x_294_ = lean_nat_dec_lt(v_j_292_, v___x_293_);
if (v___x_294_ == 0)
{
lean_dec(v_j_292_);
lean_dec(v_x_288_);
lean_dec(v_x_287_);
return v_x_284_;
}
else
{
lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_333_; 
lean_inc_ref(v_es_289_);
v_isSharedCheck_333_ = !lean_is_exclusive(v_x_284_);
if (v_isSharedCheck_333_ == 0)
{
lean_object* v_unused_334_; 
v_unused_334_ = lean_ctor_get(v_x_284_, 0);
lean_dec(v_unused_334_);
v___x_296_ = v_x_284_;
v_isShared_297_ = v_isSharedCheck_333_;
goto v_resetjp_295_;
}
else
{
lean_dec(v_x_284_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_333_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v_v_298_; lean_object* v___x_299_; lean_object* v_xs_x27_300_; lean_object* v___y_302_; 
v_v_298_ = lean_array_fget(v_es_289_, v_j_292_);
v___x_299_ = lean_box(0);
v_xs_x27_300_ = lean_array_fset(v_es_289_, v_j_292_, v___x_299_);
switch(lean_obj_tag(v_v_298_))
{
case 0:
{
lean_object* v_key_307_; lean_object* v_val_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_318_; 
v_key_307_ = lean_ctor_get(v_v_298_, 0);
v_val_308_ = lean_ctor_get(v_v_298_, 1);
v_isSharedCheck_318_ = !lean_is_exclusive(v_v_298_);
if (v_isSharedCheck_318_ == 0)
{
v___x_310_ = v_v_298_;
v_isShared_311_ = v_isSharedCheck_318_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_val_308_);
lean_inc(v_key_307_);
lean_dec(v_v_298_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_318_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
uint8_t v___x_312_; 
v___x_312_ = lean_name_eq(v_x_287_, v_key_307_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; lean_object* v___x_314_; 
lean_del_object(v___x_310_);
v___x_313_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_307_, v_val_308_, v_x_287_, v_x_288_);
v___x_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
v___y_302_ = v___x_314_;
goto v___jp_301_;
}
else
{
lean_object* v___x_316_; 
lean_dec(v_val_308_);
lean_dec(v_key_307_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 1, v_x_288_);
lean_ctor_set(v___x_310_, 0, v_x_287_);
v___x_316_ = v___x_310_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_x_287_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v_x_288_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
v___y_302_ = v___x_316_;
goto v___jp_301_;
}
}
}
}
case 1:
{
lean_object* v_node_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_331_; 
v_node_319_ = lean_ctor_get(v_v_298_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v_v_298_);
if (v_isSharedCheck_331_ == 0)
{
v___x_321_ = v_v_298_;
v_isShared_322_ = v_isSharedCheck_331_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_node_319_);
lean_dec(v_v_298_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_331_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
size_t v___x_323_; size_t v___x_324_; size_t v___x_325_; size_t v___x_326_; lean_object* v___x_327_; lean_object* v___x_329_; 
v___x_323_ = ((size_t)5ULL);
v___x_324_ = lean_usize_shift_right(v_x_285_, v___x_323_);
v___x_325_ = ((size_t)1ULL);
v___x_326_ = lean_usize_add(v_x_286_, v___x_325_);
v___x_327_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg(v_node_319_, v___x_324_, v___x_326_, v_x_287_, v_x_288_);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 0, v___x_327_);
v___x_329_ = v___x_321_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_327_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
v___y_302_ = v___x_329_;
goto v___jp_301_;
}
}
}
default: 
{
lean_object* v___x_332_; 
v___x_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_332_, 0, v_x_287_);
lean_ctor_set(v___x_332_, 1, v_x_288_);
v___y_302_ = v___x_332_;
goto v___jp_301_;
}
}
v___jp_301_:
{
lean_object* v___x_303_; lean_object* v___x_305_; 
v___x_303_ = lean_array_fset(v_xs_x27_300_, v_j_292_, v___y_302_);
lean_dec(v_j_292_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 0, v___x_303_);
v___x_305_ = v___x_296_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v___x_303_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
}
else
{
lean_object* v_ks_335_; lean_object* v_vs_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_354_; 
v_ks_335_ = lean_ctor_get(v_x_284_, 0);
v_vs_336_ = lean_ctor_get(v_x_284_, 1);
v_isSharedCheck_354_ = !lean_is_exclusive(v_x_284_);
if (v_isSharedCheck_354_ == 0)
{
v___x_338_ = v_x_284_;
v_isShared_339_ = v_isSharedCheck_354_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_vs_336_);
lean_inc(v_ks_335_);
lean_dec(v_x_284_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_354_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_341_; 
if (v_isShared_339_ == 0)
{
v___x_341_ = v___x_338_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_ks_335_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v_vs_336_);
v___x_341_ = v_reuseFailAlloc_353_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
lean_object* v_newNode_342_; size_t v___x_343_; uint8_t v___x_344_; 
v_newNode_342_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg(v___x_341_, v_x_287_, v_x_288_);
v___x_343_ = ((size_t)7ULL);
v___x_344_ = lean_usize_dec_le(v___x_343_, v_x_286_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; lean_object* v___x_346_; uint8_t v___x_347_; 
v___x_345_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_342_);
v___x_346_ = lean_unsigned_to_nat(4u);
v___x_347_ = lean_nat_dec_lt(v___x_345_, v___x_346_);
lean_dec(v___x_345_);
if (v___x_347_ == 0)
{
lean_object* v_ks_348_; lean_object* v_vs_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v_ks_348_ = lean_ctor_get(v_newNode_342_, 0);
lean_inc_ref(v_ks_348_);
v_vs_349_ = lean_ctor_get(v_newNode_342_, 1);
lean_inc_ref(v_vs_349_);
lean_dec_ref(v_newNode_342_);
v___x_350_ = lean_unsigned_to_nat(0u);
v___x_351_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__0);
v___x_352_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__3___redArg(v_x_286_, v_ks_348_, v_vs_349_, v___x_350_, v___x_351_);
lean_dec_ref(v_vs_349_);
lean_dec_ref(v_ks_348_);
return v___x_352_;
}
else
{
return v_newNode_342_;
}
}
else
{
return v_newNode_342_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_284_ = stack[0].m_obj;
size_t v_x_285_ = stack[1].m_num;
size_t v_x_286_ = stack[2].m_num;
lean_object* v_x_287_ = stack[3].m_obj;
lean_object* v_x_288_ = stack[4].m_obj;
lean_object* v_res_355_;
v_res_355_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg(v_x_284_, v_x_285_, v_x_286_, v_x_287_, v_x_288_);
stack->m_obj
 = v_res_355_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__3___redArg(size_t v_depth_356_, lean_object* v_keys_357_, lean_object* v_vals_358_, lean_object* v_i_359_, lean_object* v_entries_360_){
_start:
{
lean_object* v___x_361_; uint8_t v___x_362_; 
v___x_361_ = lean_array_get_size(v_keys_357_);
v___x_362_ = lean_nat_dec_lt(v_i_359_, v___x_361_);
if (v___x_362_ == 0)
{
lean_dec(v_i_359_);
return v_entries_360_;
}
else
{
lean_object* v_k_363_; lean_object* v_v_364_; uint64_t v___y_366_; 
v_k_363_ = lean_array_fget_borrowed(v_keys_357_, v_i_359_);
v_v_364_ = lean_array_fget_borrowed(v_vals_358_, v_i_359_);
if (lean_obj_tag(v_k_363_) == 0)
{
uint64_t v___x_377_; 
v___x_377_ = 1723ULL;
v___y_366_ = v___x_377_;
goto v___jp_365_;
}
else
{
uint64_t v_hash_378_; 
v_hash_378_ = lean_ctor_get_uint64(v_k_363_, sizeof(void*)*2);
v___y_366_ = v_hash_378_;
goto v___jp_365_;
}
v___jp_365_:
{
size_t v_h_367_; size_t v___x_368_; lean_object* v___x_369_; size_t v___x_370_; size_t v___x_371_; size_t v___x_372_; size_t v_h_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v_h_367_ = lean_uint64_to_usize(v___y_366_);
v___x_368_ = ((size_t)5ULL);
v___x_369_ = lean_unsigned_to_nat(1u);
v___x_370_ = ((size_t)1ULL);
v___x_371_ = lean_usize_sub(v_depth_356_, v___x_370_);
v___x_372_ = lean_usize_mul(v___x_368_, v___x_371_);
v_h_373_ = lean_usize_shift_right(v_h_367_, v___x_372_);
v___x_374_ = lean_nat_add(v_i_359_, v___x_369_);
lean_dec(v_i_359_);
lean_inc(v_v_364_);
lean_inc(v_k_363_);
v___x_375_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg(v_entries_360_, v_h_373_, v_depth_356_, v_k_363_, v_v_364_);
v_i_359_ = v___x_374_;
v_entries_360_ = v___x_375_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_356_ = stack[0].m_num;
lean_object* v_keys_357_ = stack[1].m_obj;
lean_object* v_vals_358_ = stack[2].m_obj;
lean_object* v_i_359_ = stack[3].m_obj;
lean_object* v_entries_360_ = stack[4].m_obj;
lean_object* v_res_379_;
v_res_379_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__3___redArg(v_depth_356_, v_keys_357_, v_vals_358_, v_i_359_, v_entries_360_);
stack->m_obj
 = v_res_379_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_380_, lean_object* v_keys_381_, lean_object* v_vals_382_, lean_object* v_i_383_, lean_object* v_entries_384_){
_start:
{
size_t v_depth_boxed_385_; lean_object* v_res_386_; 
v_depth_boxed_385_ = lean_unbox_usize(v_depth_380_);
lean_dec(v_depth_380_);
v_res_386_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__3___redArg(v_depth_boxed_385_, v_keys_381_, v_vals_382_, v_i_383_, v_entries_384_);
lean_dec_ref(v_vals_382_);
lean_dec_ref(v_keys_381_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___boxed(lean_object* v_x_387_, lean_object* v_x_388_, lean_object* v_x_389_, lean_object* v_x_390_, lean_object* v_x_391_){
_start:
{
size_t v_x_1186__boxed_392_; size_t v_x_1187__boxed_393_; lean_object* v_res_394_; 
v_x_1186__boxed_392_ = lean_unbox_usize(v_x_388_);
lean_dec(v_x_388_);
v_x_1187__boxed_393_ = lean_unbox_usize(v_x_389_);
lean_dec(v_x_389_);
v_res_394_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg(v_x_387_, v_x_1186__boxed_392_, v_x_1187__boxed_393_, v_x_390_, v_x_391_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0___redArg(lean_object* v_x_395_, lean_object* v_x_396_, lean_object* v_x_397_){
_start:
{
uint64_t v___y_399_; 
if (lean_obj_tag(v_x_396_) == 0)
{
uint64_t v___x_403_; 
v___x_403_ = 1723ULL;
v___y_399_ = v___x_403_;
goto v___jp_398_;
}
else
{
uint64_t v_hash_404_; 
v_hash_404_ = lean_ctor_get_uint64(v_x_396_, sizeof(void*)*2);
v___y_399_ = v_hash_404_;
goto v___jp_398_;
}
v___jp_398_:
{
size_t v___x_400_; size_t v___x_401_; lean_object* v___x_402_; 
v___x_400_ = lean_uint64_to_usize(v___y_399_);
v___x_401_ = ((size_t)1ULL);
v___x_402_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg(v_x_395_, v___x_400_, v___x_401_, v_x_396_, v_x_397_);
return v___x_402_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4_spec__7___redArg(lean_object* v_keys_405_, lean_object* v_vals_406_, lean_object* v_i_407_, lean_object* v_k_408_){
_start:
{
lean_object* v___x_409_; uint8_t v___x_410_; 
v___x_409_ = lean_array_get_size(v_keys_405_);
v___x_410_ = lean_nat_dec_lt(v_i_407_, v___x_409_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; 
lean_dec(v_i_407_);
v___x_411_ = lean_box(0);
return v___x_411_;
}
else
{
lean_object* v_k_x27_412_; uint8_t v___x_413_; 
v_k_x27_412_ = lean_array_fget_borrowed(v_keys_405_, v_i_407_);
v___x_413_ = lean_name_eq(v_k_408_, v_k_x27_412_);
if (v___x_413_ == 0)
{
lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_414_ = lean_unsigned_to_nat(1u);
v___x_415_ = lean_nat_add(v_i_407_, v___x_414_);
lean_dec(v_i_407_);
v_i_407_ = v___x_415_;
goto _start;
}
else
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = lean_array_fget_borrowed(v_vals_406_, v_i_407_);
lean_dec(v_i_407_);
lean_inc(v___x_417_);
v___x_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
return v___x_418_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_keys_419_, lean_object* v_vals_420_, lean_object* v_i_421_, lean_object* v_k_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4_spec__7___redArg(v_keys_419_, v_vals_420_, v_i_421_, v_k_422_);
lean_dec(v_k_422_);
lean_dec_ref(v_vals_420_);
lean_dec_ref(v_keys_419_);
return v_res_423_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4___redArg(lean_object* v_x_424_, size_t v_x_425_, lean_object* v_x_426_){
_start:
{
if (lean_obj_tag(v_x_424_) == 0)
{
lean_object* v_es_427_; lean_object* v___x_428_; size_t v___x_429_; size_t v___x_430_; lean_object* v_j_431_; lean_object* v___x_432_; 
v_es_427_ = lean_ctor_get(v_x_424_, 0);
v___x_428_ = lean_box(2);
v___x_429_ = ((size_t)31ULL);
v___x_430_ = lean_usize_land(v_x_425_, v___x_429_);
v_j_431_ = lean_usize_to_nat(v___x_430_);
v___x_432_ = lean_array_get_borrowed(v___x_428_, v_es_427_, v_j_431_);
lean_dec(v_j_431_);
switch(lean_obj_tag(v___x_432_))
{
case 0:
{
lean_object* v_key_433_; lean_object* v_val_434_; uint8_t v___x_435_; 
v_key_433_ = lean_ctor_get(v___x_432_, 0);
v_val_434_ = lean_ctor_get(v___x_432_, 1);
v___x_435_ = lean_name_eq(v_x_426_, v_key_433_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; 
v___x_436_ = lean_box(0);
return v___x_436_;
}
else
{
lean_object* v___x_437_; 
lean_inc(v_val_434_);
v___x_437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_437_, 0, v_val_434_);
return v___x_437_;
}
}
case 1:
{
lean_object* v_node_438_; size_t v___x_439_; size_t v___x_440_; 
v_node_438_ = lean_ctor_get(v___x_432_, 0);
v___x_439_ = ((size_t)5ULL);
v___x_440_ = lean_usize_shift_right(v_x_425_, v___x_439_);
v_x_424_ = v_node_438_;
v_x_425_ = v___x_440_;
goto _start;
}
default: 
{
lean_object* v___x_442_; 
v___x_442_ = lean_box(0);
return v___x_442_;
}
}
}
else
{
lean_object* v_ks_443_; lean_object* v_vs_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v_ks_443_ = lean_ctor_get(v_x_424_, 0);
v_vs_444_ = lean_ctor_get(v_x_424_, 1);
v___x_445_ = lean_unsigned_to_nat(0u);
v___x_446_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4_spec__7___redArg(v_ks_443_, v_vs_444_, v___x_445_, v_x_426_);
return v___x_446_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_424_ = stack[0].m_obj;
size_t v_x_425_ = stack[1].m_num;
lean_object* v_x_426_ = stack[2].m_obj;
lean_object* v_res_447_;
v_res_447_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4___redArg(v_x_424_, v_x_425_, v_x_426_);
stack->m_obj
 = v_res_447_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4___redArg___boxed(lean_object* v_x_448_, lean_object* v_x_449_, lean_object* v_x_450_){
_start:
{
size_t v_x_1480__boxed_451_; lean_object* v_res_452_; 
v_x_1480__boxed_451_ = lean_unbox_usize(v_x_449_);
lean_dec(v_x_449_);
v_res_452_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4___redArg(v_x_448_, v_x_1480__boxed_451_, v_x_450_);
lean_dec(v_x_450_);
lean_dec_ref(v_x_448_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3___redArg(lean_object* v_x_453_, lean_object* v_x_454_){
_start:
{
uint64_t v___y_456_; 
if (lean_obj_tag(v_x_454_) == 0)
{
uint64_t v___x_459_; 
v___x_459_ = 1723ULL;
v___y_456_ = v___x_459_;
goto v___jp_455_;
}
else
{
uint64_t v_hash_460_; 
v_hash_460_ = lean_ctor_get_uint64(v_x_454_, sizeof(void*)*2);
v___y_456_ = v_hash_460_;
goto v___jp_455_;
}
v___jp_455_:
{
size_t v___x_457_; lean_object* v___x_458_; 
v___x_457_ = lean_uint64_to_usize(v___y_456_);
v___x_458_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4___redArg(v_x_453_, v___x_457_, v_x_454_);
return v___x_458_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3___redArg___boxed(lean_object* v_x_461_, lean_object* v_x_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3___redArg(v_x_461_, v_x_462_);
lean_dec(v_x_462_);
lean_dec_ref(v_x_461_);
return v_res_463_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_registerMatchEqns_spec__1(lean_object* v_as_464_, size_t v_i_465_, size_t v_stop_466_, lean_object* v_b_467_){
_start:
{
uint8_t v___x_468_; 
v___x_468_ = lean_usize_dec_eq(v_i_465_, v_stop_466_);
if (v___x_468_ == 0)
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; size_t v___x_472_; size_t v___x_473_; 
v___x_469_ = lean_array_uget_borrowed(v_as_464_, v_i_465_);
v___x_470_ = lean_box(0);
lean_inc(v___x_469_);
v___x_471_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0___redArg(v_b_467_, v___x_469_, v___x_470_);
v___x_472_ = ((size_t)1ULL);
v___x_473_ = lean_usize_add(v_i_465_, v___x_472_);
v_i_465_ = v___x_473_;
v_b_467_ = v___x_471_;
goto _start;
}
else
{
return v_b_467_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_registerMatchEqns_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_464_ = stack[0].m_obj;
size_t v_i_465_ = stack[1].m_num;
size_t v_stop_466_ = stack[2].m_num;
lean_object* v_b_467_ = stack[3].m_obj;
lean_object* v_res_475_;
v_res_475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_registerMatchEqns_spec__1(v_as_464_, v_i_465_, v_stop_466_, v_b_467_);
stack->m_obj
 = v_res_475_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_registerMatchEqns_spec__1___boxed(lean_object* v_as_476_, lean_object* v_i_477_, lean_object* v_stop_478_, lean_object* v_b_479_){
_start:
{
size_t v_i_boxed_480_; size_t v_stop_boxed_481_; lean_object* v_res_482_; 
v_i_boxed_480_ = lean_unbox_usize(v_i_477_);
lean_dec(v_i_477_);
v_stop_boxed_481_ = lean_unbox_usize(v_stop_478_);
lean_dec(v_stop_478_);
v_res_482_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_registerMatchEqns_spec__1(v_as_476_, v_i_boxed_480_, v_stop_boxed_481_, v_b_479_);
lean_dec_ref(v_as_476_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_registerMatchEqns___redArg___lam__0(lean_object* v_matchEqns_487_, lean_object* v_matchDeclName_488_, lean_object* v_x_489_){
_start:
{
lean_object* v_map_490_; lean_object* v_eqns_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_542_; 
v_map_490_ = lean_ctor_get(v_x_489_, 0);
v_eqns_491_ = lean_ctor_get(v_x_489_, 1);
v_isSharedCheck_542_ = !lean_is_exclusive(v_x_489_);
if (v_isSharedCheck_542_ == 0)
{
v___x_493_ = v_x_489_;
v_isShared_494_ = v_isSharedCheck_542_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_eqns_491_);
lean_inc(v_map_490_);
lean_dec(v_x_489_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_542_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___y_496_; lean_object* v___x_533_; 
v___x_533_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3___redArg(v_map_490_, v_matchDeclName_488_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_object* v___x_534_; 
lean_inc_ref(v_matchEqns_487_);
v___x_534_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0___redArg(v_map_490_, v_matchDeclName_488_, v_matchEqns_487_);
v___y_496_ = v___x_534_;
goto v___jp_495_;
}
else
{
lean_object* v_val_535_; lean_object* v_eqnNames_536_; lean_object* v_eqnNames_537_; lean_object* v___x_538_; lean_object* v___x_539_; uint8_t v___x_540_; 
v_val_535_ = lean_ctor_get(v___x_533_, 0);
lean_inc(v_val_535_);
lean_dec_ref_known(v___x_533_, 1);
v_eqnNames_536_ = lean_ctor_get(v_val_535_, 0);
lean_inc_ref(v_eqnNames_536_);
lean_dec(v_val_535_);
v_eqnNames_537_ = lean_ctor_get(v_matchEqns_487_, 0);
v___x_538_ = lean_array_get_size(v_eqnNames_536_);
v___x_539_ = lean_array_get_size(v_eqnNames_537_);
v___x_540_ = lean_nat_dec_eq(v___x_538_, v___x_539_);
if (v___x_540_ == 0)
{
lean_dec_ref(v_eqnNames_536_);
goto v___jp_520_;
}
else
{
uint8_t v___x_541_; 
v___x_541_ = l_Array_isEqvAux___at___00Lean_Meta_Match_registerMatchEqns_spec__4___redArg(v_eqnNames_536_, v_eqnNames_537_, v___x_538_);
lean_dec_ref(v_eqnNames_536_);
if (v___x_541_ == 0)
{
goto v___jp_520_;
}
else
{
lean_dec(v_matchDeclName_488_);
v___y_496_ = v_map_490_;
goto v___jp_495_;
}
}
}
v___jp_495_:
{
lean_object* v_eqnNames_497_; lean_object* v___x_498_; lean_object* v___x_499_; uint8_t v___x_500_; 
v_eqnNames_497_ = lean_ctor_get(v_matchEqns_487_, 0);
lean_inc_ref(v_eqnNames_497_);
lean_dec_ref(v_matchEqns_487_);
v___x_498_ = lean_unsigned_to_nat(0u);
v___x_499_ = lean_array_get_size(v_eqnNames_497_);
v___x_500_ = lean_nat_dec_lt(v___x_498_, v___x_499_);
if (v___x_500_ == 0)
{
lean_object* v___x_502_; 
lean_dec_ref(v_eqnNames_497_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 0, v___y_496_);
v___x_502_ = v___x_493_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v___y_496_);
lean_ctor_set(v_reuseFailAlloc_503_, 1, v_eqns_491_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
else
{
uint8_t v___x_504_; 
v___x_504_ = lean_nat_dec_le(v___x_499_, v___x_499_);
if (v___x_504_ == 0)
{
if (v___x_500_ == 0)
{
lean_object* v___x_506_; 
lean_dec_ref(v_eqnNames_497_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 0, v___y_496_);
v___x_506_ = v___x_493_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___y_496_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v_eqns_491_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
else
{
size_t v___x_508_; size_t v___x_509_; lean_object* v___x_510_; lean_object* v___x_512_; 
v___x_508_ = ((size_t)0ULL);
v___x_509_ = lean_usize_of_nat(v___x_499_);
v___x_510_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_registerMatchEqns_spec__1(v_eqnNames_497_, v___x_508_, v___x_509_, v_eqns_491_);
lean_dec_ref(v_eqnNames_497_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 1, v___x_510_);
lean_ctor_set(v___x_493_, 0, v___y_496_);
v___x_512_ = v___x_493_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___y_496_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v___x_510_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
else
{
size_t v___x_514_; size_t v___x_515_; lean_object* v___x_516_; lean_object* v___x_518_; 
v___x_514_ = ((size_t)0ULL);
v___x_515_ = lean_usize_of_nat(v___x_499_);
v___x_516_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_registerMatchEqns_spec__1(v_eqnNames_497_, v___x_514_, v___x_515_, v_eqns_491_);
lean_dec_ref(v_eqnNames_497_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 1, v___x_516_);
lean_ctor_set(v___x_493_, 0, v___y_496_);
v___x_518_ = v___x_493_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___y_496_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v___x_516_);
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
v___jp_520_:
{
uint8_t v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_521_ = 1;
v___x_522_ = ((lean_object*)(l_Lean_Meta_Match_registerMatchEqns___redArg___lam__0___closed__0));
v___x_523_ = ((lean_object*)(l_Lean_Meta_Match_registerMatchEqns___redArg___lam__0___closed__1));
v___x_524_ = lean_unsigned_to_nat(49u);
v___x_525_ = lean_unsigned_to_nat(10u);
v___x_526_ = ((lean_object*)(l_Lean_Meta_Match_registerMatchEqns___redArg___lam__0___closed__2));
v___x_527_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_matchDeclName_488_, v___x_521_);
v___x_528_ = lean_string_append(v___x_526_, v___x_527_);
lean_dec_ref(v___x_527_);
v___x_529_ = ((lean_object*)(l_Lean_Meta_Match_registerMatchEqns___redArg___lam__0___closed__3));
v___x_530_ = lean_string_append(v___x_528_, v___x_529_);
v___x_531_ = l_mkPanicMessageWithDecl(v___x_522_, v___x_523_, v___x_524_, v___x_525_, v___x_530_);
lean_dec_ref(v___x_530_);
v___x_532_ = lean_panic_fn_borrowed(v_map_490_, v___x_531_);
lean_dec_ref(v_map_490_);
v___y_496_ = v___x_532_;
goto v___jp_495_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_registerMatchEqns___redArg___closed__0(void){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___redArg___closed__0);
v___x_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
return v___x_544_;
}
}
static lean_object* _init_l_Lean_Meta_Match_registerMatchEqns___redArg___closed__1(void){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = lean_obj_once(&l_Lean_Meta_Match_registerMatchEqns___redArg___closed__0, &l_Lean_Meta_Match_registerMatchEqns___redArg___closed__0_once, _init_l_Lean_Meta_Match_registerMatchEqns___redArg___closed__0);
v___x_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
lean_ctor_set(v___x_546_, 1, v___x_545_);
return v___x_546_;
}
}
lean_object* l_Lean_Meta_Match_registerMatchEqns___redArg(lean_object* v_matchDeclName_547_, lean_object* v_matchEqns_548_, lean_object* v_a_549_){
_start:
{
lean_object* v___f_551_; lean_object* v___x_552_; lean_object* v_env_553_; lean_object* v_nextMacroScope_554_; lean_object* v_ngen_555_; lean_object* v_auxDeclNGen_556_; lean_object* v_traceState_557_; lean_object* v_recordedDeps_558_; lean_object* v_messages_559_; lean_object* v_infoState_560_; lean_object* v_snapshotTasks_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_577_; 
v___f_551_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_registerMatchEqns___redArg___lam__0), 3, 2);
lean_closure_set(v___f_551_, 0, v_matchEqns_548_);
lean_closure_set(v___f_551_, 1, v_matchDeclName_547_);
v___x_552_ = lean_st_ref_take(v_a_549_);
v_env_553_ = lean_ctor_get(v___x_552_, 0);
v_nextMacroScope_554_ = lean_ctor_get(v___x_552_, 1);
v_ngen_555_ = lean_ctor_get(v___x_552_, 2);
v_auxDeclNGen_556_ = lean_ctor_get(v___x_552_, 3);
v_traceState_557_ = lean_ctor_get(v___x_552_, 4);
v_recordedDeps_558_ = lean_ctor_get(v___x_552_, 6);
v_messages_559_ = lean_ctor_get(v___x_552_, 7);
v_infoState_560_ = lean_ctor_get(v___x_552_, 8);
v_snapshotTasks_561_ = lean_ctor_get(v___x_552_, 9);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_577_ == 0)
{
lean_object* v_unused_578_; 
v_unused_578_ = lean_ctor_get(v___x_552_, 5);
lean_dec(v_unused_578_);
v___x_563_ = v___x_552_;
v_isShared_564_ = v_isSharedCheck_577_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_snapshotTasks_561_);
lean_inc(v_infoState_560_);
lean_inc(v_messages_559_);
lean_inc(v_recordedDeps_558_);
lean_inc(v_traceState_557_);
lean_inc(v_auxDeclNGen_556_);
lean_inc(v_ngen_555_);
lean_inc(v_nextMacroScope_554_);
lean_inc(v_env_553_);
lean_dec(v___x_552_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_577_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_565_; lean_object* v_asyncMode_566_; lean_object* v___x_567_; lean_object* v___x_568_; uint8_t v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_573_; 
v___x_565_ = l_Lean_Meta_Match_matchEqnsExt;
v_asyncMode_566_ = lean_ctor_get(v___x_565_, 2);
v___x_567_ = lean_box(0);
v___x_568_ = lean_box(0);
v___x_569_ = 1;
v___x_570_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_565_, v_env_553_, v___f_551_, v_asyncMode_566_, v___x_568_, v___x_569_);
v___x_571_ = lean_obj_once(&l_Lean_Meta_Match_registerMatchEqns___redArg___closed__1, &l_Lean_Meta_Match_registerMatchEqns___redArg___closed__1_once, _init_l_Lean_Meta_Match_registerMatchEqns___redArg___closed__1);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 5, v___x_571_);
lean_ctor_set(v___x_563_, 0, v___x_570_);
v___x_573_ = v___x_563_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_570_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v_nextMacroScope_554_);
lean_ctor_set(v_reuseFailAlloc_576_, 2, v_ngen_555_);
lean_ctor_set(v_reuseFailAlloc_576_, 3, v_auxDeclNGen_556_);
lean_ctor_set(v_reuseFailAlloc_576_, 4, v_traceState_557_);
lean_ctor_set(v_reuseFailAlloc_576_, 5, v___x_571_);
lean_ctor_set(v_reuseFailAlloc_576_, 6, v_recordedDeps_558_);
lean_ctor_set(v_reuseFailAlloc_576_, 7, v_messages_559_);
lean_ctor_set(v_reuseFailAlloc_576_, 8, v_infoState_560_);
lean_ctor_set(v_reuseFailAlloc_576_, 9, v_snapshotTasks_561_);
v___x_573_ = v_reuseFailAlloc_576_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = lean_st_ref_put(v_a_549_, v___x_573_);
v___x_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_575_, 0, v___x_567_);
return v___x_575_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Match_registerMatchEqns___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_matchDeclName_547_ = stack[0].m_obj;
lean_object* v_matchEqns_548_ = stack[1].m_obj;
lean_object* v_a_549_ = stack[2].m_obj;
lean_object* v_res_579_;
v_res_579_ = l_Lean_Meta_Match_registerMatchEqns___redArg(v_matchDeclName_547_, v_matchEqns_548_, v_a_549_);
stack->m_obj
 = v_res_579_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_registerMatchEqns___redArg___boxed(lean_object* v_matchDeclName_580_, lean_object* v_matchEqns_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Lean_Meta_Match_registerMatchEqns___redArg(v_matchDeclName_580_, v_matchEqns_581_, v_a_582_);
lean_dec(v_a_582_);
return v_res_584_;
}
}
lean_object* l_Lean_Meta_Match_registerMatchEqns(lean_object* v_matchDeclName_585_, lean_object* v_matchEqns_586_, lean_object* v_a_587_, lean_object* v_a_588_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Lean_Meta_Match_registerMatchEqns___redArg(v_matchDeclName_585_, v_matchEqns_586_, v_a_588_);
return v___x_590_;
}
}
LEAN_EXPORT void l_Lean_Meta_Match_registerMatchEqns_0interp(lean_interpreter_value* stack)
{
lean_object* v_matchDeclName_585_ = stack[0].m_obj;
lean_object* v_matchEqns_586_ = stack[1].m_obj;
lean_object* v_a_587_ = stack[2].m_obj;
lean_object* v_a_588_ = stack[3].m_obj;
lean_object* v_res_591_;
v_res_591_ = l_Lean_Meta_Match_registerMatchEqns(v_matchDeclName_585_, v_matchEqns_586_, v_a_587_, v_a_588_);
stack->m_obj
 = v_res_591_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_registerMatchEqns___boxed(lean_object* v_matchDeclName_592_, lean_object* v_matchEqns_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Lean_Meta_Match_registerMatchEqns(v_matchDeclName_592_, v_matchEqns_593_, v_a_594_, v_a_595_);
lean_dec(v_a_595_);
lean_dec_ref(v_a_594_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0(lean_object* v_00_u03b2_598_, lean_object* v_x_599_, lean_object* v_x_600_, lean_object* v_x_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0___redArg(v_x_599_, v_x_600_, v_x_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3(lean_object* v_00_u03b2_603_, lean_object* v_x_604_, lean_object* v_x_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3___redArg(v_x_604_, v_x_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3___boxed(lean_object* v_00_u03b2_607_, lean_object* v_x_608_, lean_object* v_x_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3(v_00_u03b2_607_, v_x_608_, v_x_609_);
lean_dec(v_x_609_);
lean_dec_ref(v_x_608_);
return v_res_610_;
}
}
uint8_t l_Array_isEqvAux___at___00Lean_Meta_Match_registerMatchEqns_spec__4(lean_object* v_xs_611_, lean_object* v_ys_612_, lean_object* v_hsz_613_, lean_object* v_x_614_, lean_object* v_x_615_){
_start:
{
uint8_t v___x_616_; 
v___x_616_ = l_Array_isEqvAux___at___00Lean_Meta_Match_registerMatchEqns_spec__4___redArg(v_xs_611_, v_ys_612_, v_x_614_);
return v___x_616_;
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00Lean_Meta_Match_registerMatchEqns_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_611_ = stack[0].m_obj;
lean_object* v_ys_612_ = stack[1].m_obj;
lean_object* v_x_614_ = stack[3].m_obj;
uint8_t v_res_617_;
v_res_617_ = l_Array_isEqvAux___at___00Lean_Meta_Match_registerMatchEqns_spec__4(v_xs_611_, v_ys_612_, lean_box(0), v_x_614_, lean_box(0));
stack->m_num = v_res_617_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Meta_Match_registerMatchEqns_spec__4___boxed(lean_object* v_xs_618_, lean_object* v_ys_619_, lean_object* v_hsz_620_, lean_object* v_x_621_, lean_object* v_x_622_){
_start:
{
uint8_t v_res_623_; lean_object* v_r_624_; 
v_res_623_ = l_Array_isEqvAux___at___00Lean_Meta_Match_registerMatchEqns_spec__4(v_xs_618_, v_ys_619_, v_hsz_620_, v_x_621_, v_x_622_);
lean_dec_ref(v_ys_619_);
lean_dec_ref(v_xs_618_);
v_r_624_ = lean_box(v_res_623_);
return v_r_624_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0(lean_object* v_00_u03b2_625_, lean_object* v_x_626_, size_t v_x_627_, size_t v_x_628_, lean_object* v_x_629_, lean_object* v_x_630_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg(v_x_626_, v_x_627_, v_x_628_, v_x_629_, v_x_630_);
return v___x_631_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_626_ = stack[1].m_obj;
size_t v_x_627_ = stack[2].m_num;
size_t v_x_628_ = stack[3].m_num;
lean_object* v_x_629_ = stack[4].m_obj;
lean_object* v_x_630_ = stack[5].m_obj;
lean_object* v_res_632_;
v_res_632_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0(lean_box(0), v_x_626_, v_x_627_, v_x_628_, v_x_629_, v_x_630_);
stack->m_obj
 = v_res_632_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___boxed(lean_object* v_00_u03b2_633_, lean_object* v_x_634_, lean_object* v_x_635_, lean_object* v_x_636_, lean_object* v_x_637_, lean_object* v_x_638_){
_start:
{
size_t v_x_1892__boxed_639_; size_t v_x_1893__boxed_640_; lean_object* v_res_641_; 
v_x_1892__boxed_639_ = lean_unbox_usize(v_x_635_);
lean_dec(v_x_635_);
v_x_1893__boxed_640_ = lean_unbox_usize(v_x_636_);
lean_dec(v_x_636_);
v_res_641_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0(v_00_u03b2_633_, v_x_634_, v_x_1892__boxed_639_, v_x_1893__boxed_640_, v_x_637_, v_x_638_);
return v_res_641_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4(lean_object* v_00_u03b2_642_, lean_object* v_x_643_, size_t v_x_644_, lean_object* v_x_645_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4___redArg(v_x_643_, v_x_644_, v_x_645_);
return v___x_646_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_643_ = stack[1].m_obj;
size_t v_x_644_ = stack[2].m_num;
lean_object* v_x_645_ = stack[3].m_obj;
lean_object* v_res_647_;
v_res_647_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4(lean_box(0), v_x_643_, v_x_644_, v_x_645_);
stack->m_obj
 = v_res_647_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4___boxed(lean_object* v_00_u03b2_648_, lean_object* v_x_649_, lean_object* v_x_650_, lean_object* v_x_651_){
_start:
{
size_t v_x_1920__boxed_652_; lean_object* v_res_653_; 
v_x_1920__boxed_652_ = lean_unbox_usize(v_x_650_);
lean_dec(v_x_650_);
v_res_653_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4(v_00_u03b2_648_, v_x_649_, v_x_1920__boxed_652_, v_x_651_);
lean_dec(v_x_651_);
lean_dec_ref(v_x_649_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_654_, lean_object* v_n_655_, lean_object* v_k_656_, lean_object* v_v_657_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg(v_n_655_, v_k_656_, v_v_657_);
return v___x_658_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_659_, size_t v_depth_660_, lean_object* v_keys_661_, lean_object* v_vals_662_, lean_object* v_heq_663_, lean_object* v_i_664_, lean_object* v_entries_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__3___redArg(v_depth_660_, v_keys_661_, v_vals_662_, v_i_664_, v_entries_665_);
return v___x_666_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_depth_660_ = stack[1].m_num;
lean_object* v_keys_661_ = stack[2].m_obj;
lean_object* v_vals_662_ = stack[3].m_obj;
lean_object* v_i_664_ = stack[5].m_obj;
lean_object* v_entries_665_ = stack[6].m_obj;
lean_object* v_res_667_;
v_res_667_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__3(lean_box(0), v_depth_660_, v_keys_661_, v_vals_662_, lean_box(0), v_i_664_, v_entries_665_);
stack->m_obj
 = v_res_667_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_668_, lean_object* v_depth_669_, lean_object* v_keys_670_, lean_object* v_vals_671_, lean_object* v_heq_672_, lean_object* v_i_673_, lean_object* v_entries_674_){
_start:
{
size_t v_depth_boxed_675_; lean_object* v_res_676_; 
v_depth_boxed_675_ = lean_unbox_usize(v_depth_669_);
lean_dec(v_depth_669_);
v_res_676_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__3(v_00_u03b2_668_, v_depth_boxed_675_, v_keys_670_, v_vals_671_, v_heq_672_, v_i_673_, v_entries_674_);
lean_dec_ref(v_vals_671_);
lean_dec_ref(v_keys_670_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4_spec__7(lean_object* v_00_u03b2_677_, lean_object* v_keys_678_, lean_object* v_vals_679_, lean_object* v_heq_680_, lean_object* v_i_681_, lean_object* v_k_682_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4_spec__7___redArg(v_keys_678_, v_vals_679_, v_i_681_, v_k_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b2_684_, lean_object* v_keys_685_, lean_object* v_vals_686_, lean_object* v_heq_687_, lean_object* v_i_688_, lean_object* v_k_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4_spec__7(v_00_u03b2_684_, v_keys_685_, v_vals_686_, v_heq_687_, v_i_688_, v_k_689_);
lean_dec(v_k_689_);
lean_dec_ref(v_vals_686_);
lean_dec_ref(v_keys_685_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_691_, lean_object* v_x_692_, lean_object* v_x_693_, lean_object* v_x_694_, lean_object* v_x_695_){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2_spec__6___redArg(v_x_692_, v_x_693_, v_x_694_, v_x_695_);
return v___x_696_;
}
}
LEAN_EXPORT void l_Lean_Meta_Match_getEquationsFor_0interp(lean_interpreter_value* stack)
{
lean_object* v_matchDeclName_697_ = stack[0].m_obj;
lean_object* v_a_698_ = stack[1].m_obj;
lean_object* v_a_699_ = stack[2].m_obj;
lean_object* v_a_700_ = stack[3].m_obj;
lean_object* v_a_701_ = stack[4].m_obj;
lean_object* v_res_703_;
v_res_703_ = lean_get_match_equations_for(v_matchDeclName_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_);
stack->m_obj
 = v_res_703_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getEquationsFor___boxed(lean_object* v_matchDeclName_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_00___x40___internal___hyg_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = lean_get_match_equations_for(v_matchDeclName_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
return v_res_710_;
}
}
LEAN_EXPORT void l_Lean_Meta_Match_genMatchCongrEqns_0interp(lean_interpreter_value* stack)
{
lean_object* v_matchDeclName_711_ = stack[0].m_obj;
lean_object* v_a_712_ = stack[1].m_obj;
lean_object* v_a_713_ = stack[2].m_obj;
lean_object* v_a_714_ = stack[3].m_obj;
lean_object* v_a_715_ = stack[4].m_obj;
lean_object* v_res_717_;
v_res_717_ = lean_get_congr_match_equations_for(v_matchDeclName_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
stack->m_obj
 = v_res_717_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_genMatchCongrEqns___boxed(lean_object* v_matchDeclName_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_00___x40___internal___hyg_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = lean_get_congr_match_equations_for(v_matchDeclName_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_);
return v_res_724_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_725_, lean_object* v_i_726_, lean_object* v_k_727_){
_start:
{
lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_728_ = lean_array_get_size(v_keys_725_);
v___x_729_ = lean_nat_dec_lt(v_i_726_, v___x_728_);
if (v___x_729_ == 0)
{
lean_dec(v_i_726_);
return v___x_729_;
}
else
{
lean_object* v_k_x27_730_; uint8_t v___x_731_; 
v_k_x27_730_ = lean_array_fget_borrowed(v_keys_725_, v_i_726_);
v___x_731_ = lean_name_eq(v_k_727_, v_k_x27_730_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = lean_unsigned_to_nat(1u);
v___x_733_ = lean_nat_add(v_i_726_, v___x_732_);
lean_dec(v_i_726_);
v_i_726_ = v___x_733_;
goto _start;
}
else
{
lean_dec(v_i_726_);
return v___x_729_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_725_ = stack[0].m_obj;
lean_object* v_i_726_ = stack[1].m_obj;
lean_object* v_k_727_ = stack[2].m_obj;
uint8_t v_res_735_;
v_res_735_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1___redArg(v_keys_725_, v_i_726_, v_k_727_);
stack->m_num = v_res_735_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_736_, lean_object* v_i_737_, lean_object* v_k_738_){
_start:
{
uint8_t v_res_739_; lean_object* v_r_740_; 
v_res_739_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1___redArg(v_keys_736_, v_i_737_, v_k_738_);
lean_dec(v_k_738_);
lean_dec_ref(v_keys_736_);
v_r_740_ = lean_box(v_res_739_);
return v_r_740_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0___redArg(lean_object* v_x_741_, size_t v_x_742_, lean_object* v_x_743_){
_start:
{
if (lean_obj_tag(v_x_741_) == 0)
{
lean_object* v_es_744_; lean_object* v___x_745_; size_t v___x_746_; size_t v___x_747_; lean_object* v_j_748_; lean_object* v___x_749_; 
v_es_744_ = lean_ctor_get(v_x_741_, 0);
v___x_745_ = lean_box(2);
v___x_746_ = ((size_t)31ULL);
v___x_747_ = lean_usize_land(v_x_742_, v___x_746_);
v_j_748_ = lean_usize_to_nat(v___x_747_);
v___x_749_ = lean_array_get_borrowed(v___x_745_, v_es_744_, v_j_748_);
lean_dec(v_j_748_);
switch(lean_obj_tag(v___x_749_))
{
case 0:
{
lean_object* v_key_750_; uint8_t v___x_751_; 
v_key_750_ = lean_ctor_get(v___x_749_, 0);
v___x_751_ = lean_name_eq(v_x_743_, v_key_750_);
return v___x_751_;
}
case 1:
{
lean_object* v_node_752_; size_t v___x_753_; size_t v___x_754_; 
v_node_752_ = lean_ctor_get(v___x_749_, 0);
v___x_753_ = ((size_t)5ULL);
v___x_754_ = lean_usize_shift_right(v_x_742_, v___x_753_);
v_x_741_ = v_node_752_;
v_x_742_ = v___x_754_;
goto _start;
}
default: 
{
uint8_t v___x_756_; 
v___x_756_ = 0;
return v___x_756_;
}
}
}
else
{
lean_object* v_ks_757_; lean_object* v___x_758_; uint8_t v___x_759_; 
v_ks_757_ = lean_ctor_get(v_x_741_, 0);
v___x_758_ = lean_unsigned_to_nat(0u);
v___x_759_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1___redArg(v_ks_757_, v___x_758_, v_x_743_);
return v___x_759_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_741_ = stack[0].m_obj;
size_t v_x_742_ = stack[1].m_num;
lean_object* v_x_743_ = stack[2].m_obj;
uint8_t v_res_760_;
v_res_760_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0___redArg(v_x_741_, v_x_742_, v_x_743_);
stack->m_num = v_res_760_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0___redArg___boxed(lean_object* v_x_761_, lean_object* v_x_762_, lean_object* v_x_763_){
_start:
{
size_t v_x_305__boxed_764_; uint8_t v_res_765_; lean_object* v_r_766_; 
v_x_305__boxed_764_ = lean_unbox_usize(v_x_762_);
lean_dec(v_x_762_);
v_res_765_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0___redArg(v_x_761_, v_x_305__boxed_764_, v_x_763_);
lean_dec(v_x_763_);
lean_dec_ref(v_x_761_);
v_r_766_ = lean_box(v_res_765_);
return v_r_766_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0___redArg(lean_object* v_x_767_, lean_object* v_x_768_){
_start:
{
uint64_t v___y_770_; 
if (lean_obj_tag(v_x_768_) == 0)
{
uint64_t v___x_773_; 
v___x_773_ = 1723ULL;
v___y_770_ = v___x_773_;
goto v___jp_769_;
}
else
{
uint64_t v_hash_774_; 
v_hash_774_ = lean_ctor_get_uint64(v_x_768_, sizeof(void*)*2);
v___y_770_ = v_hash_774_;
goto v___jp_769_;
}
v___jp_769_:
{
size_t v___x_771_; uint8_t v___x_772_; 
v___x_771_ = lean_uint64_to_usize(v___y_770_);
v___x_772_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0___redArg(v_x_767_, v___x_771_, v_x_768_);
return v___x_772_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_767_ = stack[0].m_obj;
lean_object* v_x_768_ = stack[1].m_obj;
uint8_t v_res_775_;
v_res_775_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0___redArg(v_x_767_, v_x_768_);
stack->m_num = v_res_775_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0___redArg___boxed(lean_object* v_x_776_, lean_object* v_x_777_){
_start:
{
uint8_t v_res_778_; lean_object* v_r_779_; 
v_res_778_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0___redArg(v_x_776_, v_x_777_);
lean_dec(v_x_777_);
lean_dec_ref(v_x_776_);
v_r_779_ = lean_box(v_res_778_);
return v_r_779_;
}
}
uint8_t l_Lean_Meta_Match_isMatchEqnTheorem(lean_object* v_env_782_, lean_object* v_declName_783_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_Lean_Name_eraseMacroScopes(v_declName_783_);
if (lean_obj_tag(v___x_784_) == 1)
{
lean_object* v_str_785_; uint8_t v___x_786_; 
v_str_785_ = lean_ctor_get(v___x_784_, 1);
lean_inc_ref(v_str_785_);
lean_dec_ref_known(v___x_784_, 2);
v___x_786_ = l_Lean_Meta_isEqnLikeSuffix(v_str_785_);
if (v___x_786_ == 0)
{
lean_dec(v_declName_783_);
lean_dec_ref(v_env_782_);
return v___x_786_;
}
else
{
lean_object* v___x_787_; uint8_t v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v_eqns_792_; uint8_t v___x_793_; 
v___x_787_ = l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default;
v___x_788_ = 0;
v___x_789_ = l_Lean_Meta_Match_matchEqnsExt;
v___x_790_ = ((lean_object*)(l_Lean_Meta_Match_isMatchEqnTheorem___closed__0));
lean_inc(v_declName_783_);
v___x_791_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_787_, v___x_789_, v_env_782_, v___x_790_, v_declName_783_, v___x_788_);
v_eqns_792_ = lean_ctor_get(v___x_791_, 1);
lean_inc_ref(v_eqns_792_);
lean_dec(v___x_791_);
v___x_793_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0___redArg(v_eqns_792_, v_declName_783_);
lean_dec(v_declName_783_);
lean_dec_ref(v_eqns_792_);
return v___x_793_;
}
}
else
{
uint8_t v___x_794_; 
lean_dec(v___x_784_);
lean_dec(v_declName_783_);
lean_dec_ref(v_env_782_);
v___x_794_ = 0;
return v___x_794_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Match_isMatchEqnTheorem_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_782_ = stack[0].m_obj;
lean_object* v_declName_783_ = stack[1].m_obj;
uint8_t v_res_795_;
v_res_795_ = l_Lean_Meta_Match_isMatchEqnTheorem(v_env_782_, v_declName_783_);
stack->m_num = v_res_795_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_isMatchEqnTheorem___boxed(lean_object* v_env_796_, lean_object* v_declName_797_){
_start:
{
uint8_t v_res_798_; lean_object* v_r_799_; 
v_res_798_ = l_Lean_Meta_Match_isMatchEqnTheorem(v_env_796_, v_declName_797_);
v_r_799_ = lean_box(v_res_798_);
return v_r_799_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0(lean_object* v_00_u03b2_800_, lean_object* v_x_801_, lean_object* v_x_802_){
_start:
{
uint8_t v___x_803_; 
v___x_803_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0___redArg(v_x_801_, v_x_802_);
return v___x_803_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_801_ = stack[1].m_obj;
lean_object* v_x_802_ = stack[2].m_obj;
uint8_t v_res_804_;
v_res_804_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0(lean_box(0), v_x_801_, v_x_802_);
stack->m_num = v_res_804_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0___boxed(lean_object* v_00_u03b2_805_, lean_object* v_x_806_, lean_object* v_x_807_){
_start:
{
uint8_t v_res_808_; lean_object* v_r_809_; 
v_res_808_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0(v_00_u03b2_805_, v_x_806_, v_x_807_);
lean_dec(v_x_807_);
lean_dec_ref(v_x_806_);
v_r_809_ = lean_box(v_res_808_);
return v_r_809_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0(lean_object* v_00_u03b2_810_, lean_object* v_x_811_, size_t v_x_812_, lean_object* v_x_813_){
_start:
{
uint8_t v___x_814_; 
v___x_814_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0___redArg(v_x_811_, v_x_812_, v_x_813_);
return v___x_814_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_811_ = stack[1].m_obj;
size_t v_x_812_ = stack[2].m_num;
lean_object* v_x_813_ = stack[3].m_obj;
uint8_t v_res_815_;
v_res_815_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0(lean_box(0), v_x_811_, v_x_812_, v_x_813_);
stack->m_num = v_res_815_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0___boxed(lean_object* v_00_u03b2_816_, lean_object* v_x_817_, lean_object* v_x_818_, lean_object* v_x_819_){
_start:
{
size_t v_x_444__boxed_820_; uint8_t v_res_821_; lean_object* v_r_822_; 
v_x_444__boxed_820_ = lean_unbox_usize(v_x_818_);
lean_dec(v_x_818_);
v_res_821_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0(v_00_u03b2_816_, v_x_817_, v_x_444__boxed_820_, v_x_819_);
lean_dec(v_x_819_);
lean_dec_ref(v_x_817_);
v_r_822_ = lean_box(v_res_821_);
return v_r_822_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_823_, lean_object* v_keys_824_, lean_object* v_vals_825_, lean_object* v_heq_826_, lean_object* v_i_827_, lean_object* v_k_828_){
_start:
{
uint8_t v___x_829_; 
v___x_829_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1___redArg(v_keys_824_, v_i_827_, v_k_828_);
return v___x_829_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_824_ = stack[1].m_obj;
lean_object* v_vals_825_ = stack[2].m_obj;
lean_object* v_i_827_ = stack[4].m_obj;
lean_object* v_k_828_ = stack[5].m_obj;
uint8_t v_res_830_;
v_res_830_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1(lean_box(0), v_keys_824_, v_vals_825_, lean_box(0), v_i_827_, v_k_828_);
stack->m_num = v_res_830_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_831_, lean_object* v_keys_832_, lean_object* v_vals_833_, lean_object* v_heq_834_, lean_object* v_i_835_, lean_object* v_k_836_){
_start:
{
uint8_t v_res_837_; lean_object* v_r_838_; 
v_res_837_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1(v_00_u03b2_831_, v_keys_832_, v_vals_833_, v_heq_834_, v_i_835_, v_k_836_);
lean_dec(v_k_836_);
lean_dec_ref(v_vals_833_);
lean_dec_ref(v_keys_832_);
v_r_838_ = lean_box(v_res_837_);
return v_r_838_;
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
res = l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2_();
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
