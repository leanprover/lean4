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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2_(lean_object* v___x_195_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_197_, 0, v___x_195_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2____boxed(lean_object* v___x_198_, lean_object* v___y_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2_(v___x_198_);
return v_res_200_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_201_; lean_object* v___f_202_; 
v___x_201_ = lean_obj_once(&l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__1, &l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__1_once, _init_l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__1);
v___f_202_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_202_, 0, v___x_201_);
return v___f_202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; uint8_t v___x_217_; uint8_t v___x_218_; lean_object* v___x_219_; 
v___f_213_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2_);
v___x_214_ = lean_box(0);
v___x_215_ = lean_box(1);
v___x_216_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__5_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2_));
v___x_217_ = 0;
v___x_218_ = 1;
v___x_219_ = l_Lean_registerEnvExtension___redArg(v___f_213_, v___x_214_, v___x_215_, v___x_216_, v___x_217_, v___x_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2____boxed(lean_object* v_a_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqsExt_3224184366____hygCtx___hyg_2_();
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Match_registerMatchEqns_spec__2(lean_object* v_map_222_, lean_object* v_msg_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = lean_panic_fn_borrowed(v_map_222_, v_msg_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Match_registerMatchEqns_spec__2___boxed(lean_object* v_map_225_, lean_object* v_msg_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_panic___at___00Lean_Meta_Match_registerMatchEqns_spec__2(v_map_225_, v_msg_226_);
lean_dec_ref(v_map_225_);
return v_res_227_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Meta_Match_registerMatchEqns_spec__4___redArg(lean_object* v_xs_228_, lean_object* v_ys_229_, lean_object* v_x_230_){
_start:
{
lean_object* v_zero_231_; uint8_t v_isZero_232_; 
v_zero_231_ = lean_unsigned_to_nat(0u);
v_isZero_232_ = lean_nat_dec_eq(v_x_230_, v_zero_231_);
if (v_isZero_232_ == 1)
{
lean_dec(v_x_230_);
return v_isZero_232_;
}
else
{
lean_object* v_one_233_; lean_object* v_n_234_; lean_object* v___x_235_; lean_object* v___x_236_; uint8_t v___x_237_; 
v_one_233_ = lean_unsigned_to_nat(1u);
v_n_234_ = lean_nat_sub(v_x_230_, v_one_233_);
lean_dec(v_x_230_);
v___x_235_ = lean_array_fget_borrowed(v_xs_228_, v_n_234_);
v___x_236_ = lean_array_fget_borrowed(v_ys_229_, v_n_234_);
v___x_237_ = lean_name_eq(v___x_235_, v___x_236_);
if (v___x_237_ == 0)
{
lean_dec(v_n_234_);
return v___x_237_;
}
else
{
v_x_230_ = v_n_234_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Meta_Match_registerMatchEqns_spec__4___redArg___boxed(lean_object* v_xs_239_, lean_object* v_ys_240_, lean_object* v_x_241_){
_start:
{
uint8_t v_res_242_; lean_object* v_r_243_; 
v_res_242_ = l_Array_isEqvAux___at___00Lean_Meta_Match_registerMatchEqns_spec__4___redArg(v_xs_239_, v_ys_240_, v_x_241_);
lean_dec_ref(v_ys_240_);
lean_dec_ref(v_xs_239_);
v_r_243_ = lean_box(v_res_242_);
return v_r_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2_spec__6___redArg(lean_object* v_x_244_, lean_object* v_x_245_, lean_object* v_x_246_, lean_object* v_x_247_){
_start:
{
lean_object* v_ks_248_; lean_object* v_vs_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_273_; 
v_ks_248_ = lean_ctor_get(v_x_244_, 0);
v_vs_249_ = lean_ctor_get(v_x_244_, 1);
v_isSharedCheck_273_ = !lean_is_exclusive(v_x_244_);
if (v_isSharedCheck_273_ == 0)
{
v___x_251_ = v_x_244_;
v_isShared_252_ = v_isSharedCheck_273_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_vs_249_);
lean_inc(v_ks_248_);
lean_dec(v_x_244_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_273_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_253_; uint8_t v___x_254_; 
v___x_253_ = lean_array_get_size(v_ks_248_);
v___x_254_ = lean_nat_dec_lt(v_x_245_, v___x_253_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_258_; 
lean_dec(v_x_245_);
v___x_255_ = lean_array_push(v_ks_248_, v_x_246_);
v___x_256_ = lean_array_push(v_vs_249_, v_x_247_);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 1, v___x_256_);
lean_ctor_set(v___x_251_, 0, v___x_255_);
v___x_258_ = v___x_251_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_255_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v___x_256_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
else
{
lean_object* v_k_x27_260_; uint8_t v___x_261_; 
v_k_x27_260_ = lean_array_fget_borrowed(v_ks_248_, v_x_245_);
v___x_261_ = lean_name_eq(v_x_246_, v_k_x27_260_);
if (v___x_261_ == 0)
{
lean_object* v___x_263_; 
if (v_isShared_252_ == 0)
{
v___x_263_ = v___x_251_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_ks_248_);
lean_ctor_set(v_reuseFailAlloc_267_, 1, v_vs_249_);
v___x_263_ = v_reuseFailAlloc_267_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = lean_unsigned_to_nat(1u);
v___x_265_ = lean_nat_add(v_x_245_, v___x_264_);
lean_dec(v_x_245_);
v_x_244_ = v___x_263_;
v_x_245_ = v___x_265_;
goto _start;
}
}
else
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_271_; 
v___x_268_ = lean_array_fset(v_ks_248_, v_x_245_, v_x_246_);
v___x_269_ = lean_array_fset(v_vs_249_, v_x_245_, v_x_247_);
lean_dec(v_x_245_);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 1, v___x_269_);
lean_ctor_set(v___x_251_, 0, v___x_268_);
v___x_271_ = v___x_251_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v___x_268_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v___x_269_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg(lean_object* v_n_274_, lean_object* v_k_275_, lean_object* v_v_276_){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = lean_unsigned_to_nat(0u);
v___x_278_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2_spec__6___redArg(v_n_274_, v___x_277_, v_k_275_, v_v_276_);
return v___x_278_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg(lean_object* v_x_280_, size_t v_x_281_, size_t v_x_282_, lean_object* v_x_283_, lean_object* v_x_284_){
_start:
{
if (lean_obj_tag(v_x_280_) == 0)
{
lean_object* v_es_285_; size_t v___x_286_; size_t v___x_287_; lean_object* v_j_288_; lean_object* v___x_289_; uint8_t v___x_290_; 
v_es_285_ = lean_ctor_get(v_x_280_, 0);
v___x_286_ = ((size_t)31ULL);
v___x_287_ = lean_usize_land(v_x_281_, v___x_286_);
v_j_288_ = lean_usize_to_nat(v___x_287_);
v___x_289_ = lean_array_get_size(v_es_285_);
v___x_290_ = lean_nat_dec_lt(v_j_288_, v___x_289_);
if (v___x_290_ == 0)
{
lean_dec(v_j_288_);
lean_dec(v_x_284_);
lean_dec(v_x_283_);
return v_x_280_;
}
else
{
lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_329_; 
lean_inc_ref(v_es_285_);
v_isSharedCheck_329_ = !lean_is_exclusive(v_x_280_);
if (v_isSharedCheck_329_ == 0)
{
lean_object* v_unused_330_; 
v_unused_330_ = lean_ctor_get(v_x_280_, 0);
lean_dec(v_unused_330_);
v___x_292_ = v_x_280_;
v_isShared_293_ = v_isSharedCheck_329_;
goto v_resetjp_291_;
}
else
{
lean_dec(v_x_280_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_329_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v_v_294_; lean_object* v___x_295_; lean_object* v_xs_x27_296_; lean_object* v___y_298_; 
v_v_294_ = lean_array_fget(v_es_285_, v_j_288_);
v___x_295_ = lean_box(0);
v_xs_x27_296_ = lean_array_fset(v_es_285_, v_j_288_, v___x_295_);
switch(lean_obj_tag(v_v_294_))
{
case 0:
{
lean_object* v_key_303_; lean_object* v_val_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_314_; 
v_key_303_ = lean_ctor_get(v_v_294_, 0);
v_val_304_ = lean_ctor_get(v_v_294_, 1);
v_isSharedCheck_314_ = !lean_is_exclusive(v_v_294_);
if (v_isSharedCheck_314_ == 0)
{
v___x_306_ = v_v_294_;
v_isShared_307_ = v_isSharedCheck_314_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_val_304_);
lean_inc(v_key_303_);
lean_dec(v_v_294_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_314_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
uint8_t v___x_308_; 
v___x_308_ = lean_name_eq(v_x_283_, v_key_303_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; lean_object* v___x_310_; 
lean_del_object(v___x_306_);
v___x_309_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_303_, v_val_304_, v_x_283_, v_x_284_);
v___x_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
v___y_298_ = v___x_310_;
goto v___jp_297_;
}
else
{
lean_object* v___x_312_; 
lean_dec(v_val_304_);
lean_dec(v_key_303_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 1, v_x_284_);
lean_ctor_set(v___x_306_, 0, v_x_283_);
v___x_312_ = v___x_306_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_x_283_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v_x_284_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
v___y_298_ = v___x_312_;
goto v___jp_297_;
}
}
}
}
case 1:
{
lean_object* v_node_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_327_; 
v_node_315_ = lean_ctor_get(v_v_294_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v_v_294_);
if (v_isSharedCheck_327_ == 0)
{
v___x_317_ = v_v_294_;
v_isShared_318_ = v_isSharedCheck_327_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_node_315_);
lean_dec(v_v_294_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_327_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
size_t v___x_319_; size_t v___x_320_; size_t v___x_321_; size_t v___x_322_; lean_object* v___x_323_; lean_object* v___x_325_; 
v___x_319_ = ((size_t)5ULL);
v___x_320_ = lean_usize_shift_right(v_x_281_, v___x_319_);
v___x_321_ = ((size_t)1ULL);
v___x_322_ = lean_usize_add(v_x_282_, v___x_321_);
v___x_323_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg(v_node_315_, v___x_320_, v___x_322_, v_x_283_, v_x_284_);
if (v_isShared_318_ == 0)
{
lean_ctor_set(v___x_317_, 0, v___x_323_);
v___x_325_ = v___x_317_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_323_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
v___y_298_ = v___x_325_;
goto v___jp_297_;
}
}
}
default: 
{
lean_object* v___x_328_; 
v___x_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_328_, 0, v_x_283_);
lean_ctor_set(v___x_328_, 1, v_x_284_);
v___y_298_ = v___x_328_;
goto v___jp_297_;
}
}
v___jp_297_:
{
lean_object* v___x_299_; lean_object* v___x_301_; 
v___x_299_ = lean_array_fset(v_xs_x27_296_, v_j_288_, v___y_298_);
lean_dec(v_j_288_);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 0, v___x_299_);
v___x_301_ = v___x_292_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_299_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
}
else
{
lean_object* v_ks_331_; lean_object* v_vs_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_350_; 
v_ks_331_ = lean_ctor_get(v_x_280_, 0);
v_vs_332_ = lean_ctor_get(v_x_280_, 1);
v_isSharedCheck_350_ = !lean_is_exclusive(v_x_280_);
if (v_isSharedCheck_350_ == 0)
{
v___x_334_ = v_x_280_;
v_isShared_335_ = v_isSharedCheck_350_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_vs_332_);
lean_inc(v_ks_331_);
lean_dec(v_x_280_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_350_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_337_; 
if (v_isShared_335_ == 0)
{
v___x_337_ = v___x_334_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_ks_331_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v_vs_332_);
v___x_337_ = v_reuseFailAlloc_349_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
lean_object* v_newNode_338_; size_t v___x_339_; uint8_t v___x_340_; 
v_newNode_338_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg(v___x_337_, v_x_283_, v_x_284_);
v___x_339_ = ((size_t)7ULL);
v___x_340_ = lean_usize_dec_le(v___x_339_, v_x_282_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; lean_object* v___x_342_; uint8_t v___x_343_; 
v___x_341_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_338_);
v___x_342_ = lean_unsigned_to_nat(4u);
v___x_343_ = lean_nat_dec_lt(v___x_341_, v___x_342_);
lean_dec(v___x_341_);
if (v___x_343_ == 0)
{
lean_object* v_ks_344_; lean_object* v_vs_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v_ks_344_ = lean_ctor_get(v_newNode_338_, 0);
lean_inc_ref(v_ks_344_);
v_vs_345_ = lean_ctor_get(v_newNode_338_, 1);
lean_inc_ref(v_vs_345_);
lean_dec_ref(v_newNode_338_);
v___x_346_ = lean_unsigned_to_nat(0u);
v___x_347_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__0);
v___x_348_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__3___redArg(v_x_282_, v_ks_344_, v_vs_345_, v___x_346_, v___x_347_);
lean_dec_ref(v_vs_345_);
lean_dec_ref(v_ks_344_);
return v___x_348_;
}
else
{
return v_newNode_338_;
}
}
else
{
return v_newNode_338_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__3___redArg(size_t v_depth_351_, lean_object* v_keys_352_, lean_object* v_vals_353_, lean_object* v_i_354_, lean_object* v_entries_355_){
_start:
{
lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_356_ = lean_array_get_size(v_keys_352_);
v___x_357_ = lean_nat_dec_lt(v_i_354_, v___x_356_);
if (v___x_357_ == 0)
{
lean_dec(v_i_354_);
return v_entries_355_;
}
else
{
lean_object* v_k_358_; lean_object* v_v_359_; uint64_t v___y_361_; 
v_k_358_ = lean_array_fget_borrowed(v_keys_352_, v_i_354_);
v_v_359_ = lean_array_fget_borrowed(v_vals_353_, v_i_354_);
if (lean_obj_tag(v_k_358_) == 0)
{
uint64_t v___x_372_; 
v___x_372_ = 1723ULL;
v___y_361_ = v___x_372_;
goto v___jp_360_;
}
else
{
uint64_t v_hash_373_; 
v_hash_373_ = lean_ctor_get_uint64(v_k_358_, sizeof(void*)*2);
v___y_361_ = v_hash_373_;
goto v___jp_360_;
}
v___jp_360_:
{
size_t v_h_362_; size_t v___x_363_; lean_object* v___x_364_; size_t v___x_365_; size_t v___x_366_; size_t v___x_367_; size_t v_h_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v_h_362_ = lean_uint64_to_usize(v___y_361_);
v___x_363_ = ((size_t)5ULL);
v___x_364_ = lean_unsigned_to_nat(1u);
v___x_365_ = ((size_t)1ULL);
v___x_366_ = lean_usize_sub(v_depth_351_, v___x_365_);
v___x_367_ = lean_usize_mul(v___x_363_, v___x_366_);
v_h_368_ = lean_usize_shift_right(v_h_362_, v___x_367_);
v___x_369_ = lean_nat_add(v_i_354_, v___x_364_);
lean_dec(v_i_354_);
lean_inc(v_v_359_);
lean_inc(v_k_358_);
v___x_370_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg(v_entries_355_, v_h_368_, v_depth_351_, v_k_358_, v_v_359_);
v_i_354_ = v___x_369_;
v_entries_355_ = v___x_370_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_374_, lean_object* v_keys_375_, lean_object* v_vals_376_, lean_object* v_i_377_, lean_object* v_entries_378_){
_start:
{
size_t v_depth_boxed_379_; lean_object* v_res_380_; 
v_depth_boxed_379_ = lean_unbox_usize(v_depth_374_);
lean_dec(v_depth_374_);
v_res_380_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__3___redArg(v_depth_boxed_379_, v_keys_375_, v_vals_376_, v_i_377_, v_entries_378_);
lean_dec_ref(v_vals_376_);
lean_dec_ref(v_keys_375_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___boxed(lean_object* v_x_381_, lean_object* v_x_382_, lean_object* v_x_383_, lean_object* v_x_384_, lean_object* v_x_385_){
_start:
{
size_t v_x_1145__boxed_386_; size_t v_x_1146__boxed_387_; lean_object* v_res_388_; 
v_x_1145__boxed_386_ = lean_unbox_usize(v_x_382_);
lean_dec(v_x_382_);
v_x_1146__boxed_387_ = lean_unbox_usize(v_x_383_);
lean_dec(v_x_383_);
v_res_388_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg(v_x_381_, v_x_1145__boxed_386_, v_x_1146__boxed_387_, v_x_384_, v_x_385_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0___redArg(lean_object* v_x_389_, lean_object* v_x_390_, lean_object* v_x_391_){
_start:
{
uint64_t v___y_393_; 
if (lean_obj_tag(v_x_390_) == 0)
{
uint64_t v___x_397_; 
v___x_397_ = 1723ULL;
v___y_393_ = v___x_397_;
goto v___jp_392_;
}
else
{
uint64_t v_hash_398_; 
v_hash_398_ = lean_ctor_get_uint64(v_x_390_, sizeof(void*)*2);
v___y_393_ = v_hash_398_;
goto v___jp_392_;
}
v___jp_392_:
{
size_t v___x_394_; size_t v___x_395_; lean_object* v___x_396_; 
v___x_394_ = lean_uint64_to_usize(v___y_393_);
v___x_395_ = ((size_t)1ULL);
v___x_396_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg(v_x_389_, v___x_394_, v___x_395_, v_x_390_, v_x_391_);
return v___x_396_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4_spec__7___redArg(lean_object* v_keys_399_, lean_object* v_vals_400_, lean_object* v_i_401_, lean_object* v_k_402_){
_start:
{
lean_object* v___x_403_; uint8_t v___x_404_; 
v___x_403_ = lean_array_get_size(v_keys_399_);
v___x_404_ = lean_nat_dec_lt(v_i_401_, v___x_403_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; 
lean_dec(v_i_401_);
v___x_405_ = lean_box(0);
return v___x_405_;
}
else
{
lean_object* v_k_x27_406_; uint8_t v___x_407_; 
v_k_x27_406_ = lean_array_fget_borrowed(v_keys_399_, v_i_401_);
v___x_407_ = lean_name_eq(v_k_402_, v_k_x27_406_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = lean_unsigned_to_nat(1u);
v___x_409_ = lean_nat_add(v_i_401_, v___x_408_);
lean_dec(v_i_401_);
v_i_401_ = v___x_409_;
goto _start;
}
else
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = lean_array_fget_borrowed(v_vals_400_, v_i_401_);
lean_dec(v_i_401_);
lean_inc(v___x_411_);
v___x_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
return v___x_412_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_keys_413_, lean_object* v_vals_414_, lean_object* v_i_415_, lean_object* v_k_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4_spec__7___redArg(v_keys_413_, v_vals_414_, v_i_415_, v_k_416_);
lean_dec(v_k_416_);
lean_dec_ref(v_vals_414_);
lean_dec_ref(v_keys_413_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4___redArg(lean_object* v_x_418_, size_t v_x_419_, lean_object* v_x_420_){
_start:
{
if (lean_obj_tag(v_x_418_) == 0)
{
lean_object* v_es_421_; lean_object* v___x_422_; size_t v___x_423_; size_t v___x_424_; lean_object* v_j_425_; lean_object* v___x_426_; 
v_es_421_ = lean_ctor_get(v_x_418_, 0);
v___x_422_ = lean_box(2);
v___x_423_ = ((size_t)31ULL);
v___x_424_ = lean_usize_land(v_x_419_, v___x_423_);
v_j_425_ = lean_usize_to_nat(v___x_424_);
v___x_426_ = lean_array_get_borrowed(v___x_422_, v_es_421_, v_j_425_);
lean_dec(v_j_425_);
switch(lean_obj_tag(v___x_426_))
{
case 0:
{
lean_object* v_key_427_; lean_object* v_val_428_; uint8_t v___x_429_; 
v_key_427_ = lean_ctor_get(v___x_426_, 0);
v_val_428_ = lean_ctor_get(v___x_426_, 1);
v___x_429_ = lean_name_eq(v_x_420_, v_key_427_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; 
v___x_430_ = lean_box(0);
return v___x_430_;
}
else
{
lean_object* v___x_431_; 
lean_inc(v_val_428_);
v___x_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_431_, 0, v_val_428_);
return v___x_431_;
}
}
case 1:
{
lean_object* v_node_432_; size_t v___x_433_; size_t v___x_434_; 
v_node_432_ = lean_ctor_get(v___x_426_, 0);
v___x_433_ = ((size_t)5ULL);
v___x_434_ = lean_usize_shift_right(v_x_419_, v___x_433_);
v_x_418_ = v_node_432_;
v_x_419_ = v___x_434_;
goto _start;
}
default: 
{
lean_object* v___x_436_; 
v___x_436_ = lean_box(0);
return v___x_436_;
}
}
}
else
{
lean_object* v_ks_437_; lean_object* v_vs_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v_ks_437_ = lean_ctor_get(v_x_418_, 0);
v_vs_438_ = lean_ctor_get(v_x_418_, 1);
v___x_439_ = lean_unsigned_to_nat(0u);
v___x_440_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4_spec__7___redArg(v_ks_437_, v_vs_438_, v___x_439_, v_x_420_);
return v___x_440_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4___redArg___boxed(lean_object* v_x_441_, lean_object* v_x_442_, lean_object* v_x_443_){
_start:
{
size_t v_x_1335__boxed_444_; lean_object* v_res_445_; 
v_x_1335__boxed_444_ = lean_unbox_usize(v_x_442_);
lean_dec(v_x_442_);
v_res_445_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4___redArg(v_x_441_, v_x_1335__boxed_444_, v_x_443_);
lean_dec(v_x_443_);
lean_dec_ref(v_x_441_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3___redArg(lean_object* v_x_446_, lean_object* v_x_447_){
_start:
{
uint64_t v___y_449_; 
if (lean_obj_tag(v_x_447_) == 0)
{
uint64_t v___x_452_; 
v___x_452_ = 1723ULL;
v___y_449_ = v___x_452_;
goto v___jp_448_;
}
else
{
uint64_t v_hash_453_; 
v_hash_453_ = lean_ctor_get_uint64(v_x_447_, sizeof(void*)*2);
v___y_449_ = v_hash_453_;
goto v___jp_448_;
}
v___jp_448_:
{
size_t v___x_450_; lean_object* v___x_451_; 
v___x_450_ = lean_uint64_to_usize(v___y_449_);
v___x_451_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4___redArg(v_x_446_, v___x_450_, v_x_447_);
return v___x_451_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3___redArg___boxed(lean_object* v_x_454_, lean_object* v_x_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3___redArg(v_x_454_, v_x_455_);
lean_dec(v_x_455_);
lean_dec_ref(v_x_454_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_registerMatchEqns_spec__1(lean_object* v_as_457_, size_t v_i_458_, size_t v_stop_459_, lean_object* v_b_460_){
_start:
{
uint8_t v___x_461_; 
v___x_461_ = lean_usize_dec_eq(v_i_458_, v_stop_459_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; size_t v___x_465_; size_t v___x_466_; 
v___x_462_ = lean_array_uget_borrowed(v_as_457_, v_i_458_);
v___x_463_ = lean_box(0);
lean_inc(v___x_462_);
v___x_464_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0___redArg(v_b_460_, v___x_462_, v___x_463_);
v___x_465_ = ((size_t)1ULL);
v___x_466_ = lean_usize_add(v_i_458_, v___x_465_);
v_i_458_ = v___x_466_;
v_b_460_ = v___x_464_;
goto _start;
}
else
{
return v_b_460_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_registerMatchEqns_spec__1___boxed(lean_object* v_as_468_, lean_object* v_i_469_, lean_object* v_stop_470_, lean_object* v_b_471_){
_start:
{
size_t v_i_boxed_472_; size_t v_stop_boxed_473_; lean_object* v_res_474_; 
v_i_boxed_472_ = lean_unbox_usize(v_i_469_);
lean_dec(v_i_469_);
v_stop_boxed_473_ = lean_unbox_usize(v_stop_470_);
lean_dec(v_stop_470_);
v_res_474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_registerMatchEqns_spec__1(v_as_468_, v_i_boxed_472_, v_stop_boxed_473_, v_b_471_);
lean_dec_ref(v_as_468_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_registerMatchEqns___redArg___lam__0(lean_object* v_matchEqns_479_, lean_object* v_matchDeclName_480_, lean_object* v_x_481_){
_start:
{
lean_object* v_map_482_; lean_object* v_eqns_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_534_; 
v_map_482_ = lean_ctor_get(v_x_481_, 0);
v_eqns_483_ = lean_ctor_get(v_x_481_, 1);
v_isSharedCheck_534_ = !lean_is_exclusive(v_x_481_);
if (v_isSharedCheck_534_ == 0)
{
v___x_485_ = v_x_481_;
v_isShared_486_ = v_isSharedCheck_534_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_eqns_483_);
lean_inc(v_map_482_);
lean_dec(v_x_481_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_534_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___y_488_; lean_object* v___x_525_; 
v___x_525_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3___redArg(v_map_482_, v_matchDeclName_480_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v___x_526_; 
lean_inc_ref(v_matchEqns_479_);
v___x_526_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0___redArg(v_map_482_, v_matchDeclName_480_, v_matchEqns_479_);
v___y_488_ = v___x_526_;
goto v___jp_487_;
}
else
{
lean_object* v_val_527_; lean_object* v_eqnNames_528_; lean_object* v_eqnNames_529_; lean_object* v___x_530_; lean_object* v___x_531_; uint8_t v___x_532_; 
v_val_527_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_val_527_);
lean_dec_ref_known(v___x_525_, 1);
v_eqnNames_528_ = lean_ctor_get(v_val_527_, 0);
lean_inc_ref(v_eqnNames_528_);
lean_dec(v_val_527_);
v_eqnNames_529_ = lean_ctor_get(v_matchEqns_479_, 0);
v___x_530_ = lean_array_get_size(v_eqnNames_528_);
v___x_531_ = lean_array_get_size(v_eqnNames_529_);
v___x_532_ = lean_nat_dec_eq(v___x_530_, v___x_531_);
if (v___x_532_ == 0)
{
lean_dec_ref(v_eqnNames_528_);
goto v___jp_512_;
}
else
{
uint8_t v___x_533_; 
v___x_533_ = l_Array_isEqvAux___at___00Lean_Meta_Match_registerMatchEqns_spec__4___redArg(v_eqnNames_528_, v_eqnNames_529_, v___x_530_);
lean_dec_ref(v_eqnNames_528_);
if (v___x_533_ == 0)
{
goto v___jp_512_;
}
else
{
lean_dec(v_matchDeclName_480_);
v___y_488_ = v_map_482_;
goto v___jp_487_;
}
}
}
v___jp_487_:
{
lean_object* v_eqnNames_489_; lean_object* v___x_490_; lean_object* v___x_491_; uint8_t v___x_492_; 
v_eqnNames_489_ = lean_ctor_get(v_matchEqns_479_, 0);
lean_inc_ref(v_eqnNames_489_);
lean_dec_ref(v_matchEqns_479_);
v___x_490_ = lean_unsigned_to_nat(0u);
v___x_491_ = lean_array_get_size(v_eqnNames_489_);
v___x_492_ = lean_nat_dec_lt(v___x_490_, v___x_491_);
if (v___x_492_ == 0)
{
lean_object* v___x_494_; 
lean_dec_ref(v_eqnNames_489_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 0, v___y_488_);
v___x_494_ = v___x_485_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___y_488_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v_eqns_483_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
else
{
uint8_t v___x_496_; 
v___x_496_ = lean_nat_dec_le(v___x_491_, v___x_491_);
if (v___x_496_ == 0)
{
if (v___x_492_ == 0)
{
lean_object* v___x_498_; 
lean_dec_ref(v_eqnNames_489_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 0, v___y_488_);
v___x_498_ = v___x_485_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___y_488_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v_eqns_483_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
else
{
size_t v___x_500_; size_t v___x_501_; lean_object* v___x_502_; lean_object* v___x_504_; 
v___x_500_ = ((size_t)0ULL);
v___x_501_ = lean_usize_of_nat(v___x_491_);
v___x_502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_registerMatchEqns_spec__1(v_eqnNames_489_, v___x_500_, v___x_501_, v_eqns_483_);
lean_dec_ref(v_eqnNames_489_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 1, v___x_502_);
lean_ctor_set(v___x_485_, 0, v___y_488_);
v___x_504_ = v___x_485_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___y_488_);
lean_ctor_set(v_reuseFailAlloc_505_, 1, v___x_502_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
else
{
size_t v___x_506_; size_t v___x_507_; lean_object* v___x_508_; lean_object* v___x_510_; 
v___x_506_ = ((size_t)0ULL);
v___x_507_ = lean_usize_of_nat(v___x_491_);
v___x_508_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_registerMatchEqns_spec__1(v_eqnNames_489_, v___x_506_, v___x_507_, v_eqns_483_);
lean_dec_ref(v_eqnNames_489_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 1, v___x_508_);
lean_ctor_set(v___x_485_, 0, v___y_488_);
v___x_510_ = v___x_485_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___y_488_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v___x_508_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
v___jp_512_:
{
uint8_t v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_513_ = 1;
v___x_514_ = ((lean_object*)(l_Lean_Meta_Match_registerMatchEqns___redArg___lam__0___closed__0));
v___x_515_ = ((lean_object*)(l_Lean_Meta_Match_registerMatchEqns___redArg___lam__0___closed__1));
v___x_516_ = lean_unsigned_to_nat(49u);
v___x_517_ = lean_unsigned_to_nat(10u);
v___x_518_ = ((lean_object*)(l_Lean_Meta_Match_registerMatchEqns___redArg___lam__0___closed__2));
v___x_519_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_matchDeclName_480_, v___x_513_);
v___x_520_ = lean_string_append(v___x_518_, v___x_519_);
lean_dec_ref(v___x_519_);
v___x_521_ = ((lean_object*)(l_Lean_Meta_Match_registerMatchEqns___redArg___lam__0___closed__3));
v___x_522_ = lean_string_append(v___x_520_, v___x_521_);
v___x_523_ = l_mkPanicMessageWithDecl(v___x_514_, v___x_515_, v___x_516_, v___x_517_, v___x_522_);
lean_dec_ref(v___x_522_);
v___x_524_ = lean_panic_fn_borrowed(v_map_482_, v___x_523_);
lean_dec_ref(v_map_482_);
v___y_488_ = v___x_524_;
goto v___jp_487_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_registerMatchEqns___redArg___closed__0(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___redArg___closed__0);
v___x_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
return v___x_536_;
}
}
static lean_object* _init_l_Lean_Meta_Match_registerMatchEqns___redArg___closed__1(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = lean_obj_once(&l_Lean_Meta_Match_registerMatchEqns___redArg___closed__0, &l_Lean_Meta_Match_registerMatchEqns___redArg___closed__0_once, _init_l_Lean_Meta_Match_registerMatchEqns___redArg___closed__0);
v___x_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_registerMatchEqns___redArg(lean_object* v_matchDeclName_539_, lean_object* v_matchEqns_540_, lean_object* v_a_541_){
_start:
{
lean_object* v___f_543_; lean_object* v___x_544_; lean_object* v_env_545_; lean_object* v_nextMacroScope_546_; lean_object* v_ngen_547_; lean_object* v_auxDeclNGen_548_; lean_object* v_traceState_549_; lean_object* v_recordedDeps_550_; lean_object* v_messages_551_; lean_object* v_infoState_552_; lean_object* v_snapshotTasks_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_569_; 
v___f_543_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_registerMatchEqns___redArg___lam__0), 3, 2);
lean_closure_set(v___f_543_, 0, v_matchEqns_540_);
lean_closure_set(v___f_543_, 1, v_matchDeclName_539_);
v___x_544_ = lean_st_ref_take(v_a_541_);
v_env_545_ = lean_ctor_get(v___x_544_, 0);
v_nextMacroScope_546_ = lean_ctor_get(v___x_544_, 1);
v_ngen_547_ = lean_ctor_get(v___x_544_, 2);
v_auxDeclNGen_548_ = lean_ctor_get(v___x_544_, 3);
v_traceState_549_ = lean_ctor_get(v___x_544_, 4);
v_recordedDeps_550_ = lean_ctor_get(v___x_544_, 6);
v_messages_551_ = lean_ctor_get(v___x_544_, 7);
v_infoState_552_ = lean_ctor_get(v___x_544_, 8);
v_snapshotTasks_553_ = lean_ctor_get(v___x_544_, 9);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_569_ == 0)
{
lean_object* v_unused_570_; 
v_unused_570_ = lean_ctor_get(v___x_544_, 5);
lean_dec(v_unused_570_);
v___x_555_ = v___x_544_;
v_isShared_556_ = v_isSharedCheck_569_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_snapshotTasks_553_);
lean_inc(v_infoState_552_);
lean_inc(v_messages_551_);
lean_inc(v_recordedDeps_550_);
lean_inc(v_traceState_549_);
lean_inc(v_auxDeclNGen_548_);
lean_inc(v_ngen_547_);
lean_inc(v_nextMacroScope_546_);
lean_inc(v_env_545_);
lean_dec(v___x_544_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_569_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_557_; lean_object* v_asyncMode_558_; lean_object* v___x_559_; lean_object* v___x_560_; uint8_t v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_565_; 
v___x_557_ = l_Lean_Meta_Match_matchEqnsExt;
v_asyncMode_558_ = lean_ctor_get(v___x_557_, 2);
v___x_559_ = lean_box(0);
v___x_560_ = lean_box(0);
v___x_561_ = 1;
v___x_562_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_557_, v_env_545_, v___f_543_, v_asyncMode_558_, v___x_560_, v___x_561_);
v___x_563_ = lean_obj_once(&l_Lean_Meta_Match_registerMatchEqns___redArg___closed__1, &l_Lean_Meta_Match_registerMatchEqns___redArg___closed__1_once, _init_l_Lean_Meta_Match_registerMatchEqns___redArg___closed__1);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 5, v___x_563_);
lean_ctor_set(v___x_555_, 0, v___x_562_);
v___x_565_ = v___x_555_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_562_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v_nextMacroScope_546_);
lean_ctor_set(v_reuseFailAlloc_568_, 2, v_ngen_547_);
lean_ctor_set(v_reuseFailAlloc_568_, 3, v_auxDeclNGen_548_);
lean_ctor_set(v_reuseFailAlloc_568_, 4, v_traceState_549_);
lean_ctor_set(v_reuseFailAlloc_568_, 5, v___x_563_);
lean_ctor_set(v_reuseFailAlloc_568_, 6, v_recordedDeps_550_);
lean_ctor_set(v_reuseFailAlloc_568_, 7, v_messages_551_);
lean_ctor_set(v_reuseFailAlloc_568_, 8, v_infoState_552_);
lean_ctor_set(v_reuseFailAlloc_568_, 9, v_snapshotTasks_553_);
v___x_565_ = v_reuseFailAlloc_568_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = lean_st_ref_put(v_a_541_, v___x_565_);
v___x_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_567_, 0, v___x_559_);
return v___x_567_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_registerMatchEqns___redArg___boxed(lean_object* v_matchDeclName_571_, lean_object* v_matchEqns_572_, lean_object* v_a_573_, lean_object* v_a_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lean_Meta_Match_registerMatchEqns___redArg(v_matchDeclName_571_, v_matchEqns_572_, v_a_573_);
lean_dec(v_a_573_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_registerMatchEqns(lean_object* v_matchDeclName_576_, lean_object* v_matchEqns_577_, lean_object* v_a_578_, lean_object* v_a_579_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_Lean_Meta_Match_registerMatchEqns___redArg(v_matchDeclName_576_, v_matchEqns_577_, v_a_579_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_registerMatchEqns___boxed(lean_object* v_matchDeclName_582_, lean_object* v_matchEqns_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lean_Meta_Match_registerMatchEqns(v_matchDeclName_582_, v_matchEqns_583_, v_a_584_, v_a_585_);
lean_dec(v_a_585_);
lean_dec_ref(v_a_584_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0(lean_object* v_00_u03b2_588_, lean_object* v_x_589_, lean_object* v_x_590_, lean_object* v_x_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0___redArg(v_x_589_, v_x_590_, v_x_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3(lean_object* v_00_u03b2_593_, lean_object* v_x_594_, lean_object* v_x_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3___redArg(v_x_594_, v_x_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3___boxed(lean_object* v_00_u03b2_597_, lean_object* v_x_598_, lean_object* v_x_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3(v_00_u03b2_597_, v_x_598_, v_x_599_);
lean_dec(v_x_599_);
lean_dec_ref(v_x_598_);
return v_res_600_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Meta_Match_registerMatchEqns_spec__4(lean_object* v_xs_601_, lean_object* v_ys_602_, lean_object* v_hsz_603_, lean_object* v_x_604_, lean_object* v_x_605_){
_start:
{
uint8_t v___x_606_; 
v___x_606_ = l_Array_isEqvAux___at___00Lean_Meta_Match_registerMatchEqns_spec__4___redArg(v_xs_601_, v_ys_602_, v_x_604_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Meta_Match_registerMatchEqns_spec__4___boxed(lean_object* v_xs_607_, lean_object* v_ys_608_, lean_object* v_hsz_609_, lean_object* v_x_610_, lean_object* v_x_611_){
_start:
{
uint8_t v_res_612_; lean_object* v_r_613_; 
v_res_612_ = l_Array_isEqvAux___at___00Lean_Meta_Match_registerMatchEqns_spec__4(v_xs_607_, v_ys_608_, v_hsz_609_, v_x_610_, v_x_611_);
lean_dec_ref(v_ys_608_);
lean_dec_ref(v_xs_607_);
v_r_613_ = lean_box(v_res_612_);
return v_r_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0(lean_object* v_00_u03b2_614_, lean_object* v_x_615_, size_t v_x_616_, size_t v_x_617_, lean_object* v_x_618_, lean_object* v_x_619_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg(v_x_615_, v_x_616_, v_x_617_, v_x_618_, v_x_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___boxed(lean_object* v_00_u03b2_621_, lean_object* v_x_622_, lean_object* v_x_623_, lean_object* v_x_624_, lean_object* v_x_625_, lean_object* v_x_626_){
_start:
{
size_t v_x_1610__boxed_627_; size_t v_x_1611__boxed_628_; lean_object* v_res_629_; 
v_x_1610__boxed_627_ = lean_unbox_usize(v_x_623_);
lean_dec(v_x_623_);
v_x_1611__boxed_628_ = lean_unbox_usize(v_x_624_);
lean_dec(v_x_624_);
v_res_629_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0(v_00_u03b2_621_, v_x_622_, v_x_1610__boxed_627_, v_x_1611__boxed_628_, v_x_625_, v_x_626_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4(lean_object* v_00_u03b2_630_, lean_object* v_x_631_, size_t v_x_632_, lean_object* v_x_633_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4___redArg(v_x_631_, v_x_632_, v_x_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4___boxed(lean_object* v_00_u03b2_635_, lean_object* v_x_636_, lean_object* v_x_637_, lean_object* v_x_638_){
_start:
{
size_t v_x_1627__boxed_639_; lean_object* v_res_640_; 
v_x_1627__boxed_639_ = lean_unbox_usize(v_x_637_);
lean_dec(v_x_637_);
v_res_640_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4(v_00_u03b2_635_, v_x_636_, v_x_1627__boxed_639_, v_x_638_);
lean_dec(v_x_638_);
lean_dec_ref(v_x_636_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_641_, lean_object* v_n_642_, lean_object* v_k_643_, lean_object* v_v_644_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg(v_n_642_, v_k_643_, v_v_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_646_, size_t v_depth_647_, lean_object* v_keys_648_, lean_object* v_vals_649_, lean_object* v_heq_650_, lean_object* v_i_651_, lean_object* v_entries_652_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__3___redArg(v_depth_647_, v_keys_648_, v_vals_649_, v_i_651_, v_entries_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_654_, lean_object* v_depth_655_, lean_object* v_keys_656_, lean_object* v_vals_657_, lean_object* v_heq_658_, lean_object* v_i_659_, lean_object* v_entries_660_){
_start:
{
size_t v_depth_boxed_661_; lean_object* v_res_662_; 
v_depth_boxed_661_ = lean_unbox_usize(v_depth_655_);
lean_dec(v_depth_655_);
v_res_662_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__3(v_00_u03b2_654_, v_depth_boxed_661_, v_keys_656_, v_vals_657_, v_heq_658_, v_i_659_, v_entries_660_);
lean_dec_ref(v_vals_657_);
lean_dec_ref(v_keys_656_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4_spec__7(lean_object* v_00_u03b2_663_, lean_object* v_keys_664_, lean_object* v_vals_665_, lean_object* v_heq_666_, lean_object* v_i_667_, lean_object* v_k_668_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4_spec__7___redArg(v_keys_664_, v_vals_665_, v_i_667_, v_k_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b2_670_, lean_object* v_keys_671_, lean_object* v_vals_672_, lean_object* v_heq_673_, lean_object* v_i_674_, lean_object* v_k_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_registerMatchEqns_spec__3_spec__4_spec__7(v_00_u03b2_670_, v_keys_671_, v_vals_672_, v_heq_673_, v_i_674_, v_k_675_);
lean_dec(v_k_675_);
lean_dec_ref(v_vals_672_);
lean_dec_ref(v_keys_671_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_677_, lean_object* v_x_678_, lean_object* v_x_679_, lean_object* v_x_680_, lean_object* v_x_681_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2_spec__6___redArg(v_x_678_, v_x_679_, v_x_680_, v_x_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getEquationsFor___boxed(lean_object* v_matchDeclName_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_00___x40___internal___hyg_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = lean_get_match_equations_for(v_matchDeclName_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_genMatchCongrEqns___boxed(lean_object* v_matchDeclName_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_00___x40___internal___hyg_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = lean_get_congr_match_equations_for(v_matchDeclName_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_);
return v_res_708_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_709_, lean_object* v_i_710_, lean_object* v_k_711_){
_start:
{
lean_object* v___x_712_; uint8_t v___x_713_; 
v___x_712_ = lean_array_get_size(v_keys_709_);
v___x_713_ = lean_nat_dec_lt(v_i_710_, v___x_712_);
if (v___x_713_ == 0)
{
lean_dec(v_i_710_);
return v___x_713_;
}
else
{
lean_object* v_k_x27_714_; uint8_t v___x_715_; 
v_k_x27_714_ = lean_array_fget_borrowed(v_keys_709_, v_i_710_);
v___x_715_ = lean_name_eq(v_k_711_, v_k_x27_714_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = lean_unsigned_to_nat(1u);
v___x_717_ = lean_nat_add(v_i_710_, v___x_716_);
lean_dec(v_i_710_);
v_i_710_ = v___x_717_;
goto _start;
}
else
{
lean_dec(v_i_710_);
return v___x_713_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_719_, lean_object* v_i_720_, lean_object* v_k_721_){
_start:
{
uint8_t v_res_722_; lean_object* v_r_723_; 
v_res_722_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1___redArg(v_keys_719_, v_i_720_, v_k_721_);
lean_dec(v_k_721_);
lean_dec_ref(v_keys_719_);
v_r_723_ = lean_box(v_res_722_);
return v_r_723_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0___redArg(lean_object* v_x_724_, size_t v_x_725_, lean_object* v_x_726_){
_start:
{
if (lean_obj_tag(v_x_724_) == 0)
{
lean_object* v_es_727_; lean_object* v___x_728_; size_t v___x_729_; size_t v___x_730_; lean_object* v_j_731_; lean_object* v___x_732_; 
v_es_727_ = lean_ctor_get(v_x_724_, 0);
v___x_728_ = lean_box(2);
v___x_729_ = ((size_t)31ULL);
v___x_730_ = lean_usize_land(v_x_725_, v___x_729_);
v_j_731_ = lean_usize_to_nat(v___x_730_);
v___x_732_ = lean_array_get_borrowed(v___x_728_, v_es_727_, v_j_731_);
lean_dec(v_j_731_);
switch(lean_obj_tag(v___x_732_))
{
case 0:
{
lean_object* v_key_733_; uint8_t v___x_734_; 
v_key_733_ = lean_ctor_get(v___x_732_, 0);
v___x_734_ = lean_name_eq(v_x_726_, v_key_733_);
return v___x_734_;
}
case 1:
{
lean_object* v_node_735_; size_t v___x_736_; size_t v___x_737_; 
v_node_735_ = lean_ctor_get(v___x_732_, 0);
v___x_736_ = ((size_t)5ULL);
v___x_737_ = lean_usize_shift_right(v_x_725_, v___x_736_);
v_x_724_ = v_node_735_;
v_x_725_ = v___x_737_;
goto _start;
}
default: 
{
uint8_t v___x_739_; 
v___x_739_ = 0;
return v___x_739_;
}
}
}
else
{
lean_object* v_ks_740_; lean_object* v___x_741_; uint8_t v___x_742_; 
v_ks_740_ = lean_ctor_get(v_x_724_, 0);
v___x_741_ = lean_unsigned_to_nat(0u);
v___x_742_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1___redArg(v_ks_740_, v___x_741_, v_x_726_);
return v___x_742_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0___redArg___boxed(lean_object* v_x_743_, lean_object* v_x_744_, lean_object* v_x_745_){
_start:
{
size_t v_x_299__boxed_746_; uint8_t v_res_747_; lean_object* v_r_748_; 
v_x_299__boxed_746_ = lean_unbox_usize(v_x_744_);
lean_dec(v_x_744_);
v_res_747_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0___redArg(v_x_743_, v_x_299__boxed_746_, v_x_745_);
lean_dec(v_x_745_);
lean_dec_ref(v_x_743_);
v_r_748_ = lean_box(v_res_747_);
return v_r_748_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0___redArg(lean_object* v_x_749_, lean_object* v_x_750_){
_start:
{
uint64_t v___y_752_; 
if (lean_obj_tag(v_x_750_) == 0)
{
uint64_t v___x_755_; 
v___x_755_ = 1723ULL;
v___y_752_ = v___x_755_;
goto v___jp_751_;
}
else
{
uint64_t v_hash_756_; 
v_hash_756_ = lean_ctor_get_uint64(v_x_750_, sizeof(void*)*2);
v___y_752_ = v_hash_756_;
goto v___jp_751_;
}
v___jp_751_:
{
size_t v___x_753_; uint8_t v___x_754_; 
v___x_753_ = lean_uint64_to_usize(v___y_752_);
v___x_754_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0___redArg(v_x_749_, v___x_753_, v_x_750_);
return v___x_754_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0___redArg___boxed(lean_object* v_x_757_, lean_object* v_x_758_){
_start:
{
uint8_t v_res_759_; lean_object* v_r_760_; 
v_res_759_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0___redArg(v_x_757_, v_x_758_);
lean_dec(v_x_758_);
lean_dec_ref(v_x_757_);
v_r_760_ = lean_box(v_res_759_);
return v_r_760_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Match_isMatchEqnTheorem(lean_object* v_env_763_, lean_object* v_declName_764_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_Lean_Name_eraseMacroScopes(v_declName_764_);
if (lean_obj_tag(v___x_765_) == 1)
{
lean_object* v_str_766_; uint8_t v___x_767_; 
v_str_766_ = lean_ctor_get(v___x_765_, 1);
lean_inc_ref(v_str_766_);
lean_dec_ref_known(v___x_765_, 2);
v___x_767_ = l_Lean_Meta_isEqnLikeSuffix(v_str_766_);
if (v___x_767_ == 0)
{
lean_dec(v_declName_764_);
lean_dec_ref(v_env_763_);
return v___x_767_;
}
else
{
lean_object* v___x_768_; uint8_t v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v_eqns_773_; uint8_t v___x_774_; 
v___x_768_ = l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default;
v___x_769_ = 0;
v___x_770_ = l_Lean_Meta_Match_matchEqnsExt;
v___x_771_ = ((lean_object*)(l_Lean_Meta_Match_isMatchEqnTheorem___closed__0));
lean_inc(v_declName_764_);
v___x_772_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_768_, v___x_770_, v_env_763_, v___x_771_, v_declName_764_, v___x_769_);
v_eqns_773_ = lean_ctor_get(v___x_772_, 1);
lean_inc_ref(v_eqns_773_);
lean_dec(v___x_772_);
v___x_774_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0___redArg(v_eqns_773_, v_declName_764_);
lean_dec(v_declName_764_);
lean_dec_ref(v_eqns_773_);
return v___x_774_;
}
}
else
{
uint8_t v___x_775_; 
lean_dec(v___x_765_);
lean_dec(v_declName_764_);
lean_dec_ref(v_env_763_);
v___x_775_ = 0;
return v___x_775_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_isMatchEqnTheorem___boxed(lean_object* v_env_776_, lean_object* v_declName_777_){
_start:
{
uint8_t v_res_778_; lean_object* v_r_779_; 
v_res_778_ = l_Lean_Meta_Match_isMatchEqnTheorem(v_env_776_, v_declName_777_);
v_r_779_ = lean_box(v_res_778_);
return v_r_779_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0(lean_object* v_00_u03b2_780_, lean_object* v_x_781_, lean_object* v_x_782_){
_start:
{
uint8_t v___x_783_; 
v___x_783_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0___redArg(v_x_781_, v_x_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0___boxed(lean_object* v_00_u03b2_784_, lean_object* v_x_785_, lean_object* v_x_786_){
_start:
{
uint8_t v_res_787_; lean_object* v_r_788_; 
v_res_787_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0(v_00_u03b2_784_, v_x_785_, v_x_786_);
lean_dec(v_x_786_);
lean_dec_ref(v_x_785_);
v_r_788_ = lean_box(v_res_787_);
return v_r_788_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0(lean_object* v_00_u03b2_789_, lean_object* v_x_790_, size_t v_x_791_, lean_object* v_x_792_){
_start:
{
uint8_t v___x_793_; 
v___x_793_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0___redArg(v_x_790_, v_x_791_, v_x_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0___boxed(lean_object* v_00_u03b2_794_, lean_object* v_x_795_, lean_object* v_x_796_, lean_object* v_x_797_){
_start:
{
size_t v_x_391__boxed_798_; uint8_t v_res_799_; lean_object* v_r_800_; 
v_x_391__boxed_798_ = lean_unbox_usize(v_x_796_);
lean_dec(v_x_796_);
v_res_799_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0(v_00_u03b2_794_, v_x_795_, v_x_391__boxed_798_, v_x_797_);
lean_dec(v_x_797_);
lean_dec_ref(v_x_795_);
v_r_800_ = lean_box(v_res_799_);
return v_r_800_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_801_, lean_object* v_keys_802_, lean_object* v_vals_803_, lean_object* v_heq_804_, lean_object* v_i_805_, lean_object* v_k_806_){
_start:
{
uint8_t v___x_807_; 
v___x_807_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1___redArg(v_keys_802_, v_i_805_, v_k_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_808_, lean_object* v_keys_809_, lean_object* v_vals_810_, lean_object* v_heq_811_, lean_object* v_i_812_, lean_object* v_k_813_){
_start:
{
uint8_t v_res_814_; lean_object* v_r_815_; 
v_res_814_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1(v_00_u03b2_808_, v_keys_809_, v_vals_810_, v_heq_811_, v_i_812_, v_k_813_);
lean_dec(v_k_813_);
lean_dec_ref(v_vals_810_);
lean_dec_ref(v_keys_809_);
v_r_815_ = lean_box(v_res_814_);
return v_r_815_;
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
